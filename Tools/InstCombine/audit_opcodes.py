#!/usr/bin/env python3
"""Advisory comparison of explicit C++ constructors with output opcode fields.

An enclosing source span may include other branches, and IRBuilder can fold
constants. Consequently these are review candidates, never automatic edits.
"""
from __future__ import annotations
import json
import re
from pathlib import Path
from build_catalog import load_inventory

DOC = Path(__file__).resolve().parents[2] / 'docs/instcombine'
DIRECT = {
    'Neg': 'sub', 'Not': 'xor', 'DisjointOr': 'or',
    'GetElementPtr': 'getelementptr', 'PHINode': 'phi',
    'Return': 'ret', 'Branch': 'br', 'Switch': 'switch', 'Unreachable': 'unreachable',
    'IsNull': 'icmp', 'IsNotNull': 'icmp', 'IsNeg': 'icmp', 'IsNotNeg': 'icmp',
    'GEP': 'getelementptr', 'InBoundsGEP': 'getelementptr',
    'PtrAdd': 'getelementptr', 'InBoundsPtrAdd': 'getelementptr',
    'BinaryIntrinsic': 'call', 'UnaryIntrinsic': 'call', 'Intrinsic': 'call',
    'FAbs': 'call', 'CopySign': 'call', 'Ldexp': 'call', 'VectorReverse': 'call',
    'VScale': 'call', 'AndReduce': 'call', 'OrReduce': 'call', 'AddReduce': 'call',
    'NonTerminatorUnreachable': 'store',
    'AlignedLoad': 'load', 'AlignedStore': 'store',
    'LogicalAnd': 'select', 'LogicalOr': 'select',
    'CallBr': 'callbr', 'LandingPad': 'landingpad',
    'CondBr': 'br', 'UncondBr': 'br',
    'IsFPClass': 'call', 'Assumption': 'call',
    'AlignmentAssumption': 'call', 'NonnullAssumption': 'call',
    'LaunderInvariantGroup': 'call', 'MaskedLoad': 'call',
    'MemSet': 'call', 'MemTransferInst': 'call', 'InsertVector': 'call',
}
SIMPLE = '''Add Sub Mul UDiv SDiv URem SRem Shl LShr AShr And Or Xor
FNeg FAdd FSub FMul FDiv FRem Trunc ZExt SExt FPTrunc FPExt FPToUI FPToSI
UIToFP SIToFP PtrToInt PtrToAddr IntToPtr BitCast AddrSpaceCast ICmp FCmp
Select Freeze Call Invoke PHI Load Store Alloca ExtractElement InsertElement
ShuffleVector ExtractValue InsertValue'''.split()
DIRECT.update({name: name.lower() for name in SIMPLE})
TOKEN = re.compile(r'\b[Cc]reate([A-Z]\w*)\s*\(|\bnew\s+([A-Z]\w*)Inst\s*\('
                   r'|\b([A-Z]\w*)Inst::Create\s*\(|\b(PHINode)::Create\s*\(')

GENERIC = re.compile(
    r'\b(?:(?:CastInst|BinaryOperator|UnaryOperator|CmpInst)::Create(?:Exact|NSW|NUW|WithCopiedFlags)?|'
    r'(?:[A-Za-z_]\w*\.)?Create(?:Cast|BinOp|UnOp|ExactBinOp|NoWrapBinOp))\s*\(\s*'
    r'Instruction::([A-Z]\w*)')

def opcode(name):
    name = re.sub(r'(?:FMF)?WithUnknownProfile$', '', name)
    name = re.sub(r'FMF$', '', name)
    name = re.sub(r'Inst$', '', name)
    name = re.sub(r'^(?:NSW|NUW|Exact)', '', name)
    if re.fullmatch(r'[IF]Cmp(?:EQ|NE|U?GT|U?GE|U?LT|U?LE|SGT|SGE|SLT|SLE|OEQ|ONE|UEQ|UNE|UNO|ORD)', name):
        return 'icmp' if name.startswith('I') else 'fcmp'
    return DIRECT.get(name)

def main():
    entries = [e for e in load_inventory() if e.get('kind', 'rewrite') in
               ('rewrite', 'mutation', 'metadata-mutation')]
    findings = []
    constructors = 0
    for path in sorted((DOC / 'source').glob('*.cpp')):
        # Remove comments without changing line numbers.
        source = re.sub(r'/\*.*?\*/|//[^\n]*',
                        lambda m: '\n' * m.group().count('\n'),
                        path.read_text(), flags=re.S)
        local = [e for e in entries if e['file'] == path.name]
        lines = source.splitlines()
        sites = []
        for match in TOKEN.finditer(source):
            name = next(group for group in match.groups() if group)
            sites.append((match, opcode(name)))
        for match in GENERIC.finditer(source):
            sites.append((match, opcode(match.group(1))))
        for match, op in sorted(sites, key=lambda item: item[0].start()):
            if op is None:
                continue
            lineno = source.count('\n', 0, match.start()) + 1
            line = lines[lineno - 1]
            constructors += 1
            covered = [e for e in local if e['line_start'] <= lineno <= e['line_end']]
            missing = [e['id'] for e in covered if op not in e['rewrite_opcodes']]
            if missing:
                findings.append({'file': path.name, 'line': lineno,
                    'constructor': match.group().strip(), 'opcode': op,
                    'inventory_ids_missing_opcode': missing,
                    'source': line.strip()})
    result = {'description': __doc__.strip(), 'recognized_constructor_sites': constructors,
              'candidate_sites': len(findings), 'findings': findings}
    (DOC / 'opcode-audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'{len(findings)} constructor sites need opcode/span/folding review; no entries changed.')

if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

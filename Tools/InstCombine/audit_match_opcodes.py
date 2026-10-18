#!/usr/bin/env python3
"""Find explicit PatternMatch opcodes absent from enclosing inventory match lists.

This is advisory: a source span can include sibling guards, and generic helpers
or ConstantExpr patterns need human interpretation. It does not edit entries.
"""
import json
import re
from pathlib import Path
from build_catalog import load_inventory

DOC = Path(__file__).resolve().parents[2] / 'docs/instcombine'
OPCODES = {name: name.lower() for name in '''Add Sub Mul UDiv SDiv URem SRem
Shl LShr AShr And Or Xor FNeg FAdd FSub FMul FDiv FRem Trunc ZExt SExt FPTrunc
FPExt FPToUI FPToSI UIToFP SIToFP PtrToInt PtrToAddr IntToPtr BitCast AddrSpaceCast
ICmp FCmp Select Freeze ExtractElement InsertElement ShuffleVector ExtractValue
InsertValue'''.split()}
OPCODES.update(Not='xor', Neg='sub', GEP='getelementptr', Intrinsic='call')
PATTERN = re.compile(r'\bm_((?:c_)?[A-Z]\w*)\s*(?:\(|<)')

def main():
    entries = [e for e in load_inventory() if e.get('kind', 'rewrite') in
               ('rewrite', 'mutation', 'metadata-mutation')]
    findings = []
    sites = 0
    for path in sorted((DOC / 'source').glob('*.cpp')):
        source = re.sub(r'/\*.*?\*/|//[^\n]*',
                        lambda m: '\n' * m.group().count('\n'),
                        path.read_text(), flags=re.S)
        local = [e for e in entries if e['file'] == path.name]
        for lineno, line in enumerate(source.splitlines(), 1):
            for match in PATTERN.finditer(line):
                name = re.sub(r'^c_', '', match.group(1))
                name = re.sub(r'^(?:NSW|NUW|Exact|Disjoint)', '', name)
                op = OPCODES.get(name)
                if op is None:
                    continue
                sites += 1
                missing = [e for e in local if e['line_start'] <= lineno <= e['line_end']
                           and op not in e['match_opcodes']]
                if missing:
                    findings.append({'file': path.name, 'line': lineno,
                        'matcher': match.group().strip(), 'opcode': op,
                        'inventory_ids_missing_opcode': [e['id'] for e in missing],
                        'source': line.strip()})
    result = {'description': __doc__.strip(), 'recognized_matcher_sites': sites,
              'candidate_sites': len(findings), 'findings': findings}
    (DOC / 'match-opcode-audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'{len(findings)} matcher sites need source-guard/span review; no entries changed.')

if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

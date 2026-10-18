#!/usr/bin/env python3
"""Find listed replacement opcodes not explained by direct constructors in an entry.

This is advisory. Helpers, retained operations, mutation, and constructors outside
an entry's span can explain a candidate. APInt/ConstantExpr computations do not
by themselves create runtime instructions. Never remove an opcode automatically.
"""
from __future__ import annotations
import argparse
import json
import re
from audit_opcodes import TOKEN, opcode
from build_catalog import DOC, load_inventory


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    candidates = []
    sources = {}
    for entry in load_inventory():
        if entry.get('kind', 'rewrite') not in ('rewrite', 'mutation', 'metadata-mutation'):
            continue
        if not entry['rewrite_opcodes'] or entry.get('rewrite_opcode_parameter'):
            continue
        name = entry['file']
        if name not in sources:
            sources[name] = (DOC / 'source' / name).read_text().splitlines()
        source = '\n'.join(sources[name][entry['line_start'] - 1:entry['line_end']])
        uncommented = re.sub(r'/\*.*?\*/|//[^\n]*', '', source, flags=re.S)
        # Unknown constructor opcodes would swamp this deliberately narrow audit.
        if re.search(r'Create(?:BinOp|Cast|Intrinsic|BinaryIntrinsic|UnaryIntrinsic|UnOp)|'
                     r'(?:BinaryOperator|CastInst|CmpInst)::Create\s*\(', uncommented):
            continue
        recognized = {opcode(next(g for g in match.groups() if g))
                      for match in TOKEN.finditer(uncommented)} - {None}
        extra = set(entry['rewrite_opcodes']) - recognized
        if not recognized or not extra:
            continue
        candidates.append({
            'inventory_id': entry['id'], 'file': name,
            'line_start': entry['line_start'], 'line_end': entry['line_end'],
            'listed_replacement_opcodes': entry['rewrite_opcodes'],
            'recognized_constructor_opcodes': sorted(recognized),
            'opcodes_needing_review': sorted(extra),
            'description': entry['description'],
            'source': source,
        })
    report = {'description': __doc__.strip(), 'candidate_count': len(candidates),
              'candidates': candidates}
    (DOC / 'extra-output-opcode-audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'{len(candidates)} entries need helper/mutation/constant-folding review; no entries changed.')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Advisory review of LLVM compound/alias matchers against inventory opcodes.

Mappings were checked against llvm/IR/PatternMatch.h at the audit's pinned
commit. An alias can include alternatives excluded by surrounding guards,
so findings are candidates only and never change inventory automatically.
"""
import json
import re
from pathlib import Path
from build_catalog import load_inventory
from audit_match_opcodes import PATTERN

DOC = Path(__file__).resolve().parents[2] / 'docs/instcombine'
ALIASES = {
    'AddLike': ['add', 'or'], 'SExtLike': ['sext', 'zext'],
    'SExtOrSelf': ['sext'], 'ZExtOrSelf': ['zext'],
    'ZExtOrSExt': ['zext', 'sext'], 'ZExtOrSExtOrSelf': ['zext', 'sext'],
    'TruncOrSelf': ['trunc'], 'ZExtOrTruncOrSelf': ['zext', 'trunc'],
    'ShlOrSelf': ['shl'], 'NNegZExt': ['zext'],
    'Shr': ['lshr', 'ashr'], 'Shift': ['shl', 'lshr', 'ashr'],
    'LogicalShift': ['shl', 'lshr'], 'BitwiseLogic': ['and', 'or', 'xor'],
    'LogicalAnd': ['and', 'select'], 'LogicalOr': ['or', 'select'],
    'LogicalOp': ['and', 'or', 'select'], 'ICmpLike': ['icmp', 'trunc'],
    'SelectLike': ['select', 'zext', 'sext'],
    'IDiv': ['sdiv', 'udiv'], 'IRem': ['srem', 'urem'],
    'IToFP': ['uitofp', 'sitofp'], 'FPToI': ['fptoui', 'fptosi'],
    'Cmp': ['icmp', 'fcmp'], 'SpecificCmp': ['icmp', 'fcmp'],
    'SpecificICmp': ['icmp'], 'SpecificFCmp': ['fcmp'],
    'ElementWiseBitCast': ['bitcast'], 'PtrToIntSameSize': ['ptrtoint'],
    'PtrToIntOrAddr': ['ptrtoint', 'ptrtoaddr'], 'PtrAdd': ['getelementptr'],
    'ExtractElt': ['extractelement'], 'InsertElt': ['insertelement'],
    'Shuffle': ['shufflevector'], 'Load': ['load'],
    'NotForbidPoison': ['xor'],
    'Signum': ['ashr', 'lshr', 'sub', 'or'],
    'OrdOrUnordFMax': ['select', 'fcmp'],
    'OrdOrUnordFMin': ['select', 'fcmp'],
    'Br': ['br'], 'UnconditionalBr': ['br'],
}
for name in '''BSwap BitReverse CopySign Ctlz Cttz Ctpop Deinterleave2 FAbs
FCanonicalize FShl FShr MaskedGather MaskedLoad MaxOrMin SMax SMin UMax UMin
Sqrt VScale VecReverse VectorInsert WithOverflowInst AddRdx FaddRdx'''.split():
    ALIASES[name] = ['call']


ALIASES['UAddWithOverflow'] = ['icmp', 'add', 'xor']

def main():
    entries = [e for e in load_inventory() if e.get('kind', 'rewrite') in
               ('rewrite', 'mutation', 'metadata-mutation')]
    rows = []
    recognized = 0
    for path in sorted((DOC / 'source').glob('*.cpp')):
        source = re.sub(r'/\*.*?\*/|//[^\n]*',
                        lambda m: '\n' * m.group().count('\n'),
                        path.read_text(), flags=re.S)
        local = [e for e in entries if e['file'] == path.name]
        for lineno, line in enumerate(source.splitlines(), 1):
            for match in PATTERN.finditer(line):
                name = re.sub(r'^c_', '', match.group(1))
                name = re.sub(r'^(?:NSW|NUW|Exact|Disjoint)', '', name)
                ops = ALIASES.get(name)
                if ops is None:
                    continue
                recognized += 1
                for e in local:
                    if not e['line_start'] <= lineno <= e['line_end']:
                        continue
                    missing = sorted(set(ops) - set(e['match_opcodes']))
                    if missing:
                        rows.append({'inventory_id': e['id'], 'file': path.name,
                            'line': lineno, 'matcher': match.group().strip(),
                            'missing_possible_opcodes': missing, 'source': line.strip()})
    review_path = DOC / 'match-alias-review.json'
    reviews = json.loads(review_path.read_text())['reviews'] if review_path.exists() else []
    review_by_key = {(r['inventory_id'], r['file'], r['line'], r['matcher']): r for r in reviews}
    for row in rows:
        key = (row['inventory_id'], row['file'], row['line'], row['matcher'])
        review = review_by_key.get(key)
        if review and set(row['missing_possible_opcodes']) <= set(review['excluded_opcodes']):
            row['reviewed_exclusion'] = review['reason']
    unresolved = sum('reviewed_exclusion' not in row for row in rows)
    pin = json.loads((DOC / 'llvm-pin.json').read_text())
    result = {'description': __doc__.strip(),
              'matcher_definitions': f"https://github.com/llvm/llvm-project/blob/{pin['commit']}/llvm/include/llvm/IR/PatternMatch.h",
              'recognized_alias_sites': recognized, 'candidate_count': len(rows),
              'unreviewed_candidates': unresolved,
              'findings': rows}
    (DOC / 'match-alias-audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'{len(rows)} alias matcher candidates, {unresolved} unreviewed; no inventory changes.')

if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

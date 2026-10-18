#!/usr/bin/env python3
"""Flag direct analysis calls in entries currently marked analysis-free.

This is advisory: a call on constants may need no SSA analysis, and calls through
helpers or guards outside an entry's source span require separate manual review.
"""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/instcombine'
ANALYSIS = re.compile(
    r'\b(?:computeKnownBits|ComputeNumSignBits|computeConstantRange|'
    r'computeOverflowFor\w+|willNotOverflow\w+|isKnown\w+|'
    r'isGuaranteedNotToBe\w+|isGuaranteedToTransferExecutionToSuccessor|'
    r'isImpliedCondition|isImpliedByDomCondition|isImpliedByDomConditions|'
    r'isSafeToSpeculativelyExecute|isDereferenceable\w*|'
    r'getKnownAlignment|haveNoCommonBitsSet|isNeverPoison)\s*\('
)


def main():
    report = []
    for path in sorted((DOC / 'inventory').glob('*.json')):
        if path.name.endswith('-coverage.json'):
            continue
        for entry in json.loads(path.read_text()):
            if entry['uses_analysis']:
                continue
            lines = (DOC / 'source' / entry['file']).read_text().splitlines()
            hits = []
            for i in range(entry['line_start'] - 1, entry['line_end']):
                code = lines[i].split('//', 1)[0]
                for match in ANALYSIS.finditer(code):
                    hits.append({'line': i + 1, 'call': match.group().rstrip(' (')})
            if hits:
                report.append({'inventory': path.name, 'id': entry['id'],
                               'file': entry['file'], 'hits': hits,
                               'review_note': entry.get('analysis_audit_note')})
    (DOC / 'analysis-guard-audit.json').write_text(json.dumps(report, indent=2) + '\n')
    unreviewed = sum(not row['review_note'] for row in report)
    print(f'{len(report)} entries contain direct analysis-like calls; {unreviewed} lack a recorded review note. No statuses changed.')


if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

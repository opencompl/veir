#!/usr/bin/env python3
"""Reconcile source-site coverage and explicit exclusions with reviewer claims.

A fully mapped checklist is necessary, not sufficient, for exhaustive coverage.
The manual audit's complete flag is also required; this never infers it from ranges.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/instcombine'


def coverage_report(sites, entries=None):
    """Reconcile supplied candidates against current human audit records."""
    if entries is None:
        entries = []
        for path in (DOC / 'inventory').glob('*.json'):
            if not path.name.endswith('-coverage.json'):
                entries.extend(json.loads(path.read_text()))
    incomplete = {}
    for entry in entries:
        if entry.get('kind') == 'incomplete-family':
            incomplete.setdefault(entry['file'], []).append(entry['id'])
    excluded = {}
    for path in DOC.glob('site-exclusions-*.json'):
        for item in json.loads(path.read_text()):
            if not item.get('reason'):
                raise ValueError(f'{path}: exclusion without reason')
            if item.get('reviewed', True):
                excluded[item['file'], item['line']] = item['reason']
    claims = {}
    for path in (DOC / 'inventory').glob('*-coverage.json'):
        data = json.loads(path.read_text())
        for name, claim in data.get('files', {}).items():
            claims.setdefault(name, []).append(claim)
        for item in data.get('scope', []):
            claims.setdefault(item['file'], []).append(item)
    pin = json.loads((DOC / 'llvm-pin.json').read_text())
    report = []
    for item in pin['files']:
        name = item['name']
        if name in ('CMakeLists.txt', 'InstCombineCLOptions.cpp', 'InstCombineCLOptions.h', 'InstCombineCLOptions.td'):
            report.append({'file': name, 'complete': True, 'reason': 'Build configuration or command-line option declarations; no rewrite definitions.'})
            continue
        local = [s for s in sites if s['file'] == name]
        uncovered = [s['line'] for s in local if not s['inventory_ids'] and (name, s['line']) not in excluded]
        local_claims = claims.get(name, [])
        claimed = any(c.get('complete', False) for c in local_claims)
        reviewed_ranges = sorted(r for c in local_claims if c.get('range_complete', False)
                                 for r in c.get('covered_ranges', []))
        reviewed_through = 0
        for start, end in reviewed_ranges:
            if start > reviewed_through + 1:
                break
            reviewed_through = max(reviewed_through, end)
        line_count = len((DOC / 'source' / name).read_text().splitlines())
        claimed = claimed or reviewed_through >= line_count
        report.append({'file': name, 'manual_audit_complete': claimed, 'candidate_sites': len(local), 'completed_range_union_through': reviewed_through,
                       'unresolved_sites': uncovered, 'incomplete_family_ids': incomplete.get(name, []),
                       'complete': claimed and not uncovered and not incomplete.get(name)})
    return report


def main():
    sites = json.loads((DOC / 'candidate-sites.json').read_text())
    report = coverage_report(sites)
    (DOC / 'coverage-report.json').write_text(json.dumps(report, indent=2) + '\n')
    complete = [r['file'] for r in report if r['complete']]
    unresolved = sum(len(r.get('unresolved_sites', [])) for r in report)
    print(f'{len(complete)}/{len(report)} source files reconciled; {unresolved} unclassified candidate sites.')
    print('Reconciled: ' + ', '.join(complete))


if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

#!/usr/bin/env python3
"""Advisory checks for stale entry spans and overlapping rewrite records.

No-site entries can be legitimate branch bodies sharing a final return, or
metadata mutations absent from the heuristic. Overlap can also be intentional.
Neither diagnostic changes statuses or establishes source completeness.
"""
import json
from pathlib import Path
from build_catalog import load_inventory, candidate_sites

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/instcombine'


def main():
    entries = [e for e in load_inventory()
               if e.get('kind', 'rewrite') in ('rewrite', 'mutation', 'metadata-mutation')]
    sites = candidate_sites()
    mapped = set()
    overlapping = []
    for site in sites:
        ids = [e['id'] for e in entries if e['file'] == site['file']
               and e['line_start'] <= site['line'] <= e['line_end']]
        mapped.update(ids)
        if len(ids) > 1:
            overlapping.append({**site, 'inventory_ids': ids})
    no_site = [{'id': e['id'], 'file': e['file'],
                'range': [e['line_start'], e['line_end']], 'description': e['description']}
               for e in entries if e['id'] not in mapped]
    report = {'entries_without_candidate_site': no_site,
              'sites_with_multiple_rewrite_entries': overlapping}
    (DOC / 'entry-sites-audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'{len(no_site)} rewrite entries have no heuristic site; '
          f'{len(overlapping)} sites map to multiple rewrite entries. Review required; no statuses changed.')


if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

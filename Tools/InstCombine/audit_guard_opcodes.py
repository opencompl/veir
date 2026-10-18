#!/usr/bin/env python3
"""Advisory opcode review of enclosing C++ if-guards outside source entry spans.

Uses optional tree-sitter==0.25.2 and tree-sitter-cpp==0.23.4. It complements the
span-local matcher audit: many inventory references name only a return statement.
Negative/exclusion guards, sibling spans and constant expressions need review.
"""
import json
import re
from pathlib import Path
from tree_sitter import Language, Parser
import tree_sitter_cpp
from build_catalog import load_inventory
from audit_match_opcodes import OPCODES, PATTERN
from audit_match_aliases import ALIASES
from audit_analysis_guards import ANALYSIS

DOC = Path(__file__).resolve().parents[2] / 'docs/instcombine'

def main():
    parser = Parser(Language(tree_sitter_cpp.language()))
    entries = [e for e in load_inventory() if e.get('kind', 'rewrite') in
               ('rewrite', 'mutation', 'metadata-mutation')]
    findings = {}
    analysis_findings = {}
    for path in sorted((DOC / 'source').glob('*.cpp')):
        local = [e for e in entries if e['file'] == path.name]
        if not local:
            continue
        data = path.read_bytes()
        tree = parser.parse(data)
        stack = [tree.root_node]
        while stack:
            node = stack.pop()
            stack.extend(node.named_children)
            if node.type != 'return_statement':
                continue
            body = data[node.start_byte:node.end_byte].decode()
            if re.fullmatch(r'return\s+(?:nullptr|false|true|0|std::nullopt)\s*;', body):
                continue
            line = node.start_point.row + 1
            covered = [e for e in local if e['line_start'] <= line <= e['line_end']]
            if not covered:
                continue
            parent = node.parent
            while parent is not None and parent.type != 'function_definition':
                if parent.type == 'if_statement':
                    guard = parent.child_by_field_name('condition')
                    if guard is not None:
                        text = data[guard.start_byte:guard.end_byte].decode()
                        for call in ANALYSIS.finditer(text):
                            call_line = guard.start_point.row + 1 + text[:call.start()].count('\n')
                            for e in covered:
                                if e['uses_analysis'] or e['line_start'] <= call_line <= e['line_end']:
                                    continue
                                key = (e['id'], call_line, call.group())
                                analysis_findings[key] = {'inventory_id': e['id'], 'file': path.name,
                                    'return_line': line, 'guard_line': call_line,
                                    'call': call.group().strip(), 'guard': text.strip(),
                                    'review_note': e.get('analysis_audit_note')}
                        alternative = parent.child_by_field_name('alternative')
                        for match in PATTERN.finditer(text):
                            # An ancestor's failed if-condition is not a positive
                            # match requirement for a return in its else arm.
                            if alternative is not None and alternative.start_byte <= node.start_byte < alternative.end_byte:
                                continue
                            name = re.sub(r'^c_', '', match.group(1))
                            name = re.sub(r'^(?:NSW|NUW|Exact|Disjoint)', '', name)
                            ops = [OPCODES[name]] if name in OPCODES else ALIASES.get(name, [])
                            match_line = guard.start_point.row + 1 + text[:match.start()].count('\n')
                            for op in ops:
                                for e in covered:
                                    if op in e['match_opcodes'] or e['line_start'] <= match_line <= e['line_end']:
                                        continue
                                    key = (e['id'], match_line, op)
                                    findings[key] = {'inventory_id': e['id'], 'file': path.name,
                                        'return_line': line, 'guard_line': match_line,
                                        'matcher': match.group().strip(), 'opcode': op,
                                        'guard': text.strip()}
                parent = parent.parent
    rows = sorted(findings.values(), key=lambda r:(r['file'],r['guard_line'],r['inventory_id']))
    (DOC / 'guard-opcode-audit.json').write_text(json.dumps({
        'description': __doc__.strip(), 'findings': rows,
        'candidate_count':len(rows)}, indent=2) + '\n')
    analysis_rows = sorted(analysis_findings.values(), key=lambda r:(r['file'],r['guard_line'],r['inventory_id']))
    (DOC / 'enclosing-analysis-audit.json').write_text(json.dumps({
        'description': 'Analysis-like calls in enclosing if-guards outside entry spans marked uses_analysis=false. Advisory only; constant calls and exclusion conditions require source review.',
        'findings': analysis_rows, 'candidate_count': len(analysis_rows)}, indent=2) + '\n')
    print(f'{len(rows)} enclosing-guard opcode candidates; {len(analysis_rows)} analysis candidates; no entries changed.')

if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

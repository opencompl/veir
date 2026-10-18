#!/usr/bin/env python3
"""Cross-check inventory function names against C++ syntax, without LLVM headers.

Optional dependencies: tree-sitter==0.25.2, tree-sitter-cpp==0.23.4.
This reports mismatches; it never rewrites hand-reviewed inventory descriptions.
"""
import json
from pathlib import Path
from tree_sitter import Language, Parser
import tree_sitter_cpp

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/instcombine'


def main():
    language = Language(tree_sitter_cpp.language())
    parser = Parser(language)
    index = []
    for source in sorted((DOC / 'source').glob('*')):
        if source.suffix not in ('.h', '.cpp'):
            continue
        data = source.read_bytes()
        tree = parser.parse(data)
        stack = [tree.root_node]
        while stack:
            node = stack.pop()
            if node.type == 'function_definition':
                declarator = node.child_by_field_name('declarator')
                while declarator is not None and declarator.type != 'function_declarator':
                    declarator = declarator.child_by_field_name('declarator')
                if declarator is not None:
                    name = declarator.child_by_field_name('declarator')
                    index.append({'file': source.name, 'name': data[name.start_byte:name.end_byte].decode(),
                                  'line_start': node.start_point.row + 1,
                                  'line_end': node.end_point.row + 1, 'parse_error': node.has_error})
            stack.extend(node.named_children)
    (DOC / 'function-index.json').write_text(json.dumps(index, indent=2) + '\n')
    errors = []
    boundaries = []
    for path in sorted((DOC / 'inventory').glob('*.json')):
        if path.name.endswith('coverage.json'):
            continue
        for entry in json.loads(path.read_text()):
            functions = [f for f in index if f['file'] == entry['file'] and
                         f['line_start'] <= entry['line_end'] and f['line_end'] >= entry['line_start']]
            if len(functions) > 1:
                boundaries.append({'id': entry['id'], 'file': entry['file'],
                                   'range': [entry['line_start'], entry['line_end']],
                                   'functions': [f['name'] for f in functions]})
            if len(functions) == 1 and entry['function'].split('::')[-1].strip() != functions[0]['name'].split('::')[-1].strip():
                errors.append({'id': entry['id'], 'file': entry['file'], 'declared': entry['function'],
                               'actual': functions[0]['name'],
                               'actual_range': [functions[0]['line_start'], functions[0]['line_end']]})
    (DOC / 'function-audit.json').write_text(json.dumps(errors, indent=2) + '\n')
    (DOC / 'function-boundary-audit.json').write_text(json.dumps(boundaries, indent=2) + '\n')
    print(f'Parsed {len(index)} functions; {len(errors)} inventory function mismatches; {len(boundaries)} entries span multiple functions.')


if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

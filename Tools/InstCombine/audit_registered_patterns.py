#!/usr/bin/env python3
"""Find concrete Pattern.Valid declarations omitted from proof manifests.

This is a syntax advisory for the simple, single-namespace entry modules. It
does not establish theorem validity or enumerate parameterized proof templates.
The global Lean checker remains responsible for types and transitive axioms.
"""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/instcombine'
CONCRETE_VALID = re.compile(
    r"(?m)^(?:public\s+)?theorem\s+([\w'.]+)\s*:\s*"
    r"(?:¬\s*)?(?:Veir\.Puddle\.)?Pattern\.Valid\s+([\w'.]+)\s*:=")


def registration_report():
    proofs = [entry for path in sorted(DOC.glob('proofs-*.json'))
              for entry in json.loads(path.read_text())]
    recorded = {variant.get('theorem') for entry in proofs
                for variant in [entry, *entry.get('additional_patterns', [])]}
    unregistered = []
    ambiguous = []
    detected = 0
    for path in sorted((ROOT / 'Veir/Passes/InstCombineLLVM').glob('*.lean')):
        source = path.read_text()
        namespaces = re.findall(r'(?m)^namespace\s+([\w.]+)', source)
        matches = list(CONCRETE_VALID.finditer(source))
        if matches and len(namespaces) != 1:
            ambiguous.append(str(path.relative_to(ROOT)))
            continue
        for match in matches:
            detected += 1
            theorem = namespaces[0] + '.' + match[1]
            if theorem not in recorded:
                unregistered.append({
                    'lean_file': str(path.relative_to(ROOT)),
                    'line': source.count('\n', 0, match.start()) + 1,
                    'theorem': theorem,
                    'definition': namespaces[0] + '.' + match[2],
                })
    return {
        'description': __doc__,
        'detected_concrete_theorems': detected,
        'unregistered': unregistered,
        'ambiguous_namespace_files': ambiguous,
    }


if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    report = registration_report()
    (DOC / 'pattern-registration-audit.json').write_text(
        json.dumps(report, indent=2) + '\n')
    print(f'{len(report["unregistered"])} concrete theorem declarations are '
          f'unregistered; {len(report["ambiguous_namespace_files"])} namespace '
          'layouts need manual review. No proof statuses changed.')

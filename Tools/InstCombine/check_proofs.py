#!/usr/bin/env python3
"""Build recorded Puddle validity/counterexample proofs and inspect their axioms."""
import argparse
import json
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile
from proof_context import proof_context_sha256

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/instcombine'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    proofs = []
    for path in sorted(DOC.glob('proofs-*.json')):
        proofs.extend(json.loads(path.read_text()))
    checked = []
    for proof in proofs:
        if proof.get('status') not in ('proven', 'succeeded', 'counterexample'):
            continue
        checked.append(proof)
        for variant in proof.get('additional_patterns', []):
            checked.append({**variant, 'inventory_id': proof['inventory_id'], 'status': proof['status']})
    if not checked:
        raise SystemExit('No proofs or counterexamples recorded; nothing verified.')
    for field in ('definition', 'theorem'):
        names = [p.get(field) for p in checked]
        if len(names) != len(set(names)):
            raise SystemExit(f'Duplicate recorded {field}; patterns must not be counted twice.')
    context_hash = proof_context_sha256()
    modules = set()
    execution_modules = {m for p in proofs if p.get('status') in ('proven', 'succeeded', 'counterexample')
                         for m in p.get('execution_modules', [])}
    for proof in checked:
        path = ROOT / proof['lean_file']
        if not path.is_file():
            raise SystemExit(f'Missing Lean source: {path}')
        module = str(path.relative_to(ROOT).with_suffix('')).replace('/', '.')
        modules.add(module)
        if not proof.get('theorem') or not proof.get('definition'):
            raise SystemExit(f'Missing theorem or pattern definition name: {path}')
    subprocess.run(['lake', 'build', *sorted(modules | execution_modules)], cwd=ROOT, check=True)
    imports = '\n'.join(f'import {module}' for module in sorted(modules))
    commands = '\n'.join(
        f'example : {"¬ " if p["status"] == "counterexample" else ""}'
        f'Veir.Puddle.Pattern.Valid {p["definition"]} := {p["theorem"]}\n'
        f'#print axioms {p["theorem"]}' for p in checked
    )
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir=ROOT, delete=False) as output:
        output.write(imports + '\n' + commands + '\n')
        scratch = Path(output.name)
    try:
        proc = subprocess.run(['lake', 'env', 'lean', str(scratch)], cwd=ROOT, capture_output=True, text=True)
    finally:
        scratch.unlink()
    log = proc.stdout + proc.stderr
    (DOC / 'proof-validation.log').write_text(log)
    if proc.returncode:
        raise SystemExit(log)
    if 'sorryAx' in log:
        raise SystemExit('Rejected: recorded theorem depends on sorryAx.')
    reported = re.findall(
        r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)", log, re.M)
    if sorted(reported) != sorted(p['theorem'] for p in checked):
        raise SystemExit('Axiom output does not account for every recorded theorem exactly once.')
    axiom_lists = re.findall(r'depends on axioms:\s*\[([^]]*)\]', log, re.S)
    unrecognized = {x.strip() for xs in axiom_lists for x in xs.split(',') if x.strip()} - ALLOWED_AXIOMS
    if unrecognized:
        raise SystemExit(f'Unexpected axioms require review: {sorted(unrecognized)}')
    if 'Lean.ofReduceBool' in log:
        raise SystemExit('Native-evaluation axiom requires explicit scope review; not counted as kernel-only verification.')
    if proof_context_sha256() != context_hash:
        raise SystemExit('Lean sources changed during validation; retry after edits finish.')
    verification = [{'context_sha256': context_hash, 'status': p['status'], 'inventory_id': p.get('inventory_id'), 'theorem': p['theorem'], 'lean_file': p['lean_file'], 'sha256': hashlib.sha256((ROOT / p['lean_file']).read_bytes()).hexdigest()} for p in checked]
    positives = [p for p in verification if p['status'] != 'counterexample']
    negatives = [p for p in verification if p['status'] == 'counterexample']
    (DOC / 'verified-proofs.json').write_text(json.dumps(positives, indent=2) + '\n')
    (DOC / 'verified-counterexamples.json').write_text(json.dumps(negatives, indent=2) + '\n')
    print(f'Built {len(modules)} modules; inspected {len(positives)} validity proofs and '
          f'{len(negatives)} counterexample proofs.')


if __name__ == '__main__':
    main()

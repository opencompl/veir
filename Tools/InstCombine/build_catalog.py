#!/usr/bin/env python3
"""Validate the pinned source audit and render its human-readable inventory.

No inferred proof statuses: only proof manifests containing explicit validated results
can mark a rewrite proven. Candidate sites are a mechanical audit aid, not a rewrite count.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
from proof_context import proof_context_sha256
from check_coverage import coverage_report
from audit_registered_patterns import registration_report

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/instcombine'

# LLVM instruction mnemonics, including ptrtoaddr in the pinned revision.
# Intrinsic identities and non-instruction values belong in separate fields.
LLVM_OPCODES = set('''
ret br switch indirectbr invoke resume unreachable cleanupret catchret catchswitch
callbr fneg add fadd sub fsub mul fmul udiv sdiv fdiv urem srem frem shl lshr ashr
and or xor alloca load store getelementptr fence cmpxchg atomicrmw trunc zext sext
fptrunc fpext fptoui fptosi uitofp sitofp ptrtoint ptrtoaddr inttoptr bitcast
addrspacecast icmp fcmp phi select freeze call va_arg landingpad catchpad cleanuppad
extractelement insertelement shufflevector extractvalue insertvalue
'''.split())


def load_inventory():
    entries = []
    for path in sorted((DOC / 'inventory').glob('*.json')):
        if path.name.endswith('-coverage.json'):
            continue
        data = json.loads(path.read_text())
        if not isinstance(data, list):
            raise ValueError(f'{path}: expected list')
        entries.extend(data)
    ids = set()
    for entry in entries:
        ident = entry['id']
        if ident in ids:
            raise ValueError(f'duplicate ID {ident}')
        ids.add(ident)
        if entry.get('kind', 'rewrite') not in {'rewrite', 'delegation', 'analysis-helper', 'incomplete-family', 'mutation', 'metadata-mutation'}:
            raise ValueError(f'{ident}: invalid kind {entry["kind"]!r}')
        lines = (DOC / 'source' / entry['file']).read_text().splitlines()
        if not 1 <= entry['line_start'] <= entry['line_end'] <= len(lines):
            raise ValueError(f'{ident}: invalid source range')
        supports = entry.get('supporting_source_ranges', [])
        if not isinstance(supports, list):
            raise ValueError(f'{ident}: supporting_source_ranges must be a list')
        for support in supports:
            if (not isinstance(support, dict) or
                    not isinstance(support.get('line_start'), int) or
                    not isinstance(support.get('line_end'), int) or
                    not 1 <= support['line_start'] <= support['line_end'] <= len(lines) or
                    not isinstance(support.get('description'), str)):
                raise ValueError(f'{ident}: invalid supporting source range')
        for field in ('description', 'match_opcodes', 'rewrite_opcodes', 'extra_conditions', 'uses_analysis'):
            if field not in entry:
                raise ValueError(f'{ident}: missing {field}')
        for field in ('match_opcodes', 'rewrite_opcodes', 'extra_conditions'):
            if not isinstance(entry[field], list) or not all(isinstance(x, str) for x in entry[field]):
                raise ValueError(f'{ident}: {field} must be a list of strings')
        for field in ('match_opcodes', 'rewrite_opcodes'):
            invalid = set(entry[field]) - LLVM_OPCODES
            if invalid:
                raise ValueError(f'{ident}: non-opcode labels in {field}: {sorted(invalid)}')
        for field in ('match_intrinsics', 'rewrite_intrinsics', 'match_details', 'rewrite_details'):
            if field in entry and (not isinstance(entry[field], list) or not all(isinstance(x, str) for x in entry[field])):
                raise ValueError(f'{ident}: {field} must be a list of strings')
        for field in ('match_opcode_parameter', 'rewrite_opcode_parameter'):
            if field in entry and (not isinstance(entry[field], str) or not entry[field].strip()):
                raise ValueError(f'{ident}: {field} must be a nonempty string')
        if not isinstance(entry['uses_analysis'], bool):
            raise ValueError(f'{ident}: uses_analysis must be boolean')
        blocker = entry.get('puddle_blocker')
        if blocker is not None and not isinstance(blocker, str):
            raise ValueError(f'{ident}: puddle_blocker must be a string or null')
        if entry.get('status') == 'unsupported' and not blocker:
            raise ValueError(f'{ident}: unsupported status requires an explicit blocker')
    return sorted(entries, key=lambda e: (e['file'], e['line_start'], e['id']))


def candidate_sites():
    sites = []
    for path in sorted((DOC / 'source').glob('*')):
        if path.suffix not in ('.cpp', '.h'):
            continue
        for lineno, text in enumerate(path.read_text().splitlines(), 1):
            stripped = text.strip()
            if stripped.startswith(('//', '*', '#')):
                continue
            is_return = re.search(r'\breturn\b', text) and not re.search(r'\breturn\s+(nullptr|false|true|std::nullopt|0)\s*;', text)
            is_mutation = re.search(r'\b(replaceInstUsesWith|replaceOperand|eraseInstFromFunction|setOperand|setHasNoSignedWrap|setHasNoUnsignedWrap|setIsExact|setIsDisjoint|setPredicate|setIncomingValue|setOperation|swapOperands|dropPoisonGeneratingFlags)\s*\(', text)
            if is_return or is_mutation:
                sites.append({'file': path.name, 'line': lineno, 'kind': 'return' if is_return else 'mutation', 'text': stripped})
    return sites


def main():
    pin = json.loads((DOC / 'llvm-pin.json').read_text())
    for file in pin['files']:
        data = (DOC / 'source' / file['name']).read_bytes()
        if hashlib.sha256(data).hexdigest() != file['sha256']:
            raise ValueError(f'pinned source changed: {file["name"]}')
    entries = load_inventory()
    sites = candidate_sites()
    for site in sites:
        site['inventory_ids'] = [e['id'] for e in entries if e.get('kind') != 'incomplete-family' and e['file'] == site['file'] and e['line_start'] <= site['line'] <= e['line_end']]
    (DOC / 'candidate-sites.json').write_text(json.dumps(sites, indent=2) + '\n')
    proofs = []
    for path in sorted(DOC.glob('proofs-*.json')):
        proofs.extend(json.loads(path.read_text()))
    by_id = {}
    lean_file_owners = {}
    inventory_by_id = {e['id']: e for e in entries}
    for proof in proofs:
        ident = proof.get('inventory_id')
        for field in ('inventory_id', 'status', 'scope', 'reason', 'file'):
            if field in proof and not isinstance(proof[field], str):
                raise ValueError(f'{ident}: proof manifest {field} must be a string')
        variants = proof.get('additional_patterns', [])
        if not isinstance(variants, list) or not all(isinstance(v, dict) for v in variants):
            raise ValueError(f'{ident}: additional_patterns must be a list of objects')
        for variant in [proof, *variants]:
            for field in ('lean_file', 'definition', 'theorem', 'scope'):
                if field in variant and not isinstance(variant[field], str):
                    raise ValueError(f'{ident}: pattern {field} must be a string')
        if 'scope_review_complete' in proof and not isinstance(proof['scope_review_complete'], bool):
            raise ValueError(f'{ident}: scope_review_complete must be boolean')
        for field in ('remaining_supported_scope', 'unsupported_scope'):
            if field in proof and (not isinstance(proof[field], list) or
                                   not all(isinstance(x, str) and x.strip() for x in proof[field])):
                raise ValueError(f'{ident}: {field} must be a list of nonempty strings')
        if proof.get('scope_review_complete') and any(
                field not in proof for field in ('remaining_supported_scope', 'unsupported_scope')):
            raise ValueError(f'{ident}: completed scope review requires explicit remaining and unsupported lists')
        if ident not in inventory_by_id:
            raise ValueError(f'Proof manifest references absent inventory ID: {ident}')
        source = inventory_by_id[ident]
        if proof.get('file', source['file']) != source['file']:
            raise ValueError(f'{ident}: proof manifest source file disagrees with inventory')
        if 'line_start' in proof and not source['line_start'] <= proof['line_start'] <= source['line_end']:
            raise ValueError(f'{ident}: proof manifest source line is outside inventory range')
        if ident in by_id:
            raise ValueError(f'Duplicate proof manifest entry: {ident}')
        for variant in [proof, *proof.get('additional_patterns', [])]:
            if not variant.get('lean_file'):
                continue
            lean_file = variant['lean_file']
            owner = lean_file_owners.setdefault(lean_file, ident)
            if owner != ident:
                raise ValueError(f'{lean_file}: source entries {owner} and {ident} must have separate Lean files')
        by_id[ident] = proof
    verification_file = DOC / 'verified-proofs.json'
    verified = json.loads(verification_file.read_text()) if verification_file.exists() else []
    counterexample_file = DOC / 'verified-counterexamples.json'
    verified_counterexamples = (json.loads(counterexample_file.read_text())
                                if counterexample_file.exists() else [])
    context_hash = proof_context_sha256()
    verified_counterexample_keys = {
        (p['inventory_id'], p['theorem'], p['sha256']) for p in verified_counterexamples
        if p.get('context_sha256') == context_hash}
    verified_keys = {(p['inventory_id'], p['theorem'], p['sha256']) for p in verified
                     if p.get('context_sha256') == context_hash}
    for entry in entries:
        proof = by_id.get(entry['id'])
        if proof:
            entry['proof_result'] = proof
    counts = {'inventoried_entries': len(entries), 'implemented': 0, 'proven': 0, 'counterexamples': 0, 'unsupported': 0, 'pending': 0, 'delegations': 0, 'analysis_helpers': 0, 'incomplete_families': 0, 'implemented_patterns': 0, 'proven_patterns': 0, 'scope_unreviewed': 0, 'scope_pending': 0}
    body = [
        '# LLVM InstCombine rewrite inventory', '',
        '**Work in progress — this audit is not yet exhaustive.** Pending entries are not unsupported cases and are not proved rewrites.', '',
        f'Target: [`{pin["commit"]}`]({pin["repository"]}/commit/{pin["commit"]}), the `main` tip resolved at {pin["resolved_at_utc"]}.', '',
        f'Commit: {pin.get("commit_subject", "")} ({pin.get("commit_date", "")}). The local source snapshot is hash checked by `Tools/InstCombine/build_catalog.py` against `llvm-pin.json`.', '',
        'Scope: transformations defined in `llvm/lib/Transforms/InstCombine/`, including instruction replacement, operand mutation, flags, and metadata changes. Calls into transformations defined elsewhere (for example InstSimplify or libcall simplification) are delegation sites, not an inventory of those external implementations. Helper-generated and visitor rewrites must be reconciled to avoid duplicate counts.', '',
        'An entry describes a source transformation branch or an explicitly parameterized family; this is not a count of all possible type/constant instantiations. `candidate-sites.json` is a mechanical checklist of return/mutation locations, including non-rewrites. It does not establish exhaustive coverage. Coverage manifests retain unfinished source ranges.', '',
        'Puddle validity means `Veir.Puddle.Pattern.Valid` under the repository’s interpreter and refinement model. Implementation/proof counts count source entries with at least one recorded pattern in the stated proof scope; they do not assert that every upstream variant is covered. A theorem for a scalar or concrete recursive specialization is not proof of the full LLVM vector or recursive family. LLVM behavior outside that model must be documented separately. No counterexample is evidence of an LLVM bug unless it satisfies the original LLVM guards and semantics.', '',
    ]
    body.extend(['## Source index', '', '| File | Transformation entries | Delegations / helpers / unfinished families |', '| --- | ---: | ---: |'])
    for name in sorted({e['file'] for e in entries}):
        local = [e for e in entries if e['file'] == name]
        calls = sum(e.get('kind') in ('delegation', 'analysis-helper', 'incomplete-family') for e in local)
        anchor = re.sub(r'[^a-z0-9_-]', '', name.lower())
        body.append(f'| [{name}](#{anchor}) | {len(local) - calls} | {calls} |')
    body.extend(['', 'Regenerate this document with `python3 Tools/InstCombine/build_catalog.py`. Validate recorded proofs with `python3 Tools/InstCombine/check_proofs.py`; it builds Lean modules and checks theorem axioms. See `summary.json` for current counts and `inventory/*-coverage.json` for explicit gaps.', ''])
    body.extend(['The catalogue and proof checker use the Python standard library and the repository Lean toolchain. The optional C++ AST audits (`audit_functions.py`, `audit_guard_opcodes.py`) additionally use the pinned packages in `Tools/InstCombine/requirements-audit.txt`; install those into a separate Python environment before running these audits.', ''])
    previous_file = None
    for e in entries:
        if e['file'] != previous_file:
            body.extend([f'## {e["file"]}', ''])
            previous_file = e['file']
        proof = e.get('proof_result', {})
        status = proof.get('status', e.get('status', 'pending'))
        if proof.get('lean_file') and proof.get('status') in ('proven', 'succeeded', 'counterexample'):
            counts['scope_unreviewed'] += not proof.get('scope_review_complete', False)
            counts['scope_pending'] += bool(proof.get('remaining_supported_scope'))
        if e.get('kind') in ('delegation', 'analysis-helper', 'incomplete-family'):
            status = e['kind']
        if status in ('proven', 'succeeded', 'counterexample'):
            result_keys = verified_counterexample_keys if status == 'counterexample' else verified_keys
            for variant in [proof, *proof.get('additional_patterns', [])]:
                path = ROOT / variant['lean_file']
                key = (e['id'], variant['theorem'], hashlib.sha256(path.read_bytes()).hexdigest())
                if key not in result_keys:
                    status = ('implemented; counterexample awaiting independent validation'
                              if status == 'counterexample' else
                              'implemented; proof awaiting independent validation')
                    break
        if proof.get('lean_file'):
            variants = [proof, *proof.get('additional_patterns', [])]
            counts['implemented_patterns'] += len(variants)
            for variant in variants:
                path = ROOT / variant['lean_file']
                key = (e['id'], variant.get('theorem'), hashlib.sha256(path.read_bytes()).hexdigest())
                counts['proven_patterns'] += key in verified_keys
        if status == 'incomplete-family':
            counts['incomplete_families'] += 1
        elif status == 'analysis-helper':
            counts['analysis_helpers'] += 1
        elif status == 'delegation':
            counts['delegations'] += 1
        elif status in ('proven', 'succeeded'):
            counts['proven'] += 1
            counts['implemented'] += 1
        elif status == 'counterexample':
            counts['counterexamples'] += 1
            counts['implemented'] += bool(proof.get('lean_file'))
        elif status == 'unsupported':
            counts['unsupported'] += 1
        else:
            counts['pending'] += 1
            counts['implemented'] += bool(proof.get('lean_file'))
        url = f'{pin["repository"]}/blob/{pin["commit"]}/llvm/lib/Transforms/InstCombine/{e["file"]}#L{e["line_start"]}-L{e["line_end"]}'
        body.extend([f'### {e["id"]}', '', e['description'], '',
                     f'- Source: [{e["file"]}:{e["line_start"]}–{e["line_end"]}]({url}), `{e.get("function", "")}`.',
                     '- Matched opcodes: ' + (', '.join(f'`{o}`' for o in e['match_opcodes']) or '(none)') + '.',
                     '- Replacement opcodes: ' + (', '.join(f'`{o}`' for o in e['rewrite_opcodes']) or '(existing value / erased operation)') + '.',
                     '- Additional conditions: ' + ('; '.join(e['extra_conditions']) or 'None recorded.') ,
                     '- Uses analysis beyond opcode/constant matching: ' + ('**yes**' if e['uses_analysis'] else '**no dataflow analysis recorded**; structural/type/property/use-count guards may still apply') + '.',
                     f'- Result: **{status}**.'])
        for field, label in (('match_opcode_parameter', 'Matched opcode parameter'),
                             ('rewrite_opcode_parameter', 'Replacement opcode parameter')):
            if e.get(field):
                body.append(f'- {label}: ' + e[field] + '.')
        for support in e.get('supporting_source_ranges', []):
            start, end = support['line_start'], support['line_end']
            support_url = f'{pin["repository"]}/blob/{pin["commit"]}/llvm/lib/Transforms/InstCombine/{e["file"]}#L{start}-L{end}'
            body.append(f'- Supporting source: [{e["file"]}:{start}–{end}]({support_url}) — {support["description"]}.')
        for field, label in (('match_intrinsics', 'Matched intrinsics'), ('rewrite_intrinsics', 'Replacement intrinsics'), ('match_details', 'Additional match details'), ('rewrite_details', 'Additional replacement details')):
            if e.get(field):
                body.append(f'- {label}: ' + ', '.join(f'`{value}`' for value in e[field]) + '.')
        if e.get('analysis_audit_note'):
            body.append('- Analysis-call review: ' + e['analysis_audit_note'])
        if e.get('audit_note'):
            body.append('- Audit note: ' + e['audit_note'])
        if e.get('puddle_blocker'):
            body.append('- Puddle limitation ' + ('(confirmed)' if status in ('unsupported', 'counterexample') else '(requires verification)') + ': ' + e['puddle_blocker'])
        if proof.get('lean_file'):
            body.append(f'- Lean: [{proof["lean_file"]}](../../{proof["lean_file"]}); theorem `{proof.get("theorem", "unproved")}`.')
        for variant in proof.get('additional_patterns', []):
            body.append(f'- Additional pattern: [{variant["lean_file"]}](../../{variant["lean_file"]}); theorem `{variant["theorem"]}`. {variant.get("scope", "")}')
        if proof.get('reason') and proof.get('reason') != e.get('puddle_blocker'):
            body.append('- Reason: ' + proof['reason'])
        if proof.get('scope'):
            body.append('- Proof scope: ' + proof['scope'])
        if proof.get('lean_file') and proof.get('status') in ('proven', 'succeeded', 'counterexample'):
            body.append('- Full source-scope review: ' +
                        ('complete' if proof.get('scope_review_complete') else '**pending**') + '.')
            if proof.get('remaining_supported_scope'):
                body.append('- Supported variants still to implement/prove: ' +
                            '; '.join(proof['remaining_supported_scope']))
            if proof.get('unsupported_scope'):
                body.append('- Source variants blocked by the model: ' +
                            '; '.join(proof['unsupported_scope']))
        if proof.get('validation'):
            body.append('- Validation: ' + str(proof['validation']))
        body.append('')
    counts['rewrite_entries'] = counts['inventoried_entries'] - counts['delegations'] - counts['analysis_helpers'] - counts['incomplete_families']
    coverage = coverage_report(sites, entries)
    (DOC / 'coverage-report.json').write_text(json.dumps(coverage, indent=2) + '\n')
    counts['source_files_reconciled'] = sum(r['complete'] for r in coverage)
    counts['source_files_total'] = len(coverage)
    counts['coverage_complete'] = all(r['complete'] for r in coverage) and not counts['incomplete_families']
    counts['unclassified_candidate_sites'] = sum(len(r.get('unresolved_sites', [])) for r in coverage)
    counts['mechanical_candidate_sites'] = len(sites)
    counts['unmapped_candidate_sites'] = sum(not s['inventory_ids'] for s in sites)
    counts['last_verified_entries'] = len({p['inventory_id'] for p in verified})
    counts['last_verified_patterns'] = len(verified)
    counts['last_verified_counterexamples'] = len({p['inventory_id'] for p in verified_counterexamples})
    counts['verification_context_current'] = bool(verified) and all(
        p.get('context_sha256') == context_hash for p in [*verified, *verified_counterexamples])
    registration = registration_report()
    (DOC / 'pattern-registration-audit.json').write_text(
        json.dumps(registration, indent=2) + '\n')
    counts['unregistered_concrete_patterns'] = len(registration['unregistered'])
    counts['registration_files_to_review'] = len(registration['ambiguous_namespace_files'])
    matcher_review_path = DOC / 'matcher-normalization-review.json'
    matcher_review = json.loads(matcher_review_path.read_text()) if matcher_review_path.exists() else {}
    open_matcher_reviews = [item for item in matcher_review.get('findings', [])
                            if item.get('resolution') not in ('fixed', 'not_applicable')]
    counts['matcher_scope_reviews_pending'] = len(open_matcher_reviews)
    output_review_path = DOC / 'extra-output-opcode-review-luna.json'
    output_review = json.loads(output_review_path.read_text()) if output_review_path.exists() else {}
    counts['output_opcode_reviews_pending'] = sum(
        item.get('disposition') == 'needs_followup'
        for item in output_review.get('candidates', []))
    counts['complete'] = (counts['coverage_complete'] and counts['pending'] == 0 and
                          counts['output_opcode_reviews_pending'] == 0 and
                          counts['scope_unreviewed'] == 0 and counts['scope_pending'] == 0 and
                          counts['unregistered_concrete_patterns'] == 0 and
                          counts['matcher_scope_reviews_pending'] == 0 and
                          counts['registration_files_to_review'] == 0)
    checkpoint = [
        f'Current checkpoint: **{counts["implemented"]} source entries with Puddle implementations**, '
        f'**{counts["proven"]} with currently validated proofs**, '
        f'**{counts["counterexamples"]} counterexamples**, '
        f'**{counts["unsupported"]} confirmed unsupported**, and '
        f'**{counts["pending"]} pending outcomes**. '
        f'The implementations contain {counts["implemented_patterns"]} pattern variants, '
        f'of which {counts["proven_patterns"]} have currently validated proofs.', '',
        f'Within implemented entries, **{counts["scope_unreviewed"]} lack a recorded source-scope review** '
        f'and **{counts["scope_pending"]} entries record supported variants still pending**. '
        'These counts may overlap. A proved specialization does not close its source entry '
        'until remaining supported variants and unsupported model cases are accounted for.', '',
        f'Pattern registration audit: {counts["unregistered_concrete_patterns"]} concrete '
        'validity declarations are not yet registered in proof manifests; '
        f'{counts["registration_files_to_review"]} namespace layouts require manual review. '
        'Unregistered declarations are not counted as proved patterns.', '',
        f'Source review: {counts["source_files_reconciled"]}/{counts["source_files_total"]} '
        f'files reconciled; {counts["incomplete_families"]} explicitly unfinished families. '
        'Proof validation is tied to the current Lean sources and toolchain; editing '
        'those sources makes previous validation stale until the checker is rerun.', '',
    ]
    if counts['output_opcode_reviews_pending']:
        checkpoint.extend([
            f'Output-opcode metadata audit: **{counts["output_opcode_reviews_pending"]} '
            'candidates need further source/helper review**. These are unresolved '
            'audit questions, not confirmed opcode errors or failed proofs. See '
            '[extra-output-opcode-review-luna.json](extra-output-opcode-review-luna.json).', '',
        ])
    if open_matcher_reviews:
        checkpoint.extend([
            f'Additional matcher coverage review: **{len(open_matcher_reviews)} files** '
            'need review for normalized one-bit all-ones constants (`1` versus literal `-1`). '
            'This concerns which source cases match, not the validity of existing theorems. '
            'See [matcher-normalization-review.json](matcher-normalization-review.json); '
            'source width guards may exclude some candidates.', '',
        ])
    if verified and not counts['verification_context_current']:
        checkpoint.extend([
            f'The most recent successful global check validated '
            f'**{counts["last_verified_entries"]} entries / '
            f'{counts["last_verified_patterns"]} patterns**, plus '
            f'**{counts["last_verified_counterexamples"]} formal counterexample(s)**, '
            'in an earlier Lean source context. '
            'Those historical results are not counted as validation of the current edited sources.', '',
        ])
    body[body.index('## Source index'):body.index('## Source index')] = checkpoint
    if counts['complete']:
        body[2] = 'Source coverage and per-rewrite outcomes are complete under the scope described below.'
    elif counts['coverage_complete']:
        body[2] = '**Work in progress — all source files have been reviewed, but Puddle implementation and proof work is incomplete.** Pending entries are neither unsupported cases nor proved rewrites. Source descriptions remain subject to correction during implementation.'
    (DOC / 'README.md').write_text('\n'.join(line.rstrip() for line in body))
    (DOC / 'summary.json').write_text(json.dumps(counts, indent=2) + '\n')
    print(json.dumps(counts, indent=2))


if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

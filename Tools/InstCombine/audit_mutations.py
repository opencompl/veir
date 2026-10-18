#!/usr/bin/env python3
"""Advisory audit for IR mutation call sites and successful bool helpers.

Inventory ranges are only matched mechanically. Unmatched sites must be reviewed;
this script never assigns rewrite status or assumes a mutation is an optimization.
"""
from __future__ import annotations
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'docs/instcombine'
# Explicit mutator names observed in LLVM InstCombine source. Keep this list broad
# enough to catch metadata/property mutators, but avoid general getters/predicates.
MANUAL_REVIEW = {
    ('InstCombineAddSub.cpp', 684): ([], 'Common FAddCombine builder post-processing copies debug location to newly created instructions; it is metadata propagation shared by transformation callers, not a standalone rewrite.'),
    ('InstCombineAddSub.cpp', 691): ([], 'Common FAddCombine builder post-processing copies the source instruction fast-math flags to newly created instructions; it is shared construction metadata, not a standalone rewrite.'),
    ('InstCombineCasts.cpp', 74): ([], 'EvaluateInDifferentTypeImpl utility reconstructs an existing expression at a requested type; this property-copying operation is part of callers’ transforms, not a distinct source branch.'),
    ('InstCombineCasts.cpp', 94): ([], 'EvaluateInDifferentTypeImpl utility reconstructs a trunc while preserving source nowrap properties; not a standalone InstCombine rewrite.'),
    ('InstCombineCasts.cpp', 95): ([], 'EvaluateInDifferentTypeImpl utility reconstructs a trunc while preserving source nowrap properties; not a standalone InstCombine rewrite.'),
    ('InstCombineCasts.cpp', 99): ([], 'EvaluateInDifferentTypeImpl utility reconstructs a zext with the source nneg property; not a standalone InstCombine rewrite.'),
    ('InstCombineCasts.cpp', 118): ([], 'EvaluateInDifferentTypeImpl utility builds a PHI while recursively evaluating an existing PHI at another type; construction belongs to the caller’s expression transform.'),
    ('InstCombineCasts.cpp', 181): ([], 'takeName transfers a debug/name label to the rebuilt value; it does not change IR semantics or define a rewrite branch.'),
    ('InstCombineCompares.cpp', 583): (['cmpa-L646'], 'PHI construction is the implementation of rewriteGEPAsOffset, called from the indexed-pointer comparison rewrite at cmpa-L646; helper mutations are subsumed by that transformation.'),
    ('InstCombineCompares.cpp', 596): (['cmpa-L646'], 'External-use replacement completes rewriteGEPAsOffset, called from the indexed-pointer comparison rewrite at cmpa-L646; helper mutation is subsumed by that transformation.'),
    ('InstCombineNegator.cpp', 535): ([], 'Rollback cleanup erases instructions created during an unsuccessful negation attempt; it is not a successful rewrite.'),
    ('InstCombinePHI.cpp', 40): ([], 'PHIArgMergedDebugLoc copies debug location metadata to a newly created PHI; metadata setup only.'),
    ('InstructionCombining.cpp', 143): ([], 'IRBuilder inserter copies annotation metadata from the configured source instruction onto any newly inserted instruction; generic builder metadata propagation.'),
    ('InstCombineAddSub.cpp', 3255): (['fneg-L3251a', 'fneg-L3271'], 'Shared propagateSelectFMF lambda copies the fneg flags to either select-arm rewrite; the two branch records are fneg-L3251a and fneg-L3271.'),
    ('InstCombineAddSub.cpp', 3258): (['fneg-L3251a', 'fneg-L3271'], 'Shared propagateSelectFMF lambda unions fast-math flags for either select-arm rewrite; the two branch records are fneg-L3251a and fneg-L3271.'),
    ('InstCombineAndOrXor.cpp', 1648): (['bitwise-L1650'], 'Mutates the RHS is_fpclass mask for the RHS-class branch, whose replacement is recorded by bitwise-L1650; that entry’s span now includes this call.'),
    ('InstCombineAndOrXor.cpp', 3508): (['bitwise-L3511'], 'Drops samesign on a still-used RHS comparison after the delegated comparison fold; this is part of the branch recorded by bitwise-L3511, whose span now includes the mutation.'),
    ('InstCombineCompares.cpp', 683): (['cmpa-L693'], 'NewICmp applies the GEP-derived samesign property for the common-base offset-comparison branch recorded at cmpa-L693; its span now includes the shared constructor.'),
    ('InstCombineCompares.cpp', 1383): (['cmpa-L1384'], 'Populates the new comparison PHI immediately before replacing the root; this is the rewrite recorded by cmpa-L1384, whose span now includes construction.'),
    ('InstCombineCompares.cpp', 3798): (['cmpa-L3799'], 'Transfers the name to the synthesized negation within the add-equality rewrite recorded by cmpa-L3799; its span now includes the construction branch.'),
    ('InstCombineCompares.cpp', 5906): (['cmpb-L5918', 'cmpb-L5919', 'cmpb-L5936'], 'Drops samesign from the local predicate before all min/max comparison decompositions; this shared predicate normalization supports the listed outcome branches and is not a separate rewrite.'),
    ('InstCombineCompares.cpp', 6816): (['cmpb-L8304'], 'takeName labels an arithmetic result built by OptimizeOverflowCheck, which supplies the add-overflow comparison rewrite at cmpb-L8304; naming is metadata, not a separate outcome.'),
    ('InstCombineCompares.cpp', 6821): (['cmpb-L8304'], 'takeName labels an arithmetic result built by OptimizeOverflowCheck, which supplies the add-overflow comparison rewrite at cmpb-L8304; naming is metadata, not a separate outcome.'),
    ('InstCombineCompares.cpp', 7644): (['cmpb-L7655', 'cmpb-L7659', 'cmpb-L7663', 'cmpb-L7676'], 'Shared createCmpReverse helper copies comparison flags for the vector-reverse comparison outcomes listed; the mutations are common output construction, not separate rewrites.'),
    ('InstCombineCompares.cpp', 8901): (['cmpb-L8914', 'cmpb-L8918', 'cmpb-L8922', 'cmpb-L8926', 'cmpb-L8931', 'cmpb-L8936', 'cmpb-L8949'], 'Shared replacePredAndOp0 helper changes predicate for the fabs comparison outcomes listed; helper mutation supports each source branch rather than defining an additional outcome.'),
    ('InstCombineCompares.cpp', 8902): (['cmpb-L8914', 'cmpb-L8918', 'cmpb-L8922', 'cmpb-L8926', 'cmpb-L8931', 'cmpb-L8936', 'cmpb-L8949'], 'Shared replacePredAndOp0 helper replaces the fabs operand for the comparison outcomes listed; helper mutation supports each source branch rather than defining an additional outcome.'),
    ('InstCombineCompares.cpp', 8966): (['cmpb-L8996', 'cmpb-L8999', 'cmpb-L9002', 'cmpb-L9005'], 'Shared ReplacePredAndOp0 helper changes the predicate for the sqrt comparison outcomes listed; the mutation is part of those branch results.'),
    ('InstCombineCompares.cpp', 8967): (['cmpb-L8992', 'cmpb-L8996', 'cmpb-L8999', 'cmpb-L9002', 'cmpb-L9005'], 'Shared ReplacePredAndOp0 helper replaces the sqrt operand for the comparison outcomes listed; the mutation is part of those branch results.'),
    ('InstCombinePHI.cpp', 482): (['phi-L516', 'phi-L529'], 'Creates the first incoming value for the comparison/binop operand PHI builder; both outputs share this construction path.'),
    ('InstCombinePHI.cpp', 490): (['phi-L516', 'phi-L529'], 'Creates the first incoming value for the comparison/binop operand PHI builder; both outputs share this construction path.'),
    ('InstCombinePHI.cpp', 503): (['phi-L516', 'phi-L529'], 'Adds varying LHS values to the comparison/binop operand PHI builder; both outputs share this construction path.'),
    ('InstCombinePHI.cpp', 507): (['phi-L516', 'phi-L529'], 'Adds varying RHS values to the comparison/binop operand PHI builder; both outputs share this construction path.'),
    ('InstCombinePHI.cpp', 523): (['phi-L529'], 'Copies arithmetic flags onto the synthesized binary operation in the binop PHI outcome recorded by phi-L529.'),
    ('InstCombinePHI.cpp', 746): (['phi-L766-sameaddr', 'phi-L773-varyingaddr'], 'Initializes the shared load-pointer PHI builder; the same-address and varying-address results are split into the listed outcomes.'),
    ('InstCombinePHI.cpp', 749): (['phi-L766-sameaddr', 'phi-L773-varyingaddr'], 'Copies load metadata to the synthesized load in the shared PHI-load transformation, whose outcomes are listed.'),
    ('InstCombinePHI.cpp', 922): (['phi-L950', 'phi-L961', 'phi-L968'], 'Initializes the shared operand-PHI builder for cast, binop, and compare output variants listed.'),
    ('InstCombinePHI.cpp', 931): (['phi-L950', 'phi-L961', 'phi-L968'], 'Adds the remaining incoming value to the shared operand-PHI builder for the output variants listed.'),
    ('InstCombinePHI.cpp', 955): (['phi-L961'], 'Copies flags to the synthesized constant-RHS binary operation recorded by phi-L961.'),
    ('InstCombinePHI.cpp', 1201): (['phi-L1236-slice'], 'Adds a reused lowered PHI value while splitting the illegal-width PHI web recorded by phi-L1236-slice.'),
    ('InstCombinePHI.cpp', 1213): (['phi-L1236-slice'], 'Adds the extracted predecessor value to the new slice PHI for the rewrite recorded by phi-L1236-slice.'),
    ('InstCombineSelect.cpp', 3133): (['select-L3144', 'select-L3148', 'select-L3153'], 'Shared reverse-select builder copies flags to its synthesized vector select for the listed vector-reverse outcomes.'),
    ('InstCombineSelect.cpp', 4475): (['select-L4505', 'select-L4509'], 'Transfers the original select name to the synthesized select in the shared fadd-constant hoist outcomes listed.'),
    ('InstCombineSelect.cpp', 4478): (['select-L4505', 'select-L4509'], 'Transfers the original fadd name to the synthesized fadd in the shared hoist outcomes listed.'),
    ('InstCombineSelect.cpp', 4485): (['select-L4505', 'select-L4509'], 'Sets intersected fast-math flags on the synthesized fadd in the shared hoist outcomes listed.'),
    ('InstCombineSelect.cpp', 4486): (['select-L4505', 'select-L4509'], 'Sets intersected fast-math flags on the synthesized select in the shared hoist outcomes listed.'),
    ('InstructionCombining.cpp', 1396): (['ic-select-feed-binop-add-negate-false-arm-L1427', 'ic-select-feed-binop-add-negate-true-arm-L1431'], 'Builder fast-math flags set for the two select-arm add-negation rewrites listed; common construction setup, not a separate rewrite.'),
}
RETURN_REASONS = {
    ('InstCombineAndOrXor.cpp', 5192): (['bitwise-L5187'], 'Successful completion of the all-users De Morgan rewrite; source entry bitwise-L5187 records this transform but its span currently ends before this return.'),
    ('InstCombineAndOrXor.cpp', 5249): (['bitwise-L5244'], 'Successful completion of the one-inverted-operand logical rewrite; source entry bitwise-L5244 records this transform but its span currently ends before this return.'),
    ('InstCombineAndOrXor.cpp', 2606): ([], 'Boolean return from the local isNarrowableBinOpcode predicate inside visitAnd; it only approves an opcode for a later pattern.'),
    ('InstCombineSimplifyDemanded.cpp', 266): (['demanded-use-and-demand-operands-L275'], 'Boolean success signal from the shared demanded-bit helper after operand simplification/flag updates; caller returns or reprocesses the root, and branch-specific simplifications are inventoried separately.'),
    ('InstCombineMulDivRem.cpp', 2461): (['irem-factorzero-L2500'], 'Boolean success return from a local shift-or-multiply pattern matcher; it reports a matched operand shape and performs no rewrite.'),
    ('InstCombineMulDivRem.cpp', 2473): (['irem-factorzero-L2500'], 'Boolean success return from a local shift-by-constant pattern matcher; it reports a matched operand shape and performs no rewrite.'),
    ('InstCombineCompares.cpp', 6807): (['cmpb-L6807-neutral-overflow'], 'Neutral-operand outcome returns the input arithmetic value and false overflow; explicitly inventoried at cmpb-L6807-neutral-overflow.'),
    ('InstCombineCompares.cpp', 6818): (['cmpb-L6818-always-overflow'], 'Always-overflow outcome creates the arithmetic result and returns true overflow; explicitly inventoried at cmpb-L6818-always-overflow.'),
    ('InstCombineCompares.cpp', 6829): (['cmpb-L6827'], 'OptimizeOverflowCheck returns success after synthesizing a no-unsigned-overflow arithmetic result; flag/output behavior is recorded at cmpb-L6827.'),
}

MUTATORS = re.compile(r'\b(?:'
    r'(?:set|add|remove|drop|erase|replace|copy)[A-Z]\w*|set(?:FastMathFlags|Align|Alignment|ArgOperand|CalledFunction|SourceElementType|ResultElementType|NonNeg|SameSign|HasNoSignedWrap|HasNoUnsignedWrap|IsExact|IsDisjoint|Predicate|Operand|IncomingValue|Successor|Operation|Metadata|DebugLoc|Attributes|TailCallKind|Volatile|Atomic|Ordering|Weak|InBounds|InRange|NoWrap|Exact|Disjoint|Name|Type|Initializer|Linkage|Visibility|DLLStorageClass|Comdat|Section|Alignment|UnnamedAddr|DSOLocal|PersonalityFn|GC|Partition|Parent|Value|FastMathFlags)'
    r'|dropSameSign|dropPoisonGeneratingFlags|dropUBImplyingAttrsAndMetadata|copyIRFlags|copyMetadata|copyFastMathFlags|copyDbgLoc|replaceInstUsesWith|replaceOperand|replaceAllUsesWith|replaceUsesOfWith|eraseInstFromFunction|eraseFromParent|removeFromParent|swapOperands|mutateType|mutateFunctionType|setOperand|setArgOperand|setIncomingValue|setIncomingBlock|setSuccessor|setCalledOperand|setCalledFunction|addIncoming|removeIncomingValue|takeName)\s*\(')
RETURN_TRUE = re.compile(r'\breturn\s+true\s*;')

def main() -> None:
    inventories=[]
    for path in sorted((DOC/'inventory').glob('*.json')):
        if path.name.endswith('-coverage.json'): continue
        inventories.extend(json.loads(path.read_text()))
    inventory_ids = {entry['id'] for entry in inventories}
    pin = json.loads((DOC / 'llvm-pin.json').read_text())['commit']
    manual_reviews = {}
    for review_path in (DOC / 'mutation-manual-review.json', DOC / 'mutation-return-review.json'):
        if not review_path.exists():
            continue
        review = json.loads(review_path.read_text())
        if review['llvm_pin'] != pin:
            raise ValueError(f'{review_path.name}: source pin mismatch')
        for item in review['items']:
            key = (item['file'], item['line'])
            if key in manual_reviews:
                raise ValueError(f'Duplicate mutation review: {key}')
            source_line = (DOC / 'source' / item['file']).read_text().splitlines()[item['line'] - 1].strip()
            if item.get('source_text', source_line) != source_line:
                raise ValueError(f'Stale mutation review source text: {key}')
            unknown = set(item.get('related_inventory_ids', [])) - inventory_ids
            if unknown:
                raise ValueError(f'{key}: absent referenced inventory IDs: {sorted(unknown)}')
            if not item.get('reason') or not item.get('disposition'):
                raise ValueError(f'{key}: missing human review evidence')
            manual_reviews[key] = {**item, 'review_file': review_path.name}
    function_index=json.loads((DOC/'function-index.json').read_text())
    functions={}
    for f in function_index: functions.setdefault(f['file'],[]).append(f)
    out=[]
    for path in sorted((DOC/'source').glob('*.cpp')):
        for lineno,line in enumerate(path.read_text().splitlines(),1):
            stripped=line.strip()
            if stripped.startswith('//'): continue
            calls=[m.group(0).split('(')[0] for m in MUTATORS.finditer(line)]
            is_true=bool(RETURN_TRUE.search(line))
            if not calls and not is_true: continue
            fn=next((f['name'] for f in functions.get(path.name,[]) if f['line_start']<=lineno<=f['line_end']),None)
            matches=[e['id'] for e in inventories if e['file']==path.name and e['line_start']<=lineno<=e['line_end'] and e.get('kind')!='incomplete-family']
            norm=lambda name: re.sub(r'^(?:InstCombinerImpl|InstCombiner|InstCombine)[: :]*', '', name or '')
            nearby=[e for e in inventories if e['file']==path.name and norm(e.get('function'))==norm(fn) and e.get('kind')!='incomplete-family' and min(abs(lineno-e['line_start']),abs(lineno-e['line_end']))<=40]
            nearby.sort(key=lambda e:min(abs(lineno-e['line_start']),abs(lineno-e['line_end'])))
            key=(path.name,lineno)
            body_review = manual_reviews.get(key)
            note = ((body_review.get('related_inventory_ids', []), body_review['reason'])
                    if body_review else MANUAL_REVIEW.get(key))
            return_note=RETURN_REASONS.get(key) if is_true else None
            related=(note or return_note or (nearby and ([e['id'] for e in nearby], 'Unreviewed site near the listed inventory records; proximity does not establish that those records describe this mutation.')))
            out.append({
                'file':path.name,'line':lineno,'function':fn,
                'call':', '.join(calls) if calls else 'return true',
                'source':stripped,'matched_inventory_ids':matches,
                'related_inventory_ids':related[0] if related else [],
                'coverage':'covered' if matches else 'unmapped',
                'review_status': ('body-reviewed' if body_review else 'explicit-note') if note or return_note else ('span-mapped' if matches else 'needs-review'),
                'review_file': body_review['review_file'] if body_review else None,
                'review_disposition': body_review['disposition'] if body_review else None,
                'review_reason': (related[1] if related else None) if matches else (related[1] if related else 'Unreviewed site: inspect the entire function and callers; a successful Boolean return may complete a real IR rewrite.')
            })
    result={'description':'Advisory only: direct source mutation calls and return-true helpers matched to inventory spans; a covered span is not proof that every mutation/outcome is inventoried.', 'counts':{'sites':len(out),'covered':sum(x['coverage']=='covered' for x in out),'unmapped':sum(x['coverage']=='unmapped' for x in out),'mutator_sites':sum(x['call']!='return true' for x in out),'return_true_sites':sum(x['call']=='return true' for x in out),'unmapped_needing_review':sum(x['review_status']=='needs-review' for x in out)},'sites':out}
    target=DOC/'mutation-audit.json'
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result['counts'],indent=2))
    print(f'wrote {target.relative_to(ROOT)}')

if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()

module

public import Veir.IR.Basic
public import Veir.IR.Attribute

/-!
  # Symbol-table machinery (unverified)

  Phase F.4 of `harness/regions-design.md`. Implements the
  recommended **Hybrid** approach: provide a `resolveSymbol` walker
  that pass-level code can consume, **without** encoding symbol
  integrity as a `WellFormed` invariant.

  Two consequences of "unverified" here:

  1. Verified rewriters don't need to prove "I preserved symbol
     resolution"; they only need to preserve `WellFormed` (which
     ignores symbols).
  2. A pass that depends on `resolveSymbol returning `some _` must
     state that as an explicit hypothesis; it's not a free
     guarantee from `WellFormed`.

  When (if) a verified pass needs symbol resolution as a free
  guarantee, the upgrade path is to add a `SymbolsResolve : Prop`
  predicate to `IRContext` (parallels `Veir/Dominance.lean`'s
  `IRContext.Dom`), prove rewriter preservation, and discharge it
  here.

  **Currently a forward-compatibility stub.** The walker's
  signatures are stable so consumers can be written against them;
  the body is a minimal implementation that:
  - returns `none` for anything other than a flat reference
    matching an op's recorded `sym_name`
  - does not walk up scopes (single-flat-scope today)
  - does not handle nested `@A::@B` paths (they parse-fail today;
    when nested form is enabled, this walker extends)

  The full implementation depends on Phase F.5 (function.def port)
  to give us a real consumer; this file lands the API surface so
  F.5 can use it.
-/

namespace Veir

public section

/--
  Attempt to resolve a flat symbol reference (`@name`) in the
  `IRContext`. Walks every op in the context, looking for one whose
  property dictionary contains a `sym_name` `StringAttr` matching
  the requested name.

  Returns the first match. Caller is responsible for handling `none`
  (typically meaning "no such symbol in scope").

  Caveats (per Phase F.4's Hybrid scope):
  - **Scope is ignored.** A flat `@foo` resolves to *any* op named
    `foo` in the IR, regardless of which region/block it lives in.
    When scoped resolution is required (e.g., a struct's nested
    member with the same name as a top-level symbol), this needs
    extension to walk up from the `fromOp` site to the enclosing
    SymbolTable-trait op.
  - **No verification of integrity.** `WellFormed` does not include
    "every SymbolRefAttr resolves to something"; this walker can
    return `none` even on well-formed IR, and a pass consuming it
    must handle that case.
-/
def IRContext.resolveFlatSymbol {OpInfo : Type} [HasOpInfo OpInfo]
    (ctx : IRContext OpInfo) (ref : FlatSymbolRefAttr) : Option OperationPtr := Id.run do
  -- Iterate all operations; first match wins. `DictionaryAttr.entries`
  -- is `Array (ByteArray × Attribute)`; we scan linearly. Symbol-trait
  -- ops store their name under the `sym_name` key as a `StringAttr`.
  let symKey := "sym_name".toUTF8
  for entry in ctx.operations.toList do
    let opPtr := entry.1
    let op := entry.2
    for kv in op.attrs.entries do
      if kv.1 = symKey then
        match kv.2 with
        | .stringAttr name =>
          -- `String.fromUTF8?` (non-panicking): the parser only produces
          -- UTF-8 StringAttrs today, but a panic here would leak through
          -- any future caller that constructs StringAttrs programmatically.
          if let some decoded := String.fromUTF8? name.value then
            let storedRef := "@" ++ decoded
            if storedRef = ref.value then
              return some opPtr
        | _ => continue
  none

/--
  Attempt to resolve a (possibly nested) symbol reference. Today
  this just dispatches to the flat resolver if the reference has no
  nested segments; nested resolution will be extended when nested
  parsing is supported (Phase G.2/G.3 milestones).

  Note: takes the resolution site as an `OperationPtr` for future
  scope-aware resolution; today it's unused (resolution is
  flat-and-global). Pass writers should still pass the use site so
  they don't break when scoping lands.
-/
def IRContext.resolveSymbol {OpInfo : Type} [HasOpInfo OpInfo]
    (ctx : IRContext OpInfo) (_fromOp : OperationPtr) (ref : SymbolRefAttr) :
    Option OperationPtr :=
  -- Today: only the root segment is consulted; nested segments are
  -- ignored. When G.2/G.3 needs nested resolution, the second
  -- argument enables walking up region scopes from `_fromOp`.
  if ref.nestedRefs.isEmpty then
    ctx.resolveFlatSymbol ⟨ref.rootRef⟩
  else
    -- Conservative: refuse to "succeed" on a nested path we can't
    -- correctly resolve. Better to return none than to silently
    -- return the wrong op.
    none

/--
  Dispatch on `Attribute` to a symbol resolver. Pass-level convenience:
  if the attribute is a `flatSymbolRefAttr` or `symbolRefAttr`,
  attempt resolution; otherwise return `none`.
-/
def IRContext.resolveSymbolAttr {OpInfo : Type} [HasOpInfo OpInfo]
    (ctx : IRContext OpInfo) (fromOp : OperationPtr) (attr : Attribute) :
    Option OperationPtr :=
  match attr with
  | .flatSymbolRefAttr ref => ctx.resolveFlatSymbol ref
  | .symbolRefAttr ref => ctx.resolveSymbol fromOp ref
  | _ => none

end

end Veir

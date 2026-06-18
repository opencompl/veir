#!/usr/bin/env python3
"""Translates LLVM GlobalISel MIR patterns to Veir RISCV PatternRewriter rules."""

import re
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

# Map G_* opcodes to the Veir matcher name (from Veir.Passes.RISCVMatching).
# These match the LLVM dialect (.llvm .add etc.). Value: matcher function name.
LLVM_OPS = {
    'G_ADD': 'matchAdd', 'G_SUB': 'matchSub', 'G_MUL': 'matchMul',
    'G_SDIV': 'matchSdiv', 'G_UDIV': 'matchUdiv',
    'G_SREM': 'matchSrem', 'G_UREM': 'matchUrem',
    'G_AND': 'matchAnd', 'G_OR': 'matchOr', 'G_XOR': 'matchXor',
    'G_SHL': 'matchShl', 'G_LSHR': 'matchLshr', 'G_ASHR': 'matchAshr',
}

# Whether a matcher's `let some (...)` binding includes a trailing `properties`
# component. matchAnd is the odd one out and returns only (lhs, rhs).
MATCHER_HAS_PROPS = {
    'matchAdd': True, 'matchSub': True, 'matchMul': True,
    'matchSdiv': True, 'matchUdiv': True, 'matchSrem': True, 'matchUrem': True,
    'matchAnd': False, 'matchOr': True, 'matchXor': True,
    'matchShl': True, 'matchLshr': True, 'matchAshr': True,
}

BUILTIN_OPS = {'GIReplaceReg', 'GIEraseRoot', 'COPY'}

@dataclass
class Operand:
    name: str                   # e.g. "$dst", "$zero"
    ty: Optional[str] = None    # e.g. "root" from root:$dst
    is_imm: bool = False   # is immediate
    imm_val: Optional[int] = None  # immediate value


@dataclass
class Inst:
    op: str                        # e.g. "G_ADD", "GIReplaceReg"
    operands: List[Operand] = field(default_factory=list)
    name: Optional[str] = None     # optional inst name like :$mi


@dataclass
class PatFrag:
    name: str                          # e.g. "binop_left_to_zero_frags"
    outs: List[Tuple[str, str]]        # (type, name) pairs
    ins: List[Tuple[str, str]]
    alts: List[List[Inst]] = field(default_factory=list)   # possible expansions


@dataclass 
class Rule:
    name: str
    defs: List[str]
    match: List[Inst] = field(default_factory=list)     # pattern to match
    apply: List[Inst] = field(default_factory=list)     # replacement
    has_cpp: bool = False
    has_cpp_match: bool = False
    has_wip_match: bool = False
    has_matchdata: bool = False


class Parser:
    def __init__(self, src: str):
        self.src = src
        self.frags: Dict[str, PatFrag] = {}
        self.rules: Dict[str, Rule] = {}
    
    def parse(self):
        self._parse_frags()  # parse GICombinePatFrags
        self._parse_rules()  # parse GICombineRules
    
    def _extract_body(self, start: int, open_ch: str, close_ch: str) -> Optional[str]:
        depth, i = 1, start
        while i < len(self.src) and depth > 0:
            if self.src[i] == open_ch: depth += 1
            elif self.src[i] == close_ch: depth -= 1
            i += 1
        return self.src[start:i-1] if depth == 0 else None
    
    def _parse_frags(self):
        for m in re.finditer(r'def\s+(\w+)\s*:\s*GICombinePatFrag\s*<', self.src):
            body = self._extract_body(m.end(), '<', '>')
            if not body:
                continue
            
            outs_m = re.search(r'\(outs\s+([^)]+)\)', body)
            ins_m = re.search(r'\(ins\s*([^)]*)\)', body)
            outs = self._parse_params(outs_m.group(1)) if outs_m else []
            ins = self._parse_params(ins_m.group(1)) if ins_m else []
            
            frag = PatFrag(name=m.group(1), outs=outs, ins=ins)
            
            foreach_m = re.search(r'!\s*foreach\s*\(\s*(\w+)\s*,\s*\[([^\]]+)\]\s*,\s*\(pattern\s+', body, re.DOTALL)
            if foreach_m:
                var = foreach_m.group(1)
                ops = [o.strip() for o in foreach_m.group(2).split(',')]
                pat_start = foreach_m.end()
                pat = self._extract_balanced(body, pat_start)
                if pat:
                    for op in ops:
                        insts = self._parse_insts(pat.replace(var, op))
                        if insts:
                            frag.alts.append(insts)
            else:
                # Try pattern list in brackets - find each (pattern ...) with balanced parens
                for pm in re.finditer(r'\(pattern\s+', body):
                    pat = self._extract_balanced(body, pm.end())
                    if pat:
                        insts = self._parse_insts(pat)
                        if insts:
                            frag.alts.append(insts)
            
            if frag.alts:
                self.frags[frag.name] = frag
    
    def _extract_balanced(self, s: str, start: int) -> Optional[str]:
        """Extract content until parens are balanced (one more close than open)."""
        depth, i = 0, start
        while i < len(s):
            if s[i] == '(':
                depth += 1
            elif s[i] == ')':
                if depth == 0:
                    return s[start:i]
                depth -= 1
            i += 1
        return None
    
    def _parse_rules(self):
        for m in re.finditer(r'def\s+(\w+)\s*:\s*GICombineRule\s*<', self.src):
            body = self._extract_body(m.end(), '<', '>')
            if not body:
                continue
            
            rule = Rule(name=m.group(1), defs=[])
            rule.has_cpp = '[{' in body or '${' in body
            rule.has_wip_match = 'wip_match_opcode' in body
            rule.has_matchdata = '_matchinfo' in body or '_matchdata' in body
            
            defs_m = re.search(r'\(defs\s+([^)]+)\)', body)
            if defs_m:
                for item in defs_m.group(1).split(','):
                    item = item.strip()
                    rule.defs.append(item.split(':')[1].strip() if ':' in item else item)
            
            match_m = re.search(r'\(match\s+(.+?)\)\s*,\s*\(apply', body, re.DOTALL)
            if match_m:
                content = match_m.group(1)
                rule.has_cpp_match = '[{' in content
                rule.match = self._parse_insts(re.sub(r'\[\{.*?\}\]', '', content, flags=re.DOTALL))
            
            apply_m = re.search(r'\(apply\s+(.+?)\)\s*(?:>|$)', body, re.DOTALL)
            if apply_m:
                content = apply_m.group(1)
                if '[{' in content:
                    rule.has_cpp = True
                rule.apply = self._parse_insts(re.sub(r'\[\{.*?\}\]', '', content, flags=re.DOTALL))
            
            self.rules[rule.name] = rule
    
    def _parse_params(self, s: str) -> List[Tuple[str, str]]:
        params = []
        for p in s.split(','):
            p = p.strip()
            if ':' in p:
                ty, name = p.split(':', 1)
                params.append((ty.strip(), name.strip()))
            elif p.startswith('$'):
                params.append(('', p))
        return params
    
    def _parse_insts(self, s: str) -> List[Inst]:
        insts, depth, cur = [], 0, ""
        for c in s:
            if c == '(':
                if depth == 0: cur = ""
                depth += 1
                cur += c
            elif c == ')':
                depth -= 1
                cur += c
                if depth == 0:
                    inst = self._parse_inst(cur.strip())
                    if inst:
                        insts.append(inst)
                    cur = ""
            elif depth > 0:
                cur += c
        return insts
    
    def _parse_inst(self, s: str) -> Optional[Inst]:
        name_m = re.search(r'\)\s*:\s*\$(\w+)\s*$', s)
        name = f"${name_m.group(1)}" if name_m else None
        if name_m:
            s = s[:name_m.start()] + ')'
        
        if not (s.startswith('(') and s.endswith(')')):
            return None
        
        tokens = self._tokenize(s[1:-1].strip())
        if not tokens:
            return None
        
        inst = Inst(op=tokens[0], name=name)
        for t in tokens[1:]:
            op = self._parse_operand(t)
            if op:
                inst.operands.append(op)
        return inst
    
    def _tokenize(self, s: str) -> List[str]:
        tokens, cur, depth = [], "", 0
        for c in s:
            if c == '(': depth += 1; cur += c
            elif c == ')': depth -= 1; cur += c
            elif (c == ',' or c.isspace()) and depth == 0:
                if cur.strip(): tokens.append(cur.strip())
                cur = ""
            else: cur += c
        if cur.strip():
            tokens.append(cur.strip())
        return tokens
    
    def _parse_operand(self, t: str) -> Optional[Operand]:
        t = t.strip()
        
        if m := re.match(r'\(GITypeOf<"\$\w+">\s+(-?\d+)\)', t):
            return Operand(name="", is_imm=True, imm_val=int(m.group(1)))
        if m := re.match(r'\((\w+)\s+(-?\d+)\)', t):
            return Operand(name="", ty=m.group(1), is_imm=True, imm_val=int(m.group(2)))
        if re.match(r'^-?\d+$', t):
            return Operand(name="", is_imm=True, imm_val=int(t))
        if m := re.match(r'(-?\d+):\$(\w+)', t):
            return Operand(name=f"${m.group(2)}", is_imm=True, imm_val=int(m.group(1)))
        if m := re.match(r'(\w+):\$(\w+)', t):
            return Operand(name=f"${m.group(2)}", ty=m.group(1))
        if t.startswith('$'):
            return Operand(name=t)
        if m := re.match(r'GITypeOf<"\$\w+">:(\$\w+)', t):
            return Operand(name=m.group(1))
        return None


class VeirEmitter:
    """Emits a single Veir PatternRewriter rule from a match/apply pair.

    Veir model:
      - The match is a DAG of `G_*` instructions. The root op is matched with
        `matchXxx op rewriter.ctx`, binding its source operands.
      - Operands defined by *another* matched instruction are followed with
        `getDefiningOp` and matched recursively (multi-operation patterns).
      - Immediate / constant operands are matched with `matchConstantIntVal`
        plus an equality guard on the integer value.
      - A register used twice (e.g. `x op x`) gets a fresh second binding and an
        `if a != b then return rewriter` guard.
      - The apply replaces the root result with an already-bound register via
        `replaceValue`, then erases the root with `eraseOp`.

    Rules whose apply *constructs* new ops or a fresh constant are skipped:
    the matching API does not expose an op-builder, so there is nothing to call.
    """

    def __init__(self):
        self.lines: List[str] = []
        self.var_of: Dict[str, str] = {}  # TableGen name -> bound Lean ident
        self.used: set = set()            # all Lean idents already in scope
        self.guards: List[str] = []       # equality / constant guards (deferred)

    # -- helpers --------------------------------------------------------------

    @staticmethod
    def _ssa(name: str) -> str:
        """TableGen name "$x" -> Lean identifier "x"."""
        return name[1:] if name.startswith('$') else name

    def _fresh(self, base: str) -> str:
        nm, k = base, 1
        while nm in self.used:
            nm = f"{base}{k}"; k += 1
        self.used.add(nm)
        return nm

    # -- match tree -----------------------------------------------------------

    def _emit_match(self, root: Inst, op_expr: str,
                    defs: Dict[str, Inst]) -> bool:
        """Emit the matcher for `root` (whose op handle is `op_expr`), recursing
        into operands defined by other matched instructions. Returns success."""
        matcher = LLVM_OPS.get(root.op)
        if not matcher:
            return False
        srcs = root.operands[1:]
        # Two-source binops only (everything in LLVM_OPS is binary here).
        if len(srcs) != 2:
            return False

        has_props = MATCHER_HAS_PROPS.get(matcher, True)
        binds = []
        for i, o in enumerate(srcs):
            if o.is_imm and not o.name:
                base = "rhs" if i == 1 else "lhs"
            elif o.name:
                base = self._ssa(o.name)
            else:
                base = f"a{i}"
            nm = self._fresh(base)
            binds.append(nm)
            # Record binding for operands that carry a name. A repeated register
            # is recorded only once so the second occurrence triggers a guard.
            if o.name:
                if o.name in self.var_of:
                    self.guards.append(
                        f"  if {self.var_of[o.name]} != {nm} then return rewriter")
                else:
                    self.var_of[o.name] = nm

        # Bind the properties under a per-opcode name so the apply side can reuse
        # the matched record when it builds a new op of the same kind.
        if has_props:
            pnm = self._fresh("_props")
            self.props_of.setdefault(root.op, pnm)
            prop_bind = pnm
        else:
            prop_bind = "_"
        tup = ", ".join(binds + ([prop_bind] if has_props else []))
        self.lines.append(
            f"  let some ({tup}) := {matcher} {op_expr} rewriter.ctx | return rewriter")

        # Now resolve each source: constant guard, or recurse into sub-op.
        for o, nm in zip(srcs, binds):
            if o.is_imm:
                cst = self._fresh("cst")
                self.guards.append(
                    f"  let some {cst} := matchConstantIntVal {nm} rewriter.ctx | return rewriter")
                self.guards.append(
                    f"  if {cst}.value ≠ {o.imm_val} then return rewriter")
            elif o.name in defs and defs[o.name] is not root:
                # This operand is produced by another matched instruction.
                sub = defs[o.name]
                opnm = self._fresh("defOp")
                self.lines.append(
                    f"  let some {opnm} := getDefiningOp {nm} rewriter.ctx | return rewriter")
                if not self._emit_match(sub, opnm, defs):
                    return False
        return True

    # -- main entry -----------------------------------------------------------

    def emit_rule(self, name: str, comment: str,
                  match: List[Inst], apply: List[Inst]) -> Optional[str]:
        self.lines, self.var_of, self.used, self.guards = [], {}, set(), []
        self.props_of = {}

        # Build def map: result-name -> defining instruction.
        defs = {i.operands[0].name: i for i in match
                if i.op in LLVM_OPS and i.operands}
        if not defs:
            return None

        # Root = instruction whose result is not consumed by another match inst.
        consumed = {o.name for i in match if i.op in LLVM_OPS
                    for o in i.operands[1:] if o.name}
        roots = [i for n, i in defs.items() if n not in consumed]
        if len(roots) != 1:
            return None
        root = roots[0]
        root_result = root.operands[0].name

        # Emit the (possibly nested) match first; the apply may reference any
        # value bound here.
        if not self._emit_match(root, "op", defs):
            return None
        # Deferred guards (constants, equalities) go after all the binds.
        self.lines.extend(self.guards)

        # Now emit the apply. Three supported shapes:
        #   (a) replace with an already-matched register (replaceValue/eraseOp),
        #   (b) produce a fresh constant         (createOp mlir__constant),
        #   (c) build one new binop from matched operands (createOp + replaceOp).
        if not self._emit_apply(apply, root):
            return None

        header = [
            "set_option warn.sorry false in",
            f"def {name} (rewriter: PatternRewriter OpCode) (op: OperationPtr)",
            "    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do",
        ]
        return "\n".join(header + self.lines) + "\n"

    # -- apply side -----------------------------------------------------------

    def _emit_apply(self, apply: List[Inst], root: Inst) -> bool:
        if len(apply) != 1:
            return False
        inst = apply[0]

        # (a) Replace-with-register.
        if inst.op in ('GIReplaceReg', 'COPY') and len(inst.operands) >= 2:
            src = inst.operands[1]
            if src.is_imm:
                # Replace the whole op with a fresh constant of value src.imm_val.
                return self._emit_const_result(src.imm_val, root)
            repl_var = self.var_of.get(src.name)
            if repl_var is None:
                return False
            self.lines.append(
                f"  let rewriter := rewriter.replaceValue (op.getResult 0) {repl_var} sorry sorry sorry")
            self.lines.append("  rewriter.eraseOp op sorry sorry sorry")
            return True

        # (c) Build a single new binop, e.g. (G_SUB $dst, 0, $x) for mul_by_neg_one.
        if inst.op in LLVM_OPS and len(inst.operands) == 3:
            return self._emit_new_binop(inst, root)

        return False

    def _type_of(self, var: str) -> str:
        """A value expression for the LLVM integer type of a bound register."""
        return f"{var}.getType! rewriter.ctx.raw"

    def _emit_const_result(self, imm_val: int, root: Inst) -> bool:
        """Replace the root op with a freshly-built integer constant `imm_val`.
        Mirrors subiSelfToZero / mulIZeroToCst from InstCombine."""
        # Pick any matched register to source the integer type from.
        anchor = next((v for v in self.var_of.values()), None)
        if anchor is None:
            return False
        self.lines.append(
            f"  let .integerType type := ({self._type_of(anchor)}).val | return rewriter")
        self.lines.append(
            f"  let cstProp := LLVMConstantProperties.mk (.integer (IntegerAttr.mk ({imm_val}) type))")
        self.lines.append(
            f"  let (rewriter, newOp) ← rewriter.createOp (.llvm .mlir__constant) #[{self._type_of(anchor)}] #[]")
        self.lines.append(
            "    #[] #[] cstProp (some $ .before op) sorry sorry sorry sorry")
        self.lines.append("  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry")
        return True

    def _emit_new_binop(self, inst: Inst, root: Inst) -> bool:
        """Build a new two-operand op and replace the root with it. Operands may
        be matched registers or fresh constants (each needs its own createOp)."""
        new_matcher = LLVM_OPS[inst.op]
        op_llvm = self._llvm_dialect_name(inst.op)
        if op_llvm is None:
            return False

        # Resolve the two source operands to value expressions.
        arg_exprs = []
        anchor = next((v for v in self.var_of.values()), None)
        if anchor is None:
            return False
        for o in inst.operands[1:3]:
            if o.is_imm:
                # Materialise a constant operand before the new binop.
                cvar = self._fresh("cstOp")
                self.lines.append(
                    f"  let .integerType ctype := ({self._type_of(anchor)}).val | return rewriter")
                self.lines.append(
                    f"  let {cvar}Prop := LLVMConstantProperties.mk (.integer (IntegerAttr.mk ({o.imm_val}) ctype))")
                self.lines.append(
                    f"  let (rewriter, {cvar}) ← rewriter.createOp (.llvm .mlir__constant) #[{self._type_of(anchor)}] #[]")
                self.lines.append(
                    f"    #[] #[] {cvar}Prop (some $ .before op) sorry sorry sorry sorry")
                arg_exprs.append(f"({cvar}.getResult 0)")
            else:
                v = self.var_of.get(o.name)
                if v is None:
                    return False
                arg_exprs.append(v)

        args = ", ".join(arg_exprs)
        prop = self._prop_expr(inst.op)
        if prop is None:
            return False
        self.lines.append(
            f"  let (rewriter, newOp) ← rewriter.createOp (.llvm {op_llvm}) #[{self._type_of(anchor)}] #[{args}]")
        self.lines.append(
            f"    #[] #[] {prop} (some $ .before op) sorry sorry sorry sorry")
        self.lines.append("  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry")
        return True

    # Property *class* per opcode, from the dialect's properties-from-attr map.
    # Opcodes in the same class share the same `propertiesOf` type, so a matched
    # op's `_props` can be reused for any built op in the same class.
    _PROP_CLASS = {
        'G_ADD': 'NswNuw', 'G_SUB': 'NswNuw', 'G_MUL': 'NswNuw', 'G_SHL': 'NswNuw',
        'G_UDIV': 'Exact', 'G_SDIV': 'Exact', 'G_LSHR': 'Exact', 'G_ASHR': 'Exact',
        'G_OR': 'Disjoint',
        # G_XOR, G_AND, G_SREM, G_UREM, ... carry no record -> unit class below.
    }

    # Opcodes whose `propertiesOf` is the trivial unit type -> `()`.
    _UNIT_PROP_OPS = {
        'G_XOR', 'G_AND', 'G_SREM', 'G_UREM',
    }

    def _prop_expr(self, g_op: str) -> Optional[str]:
        """Properties value for a newly-built op of kind `g_op`.

        `propertiesOf` is indexed by opcode but several opcodes share a property
        record type (add/sub/mul/shl -> NswNuw; the *div/*shr -> Exact). Order:
          1. reuse a matched op's `_props` if that matched op shares `g_op`'s
             property class (same record type -> type-correct, keeps real flags),
          2. else `()` for unit-property opcodes (xor/and/rem/...),
          3. else `sorry` for a record-property opcode with nothing to reuse;
             the concrete opcode in createOp pins its type, so it's a fillable
             hole rather than a type error.
        """
        cls = self._PROP_CLASS.get(g_op)
        if cls is not None:
            for matched_op, pnm in self.props_of.items():
                if self._PROP_CLASS.get(matched_op) == cls:
                    return pnm
        if g_op in self.props_of:
            return self.props_of[g_op]
        if g_op in self._UNIT_PROP_OPS:
            return "()"
        return "sorry"

    @staticmethod
    def _llvm_dialect_name(g_op: str) -> Optional[str]:
        return {
            'G_ADD': '.add', 'G_SUB': '.sub', 'G_MUL': '.mul',
            'G_AND': '.and', 'G_OR': '.or', 'G_XOR': '.xor',
            'G_SHL': '.shl', 'G_LSHR': '.lshr', 'G_ASHR': '.ashr',
            'G_SDIV': '.sdiv', 'G_UDIV': '.udiv',
            'G_SREM': '.srem', 'G_UREM': '.urem',
        }.get(g_op)

    def _replacement(self, apply: List[Inst]) -> Optional[str]:
        """Best-effort name of the surviving register for comment generation
        only. Returns the apply's replacement register, or None."""
        if len(apply) != 1:
            return None
        inst = apply[0]
        if inst.op in ('GIReplaceReg', 'COPY') and len(inst.operands) >= 2:
            src = inst.operands[1]
            return None if src.is_imm else src.name
        return None


class Generator:
    def __init__(self, parser: Parser):
        self.parser = parser
        self.emitter = VeirEmitter()
        self.generated: List[str] = []
        self.skipped: Dict[str, str] = {}
    
    def generate(self) -> str:
        lines = [
            "import Veir.Pass",
            "import Veir.PatternRewriter.Basic",
            "import Veir.Passes.Matching",
            "",
            "namespace Veir.RISCV",
            "",
        ]
        
        for name, rule in self.parser.rules.items():
            if result := self._gen_rule(name, rule):
                lines.append(result)
        
        lines.append(self._gen_list())
        lines.append("")
        lines.append("end Veir.RISCV")
        return "\n".join(lines)
    
    def _gen_rule(self, name: str, rule: Rule) -> Optional[str]:
        if rule.has_wip_match:
            self.skipped[name] = "uses wip_match_opcode"; return None
        if rule.has_cpp_match:
            self.skipped[name] = "contains C++ in match"; return None
        if rule.has_cpp and not all(i.op in BUILTIN_OPS or i.op in LLVM_OPS for i in rule.apply):
            self.skipped[name] = "contains C++ in apply"; return None
        if rule.has_matchdata:
            self.skipped[name] = "uses matchdata"; return None
        if not rule.match or not rule.apply:
            self.skipped[name] = "no match/apply"; return None
        
        expanded = self._expand_frags(rule.match)
        if not expanded:
            self.skipped[name] = "PatFrag expansion failed"; return None
        
        for alt in expanded:
            for inst in alt:
                if inst.op not in LLVM_OPS and inst.op not in BUILTIN_OPS and inst.op not in self.parser.frags:
                    self.skipped[name] = f"unsupported: {inst.op}"; return None
        
        results = []
        for i, match in enumerate(expanded):
            suffix = f"_{i}" if len(expanded) > 1 else ""
            full = name + suffix
            if r := self.emitter.emit_rule(full, "", match, rule.apply):
                results.append(r)
                self.generated.append(full)
            else:
                self.skipped[name] = "unsupported Veir shape"
        
        return "\n".join(results) if results else None
    
    def _comment(self, match: List[Inst], apply: List[Inst]) -> str:
        # Root = the match inst whose result isn't consumed by another match inst.
        defs = {i.operands[0].name: i for i in match if i.op in LLVM_OPS and i.operands}
        consumed = {o.name for i in match if i.op in LLVM_OPS
                    for o in i.operands[1:] if o.name}
        roots = [i for n, i in defs.items() if n not in consumed]
        if not roots:
            return "translated rule"
        root = roots[0]
        opname = {
            'G_ADD': 'add', 'G_SUB': 'sub', 'G_MUL': 'mul', 'G_AND': 'and',
            'G_OR': 'or', 'G_XOR': 'xor', 'G_SHL': 'shl', 'G_LSHR': 'lshr',
            'G_ASHR': 'ashr', 'G_SDIV': 'sdiv', 'G_UDIV': 'udiv',
            'G_SREM': 'srem', 'G_UREM': 'urem',
        }.get(root.op, root.op.lower())
        parts = []
        for op in root.operands[1:3]:
            if op.is_imm:
                parts.append(str(op.imm_val))
            elif op.name:
                parts.append(op.name[1:] if op.name.startswith('$') else op.name)
        repl = self.emitter._replacement(apply)
        repl_s = (repl[1:] if repl and repl.startswith('$') else repl) or "x"
        return f"llvm.{opname} {' '.join(parts)} -> {repl_s}"
    
    def _expand_frags(self, insts: List[Inst]) -> Optional[List[List[Inst]]]:
        if not any(i.op in self.parser.frags for i in insts):
            return [insts]
        
        alts = [[]]
        for inst in insts:
            if inst.op not in self.parser.frags:
                for a in alts: a.append(inst)
                continue
            
            frag = self.parser.frags[inst.op]
            new_alts = []
            for frag_alt in frag.alts:
                if any(i.op not in LLVM_OPS and i.op not in BUILTIN_OPS for i in frag_alt):
                    continue
                expanded = self._subst_frag(frag, inst, frag_alt)
                if expanded:
                    for existing in alts:
                        new_alts.append(existing + expanded)
            if not new_alts:
                return None
            alts = new_alts
        
        return alts if alts and alts[0] else None
    
    def _subst_frag(self, frag: PatFrag, call: Inst, alt: List[Inst]) -> List[Inst]:
        param_map = {}
        for i, (_, param) in enumerate(frag.outs + frag.ins):
            if i < len(call.operands):
                param_map[param] = call.operands[i].name
        
        result = []
        for inst in alt:
            new_ops = [
                Operand(name=param_map.get(op.name, op.name), ty=op.ty, is_imm=op.is_imm, imm_val=op.imm_val)
                for op in inst.operands
            ]
            result.append(Inst(op=inst.op, operands=new_ops, name=inst.name))
        return result
    
    def _gen_list(self) -> str:
        if not self.generated:
            return "def mir_pattern_combines : List (PatternRewriter OpCode -> OperationPtr -> _) := []"
        
        lines = ["def mir_pattern_combines :="]
        entries = [f"  {n}" for n in self.generated]
        lines.append("  [" + entries[0].strip() + ",")
        for e in entries[1:-1]:
            lines.append(f"  {e.strip()},")
        if len(entries) > 1:
            lines.append(f"  {entries[-1].strip()}]")
        else:
            lines[-1] = "  [" + entries[0].strip() + "]"
        return "\n".join(lines)


def main():
    if len(sys.argv) < 2:
        print("Usage: auto_mir_veir.py <Combine.td> [--verbose]")
        sys.exit(1)
    
    verbose = "--verbose" in sys.argv
    
    with open(sys.argv[1]) as f:
        src = f.read()
    
    parser = Parser(src)
    parser.parse()
    print(f"Found {len(parser.rules)} rules")
    
    gen = Generator(parser)
    output = gen.generate()
    
    with open("../MIRCombinesVeir.lean", 'w') as f:
        f.write(f"-- AUTOGENERATED Veir file: Automated GlobalISel pattern translation from {"/".join(sys.argv[1].split('/')[3::])}\n\n")
        f.write(output)
    
    print(f"Translated: {len(gen.generated)} | Skipped: {len(gen.skipped)}")
    
    if verbose:
        by_reason = {}
        for name, reason in gen.skipped.items():
            by_reason.setdefault(reason, []).append(name)
        for reason, names in sorted(by_reason.items(), key=lambda x: -len(x[1])):
            print(f"  [{reason}] {len(names)}")


if __name__ == "__main__":
    main()
-- SUMMARY: The encoder intermediate language, the traversal into it, and its well-formedness.
import Mica.Base.Arity
import Mica.FOL.Formulas
import Mica.Base.Fixpoint
import Mica.Base.Except
import Mica.SourceTinyML.Typed
import Mica.Base.Fresh
import Mica.Verifier.RelationalEncoding.Variables

/-!
# The encoder intermediate language

`Expr` is what is left of a typed TinyML expression once its pure syntax is
resolved into value terms: a tree of calls and conditionals ending in a value.
Because a call names its result, both encodings consume the *same* tree. The
relational one binds the name existentially, the split one substitutes the
value function for it; that asymmetry is all that Skolemization is.

`encodeWith` builds the tree in continuation-passing style — every leaf hands
its value term to the continuation; `call` allocates the name of its result and
puts the continuation under it; for `ite` the continuation is pushed into both
branches, which are generated from the same supply because their scopes are
disjoint.

`Expr.WfIn` is the well-formedness of the tree: it is established once, by
induction over `Typed.Expr` (`encode_wfIn`), and consumed by each encoding
in three cases.
-/

namespace Verifier.RelationalEncoding

/-! ## The encoder intermediate language -/

/-- What is left of a TinyML expression once the traversal has resolved its
pure syntax into value terms: a tree of calls and conditionals ending in a
value.

* `ret` is the finished value term;
* `call` applies a relation-marked function and binds its result to a name;
* `ite` branches on a boolean term. -/
inductive Expr where
  | ret  : Term .value → Expr
  | call : SpecFn → Term .value → String → Expr → Expr
  | ite  : Term .bool → Expr → Expr → Expr

/-- Well-formedness of an IR expression: every term it mentions is well-formed
in `Δ`, every call resolves in `Γ`, and every call binds a name that is fresh
for `Δ` and outside `avoid`. Declaring the binder before the continuation makes
nested binders distinct as well; conditional branches may reuse a name, their
scopes being disjoint. -/
inductive Expr.WfIn (Γ : FunCtx) (avoid : List String) : Signature → Expr → Prop where
  | ret {Δ v} : v.wfIn Δ → WfIn Γ avoid Δ (.ret v)
  | call {Δ f fn arg r c} :
      (f, fn) ∈ Γ → arg.wfIn Δ → r ∉ avoid → r ∉ Δ.allNames →
      WfIn Γ avoid (Δ.declVar ⟨r, .value⟩) c →
      WfIn Γ avoid Δ (.call fn arg r c)
  | ite {Δ cond t e} :
      cond.wfIn Δ → WfIn Γ avoid Δ t → WfIn Γ avoid Δ e → WfIn Γ avoid Δ (.ite cond t e)

/-- Protecting fewer names is a weaker requirement. -/
theorem Expr.WfIn.weaken {Γ : FunCtx} {avoid avoid' : List String} {Δ : Signature} {c : Expr}
    (h : Expr.WfIn Γ avoid Δ c) (hsub : ∀ n ∈ avoid', n ∈ avoid) :
    Expr.WfIn Γ avoid' Δ c := by
  induction h with
  | ret hv => exact .ret hv
  | call hmem harg hr hfresh _ ih => exact .call hmem harg (fun hm => hr (hsub _ hm)) hfresh ih
  | ite hcond _ _ iht ihe => exact .ite hcond iht ihe

/-- Well-formedness transports to an extension that only adds names the call
binders already avoid. -/
theorem Expr.WfIn.mono {Γ : FunCtx} {avoid : List String} {Δ Δ' : Signature} {c : Expr}
    (h : Expr.WfIn Γ avoid Δ c) (hsub : Δ.Subset Δ') (hwf : Δ'.wf)
    (hnew : ∀ n ∈ Δ'.allNames, n ∈ Δ.allNames ∨ n ∈ avoid) :
    Expr.WfIn Γ avoid Δ' c := by
  induction h generalizing Δ' with
  | ret hv => exact .ret (Term.wfIn_mono _ hv hsub hwf)
  | @call Δ f fn arg r c hmem harg hr hfresh _ ih =>
      have hfresh' : r ∉ Δ'.allNames := fun hm => (hnew r hm).elim hfresh hr
      refine .call hmem (Term.wfIn_mono _ harg hsub hwf) hr hfresh'
        (ih (Signature.Subset.declVar hsub _) (Signature.wf_declVar hwf) ?_)
      intro n hn
      rw [Signature.allNames_declVar_of_not_in hfresh'] at hn
      rw [Signature.allNames_declVar_of_not_in hfresh]
      exact (List.mem_cons.mp hn).elim (fun h => .inl (h ▸ List.mem_cons_self ..))
        (fun h => (hnew n h).imp (List.mem_cons_of_mem r) id)
  | ite hcond _ _ iht ihe =>
      exact .ite (Term.wfIn_mono _ hcond hsub hwf) (iht hsub hwf hnew) (ihe hsub hwf hnew)

/-! ## The primitive encoding table -/

/-- One named primitive encoding. It tells the encoder how to make a value
term from a saturated application of an intrinsic. This structure holds data
only. `PrimEncoding.Lawful` gives the laws that the relational encoder
requires of an entry. -/
structure PrimEncoding where
  /-- The name of the intrinsic that this entry encodes. `encodePrim` uses
      this name as the search key. -/
  name : String
  /-- The number of arguments that the encoding expects. -/
  arity : Arity
  /-- True if you can use the encoding in the signature. An entry that
      applies a declared symbol needs that declaration. An entry that builds
      a term without a symbol does not. -/
  available : Signature → Bool
  /-- Make the value term for a saturated application. `encodePrim` checks
      the number of arguments. Therefore the arguments arrive as a tuple. -/
  encode : Signature → Arity.tup arity (Term .value) → Term .value

/-- The laws that the relational encoder requires of a table entry. -/
structure PrimEncoding.Lawful (e : PrimEncoding) : Prop where
  /-- Let the encoding be available in `Δ`. Let `Δ'` extend `Δ`. If the
      arguments are well-formed in `Δ'`, then the term is also well-formed
      in `Δ'`. -/
  wfIn : ∀ {Δ Δ' : Signature} {args : Arity.tup e.arity (Term .value)},
    e.available Δ = true → Δ.Subset Δ' → Δ'.wf →
    Arity.All (·.wfIn Δ') e.arity args → (e.encode Δ args).wfIn Δ'

/-- The primitive table of the encoder. It holds one entry for each intrinsic
that the encoder can encode. -/
abbrev PrimEncodings := List PrimEncoding

/-- A table is lawful if each of its entries is lawful. -/
def PrimEncodings.Lawful (primitives : PrimEncodings) : Prop :=
  ∀ e ∈ primitives, e.Lawful

/-- Find the encoding for a name. This is the first entry with that `name`. -/
def PrimEncodings.lookup? (primitives : PrimEncodings) (name : String) : Option PrimEncoding :=
  primitives.find? (·.name == name)

/-- An encoding that the table returns is an entry of that table. -/
theorem PrimEncodings.mem_of_lookup? {primitives : PrimEncodings} {name : String}
    {e : PrimEncoding} (h : primitives.lookup? name = some e) : e ∈ primitives :=
  List.mem_of_find?_eq_some h

/-- An entry that a lawful table returns is itself lawful. -/
theorem PrimEncodings.Lawful.lookup? {primitives : PrimEncodings} (hlaw : primitives.Lawful)
    {name : String} {e : PrimEncoding} (h : primitives.lookup? name = some e) : e.Lawful :=
  hlaw e (PrimEncodings.mem_of_lookup? h)

/-! ## Intrinsic application encoder -/

/-- Encode a saturated intrinsic application with the primitive table. This
function makes the two checks that all entries share. It checks that the
table holds the name. It also checks that the application has the arity of
the entry. Therefore an entry only makes a term from an argument tuple. -/
def encodePrim (primitives : PrimEncodings) (Δ : Signature) (name : String)
    (vs : List (Term .value)) : Except String (Term .value) :=
  match primitives.lookup? name with
  | none => .error s!"relational encoding: unknown intrinsic `{name}`"
  | some encoding =>
      if hlen : vs.length = encoding.arity.toNat then
        if encoding.available Δ then
          .ok (encoding.encode Δ (Arity.ofList encoding.arity vs hlen))
        else .error s!"relational encoding: unavailable intrinsic `{name}`"
      else .error s!"relational encoding: intrinsic `{name}` applied at unsupported arity"

/-- A successful encoding is well-formed in each extension of the signature.
The encoding is available in the base signature `Δ`. The `wfIn` law of the
entry then gives well-formedness in `Δ'`. -/
theorem encodePrim_wfIn {primitives : PrimEncodings} {Δ Δ' : Signature}
    {n : String} {vs : List (Term .value)} {v : Term .value}
    (hlaw : primitives.Lawful) (h : encodePrim primitives Δ n vs = .ok v)
    (hsub : Δ.Subset Δ') (hΔ' : Δ'.wf)
    (hvs : ∀ w ∈ vs, w.wfIn Δ') : v.wfIn Δ' := by
  unfold encodePrim at h
  split at h
  · simp at h
  · rename_i encoding hlookup
    split at h
    · rename_i hlen
      split at h
      · rename_i hav
        simp only [Except.ok.injEq] at h
        subst v
        exact (hlaw.lookup? hlookup).wfIn (by simpa using hav) hsub hΔ'
          (Arity.ofList_all encoding.arity vs hlen hvs)
      · simp at h
    · simp at h

/-! ## Constant and operator encoders -/

/-- Encode a TinyML constant into a value-sorted FOL term. -/
def encodeConst : TinyML.Const → Term .value
  | .int  n => .unop .ofInt  (.const (.i n))
  | .bool b => .unop .ofBool (.const (.b b))
  | .char c => .unop .ofChar (.const (.char c))
  | .string s => .unop .ofString (.const (.str s))
  | .float b => .unop .ofFloat (.const (.fp b))
  | .unit   => .const .unit

/-- Encode a TinyML unary op acting on a value-sorted argument. -/
def encodeUnOp : TinyML.UnOp → Term .value → Except String (Term .value)
  | .neg,    v => .ok (.unop .ofInt  (.unop .neg (.unop .toInt  v)))
  | .not,    v => .ok (.unop .ofBool (.unop .not (.unop .toBool v)))
  | .proj n, v => .ok (.unop .vhead (vtailN (.unop .toValList v) n))

/-- Encode a TinyML binary op acting on two value-sorted arguments. -/
def encodeBinOp : TinyML.BinOp → Term .value → Term .value → Except String (Term .value)
  | .add, a, b => .ok (.unop .ofInt  (.binop .add  (.unop .toInt a) (.unop .toInt b)))
  | .sub, a, b => .ok (.unop .ofInt  (.binop .sub  (.unop .toInt a) (.unop .toInt b)))
  | .mul, a, b => .ok (.unop .ofInt  (.binop .mul  (.unop .toInt a) (.unop .toInt b)))
  | .div, a, b => .ok (.unop .ofInt  (.binop .div  (.unop .toInt a) (.unop .toInt b)))
  | .mod, a, b => .ok (.unop .ofInt  (.binop .mod  (.unop .toInt a) (.unop .toInt b)))
  | .lt,  a, b => .ok (.unop .ofBool (.binop .less (.unop .toInt a) (.unop .toInt b)))
  | .le,  a, b => .ok (.unop .ofBool (.binop .ge   (.unop .toInt b) (.unop .toInt a)))
  | .gt,  a, b => .ok (.unop .ofBool (.binop .gt   (.unop .toInt a) (.unop .toInt b)))
  | .ge,  a, b => .ok (.unop .ofBool (.binop .ge   (.unop .toInt a) (.unop .toInt b)))
  | .eq,  a, b => .ok (.unop .ofBool (.binop .eq             a              b))
  | .and, a, b => .ok (.unop .ofBool (.ite (.unop .toBool a) (.unop .toBool b) (.const (.b false))))
  | .or,  a, b => .ok (.unop .ofBool (.ite (.unop .toBool a) (.const (.b true)) (.unop .toBool b)))

/-! ## Well-formedness of the constant and operator encoders -/

theorem encodeConst_wfIn (c : TinyML.Const) (Δ : Signature) :
    (encodeConst c).wfIn Δ := by
  cases c <;> simp [encodeConst, Term.wfIn, UnOp.wfIn, Const.wfIn]

theorem encodeUnOp_wfIn {op : TinyML.UnOp} {v v' : Term .value} {Δ : Signature}
    (h : encodeUnOp op v = .ok v') (hv : v.wfIn Δ) : v'.wfIn Δ := by
  cases op with
  | neg =>
    simp only [encodeUnOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, trivial, hv⟩
  | not =>
    simp only [encodeUnOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, trivial, hv⟩
  | proj n =>
    simp only [encodeUnOp, Except.ok.injEq] at h; subst h
    have ht : (vtailN (.unop .toValList v) n).wfIn Δ := by
      apply vtailN_wfIn
      change UnOp.toValList.wfIn Δ ∧ v.wfIn Δ
      exact ⟨trivial, hv⟩
    change UnOp.vhead.wfIn Δ ∧ (vtailN (.unop .toValList v) n).wfIn Δ
    exact ⟨trivial, ht⟩

theorem encodeBinOp_wfIn {op : TinyML.BinOp} {v1 v2 v : Term .value} {Δ : Signature}
    (h : encodeBinOp op v1 v2 = .ok v) (h1 : v1.wfIn Δ) (h2 : v2.wfIn Δ) :
    v.wfIn Δ := by
  cases op
  case add | sub | mul | div | mod | lt | gt | ge =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, ⟨trivial, h1⟩, ⟨trivial, h2⟩⟩
  case le =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, ⟨trivial, h2⟩, ⟨trivial, h1⟩⟩
  case eq =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    exact ⟨trivial, trivial, h1, h2⟩
  case and =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    change UnOp.ofBool.wfIn Δ ∧
      (Term.ite (.unop .toBool v1) (.unop .toBool v2) (.const (.b false))).wfIn Δ
    exact ⟨trivial, ⟨⟨trivial, h1⟩, ⟨trivial, h2⟩, trivial⟩⟩
  case or =>
    simp only [encodeBinOp, Except.ok.injEq] at h; subst h
    change UnOp.ofBool.wfIn Δ ∧
      (Term.ite (.unop .toBool v1) (.const (.b true)) (.unop .toBool v2)).wfIn Δ
    exact ⟨trivial, ⟨⟨trivial, h1⟩, trivial, ⟨trivial, h2⟩⟩⟩

/-! ## The traversal -/

mutual
/-- Shared structural traversal of a typed TinyML expression in
continuation-passing style. The only place that pattern-matches on
`Typed.Expr`. It either produces an IR expression, drawing call-result names
from the supply, or the message naming what the encoder does not support. -/
def encodeWith (primitives : PrimEncodings) (Δ : Signature) (Γ : FunCtx) (δ : VarEnv) :
    Typed.Expr → (Term .value → NameSupply → Except String Expr) →
      NameSupply → Except String Expr
  | .const c, k, s => k (encodeConst c) s
  | .var x _ _, k, s =>
    match δ.lookup x with
    | some v => k v s
    | none => .error s!"unbound variable: {x}"
  | .prim n _ _, _, _ => .error s!"relational encoding: standalone primitive `{n}` is not supported"
  | .unop op e _, k, s =>
    encodeWith primitives Δ Γ δ e (fun v s' => do k (← encodeUnOp op v) s') s
  | .binop op e1 e2 _, k, s =>
    encodeWith primitives Δ Γ δ e1 (fun v1 s1 =>
      encodeWith primitives Δ Γ δ e2 (fun v2 s2 => do k (← encodeBinOp op v1 v2) s2) s1) s
  | .ifThenElse c t e _, k, s =>
    encodeWith primitives Δ Γ δ c (fun b s' => do
      let thenEnc ← encodeWith primitives Δ Γ δ t k s'
      let elseEnc ← encodeWith primitives Δ Γ δ e k s'
      .ok (.ite (.unop .toBool b) thenEnc elseEnc)) s
  | .tuple es, k, s =>
    encodeListWith primitives Δ Γ δ es
      (fun vs s' => k (.unop .ofValList (Terms.toValList vs)) s') s
  | .app (.var f _ _) [arg] _, k, s =>
    match FunCtx.lookup Γ f with
    | none     => .error s!"unknown function: {f}"
    | some rel =>
      encodeWith primitives Δ Γ δ arg (fun v s' => do
        let r := s'.fresh "r"
        .ok (.call rel v r (← k (.var .value r) (s'.reserve r)))) s
  | .app (.prim n _ _) args _, k, s =>
    encodeListWith primitives Δ Γ δ args
      (fun vs s' => do k (← encodePrim primitives Δ n vs) s') s
  | .letIn b bound body, k, s =>
    encodeWith primitives Δ Γ δ bound (fun v s' =>
      encodeWith primitives Δ Γ (VarEnv.bindBinder δ b v) body k s') s
  | .letProd bs bound body, k, s =>
    encodeWith primitives Δ Γ δ bound (fun v s' =>
      encodeWith primitives Δ Γ (VarEnv.bindBinders δ bs v) body k s') s
  | .inj tag arity payload _, k, s =>
    encodeWith primitives Δ Γ δ payload
      (fun v s' => k (.unop (.ofInj tag arity) v) s') s
  | .match_ scrut branches _, k, s =>
    encodeWith primitives Δ Γ δ scrut
      (fun v s' => encodeMatchWith primitives Δ Γ δ v branches 0 k s') s
  | .app _ _ _, _, _ => .error "relational encoding: only unary calls to named top-level functions are supported"
  | .fix .., _, _    => .error "relational encoding: nested `fix` is not supported"
  | .ref .., _, _    => .error "relational encoding: heap allocation (`ref`) is not supported"
  | .deref .., _, _  => .error "relational encoding: heap dereference is not supported"
  | .store .., _, _  => .error "relational encoding: heap store is not supported"
  | .arrayLen arr, k, s =>
    encodeWith primitives Δ Γ δ arr
      (fun v s' => k (.unop .ofInt (.unop .arrayLen v)) s') s
  | .arrayMake .., _, _ | .arrayGet .., _, _ | .arraySet .., _, _ =>
      .error "relational encoding: arrays are not supported"
  | .assert _, _, _  => .error "relational encoding: `assert` is not supported"

/-- Encode a list of expressions left-to-right, collecting their value terms.
This is the list companion to `encodeWith`, needed by tuple syntax and later
other n-ary constructs. -/
def encodeListWith (primitives : PrimEncodings) (Δ : Signature) (Γ : FunCtx) (δ : VarEnv) :
    List Typed.Expr → (List (Term .value) → NameSupply → Except String Expr) →
      NameSupply → Except String Expr
  | [], k, s => k [] s
  | e :: es, k, s =>
    encodeWith primitives Δ Γ δ e (fun v s' =>
      encodeListWith primitives Δ Γ δ es (fun vs s'' => k (v :: vs) s'') s') s

/-- Encode a `match_` as an if-let chain. For each non-final branch
`(b, body)` at index `i`, the code tests whether the scrutinee value's tag
equals `i`; on the true branch the binder is bound to the payload projection
before encoding `body`; on the false branch the remaining branches are tried.
The final branch is dispatched unconditionally — the elaborator guarantees an
exhaustive list, so the trailing case must hold. An empty list (which the
elaborator never produces) is conservatively rejected. -/
def encodeMatchWith (primitives : PrimEncodings) (Δ : Signature)
    (Γ : FunCtx) (δ : VarEnv) (scrut : Term .value) :
    List (Typed.Binder × Typed.Expr) → Nat →
      (Term .value → NameSupply → Except String Expr) → NameSupply → Except String Expr
  | [], _, _, _ => .error "match: non-exhaustive"
  | (b, body) :: rest, i, k, s =>
    let δ' := VarEnv.bindBinder δ b (.unop .payloadOf scrut)
    match rest with
    | [] => encodeWith primitives Δ Γ δ' body k s
    | _ :: _ => do
      let thenEnc ← encodeWith primitives Δ Γ δ' body k s
      let elseEnc ← encodeMatchWith primitives Δ Γ δ scrut rest (i + 1) k s
      .ok (.ite (.binop .eq (.unop .tagOf scrut) (.const (.i (i : Int)))) thenEnc elseEnc)
end

/-- The closed form of the traversal: the whole expression is the result, so
the continuation returns it. -/
def encode (primitives : PrimEncodings) (Δ : Signature) (Γ : FunCtx) (δ : VarEnv)
    (e : Typed.Expr) : NameSupply → Except String Expr :=
  encodeWith primitives Δ Γ δ e (fun v _ => .ok (.ret v))

/-! ## Well-formedness of the traversal -/

/-- Contract on a traversal continuation: at any signature the traversal can
reach and any supply covering it, a well-formed value term yields a
well-formed IR expression. -/
private abbrev WfCont (Γ : FunCtx) (Δ : Signature)
    (k : Term .value → NameSupply → Except String Expr) : Prop :=
  ∀ {Δ' : Signature} {s : NameSupply}, Δ.Subset Δ' → Δ'.wf → s.Covers Δ' →
    ∀ v, v.wfIn Δ' → ∀ c, k v s = .ok c → Expr.WfIn Γ s.avoid Δ' c

/-- List-valued companion of `WfCont`. -/
private abbrev WfListCont (Γ : FunCtx) (Δ : Signature)
    (k : List (Term .value) → NameSupply → Except String Expr) : Prop :=
  ∀ {Δ' : Signature} {s : NameSupply}, Δ.Subset Δ' → Δ'.wf → s.Covers Δ' →
    ∀ vs, (∀ v ∈ vs, v.wfIn Δ') → ∀ c, k vs s = .ok c → Expr.WfIn Γ s.avoid Δ' c

/-- Per-expression statement of `encodeWith_wfIn`. -/
private def EncodeWithWfIn (primitives : PrimEncodings) (e : Typed.Expr) : Prop :=
  ∀ {Γ : FunCtx} {Δ Δ' : Signature} {δ : VarEnv} {s : NameSupply}
    {k : Term .value → NameSupply → Except String Expr} {c : Expr},
    Δ.Subset Δ' → Δ'.wf → δ.wfIn Δ' → s.Covers Δ' → WfCont Γ Δ' k →
    encodeWith primitives Δ Γ δ e k s = .ok c → Expr.WfIn Γ s.avoid Δ' c

/-- Per-list statement of `encodeWith_wfIn`. -/
private def EncodeListWithWfIn (primitives : PrimEncodings) (es : List Typed.Expr) : Prop :=
  ∀ {Γ : FunCtx} {Δ Δ' : Signature} {δ : VarEnv} {s : NameSupply}
    {k : List (Term .value) → NameSupply → Except String Expr} {c : Expr},
    Δ.Subset Δ' → Δ'.wf → δ.wfIn Δ' → s.Covers Δ' → WfListCont Γ Δ' k →
    encodeListWith primitives Δ Γ δ es k s = .ok c → Expr.WfIn Γ s.avoid Δ' c

/-- Per-branch-list statement of `encodeWith_wfIn`, parametric in the
scrutinee value and starting index. -/
private def EncodeMatchWithWfIn (primitives : PrimEncodings)
    (branches : List (Typed.Binder × Typed.Expr)) : Prop :=
  ∀ {Γ : FunCtx} {Δ Δ' : Signature} {δ : VarEnv} {s : NameSupply}
    {scrut : Term .value} {i : Nat}
    {k : Term .value → NameSupply → Except String Expr} {c : Expr},
    Δ.Subset Δ' → Δ'.wf → δ.wfIn Δ' → s.Covers Δ' → scrut.wfIn Δ' → WfCont Γ Δ' k →
    encodeMatchWith primitives Δ Γ δ scrut branches i k s = .ok c → Expr.WfIn Γ s.avoid Δ' c

/-! ## Per-case helpers for `encodeWith_wfIn` -/

namespace WfCase

private theorem const {primitives : PrimEncodings} (c : TinyML.Const) :
    EncodeWithWfIn primitives (.const c) := by
  intro _ _ _ _ _ _ _ _ hΔ' _ hcov hk henc
  simp only [encodeWith] at henc
  exact hk (Signature.Subset.refl _) hΔ' hcov _ (encodeConst_wfIn c _) _ henc

private theorem var {primitives : PrimEncodings}
    (x : String) (inst : List (TinyML.TyVar × TinyML.Typ)) (ty : TinyML.Typ) :
    EncodeWithWfIn primitives (.var x inst ty) := by
  intro _ _ _ δ _ _ _ _ hΔ' hδ hcov hk henc
  cases hlookup : δ.lookup x with
  | none => simp only [encodeWith, hlookup] at henc; cases henc
  | some v =>
      simp only [encodeWith, hlookup] at henc
      exact hk (Signature.Subset.refl _) hΔ' hcov v (hδ x v hlookup) _ henc

private theorem unop {primitives : PrimEncodings}
    (op : TinyML.UnOp) (e : Typed.Expr) (ty : TinyML.Typ)
    (ih : EncodeWithWfIn primitives e) : EncodeWithWfIn primitives (.unop op e ty) := by
  intro _ _ _ _ _ _ _ hsub hΔ' hδ hcov hk henc
  simp only [encodeWith] at henc
  refine ih hsub hΔ' hδ hcov ?_ henc
  intro Δ'' s'' hsub'' hΔ'' hcov'' v hv c' henc'
  cases hraw : encodeUnOp op v with
  | error msg => simp only [hraw, bind, Except.bind] at henc'; cases henc'
  | ok v' =>
      simp only [hraw, bind, Except.bind] at henc'
      exact hk hsub'' hΔ'' hcov'' v' (encodeUnOp_wfIn hraw hv) c' henc'

private theorem binop {primitives : PrimEncodings}
    (op : TinyML.BinOp) (e1 e2 : Typed.Expr) (ty : TinyML.Typ)
    (ih1 : EncodeWithWfIn primitives e1) (ih2 : EncodeWithWfIn primitives e2) :
    EncodeWithWfIn primitives (.binop op e1 e2 ty) := by
  intro _ _ _ δ _ _ _ hsub hΔ' hδ hcov hk henc
  simp only [encodeWith] at henc
  refine ih1 hsub hΔ' hδ hcov ?_ henc
  intro Δa sa hsa hΔa hcova v1 hv1 c1 henc1
  refine ih2 (hsub.trans hsa) hΔa
    (fun y w h => Term.wfIn_mono w (hδ y w h) hsa hΔa) hcova ?_ henc1
  intro Δb sb hsb hΔb hcovb v2 hv2 c2 henc2
  cases hraw : encodeBinOp op v1 v2 with
  | error msg => simp only [hraw, bind, Except.bind] at henc2; cases henc2
  | ok v =>
      simp only [hraw, bind, Except.bind] at henc2
      exact hk (hsa.trans hsb) hΔb hcovb v
        (encodeBinOp_wfIn hraw (Term.wfIn_mono _ hv1 hsb hΔb) hv2) c2 henc2

private theorem ifThenElse {primitives : PrimEncodings} (c t e : Typed.Expr) (ty : TinyML.Typ)
    (ihc : EncodeWithWfIn primitives c) (iht : EncodeWithWfIn primitives t)
    (ihe : EncodeWithWfIn primitives e) :
    EncodeWithWfIn primitives (.ifThenElse c t e ty) := by
  intro Γ Δ _ δ _ k _ hsub hΔ' hδ hcov hk henc
  simp only [encodeWith] at henc
  refine ihc hsub hΔ' hδ hcov ?_ henc
  intro Δa sa hsa hΔa hcova b hb c' henc'
  have hδa : δ.wfIn Δa := fun y w h => Term.wfIn_mono w (hδ y w h) hsa hΔa
  have hka : WfCont Γ Δa k := fun hs hw hc v hv cc hkc => hk (hsa.trans hs) hw hc v hv cc hkc
  cases ht : encodeWith primitives Δ Γ δ t k sa with
  | error msg => simp only [ht, bind, Except.bind] at henc'; cases henc'
  | ok thenEnc =>
    cases he : encodeWith primitives Δ Γ δ e k sa with
    | error msg => simp only [ht, he, bind, Except.bind] at henc'; cases henc'
    | ok elseEnc =>
        simp only [ht, he, bind, Except.bind, Except.ok.injEq] at henc'
        subst henc'
        exact .ite ⟨trivial, hb⟩
          (iht (hsub.trans hsa) hΔa hδa hcova hka ht)
          (ihe (hsub.trans hsa) hΔa hδa hcova hka he)

private theorem app {primitives : PrimEncodings} (hlaw : primitives.Lawful)
    (fn : Typed.Expr) (args : List Typed.Expr) (ty : TinyML.Typ)
    (ihArgs : ∀ a ∈ args, EncodeWithWfIn primitives a)
    (ihArgsList : EncodeListWithWfIn primitives args) :
    EncodeWithWfIn primitives (.app fn args ty) := by
  intro Γ Δ _ δ _ k _ hsub hΔ' hδ hcov hk henc
  match fn, args with
  | .var f _ _, [arg] =>
      cases hlk : FunCtx.lookup Γ f with
      | none => simp only [encodeWith, hlk] at henc; cases henc
      | some rel =>
          simp only [encodeWith, hlk] at henc
          refine ihArgs arg (List.mem_singleton.mpr rfl) hsub hΔ' hδ hcov ?_ henc
          intro Δa sa hsa hΔa hcova v hv c' henc'
          have hrfresh : sa.fresh "r" ∉ sa.avoid := NameSupply.fresh_not_in_avoid sa "r"
          have hrΔ : sa.fresh "r" ∉ Δa.allNames := fun hm => hrfresh (hcova _ hm)
          have hΔr : (Δa.declVar ⟨sa.fresh "r", .value⟩).wf := Signature.wf_declVar hΔa
          have hsubr : Δa.Subset (Δa.declVar ⟨sa.fresh "r", .value⟩) :=
            Signature.subset_declVar_of_fresh hrΔ
          have hcovr : (sa.reserve (sa.fresh "r")).Covers (Δa.declVar ⟨sa.fresh "r", .value⟩) :=
            NameSupply.Covers.declVar hcova _ .value
          cases hkrun : k (.var .value (sa.fresh "r")) (sa.reserve (sa.fresh "r")) with
          | error msg => simp only [hkrun, bind, Except.bind] at henc'; cases henc'
          | ok body =>
              simp only [hkrun, bind, Except.bind, Except.ok.injEq] at henc'
              subst henc'
              exact .call (FunCtx.mem_of_lookup hlk) hv hrfresh hrΔ
                ((hk (hsa.trans hsubr) hΔr hcovr _
                  (var_value_wfIn hΔr (Signature.var_mem_declVar _ _)) _ hkrun).weaken
                  (fun _ hm => List.mem_cons_of_mem _ hm))
  | .prim n _ _, args =>
      simp only [encodeWith] at henc
      refine ihArgsList hsub hΔ' hδ hcov ?_ henc
      intro Δa sa hsa hΔa hcova vs hvs c' henc'
      cases hraw : encodePrim primitives Δ n vs with
      | error msg => simp only [hraw, bind, Except.bind] at henc'; cases henc'
      | ok v =>
          simp only [hraw, bind, Except.bind] at henc'
          exact hk hsa hΔa hcova v
            (encodePrim_wfIn hlaw hraw (hsub.trans hsa) hΔa hvs) c' henc'
  | .const _, _ | .unop .., _ | .binop .., _ | .fix .., _ | .app .., _
  | .ifThenElse .., _ | .letIn .., _ | .letProd .., _ | .ref .., _ | .deref .., _ | .store .., _
  | .arrayMake .., _ | .arrayLen _, _ | .arrayGet .., _ | .arraySet .., _
  | .assert _, _ | .tuple _, _ | .inj .., _ | .match_ .., _
  | .var _ _ _, [] | .var _ _ _, _ :: _ :: _ =>
      simp only [encodeWith] at henc; cases henc

private theorem fix {primitives : PrimEncodings}
    (self : Typed.Binder) (args : List Typed.Binder) (retTy : TinyML.Typ)
    (spec : Option (Spec TinyML.Typ)) (body : Typed.Expr) :
    EncodeWithWfIn primitives (.fix self args retTy spec body) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ henc; simp only [encodeWith] at henc; cases henc

private theorem prim {primitives : PrimEncodings} (name : String)
    (inst : List (TinyML.TyVar × TinyML.Typ)) (ty : TinyML.Typ) :
    EncodeWithWfIn primitives (.prim name inst ty) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ henc; simp only [encodeWith] at henc; cases henc

private theorem letIn {primitives : PrimEncodings} (name : Typed.Binder) (bound body : Typed.Expr)
    (ihBound : EncodeWithWfIn primitives bound) (ihBody : EncodeWithWfIn primitives body) :
    EncodeWithWfIn primitives (.letIn name bound body) := by
  intro _ _ _ δ _ _ _ hsub hΔ' hδ hcov hk henc
  simp only [encodeWith] at henc
  refine ihBound hsub hΔ' hδ hcov ?_ henc
  intro Δa sa hsa hΔa hcova v hv c' henc'
  exact ihBody (hsub.trans hsa) hΔa
    (VarEnv.wfIn.bindBinder (fun y w h => Term.wfIn_mono w (hδ y w h) hsa hΔa) hv) hcova
    (fun hs hw hc w hw' cc hkc => hk (hsa.trans hs) hw hc w hw' cc hkc) henc'

private theorem letProd {primitives : PrimEncodings}
    (names : List Typed.Binder) (bound body : Typed.Expr)
    (ihBound : EncodeWithWfIn primitives bound) (ihBody : EncodeWithWfIn primitives body) :
    EncodeWithWfIn primitives (.letProd names bound body) := by
  intro _ _ _ δ _ _ _ hsub hΔ' hδ hcov hk henc
  simp only [encodeWith] at henc
  refine ihBound hsub hΔ' hδ hcov ?_ henc
  intro Δa sa hsa hΔa hcova v hv c' henc'
  exact ihBody (hsub.trans hsa) hΔa
    (VarEnv.wfIn.bindBinders (fun y w h => Term.wfIn_mono w (hδ y w h) hsa hΔa) hv) hcova
    (fun hs hw hc w hw' cc hkc => hk (hsa.trans hs) hw hc w hw' cc hkc) henc'

private theorem ref {primitives : PrimEncodings} (ownership : TinyML.Ownership) (e : Typed.Expr) :
    EncodeWithWfIn primitives (.ref ownership e) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ henc; simp only [encodeWith] at henc; cases henc

private theorem deref {primitives : PrimEncodings} (e : Typed.Expr) (ty : TinyML.Typ) :
    EncodeWithWfIn primitives (.deref e ty) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ henc; simp only [encodeWith] at henc; cases henc

private theorem store {primitives : PrimEncodings} (loc val : Typed.Expr) :
    EncodeWithWfIn primitives (.store loc val) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ henc; simp only [encodeWith] at henc; cases henc

private theorem arrayMake {primitives : PrimEncodings}
    (ownership : TinyML.Ownership) (len init : Typed.Expr) :
    EncodeWithWfIn primitives (.arrayMake ownership len init) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ henc; simp only [encodeWith] at henc; cases henc

private theorem arrayLen {primitives : PrimEncodings}
    (arr : Typed.Expr) (ih : EncodeWithWfIn primitives arr) :
    EncodeWithWfIn primitives (.arrayLen arr) := by
  intro _ _ _ _ _ _ _ hsub hΔ' hδ hcov hk henc
  simp only [encodeWith] at henc
  refine ih hsub hΔ' hδ hcov ?_ henc
  intro Δa sa hsa hΔa hcova v hv c' henc'
  exact hk hsa hΔa hcova (.unop .ofInt (.unop .arrayLen v)) ⟨trivial, trivial, hv⟩ c' henc'

private theorem arrayGet {primitives : PrimEncodings} (arr idx : Typed.Expr) (ty : TinyML.Typ) :
    EncodeWithWfIn primitives (.arrayGet arr idx ty) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ henc; simp only [encodeWith] at henc; cases henc

private theorem arraySet {primitives : PrimEncodings} (arr idx val : Typed.Expr) :
    EncodeWithWfIn primitives (.arraySet arr idx val) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ henc; simp only [encodeWith] at henc; cases henc

private theorem assert {primitives : PrimEncodings} (e : Typed.Expr) :
    EncodeWithWfIn primitives (.assert e) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ henc; simp only [encodeWith] at henc; cases henc

private theorem tuple {primitives : PrimEncodings}
    (es : List Typed.Expr) (ih : EncodeListWithWfIn primitives es) :
    EncodeWithWfIn primitives (.tuple es) := by
  intro _ _ _ _ _ _ _ hsub hΔ' hδ hcov hk henc
  simp only [encodeWith] at henc
  refine ih hsub hΔ' hδ hcov ?_ henc
  intro Δa sa hsa hΔa hcova vs hvs c' henc'
  exact hk hsa hΔa hcova (.unop .ofValList (Terms.toValList vs))
    ⟨trivial, Terms.toValList_wfIn hvs⟩ c' henc'

private theorem inj {primitives : PrimEncodings} (tag arity : Nat) (payload : Typed.Expr)
    (ty : TinyML.Typ) (ih : EncodeWithWfIn primitives payload) :
    EncodeWithWfIn primitives (.inj tag arity payload ty) := by
  intro _ _ _ _ _ _ _ hsub hΔ' hδ hcov hk henc
  simp only [encodeWith] at henc
  refine ih hsub hΔ' hδ hcov ?_ henc
  intro Δa sa hsa hΔa hcova v hv c' henc'
  exact hk hsa hΔa hcova (.unop (.ofInj tag arity) v) ⟨trivial, hv⟩ c' henc'

private theorem match_ {primitives : PrimEncodings}
    (scrut : Typed.Expr) (branches : List (Typed.Binder × Typed.Expr))
    (ty : TinyML.Typ) (ihScrut : EncodeWithWfIn primitives scrut)
    (ihBranches : EncodeMatchWithWfIn primitives branches) :
    EncodeWithWfIn primitives (.match_ scrut branches ty) := by
  intro Γ _ _ δ _ k _ hsub hΔ' hδ hcov hk henc
  simp only [encodeWith] at henc
  refine ihScrut hsub hΔ' hδ hcov ?_ henc
  intro Δa sa hsa hΔa hcova v hv c' henc'
  exact ihBranches (hsub.trans hsa) hΔa
    (fun y w h => Term.wfIn_mono w (hδ y w h) hsa hΔa) hcova hv
    (fun hs hw hc w hw' cc hkc => hk (hsa.trans hs) hw hc w hw' cc hkc) henc'

private theorem match_nil {primitives : PrimEncodings} : EncodeMatchWithWfIn primitives [] := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henc
  simp only [encodeMatchWith] at henc; cases henc

private theorem match_cons {primitives : PrimEncodings} (b : Typed.Binder) (body : Typed.Expr)
    (rest : List (Typed.Binder × Typed.Expr))
    (ihBody : EncodeWithWfIn primitives body)
    (ihRest : EncodeMatchWithWfIn primitives rest) :
    EncodeMatchWithWfIn primitives ((b, body) :: rest) := by
  intro Γ Δ Δ' δ s scrut i k _ hsub hΔ' hδ hcov hscrut hk henc
  have hpay : (Term.unop UnOp.payloadOf scrut).wfIn Δ' := ⟨trivial, hscrut⟩
  cases rest with
  | nil =>
      simp only [encodeMatchWith] at henc
      exact ihBody hsub hΔ' (VarEnv.wfIn.bindBinder hδ hpay) hcov hk henc
  | cons r rs =>
      rw [encodeMatchWith] at henc
      cases ht : encodeWith primitives Δ Γ (VarEnv.bindBinder δ b (.unop .payloadOf scrut)) body k s with
      | error msg => simp only [ht, bind, Except.bind] at henc; cases henc
      | ok thenEnc =>
        cases he : encodeMatchWith primitives Δ Γ δ scrut (r :: rs) (i + 1) k s with
        | error msg => simp only [ht, he, bind, Except.bind] at henc; cases henc
        | ok elseEnc =>
            simp only [ht, he, bind, Except.bind, Except.ok.injEq] at henc
            subst henc
            exact .ite ⟨trivial, ⟨trivial, hscrut⟩, trivial⟩
              (ihBody hsub hΔ' (VarEnv.wfIn.bindBinder hδ hpay) hcov hk ht)
              (ihRest hsub hΔ' hδ hcov hscrut hk he)

private theorem list_nil {primitives : PrimEncodings} : EncodeListWithWfIn primitives [] := by
  intro _ _ _ _ _ _ _ _ hΔ' _ hcov hk henc
  simp only [encodeListWith] at henc
  exact hk (Signature.Subset.refl _) hΔ' hcov [] (by simp) _ henc

private theorem list_cons {primitives : PrimEncodings} (e : Typed.Expr) (es : List Typed.Expr)
    (ih : EncodeWithWfIn primitives e) (ihs : EncodeListWithWfIn primitives es) :
    EncodeListWithWfIn primitives (e :: es) := by
  intro _ _ _ δ _ _ _ hsub hΔ' hδ hcov hk henc
  simp only [encodeListWith] at henc
  refine ih hsub hΔ' hδ hcov ?_ henc
  intro Δa sa hsa hΔa hcova v hv c1 henc1
  refine ihs (hsub.trans hsa) hΔa
    (fun y w h => Term.wfIn_mono w (hδ y w h) hsa hΔa) hcova ?_ henc1
  intro Δb sb hsb hΔb hcovb vs hvs c2 henc2
  refine hk (hsa.trans hsb) hΔb hcovb (v :: vs) ?_ c2 henc2
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact Term.wfIn_mono _ hv hsb hΔb
  · exact hvs q hq

end WfCase

mutual
/-- Every IR expression the traversal produces is well-formed. -/
private theorem encodeWith_wfIn_def {primitives : PrimEncodings} (hlaw : primitives.Lawful) :
    ∀ (e : Typed.Expr), EncodeWithWfIn primitives e
  | .const c => WfCase.const c
  | .var x inst ty => WfCase.var x inst ty
  | .prim n inst ty => WfCase.prim n inst ty
  | .unop op e ty => WfCase.unop op e ty (encodeWith_wfIn_def hlaw e)
  | .binop op e1 e2 ty =>
      WfCase.binop op e1 e2 ty (encodeWith_wfIn_def hlaw e1) (encodeWith_wfIn_def hlaw e2)
  | .ifThenElse c t e ty =>
      WfCase.ifThenElse c t e ty (encodeWith_wfIn_def hlaw c)
        (encodeWith_wfIn_def hlaw t) (encodeWith_wfIn_def hlaw e)
  | .app fn args ty =>
      WfCase.app hlaw fn args ty (fun a _ => encodeWith_wfIn_def hlaw a)
        (encodeListWith_wfIn_def hlaw args)
  | .fix self args retTy spec body => WfCase.fix self args retTy spec body
  | .letIn name bound body =>
      WfCase.letIn name bound body
        (encodeWith_wfIn_def hlaw bound) (encodeWith_wfIn_def hlaw body)
  | .letProd names bound body =>
      WfCase.letProd names bound body
        (encodeWith_wfIn_def hlaw bound) (encodeWith_wfIn_def hlaw body)
  | .ref ownership e => WfCase.ref ownership e
  | .deref e ty => WfCase.deref e ty
  | .store loc val => WfCase.store loc val
  | .arrayMake ownership len init => WfCase.arrayMake ownership len init
  | .arrayLen arr => WfCase.arrayLen arr (encodeWith_wfIn_def hlaw arr)
  | .arrayGet arr idx ty => WfCase.arrayGet arr idx ty
  | .arraySet arr idx val => WfCase.arraySet arr idx val
  | .assert e => WfCase.assert e
  | .tuple es => WfCase.tuple es (encodeListWith_wfIn_def hlaw es)
  | .inj tag arity payload ty =>
      WfCase.inj tag arity payload ty (encodeWith_wfIn_def hlaw payload)
  | .match_ scrut branches ty =>
      WfCase.match_ scrut branches ty
        (encodeWith_wfIn_def hlaw scrut)
        (encodeMatchWith_wfIn_def hlaw branches)

private theorem encodeListWith_wfIn_def {primitives : PrimEncodings} (hlaw : primitives.Lawful) :
    ∀ (es : List Typed.Expr), EncodeListWithWfIn primitives es
  | [] => WfCase.list_nil
  | e :: es =>
      WfCase.list_cons e es (encodeWith_wfIn_def hlaw e) (encodeListWith_wfIn_def hlaw es)

private theorem encodeMatchWith_wfIn_def {primitives : PrimEncodings} (hlaw : primitives.Lawful) :
    ∀ (branches : List (Typed.Binder × Typed.Expr)), EncodeMatchWithWfIn primitives branches
  | [] => WfCase.match_nil
  | (b, body) :: rest =>
      WfCase.match_cons b body rest
        (encodeWith_wfIn_def hlaw body)
        (encodeMatchWith_wfIn_def hlaw rest)
end

private theorem encodeWith_wfIn {primitives : PrimEncodings} {Γ : FunCtx} {Δ Δ' : Signature}
    {δ : VarEnv} {s : NameSupply} {k : Term .value → NameSupply → Except String Expr}
    {c : Expr}
    (hlaw : primitives.Lawful) (e : Typed.Expr)
    (hsub : Δ.Subset Δ') (hΔ' : Δ'.wf) (hδ : δ.wfIn Δ') (hcov : s.Covers Δ')
    (hk : WfCont Γ Δ' k)
    (henc : encodeWith primitives Δ Γ δ e k s = .ok c) :
    Expr.WfIn Γ s.avoid Δ' c :=
  encodeWith_wfIn_def hlaw e hsub hΔ' hδ hcov hk henc

/-- The continuation that ends the traversal: it returns the value term
unchanged, and its IR is well-formed wherever the term is. -/
private theorem ret_wfCont {Γ : FunCtx} {Δ : Signature} :
    WfCont Γ Δ (fun v _ => .ok (.ret v)) := by
  intro _ _ _ _ _ v hv c henc
  simp only [Except.ok.injEq] at henc
  subst henc
  exact .ret hv

/-- Well-formedness of the traversal's output. `Δ` gates the intrinsics while
`Δ'` — any extension of it — carries the local variables the encoding runs
under, and the call binders avoid every name the supply reserves. -/
theorem encode_wfIn {primitives : PrimEncodings} {Γ : FunCtx} {Δ Δ' : Signature}
    {δ : VarEnv} {s : NameSupply} {c : Expr}
    (hlaw : primitives.Lawful) (e : Typed.Expr)
    (hsub : Δ.Subset Δ') (hΔ' : Δ'.wf) (hδ : δ.wfIn Δ') (hcov : s.Covers Δ')
    (henc : encode primitives Δ Γ δ e s = .ok c) :
    Expr.WfIn Γ s.avoid Δ' c :=
  encodeWith_wfIn hlaw e hsub hΔ' hδ hcov ret_wfCont henc

/-! ## Semantic interpretation of encodings

A semantic predicate `sem : M → Env → Prop` explains how an encoding is
interpreted in an environment. Downstream constructions (e.g. the relational
encoder's least fixpoint) use these notions on top of the traversal. -/

/-- Semantic interpretation of an encoded expression in an environment. -/
abbrev SemPred (M : Type) := M → Env → Prop

/-- An encoding is monotone when its semantic interpretation is stable under
`Env.le`. -/
def SemanticMono {M : Type} (sem : SemPred M) (m : M) : Prop :=
  ∀ {ρ ρ' : Env}, Env.le ρ ρ' → sem m ρ → sem m ρ'

end Verifier.RelationalEncoding

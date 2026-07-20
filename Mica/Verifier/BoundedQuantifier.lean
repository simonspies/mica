-- SUMMARY: Lambda lifting of spec-level bounded quantifiers (Range.all/Range.exists) into axiomatized function symbols.
import Mica.TinyML.Typing
import Mica.TinyML.Spec
import Mica.Verifier.RelationalEncoding.Variables
import Mica.Verifier.Guard
import Mica.Verifier.Intrinsic
import Mica.Verifier.RelationalEncoding.Axioms

open Iris Iris.BI

/-!
# Bounded quantifiers

`Range.all lo hi (fun i -> body)` in a specification means
`∀ i, lo ≤ i < hi → body` (vacuously true on an empty range);
`Range.exists` is the dual. The surface forms elaborate to ordinary
applications of the primitives `range-all`/`range-exists`
(`allName`/`existsName`). Their registry entries have false operational and
specification semantics: a rewrite pass lambda-lifts every legitimate spec
occurrence into calls to freshly axiomatized function symbols, while any
occurrence that survives the pass fails verification normally.
-/

/-! ## Declaring a spec-function symbol triple

Generic infrastructure, shared with relation assembly in `Programs.lean`:
declaring the three solver symbols of a spec function whose relation
interpretation is the graph of its value function on its definedness domain,
and assuming its valid defining axioms, preserves the relation-assembly
invariants. -/

namespace Verifier.RelationalEncoding.SpecFn

/-- Declare the solver-facing triple of `L` and assume its defining axioms. -/
def declare (L : SpecFn) (axs : List Axiom) : VerifM Unit := do
  VerifM.declBinaryRelExact (SpecFn.rel L)
  VerifM.declUnaryExact (SpecFn.func L)
  VerifM.declUnaryRelExact (SpecFn.defined L)
  VerifM.assumeAxioms axs

/-- Declaring the triple of a fresh symbol `L` — with interpretations whose
relation is the graph of the value function on the definedness domain, and
defining axioms that are well-formed and valid in the extended
signature/environment — preserves the relation-assembly invariants and
extends the function context by `(f, L)`. -/
theorem declare_correct (L : SpecFn) (f : TinyML.Var) (axs : List Axiom)
    (R : Srt.value.denote → Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote)
    (D : Srt.value.denote → Prop)
    (Δ : Signature) (Γ : FunCtx) (st : TransState) (ρ : VerifM.Env)
    {Q : Unit → TransState → VerifM.Env → Prop}
    (hrelFresh : relName L ∉ Δ.allNames)
    (hfunFresh : funcName L ∉ Δ.allNames)
    (hdefFresh : defName L ∉ Δ.allNames)
    (hgraph : ∀ a b, R a b ↔ D a ∧ F a = b)
    (hdecls : st.decls = Δ) (howns : st.owns = []) (hvars : st.decls.vars = [])
    (hwfext : (((Δ.addBinaryRel (rel L)).addUnary (func L)).addUnaryRel (defined L)).wf)
    (hΓwf : FunCtx.wfIn Γ Δ)
    (hsplit : FunCtx.splitCompatible Γ ρ.env)
    (hdet : Relation.BinaryRelDet Γ ρ.env ρ.env)
    (haxwf : ∀ ax ∈ axs, ax.formula.wfIn
      (((Δ.addBinaryRel (rel L)).addUnary (func L)).addUnaryRel (defined L)))
    (haxeval : ∀ ax ∈ axs, ax.formula.eval (Skolemize.relSplitEnv ρ.env L R D F))
    (heval : VerifM.eval (declare L axs) st ρ Q) :
    ∃ st' ρ',
      st'.decls = ((Δ.addBinaryRel (rel L)).addUnary (func L)).addUnaryRel (defined L) ∧
      st'.owns = [] ∧ st'.decls.vars = [] ∧ st'.decls.wf ∧
      st.decls.Subset st'.decls ∧
      VerifM.Env.agreeOn st.decls ρ ρ' ∧
      FunCtx.wfIn (Γ ++ [(f, L)]) st'.decls ∧
      FunCtx.splitCompatible (Γ ++ [(f, L)]) ρ'.env ∧
      Relation.BinaryRelDet (Γ ++ [(f, L)]) ρ'.env ρ'.env ∧
      Q () st' ρ' := by
  simp only [declare] at heval
  obtain ⟨_, h1⟩ := VerifM.eval_declBinaryRelExact (VerifM.eval_bind heval)
  obtain ⟨_, h2⟩ := VerifM.eval_declUnaryExact (VerifM.eval_bind (h1 R))
  obtain ⟨_, h3⟩ := VerifM.eval_declUnaryRelExact (VerifM.eval_bind (h2 F))
  have h4 := h3 D
  set Δext : Signature :=
    ((Δ.addBinaryRel (rel L)).addUnary (func L)).addUnaryRel (defined L)
  set st3 : TransState :=
    { st with decls := ((st.decls.addBinaryRel (rel L)).addUnary
        (func L)).addUnaryRel (defined L) }
  set ρ3 : VerifM.Env :=
    ((ρ.updateBinaryRel .value .value (relName L) R).updateUnary
        .value .value (funcName L) F).updateUnaryRel
      .value (defName L) D
  have hst3 : st3.decls = Δext := by
    simp only [st3, Δext, hdecls]
  have hρ3 : ρ3.env = Skolemize.relSplitEnv ρ.env L R D F := by
    simp only [ρ3, VerifM.Env.updateUnaryRel_env, VerifM.Env.updateUnary_env,
      VerifM.Env.updateBinaryRel_env, Skolemize.relSplitEnv]
  have hsub : Δ.Subset Δext :=
    ((Signature.Subset.subset_addBinaryRel _ _).trans
      (Signature.Subset.subset_addUnary _ _)).trans
      (Signature.Subset.subset_addUnaryRel _ _)
  obtain ⟨st4, hst4, howns4, _, hQ4⟩ :=
    VerifM.eval_assumeAxioms h4 (fun ax hax => hst3 ▸ haxwf ax hax)
      (fun ax hax => hρ3 ▸ haxeval ax hax)
  have howns4' : st4.owns = [] := by rw [howns4]; exact howns
  have hvars4 : st4.decls.vars = [] := by
    rw [hst4, hst3]
    show Δ.vars = []
    rw [← hdecls]
    exact hvars
  have hwf4 : st4.decls.wf := by rw [hst4, hst3]; exact hwfext
  have hagree : Env.agreeOn Δ ρ.env ρ3.env := by
    rw [hρ3]
    exact Skolemize.relSplitEnv_agreeOn hrelFresh hfunFresh hdefFresh
  have hΓwf' : FunCtx.wfIn (Γ ++ [(f, L)]) st4.decls := by
    rw [hst4, hst3]
    refine ⟨?_, ?_⟩
    · intro x rel hxr
      rcases List.mem_append.mp hxr with hold | hnew
      · exact hsub.binaryRel _ (hΓwf.rel x rel hold)
      · simp at hnew; obtain ⟨_, rfl⟩ := hnew
        exact List.Mem.head _
    · intro x rel hxr
      rcases List.mem_append.mp hxr with hold | hnew
      · obtain ⟨hu, hr⟩ := hΓwf.split x rel hold
        exact ⟨hsub.unary _ hu, hsub.unaryRel _ hr⟩
      · simp at hnew; obtain ⟨_, rfl⟩ := hnew
        exact ⟨List.Mem.head _, List.Mem.head _⟩
  have hsplit' : FunCtx.splitCompatible (Γ ++ [(f, L)]) ρ3.env := by
    intro g rel hgr x y
    rcases List.mem_append.mp hgr with hold | hnew
    · obtain ⟨hu, hr⟩ := hΓwf.split g rel hold
      obtain ⟨her, hec, hed⟩ := SpecFn.agreeOn hagree (hΓwf.rel g rel hold) hu hr
      rw [← her, ← hec, ← hed]
      exact hsplit g rel hold x y
    · simp at hnew; obtain ⟨_, rfl⟩ := hnew
      rw [hρ3]
      exact Skolemize.relSplitEnv_graph rel ρ.env hgraph x y
  have hdet' : Relation.BinaryRelDet (Γ ++ [(f, L)]) ρ3.env ρ3.env := by
    intro g rel hgr x y₁ y₂ hy₁ hy₂
    rcases List.mem_append.mp hgr with hold | hnew
    · obtain ⟨hu, hr⟩ := hΓwf.split g rel hold
      obtain ⟨her, _, _⟩ := SpecFn.agreeOn hagree (hΓwf.rel g rel hold) hu hr
      rw [← her] at hy₁ hy₂
      exact hdet g rel hold x y₁ y₂ hy₁ hy₂
    · simp at hnew; obtain ⟨_, rfl⟩ := hnew
      rw [hρ3] at hy₁ hy₂
      obtain ⟨_, heq₁⟩ := (Skolemize.relSplitEnv_graph rel ρ.env hgraph x y₁).mp hy₁
      obtain ⟨_, heq₂⟩ := (Skolemize.relSplitEnv_graph rel ρ.env hgraph x y₂).mp hy₂
      exact heq₁.symm.trans heq₂
  have hsub4 : st.decls.Subset st4.decls := by
    rw [hst4, hst3, hdecls]
    exact hsub
  have hagree4 : VerifM.Env.agreeOn st.decls ρ ρ3 := by
    rw [hdecls]
    exact hagree
  exact ⟨st4, ρ3, by rw [hst4, hst3], howns4', hvars4, hwf4, hsub4,
    hagree4, hΓwf', hsplit', hdet', hQ4⟩

end Verifier.RelationalEncoding.SpecFn

namespace Verifier.BoundedQuantifier

/-- Internal primitive name for `Range.all`. -/
def allName : String := "range-all"

/-- Internal primitive name for `Range.exists`. -/
def existsName : String := "range-exists"

/-- Whether `n` is one of the bounded-quantifier primitives. -/
def isPrim (n : String) : Bool :=
  n = allName || n = existsName

/-! ## Registry entries

The quantifier operations are real intrinsics so the ordinary registry is the
single source of surface resolution and typing. Their operational relation,
weakest precondition, and specification precondition are all false: legitimate
specification occurrences are eliminated by this pass, while any occurrence
that survives cannot verify. No FOL symbol or axiom is required. -/

/-- A spec-only bounded-quantifier intrinsic. -/
def intrinsic (name : String) (path : String) : Verifier.Intrinsic where
  arity := .three
  name := name
  path := some ("Range", [path])
  reduce := fun _ _ _ _ => False
  wp := fun _ _ => iprop(False)
  spec :=
    { args := [("lo", .int), ("hi", .int), ("body", .arrow .int .bool)]
      retTy := .bool
      pred := .assert .false_ (.ret ("ret", .ret ())) }
  typing := Verifier.monoTyping .three
  folSym := none
  axioms := []

/-- Registry entry for `Range.all`. -/
def allIntrinsic : Verifier.Intrinsic := intrinsic allName "all"

/-- Registry entry for `Range.exists`. -/
def existsIntrinsic : Verifier.Intrinsic := intrinsic existsName "exists"

@[simp] theorem allIntrinsic_arity : allIntrinsic.arity = .three := rfl
@[simp] theorem existsIntrinsic_arity : existsIntrinsic.arity = .three := rfl
@[simp] theorem allIntrinsic_folSym : allIntrinsic.folSym = none := rfl
@[simp] theorem existsIntrinsic_folSym : existsIntrinsic.folSym = none := rfl

/-- A forbidden intrinsic is sound: its specification and weakest precondition
are both false, and it contributes no solver symbols or axioms. -/
@[reducible] def intrinsicSound (name path : String) :
    Verifier.IntrinsicSound [] (intrinsic name path) where
  specWf := by
    intro Δ _ _
    simp [intrinsic, Verifier.Intrinsic.specArgs, PredTrans.wfIn, Assertion.wfIn]
    trivial
  bridge := by
    intro _ σ Θ vs ρ Φ _
    simp only [intrinsic, Spec.instantiate, PredTrans.apply, Assertion.pre]
    iintro H
    icases H with ⟨_, %hfalse, _⟩
    exact hfalse.elim
  wp_sound := by
    intro _ _ _ vs _
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | [_, _] => exact false_elim
    | [_, _, _] => exact false_elim
    | _ :: _ :: _ :: _ :: _ => exact false_elim
  axiomWf := by
    intro _ _ _ a ha
    cases ha
  proof := by
    intro _ _ a ha
    cases ha

instance : Verifier.IntrinsicSound [] allIntrinsic := intrinsicSound _ _

instance : Verifier.IntrinsicSound [] existsIntrinsic := intrinsicSound _ _

/-! ## The rewrite pass

Runs on the typed program before relation assembly. Each occurrence
`Range.all lo hi (fun i -> body)` in a spec leaf is replaced by a plain call
`L (lo, hi, x̄)` of a fresh symbol `L = "<decl>-range-<k>"` over the packed
bounds and captured variables `x̄`; the closure is recorded as a lifted
function body `let (x̄, i) = arg in body` to be axiomatized during assembly.
Only the spec leaves change — declaration bodies (hence the program's runtime
erasure) are untouched.

The rewrite itself is `partial` and unverified: no proof depends on its
equations. Rewritten specs are re-checked from scratch by spec translation,
name freshness is validated operationally during assembly, and `run_runtime`
only needs that declaration bodies are untouched. -/

/-- One lifted occurrence of a bounded quantifier: the quantifier symbol's base
name, the quantifier kind, the captured spec variables (first-occurrence
order), and the lifted closure's packed argument name and body. -/
structure Lifting where
  name : String
  all : Bool
  captured : List TinyML.Var
  arg : String
  body : Typed.Expr

/-- State of the per-declaration rewrite: its program index, the occurrence
counter, and the lifted symbols in dependency order (inner occurrences precede
outer ones). -/
structure LiftState where
  declIdx : Nat := 0
  count : Nat := 0
  syms : List Lifting := []

abbrev LiftM := StateT LiftState (Except String)

mutual
  /-- Free program variables of a typed expression, in first-occurrence order.
  A named unary call head is resolved through the function context and is not
  captured as a value variable. -/
  private def freeVars : Typed.Expr → List TinyML.Var
    | .const _ => []
    | .var x _ => [x]
    | .prim .. => []
    | .unop _ e _ => freeVars e
    | .binop _ l r _ => freeVars l ++ freeVars r
    | .fix self args _ body =>
        (freeVars body).filter fun v =>
          self.name != some v && !args.any (·.name == some v)
    | .app (.var _ _) [arg] _ => freeVars arg
    | .app fn args _ => freeVars fn ++ args.flatMap freeVars
    | .ifThenElse c t e _ => freeVars c ++ freeVars t ++ freeVars e
    | .letIn b bound body =>
        freeVars bound ++ (freeVars body).filter (fun v => b.name != some v)
    | .letProd bs bound body =>
        freeVars bound ++ (freeVars body).filter (fun v => !bs.any (·.name == some v))
    | .ref _ e => freeVars e
    | .deref e _ => freeVars e
    | .store loc val => freeVars loc ++ freeVars val
    | .arrayMake _ len init => freeVars len ++ freeVars init
    | .arrayLen arr => freeVars arr
    | .arrayGet arr idx _ => freeVars arr ++ freeVars idx
    | .arraySet arr idx val => freeVars arr ++ freeVars idx ++ freeVars val
    | .assert e => freeVars e
    | .tuple es => es.flatMap freeVars
    | .inj _ _ payload => freeVars payload
    | .match_ scrut branches _ => freeVars scrut ++ branchFreeVars branches
    | .cast e _ => freeVars e

  private def branchFreeVars : List (Typed.Binder × Typed.Expr) → List TinyML.Var
    | [] => []
    | (b, body) :: rest =>
        (freeVars body).filter (fun v => b.name != some v) ++ branchFreeVars rest
end

/-- Lift one occurrence: allocate the quantifier symbol, record the lifted closure
`let (x̄, i) = arg in body`, and return the plain call replacing the
occurrence — the quantifier symbol applied to the packed `(lo, hi, x̄)` tuple. -/
private def lift (decl : Option String) (all : Bool) (binder : Typed.Binder)
    (body lo hi : Typed.Expr) : LiftM Typed.Expr := do
  let some decl := decl
    | throw "Range.all/Range.exists in a specification require a named declaration"
  let st ← get
  let name := s!"{decl}-range-{st.declIdx}-{st.count}"
  let captured := ((freeVars body).filter (fun v => binder.name != some v)).eraseDups
  let gBody := Typed.Expr.letProd
    (captured.map (fun x => ⟨some x, .value⟩) ++ [binder]) (.var (name ++ "-x") .value) body
  set ({ declIdx := st.declIdx,
         count := st.count + 1,
         syms := st.syms ++ [{ name, all, captured, arg := name ++ "-x", body := gBody }] } : LiftState)
  pure (.app (.var name (.arrow .value .bool))
    [.tuple (lo :: hi :: captured.map (fun x => Typed.Expr.var x .value))] .bool)

/-- Rewrite every bounded-quantifier occurrence in a spec leaf, bottom-up:
bounds and closure bodies are rewritten first, so inner occurrences are
lifted before — and their calls captured by — outer ones. -/
private partial def rewrite (decl : Option String) : Typed.Expr → LiftM Typed.Expr
  | .app (.prim n inst pty) args ty => do
      if isPrim n then
        match args with
        | [lo, hi, .fix _ [binder] _ body] => do
            let lo' ← rewrite decl lo
            let hi' ← rewrite decl hi
            let body' ← rewrite decl body
            lift decl (n = allName) binder body' lo' hi'
        | _ => throw "Range.all/Range.exists expect a literal single-argument function"
      else do
        pure (.app (.prim n inst pty) (← args.mapM (rewrite decl)) ty)
  | .const c => pure (.const c)
  | .var x ty => pure (.var x ty)
  | .prim n inst ty => pure (.prim n inst ty)
  | .unop op e ty => do pure (.unop op (← rewrite decl e) ty)
  | .binop op l r ty => do pure (.binop op (← rewrite decl l) (← rewrite decl r) ty)
  | .fix self args retTy body => do pure (.fix self args retTy (← rewrite decl body))
  | .app fn args ty => do
      pure (.app (← rewrite decl fn) (← args.mapM (rewrite decl)) ty)
  | .ifThenElse c t e ty => do
      pure (.ifThenElse (← rewrite decl c) (← rewrite decl t) (← rewrite decl e) ty)
  | .letIn b bound body => do pure (.letIn b (← rewrite decl bound) (← rewrite decl body))
  | .letProd bs bound body => do
      pure (.letProd bs (← rewrite decl bound) (← rewrite decl body))
  | .ref ownership e => do pure (.ref ownership (← rewrite decl e))
  | .deref e ty => do pure (.deref (← rewrite decl e) ty)
  | .store loc val => do pure (.store (← rewrite decl loc) (← rewrite decl val))
  | .arrayMake ownership len init => do
      pure (.arrayMake ownership (← rewrite decl len) (← rewrite decl init))
  | .arrayLen arr => do pure (.arrayLen (← rewrite decl arr))
  | .arrayGet arr idx ty => do pure (.arrayGet (← rewrite decl arr) (← rewrite decl idx) ty)
  | .arraySet arr idx val => do
      pure (.arraySet (← rewrite decl arr) (← rewrite decl idx) (← rewrite decl val))
  | .assert e => do pure (.assert (← rewrite decl e))
  | .tuple es => do pure (.tuple (← es.mapM (rewrite decl)))
  | .inj tag arity payload => do pure (.inj tag arity (← rewrite decl payload))
  | .match_ scrut branches ty => do
      pure (.match_ (← rewrite decl scrut)
        (← branches.mapM fun (b, body) => do pure (b, ← rewrite decl body)) ty)
  | .cast e ty => do pure (.cast (← rewrite decl e) ty)

/-- Rewrite the leaves of a spec assertion; `f` handles the return payload. -/
private def rewriteAssert {α β : Type} (decl : Option String) (f : α → LiftM β) :
    Spec.Assert Typed.Expr α → LiftM (Spec.Assert Typed.Expr β)
  | .ret v => .ret <$> f v
  | .assert c rest => do pure (.assert (← rewrite decl c) (← rewriteAssert decl f rest))
  | .let_ x v rest => do pure (.let_ x (← rewrite decl v) (← rewriteAssert decl f rest))
  | .bind p x ty rest => do pure (.bind p x ty (← rewriteAssert decl f rest))
  | .ite c t e => do
      pure (.ite (← rewrite decl c) (← rewriteAssert decl f t) (← rewriteAssert decl f e))

/-- Rewrite all spec leaves of a spec body. -/
private def rewriteBody (decl : Option String) (body : Spec.Body Typed.Expr) :
    LiftM (Spec.Body Typed.Expr) := do
  let pre ← rewriteAssert decl
    (fun (r, post) => do pure (r, ← rewriteAssert decl pure post)) body.2
  pure (body.1, pre)

/-- Rewrite one declaration's spec at its program index, pairing it with the
lifted symbols. -/
def runDecl (declIdx : Nat) (d : Typed.ValDecl (Spec.Body Typed.Expr)) :
    Except String (Typed.ValDecl (Spec.Body Typed.Expr) × List Lifting) :=
  match d.declMeta.spec with
  | none => .ok (d, [])
  | some body =>
      match (rewriteBody d.name.name body).run { declIdx := declIdx } with
      | .error err => .error err
      | .ok (body', st) =>
          .ok ({ d with declMeta := { d.declMeta with spec := some body' } }, st.syms)

/-- Run the bounded-quantifier pass over a typed program: rewrite every spec's
bounded-quantifier occurrences and pair each declaration with its lifted
symbols in dependency order. Declaration bodies are untouched, so the
program's runtime erasure is preserved (`run_runtime`). -/
private def runFrom : Nat → Typed.Program (Spec.Body Typed.Expr) →
    Except String (List (Typed.ValDecl (Spec.Body Typed.Expr) × List Lifting))
  | _, [] => .ok []
  | declIdx, d :: ds =>
      match runDecl declIdx d with
      | .error err => .error err
      | .ok p =>
          match runFrom (declIdx + 1) ds with
          | .error err => .error err
          | .ok ps => .ok (p :: ps)

/-- Run the bounded-quantifier pass over a typed program. The declaration
index makes generated symbol names unique even when top-level names are
shadowed. -/
def run (prog : Typed.Program (Spec.Body Typed.Expr)) :
    Except String (List (Typed.ValDecl (Spec.Body Typed.Expr) × List Lifting)) :=
  runFrom 0 prog

/-- The pass leaves a declaration's name and body untouched. -/
theorem runDecl_runtime {declIdx : Nat} {d : Typed.ValDecl (Spec.Body Typed.Expr)}
    {p : Typed.ValDecl (Spec.Body Typed.Expr) × List Lifting}
    (h : runDecl declIdx d = .ok p) : p.1.runtime = d.runtime := by
  unfold runDecl at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl

/-- The pass preserves the program's runtime erasure: only spec metadata
changes. -/
private theorem runFrom_runtime {declIdx : Nat} {prog : Typed.Program (Spec.Body Typed.Expr)}
    {pairs : List (Typed.ValDecl (Spec.Body Typed.Expr) × List Lifting)}
    (h : runFrom declIdx prog = .ok pairs) :
    Typed.Program.runtime (pairs.map Prod.fst) = prog.runtime := by
  induction prog generalizing declIdx pairs with
  | nil =>
    simp only [runFrom, Except.ok.injEq] at h
    subst h
    rfl
  | cons d ds ih =>
    rw [runFrom] at h
    split at h
    · cases h
    · rename_i p hd
      split at h
      · cases h
      · rename_i ps hds
        cases h
        simp only [List.map_cons, Typed.Program.runtime, List.map]
        rw [show p.1.runtime = d.runtime from runDecl_runtime hd]
        have := ih hds
        simp only [Typed.Program.runtime] at this
        rw [this]

/-- The pass preserves the program's runtime erasure: only spec metadata
changes. -/
theorem run_runtime {prog : Typed.Program (Spec.Body Typed.Expr)}
    {pairs : List (Typed.ValDecl (Spec.Body Typed.Expr) × List Lifting)}
    (h : run prog = .ok pairs) :
    Typed.Program.runtime (pairs.map Prod.fst) = prog.runtime := by
  exact runFrom_runtime h

/-! ## Solver-facing symbols and defining axioms

Each lifted occurrence contributes one `SpecFn`-shaped symbol triple for the
quantifier symbol `L`. The lifted closure body is compiled directly under the
matrix variables and inlined into `L`'s two defining axioms.

The canonical interpretations of `L`'s symbols are the evaluations of the
axioms' right-hand sides, so validity is by construction. -/

open Verifier.RelationalEncoding

namespace Lifting

/-- Bound index variable of the defining axioms. -/
def idx (s : Lifting) : String := s.name ++ "-i"

/-- Facts required to compile and declare a quantifier symbol: freshness of all
derived names. Established operationally by `validate`. -/
structure Valid (s : Lifting) (Δ : Signature) : Prop where
  relFresh : SpecFn.relName s.name ∉ Δ.allNames
  funFresh : SpecFn.funcName s.name ∉ Δ.allNames
  defFresh : SpecFn.defName s.name ∉ Δ.allNames
  argFresh : s.arg ∉ Δ.allNames
  idxFresh : s.idx ∉ Δ.allNames
  idxNeArg : s.idx ≠ s.arg
  argNeRel : s.arg ≠ SpecFn.relName s.name
  argNeFun : s.arg ≠ SpecFn.funcName s.name
  argNeDef : s.arg ≠ SpecFn.defName s.name
  idxNeRel : s.idx ≠ SpecFn.relName s.name
  idxNeFun : s.idx ≠ SpecFn.funcName s.name
  idxNeDef : s.idx ≠ SpecFn.defName s.name

/-- Run one decidable validation check, or fail with `msg`. -/
private def check (p : Prop) [Decidable p] (msg : String) : Except String (PLift p) :=
  if h : p then .ok ⟨h⟩ else .error msg

/-- Validate the fresh names required to compile and declare the solver-facing
quantifier symbol over `Δ`. A successful run returns the `Valid` evidence
directly. -/
def validate (s : Lifting) (Δ : Signature) : Except String (PLift (Valid s Δ)) := do
  let L := s.name
  let ⟨relFresh⟩ ← check (SpecFn.relName L ∉ Δ.allNames)
    s!"derived relation name '{SpecFn.relName L}' for a bounded quantifier conflicts with an existing symbol"
  let ⟨funFresh⟩ ← check (SpecFn.funcName L ∉ Δ.allNames)
    s!"derived value-function name '{SpecFn.funcName L}' for a bounded quantifier conflicts with an existing symbol"
  let ⟨defFresh⟩ ← check (SpecFn.defName L ∉ Δ.allNames)
    s!"derived definedness name '{SpecFn.defName L}' for a bounded quantifier conflicts with an existing symbol"
  let ⟨argFresh⟩ ← check (s.arg ∉ Δ.allNames)
    s!"bounded quantifier argument name '{s.arg}' conflicts with a global symbol"
  let ⟨idxFresh⟩ ← check (s.idx ∉ Δ.allNames)
    s!"bounded quantifier index name '{s.idx}' conflicts with a global symbol"
  let ⟨idxNeArg⟩ ← check (s.idx ≠ s.arg)
    s!"bounded quantifier index name '{s.idx}' clashes with its argument name"
  let ⟨argNeRel⟩ ← check (s.arg ≠ SpecFn.relName L)
    s!"bounded quantifier argument name '{s.arg}' clashes with derived relation name '{SpecFn.relName L}'"
  let ⟨argNeFun⟩ ← check (s.arg ≠ SpecFn.funcName L)
    s!"bounded quantifier argument name '{s.arg}' clashes with derived value-function name '{SpecFn.funcName L}'"
  let ⟨argNeDef⟩ ← check (s.arg ≠ SpecFn.defName L)
    s!"bounded quantifier argument name '{s.arg}' clashes with derived definedness name '{SpecFn.defName L}'"
  let ⟨idxNeRel⟩ ← check (s.idx ≠ SpecFn.relName L)
    s!"bounded quantifier index name '{s.idx}' clashes with derived relation name '{SpecFn.relName L}'"
  let ⟨idxNeFun⟩ ← check (s.idx ≠ SpecFn.funcName L)
    s!"bounded quantifier index name '{s.idx}' clashes with derived value-function name '{SpecFn.funcName L}'"
  let ⟨idxNeDef⟩ ← check (s.idx ≠ SpecFn.defName L)
    s!"bounded quantifier index name '{s.idx}' clashes with derived definedness name '{SpecFn.defName L}'"
  .ok ⟨⟨relFresh, funFresh, defFresh, argFresh, idxFresh, idxNeArg, argNeRel,
    argNeFun, argNeDef, idxNeRel, idxNeFun, idxNeDef⟩⟩

/-- The packed axiom variable (also the lifted closure's argument name). -/
private def pvar (s : Lifting) : Term .value := .var .value s.arg

private def ivar (s : Lifting) : Term .int := .var .int s.idx

/-- Lower bound: the packed tuple's first component. -/
private def lo (s : Lifting) : Term .int := .unop .toInt (VarEnv.prodProj s.pvar 0)

/-- Upper bound: the packed tuple's second component. -/
private def hi (s : Lifting) : Term .int := .unop .toInt (VarEnv.prodProj s.pvar 1)

/-- The bounds premise `lo ≤ i ∧ i < hi`. -/
private def bounds (s : Lifting) : Formula :=
  .and (.binpred .le s.lo s.ivar) (.binpred .lt s.ivar s.hi)

/-- The lifted closure's packed argument: the captured components of `p`
(positions `2..`) followed by the index. Matches the destructuring order of
the closure's `letProd`. -/
private def gpack (s : Lifting) : Term .value :=
  .unop .ofValList (Terms.toValList
    ((List.range s.captured.length).map (fun k => VarEnv.prodProj s.pvar (k + 2))
      ++ [.unop .ofInt s.ivar]))

/-- Compile the lifted closure body under the packed argument and index matrix
variables. Binding the TinyML argument to `gpack` shadows the same-named FOL
variable while retaining that variable inside the packed term. -/
def compile (s : Lifting) (Γ : FunCtx) (Δ : Signature) : Except String Skolemize.DefVal :=
  let Δpi := (Δ.declVar ⟨s.arg, .value⟩).declVar ⟨s.idx, .int⟩
  let env := (VarEnv.ofSignature Δpi).bind s.arg s.gpack
  encodeWith Skolemize.encoderOps Δpi Γ env s.body
    (fun value => .ok (Skolemize.DefVal.pure value))

/-- Matrix of the value axiom: the bounded quantifier over the lifted
closure's truth. -/
def matrix (s : Lifting) (body : Skolemize.DefVal) : Formula :=
  if s.all then .forall_ s.idx .int [] (.implies s.bounds body.value.isTrue)
  else .exists_ s.idx .int (.and s.bounds body.value.isTrue)

/-- Matrix of the definedness axiom: the lifted closure is defined on the
whole range (vacuously on an empty range, giving the vacuity semantics). -/
def defMatrix (s : Lifting) (body : Skolemize.DefVal) : Formula :=
  .forall_ s.idx .int [] (.implies s.bounds body.defined)

/-- Defining definedness axiom: `L-def(p)` iff the closure is defined on the
whole range. Triggered only by the `L-def` application. -/
def defAxiom (s : Lifting) (body : Skolemize.DefVal) : Formula :=
  .forall_ s.arg .value
    [.unpred (.uninterpreted (SpecFn.defName s.name) .value) s.pvar]
    (.iff (SpecFn.isDefined s.name s.pvar) (s.defMatrix body))

/-- Defining value axiom: `L-func(p)` is the boolean truth value of the
bounded quantifier. Stated as the two directions so the solver also learns
booleanness of the result. Triggered only by the `L-func` application. -/
def valAxiom (s : Lifting) (body : Skolemize.DefVal) : Formula :=
  .forall_ s.arg .value
    [.term (SpecFn.call s.name s.pvar)]
    (.and (.implies (s.matrix body) (SpecFn.call s.name s.pvar).isTrue)
          (.implies (.not (s.matrix body)) (SpecFn.call s.name s.pvar).isFalse))

/-- The axioms defining a quantifier symbol; both quantified, hence guarded. -/
def axioms (s : Lifting) (body : Skolemize.DefVal) : List Axiom :=
  [⟨s.defAxiom body, .high⟩, ⟨s.valAxiom body, .high⟩]

/-- Signature after declaring the quantifier relation, value function, and
definedness predicate. -/
def extendSignature (s : Lifting) (Δ : Signature) : Signature :=
  ((Δ.addBinaryRel (SpecFn.rel s.name)).addUnary
    (SpecFn.func s.name)).addUnaryRel (SpecFn.defined s.name)

/-- Declare and axiomatize one validated quantifier symbol. -/
def declare (s : Lifting) (body : Skolemize.DefVal) : VerifM Unit :=
  SpecFn.declare s.name (s.axioms body)

/-- Canonical interpretation of the quantifier symbol's definedness predicate:
the evaluation of the definedness axiom's right-hand side. -/
noncomputable def definterp (s : Lifting) (body : Skolemize.DefVal) (ρ : Env) :
    Srt.value.denote → Prop :=
  fun v => (s.defMatrix body).eval (ρ.updateConst .value s.arg v)

open Classical in
/-- Canonical interpretation of the quantifier symbol's value function: the
boolean truth value of the value axiom's matrix. -/
noncomputable def funcinterp (s : Lifting) (body : Skolemize.DefVal) (ρ : Env) :
    Srt.value.denote → Srt.value.denote :=
  fun v =>
    if (s.matrix body).eval (ρ.updateConst .value s.arg v)
    then Runtime.Val.bool true else Runtime.Val.bool false

/-- Canonical interpretation of the quantifier symbol's relation: the graph of the
value function on the definedness domain (deterministic and split-compatible
by construction). -/
noncomputable def relinterp (s : Lifting) (body : Skolemize.DefVal) (ρ : Env) :
    Srt.value.denote → Srt.value.denote → Prop :=
  fun a b => s.definterp body ρ a ∧ s.funcinterp body ρ a = b

/-! ### Well-formedness of the defining axioms -/

private theorem var_wfIn {Δ : Signature} {x : String} {τ : Srt}
    (hΔ : Δ.wf) (hmem : (⟨x, τ⟩ : Var) ∈ Δ.vars) : (Term.var τ x).wfIn Δ :=
  ⟨hmem, fun _ hc => Signature.wf_no_const_of_var hΔ hmem hc,
   fun _ hv => Signature.wf_unique_var hΔ hmem hv⟩

variable {s : Lifting} {Δ : Signature} {body : Skolemize.DefVal}

private theorem prodProj_wfIn {x : String} (k : Nat)
    (hΔ : Δ.wf) (hmem : (⟨x, .value⟩ : Var) ∈ Δ.vars) :
    (VarEnv.prodProj (.var .value x) k).wfIn Δ :=
  show UnOp.wfIn .vhead Δ ∧ (vtailN (.unop .toValList (.var .value x)) k).wfIn Δ from
    ⟨trivial, vtailN_wfIn (t := .unop .toValList (.var .value x))
      ⟨trivial, var_wfIn hΔ hmem⟩ k⟩

private theorem gpack_wfIn (hΔ : Δ.wf)
    (hp : (⟨s.arg, .value⟩ : Var) ∈ Δ.vars) (hi : (⟨s.idx, .int⟩ : Var) ∈ Δ.vars) :
    s.gpack.wfIn Δ := by
  refine show UnOp.wfIn .ofValList Δ ∧ (Terms.toValList _).wfIn Δ from
    ⟨trivial, Terms.toValList_wfIn ?_⟩
  intro t ht
  rcases List.mem_append.mp ht with hmem | hmem
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
    exact prodProj_wfIn _ hΔ hp
  · simp only [List.mem_singleton] at hmem
    subst hmem
    exact show UnOp.wfIn .ofInt Δ ∧ (Term.var .int s.idx).wfIn Δ from
      ⟨trivial, var_wfIn hΔ hi⟩

/-- A successfully compiled lifting body is well-formed under its two matrix
variables. -/
theorem compile_wfIn (hv : s.Valid Δ) (hΔ : Δ.wf) (hΓ : Γ.wfIn Δ)
    (henc : s.compile Γ Δ = .ok body) :
    body.wfIn ((Δ.declVar ⟨s.arg, .value⟩).declVar ⟨s.idx, .int⟩) := by
  let Δp := Δ.declVar ⟨s.arg, .value⟩
  let Δpi := Δp.declVar ⟨s.idx, .int⟩
  have hΔp : Δp.wf := Signature.wf_declVar hΔ
  have hΔpi : Δpi.wf := Signature.wf_declVar hΔp
  have hsubp : Δ.Subset Δp := Signature.subset_declVar_of_fresh hv.argFresh
  have hsubpi : Δp.Subset Δpi :=
    Signature.subset_declVar_of_fresh (by
      rw [Signature.allNames_declVar_of_not_in hv.argFresh]
      intro hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact hv.idxNeArg h
      · exact hv.idxFresh h)
  have hp : (⟨s.arg, .value⟩ : Var) ∈ Δpi.vars :=
    hsubpi.vars _ (Signature.var_mem_declVar Δ ⟨s.arg, .value⟩)
  have hi : (⟨s.idx, .int⟩ : Var) ∈ Δpi.vars :=
    Signature.var_mem_declVar Δp ⟨s.idx, .int⟩
  have hcarrier : Skolemize.wfInE Δpi
      (encodeWith Skolemize.encoderOps Δpi Γ
        ((VarEnv.ofSignature Δpi).bind s.arg s.gpack) s.body
        (fun value => .ok (Skolemize.DefVal.pure value))) := by
    refine encodeWith_indWithSig Skolemize.encoderOps_wf s.body
      (Signature.Subset.refl _) hΔpi (FunCtx.splitWfIn_mono hΓ.split (hsubp.trans hsubpi))
      ((VarEnv.ofSignature_wfIn hΔpi).bind (gpack_wfIn hΔpi hp hi)) ?_
    intro Δ' _ _ value hvalue
    exact Skolemize.DefVal.pure_wfIn hvalue
  simp only [compile] at henc
  rw [henc] at hcarrier
  exact hcarrier

private theorem bounds_wfIn (hΔ : Δ.wf)
    (hp : (⟨s.arg, .value⟩ : Var) ∈ Δ.vars) (hi : (⟨s.idx, .int⟩ : Var) ∈ Δ.vars) :
    s.bounds.wfIn Δ := by
  have hproj : ∀ k, (VarEnv.prodProj s.pvar k).wfIn Δ := fun k => prodProj_wfIn k hΔ hp
  have hlo : s.lo.wfIn Δ :=
    show UnOp.wfIn .toInt Δ ∧ (VarEnv.prodProj s.pvar 0).wfIn Δ from ⟨trivial, hproj 0⟩
  have hhi : s.hi.wfIn Δ :=
    show UnOp.wfIn .toInt Δ ∧ (VarEnv.prodProj s.pvar 1).wfIn Δ from ⟨trivial, hproj 1⟩
  have hiv : s.ivar.wfIn Δ := var_wfIn hΔ hi
  exact ⟨⟨trivial, hlo, hiv⟩, ⟨trivial, hiv, hhi⟩⟩

/-- The index variable is fresh for the signature extended by the packed
variable, so the nested `declVar` is an extension. -/
private theorem idx_fresh_declVar (harg : s.arg ∉ Δ.allNames)
    (hidx : s.idx ∉ Δ.allNames) (hai : s.idx ≠ s.arg) :
    s.idx ∉ (Δ.declVar ⟨s.arg, .value⟩).allNames := by
  rw [Signature.allNames_declVar_of_not_in harg]
  intro hmem
  rcases List.mem_cons.mp hmem with h | h
  · exact hai h
  · exact hidx h

/-- Well-formedness of the value-axiom matrix at the packed-variable
signature, given a body compiled under both matrix variables. -/
theorem matrix_wfIn (hΔ : Δ.wf)
    (hbody : body.wfIn ((Δ.declVar ⟨s.arg, .value⟩).declVar ⟨s.idx, .int⟩))
    (harg : s.arg ∉ Δ.allNames) (hidx : s.idx ∉ Δ.allNames) (hai : s.idx ≠ s.arg) :
    (s.matrix body).wfIn (Δ.declVar ⟨s.arg, .value⟩) := by
  set Δp := Δ.declVar ⟨s.arg, .value⟩ with hΔp_def
  set Δpi := Δp.declVar ⟨s.idx, .int⟩ with hΔpi_def
  have hΔp : Δp.wf := Signature.wf_declVar hΔ
  have hΔpi : Δpi.wf := Signature.wf_declVar hΔp
  have hsubpi : Δp.Subset Δpi :=
    Signature.subset_declVar_of_fresh (idx_fresh_declVar harg hidx hai)
  have hpvars : (⟨s.arg, .value⟩ : Var) ∈ Δpi.vars :=
    hsubpi.vars _ (Signature.var_mem_declVar Δ ⟨s.arg, .value⟩)
  have hivars : (⟨s.idx, .int⟩ : Var) ∈ Δpi.vars :=
    Signature.var_mem_declVar Δp ⟨s.idx, .int⟩
  have hholds : body.value.isTrue.wfIn Δpi := ⟨hbody.1, trivial, trivial⟩
  unfold matrix
  split
  · exact ⟨fun _ h => (List.not_mem_nil h).elim,
      bounds_wfIn hΔpi hpvars hivars, hholds⟩
  · exact ⟨bounds_wfIn hΔpi hpvars hivars, hholds⟩

/-- Well-formedness of the definedness-axiom matrix at the packed-variable
signature. -/
theorem defMatrix_wfIn (hΔ : Δ.wf)
    (hbody : body.wfIn ((Δ.declVar ⟨s.arg, .value⟩).declVar ⟨s.idx, .int⟩))
    (harg : s.arg ∉ Δ.allNames) (hidx : s.idx ∉ Δ.allNames) (hai : s.idx ≠ s.arg) :
    (s.defMatrix body).wfIn (Δ.declVar ⟨s.arg, .value⟩) := by
  set Δp := Δ.declVar ⟨s.arg, .value⟩ with hΔp_def
  set Δpi := Δp.declVar ⟨s.idx, .int⟩ with hΔpi_def
  have hΔp : Δp.wf := Signature.wf_declVar hΔ
  have hΔpi : Δpi.wf := Signature.wf_declVar hΔp
  have hsubpi : Δp.Subset Δpi :=
    Signature.subset_declVar_of_fresh (idx_fresh_declVar harg hidx hai)
  have hpvars : (⟨s.arg, .value⟩ : Var) ∈ Δpi.vars :=
    hsubpi.vars _ (Signature.var_mem_declVar Δ ⟨s.arg, .value⟩)
  have hivars : (⟨s.idx, .int⟩ : Var) ∈ Δpi.vars :=
    Signature.var_mem_declVar Δp ⟨s.idx, .int⟩
  exact ⟨fun _ h => (List.not_mem_nil h).elim,
    bounds_wfIn hΔpi hpvars hivars,
    hbody.2⟩

/-- Well-formedness of the defining axioms. All hypotheses are discharged
operationally by the assembly step (symbol declarations and name checks). -/
theorem axioms_wfIn (hΔ : Δ.wf)
    (hbody : body.wfIn ((Δ.declVar ⟨s.arg, .value⟩).declVar ⟨s.idx, .int⟩))
    (hlfun : SpecFn.func s.name ∈ Δ.unary) (hldef : SpecFn.defined s.name ∈ Δ.unaryRel)
    (harg : s.arg ∉ Δ.allNames) (hidx : s.idx ∉ Δ.allNames) (hai : s.idx ≠ s.arg) :
    ∀ ax ∈ s.axioms body, ax.formula.wfIn Δ := by
  intro ax hmem
  have hΔp : (Δ.declVar ⟨s.arg, .value⟩).wf := Signature.wf_declVar hΔ
  have hsubp : Δ.Subset (Δ.declVar ⟨s.arg, .value⟩) :=
    Signature.subset_declVar_of_fresh harg
  have hpwf : (Term.var .value s.arg).wfIn (Δ.declVar ⟨s.arg, .value⟩) :=
    var_wfIn hΔp (Signature.var_mem_declVar Δ ⟨s.arg, .value⟩)
  have hlfun_p : SpecFn.func s.name ∈ (Δ.declVar ⟨s.arg, .value⟩).unary :=
    hsubp.unary _ hlfun
  have hldef_p : SpecFn.defined s.name ∈ (Δ.declVar ⟨s.arg, .value⟩).unaryRel :=
    hsubp.unaryRel _ hldef
  simp only [axioms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · -- defAxiom
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact SpecFn.isDefined_wfIn hldef_p hΔp hpwf
    · exact ⟨⟨SpecFn.isDefined_wfIn hldef_p hΔp hpwf,
        defMatrix_wfIn hΔ hbody harg hidx hai⟩,
        ⟨defMatrix_wfIn hΔ hbody harg hidx hai,
        SpecFn.isDefined_wfIn hldef_p hΔp hpwf⟩⟩
  · -- valAxiom
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact SpecFn.call_wfIn hlfun_p hΔp hpwf
    · exact ⟨⟨matrix_wfIn hΔ hbody harg hidx hai,
        SpecFn.call_wfIn hlfun_p hΔp hpwf, trivial, trivial⟩,
        ⟨matrix_wfIn hΔ hbody harg hidx hai,
        SpecFn.call_wfIn hlfun_p hΔp hpwf, trivial, trivial⟩⟩

/-! ### Validity of the defining axioms under the canonical interpretations -/

/-- The environment carrying the quantifier symbol's canonical interpretations. -/
noncomputable def extend (s : Lifting) (body : Skolemize.DefVal) (ρ : Env) : Env :=
  ((ρ.updateBinaryRel .value .value (SpecFn.relName s.name) (s.relinterp body ρ)).updateUnary
      .value .value (SpecFn.funcName s.name) (s.funcinterp body ρ)).updateUnaryRel
    .value (SpecFn.defName s.name) (s.definterp body ρ)

/-- The extension only touches the quantifier symbol's three fresh names. -/
theorem extend_agreeOn {ρ : Env}
    (hrel : SpecFn.relName s.name ∉ Δ.allNames)
    (hfun : SpecFn.funcName s.name ∉ Δ.allNames)
    (hdef : SpecFn.defName s.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (s.extend body ρ) :=
  Env.agreeOn_trans
    (Env.agreeOn_update_fresh_binaryRel (b := SpecFn.rel s.name)
      (f := s.relinterp body ρ) hrel)
    (Env.agreeOn_trans
      (Env.agreeOn_update_fresh_unary (u := SpecFn.func s.name)
        (f := s.funcinterp body ρ) hfun)
      (Env.agreeOn_update_fresh_unaryRel (u := SpecFn.defined s.name)
        (f := s.definterp body ρ) hdef))

@[simp] theorem extend_evalDefined (ρ : Env) (v : Srt.value.denote) :
    SpecFn.evalDefined s.name (s.extend body ρ) v ↔ s.definterp body ρ v := by
  simp [extend, SpecFn.evalDefined, SpecFn.defined, SpecFn.defName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

@[simp] theorem extend_evalCall (ρ : Env) (v : Srt.value.denote) :
    SpecFn.evalCall s.name (s.extend body ρ) v = s.funcinterp body ρ v := by
  simp [extend, SpecFn.evalCall, SpecFn.func, SpecFn.funcName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

@[simp] theorem extend_evalRelates (ρ : Env) (a b : Srt.value.denote) :
    SpecFn.evalRelates s.name (s.extend body ρ) a b ↔ s.relinterp body ρ a b := by
  simp [extend, SpecFn.evalRelates, SpecFn.rel, SpecFn.relName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

/-- The defining axioms hold in the extended environment. Matrix
well-formedness lets their evaluation be transported past the extension. -/
theorem axioms_eval {ρ : Env}
    (hmat : (s.matrix body).wfIn (Δ.declVar ⟨s.arg, .value⟩))
    (hdefmat : (s.defMatrix body).wfIn (Δ.declVar ⟨s.arg, .value⟩))
    (hrel : SpecFn.relName s.name ∉ Δ.allNames)
    (hfun : SpecFn.funcName s.name ∉ Δ.allNames)
    (hdef : SpecFn.defName s.name ∉ Δ.allNames) :
    ∀ ax ∈ s.axioms body, ax.formula.eval (s.extend body ρ) := by
  have hagree : Env.agreeOn Δ ρ (s.extend body ρ) := extend_agreeOn hrel hfun hdef
  have htrans : ∀ (φ : Formula), φ.wfIn (Δ.declVar ⟨s.arg, .value⟩) →
      ∀ v, φ.eval ((s.extend body ρ).updateConst .value s.arg v) ↔
        φ.eval (ρ.updateConst .value s.arg v) :=
    fun φ hwf v => (Formula.eval_env_agree hwf (Env.agreeOn_declVar hagree)).symm
  intro ax hmem
  simp only [axioms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · -- defAxiom
    simp only [defAxiom, Formula.iff, Formula.eval]
    intro v
    have hA : (SpecFn.isDefined s.name s.pvar).eval
        ((s.extend body ρ).updateConst .value s.arg v) ↔ s.definterp body ρ v := by
      simp [pvar, Term.eval]
    have hB := htrans (s.defMatrix body) hdefmat v
    exact ⟨fun h => hB.mpr (hA.mp h), fun h => hA.mpr (hB.mp h)⟩
  · -- valAxiom
    simp only [valAxiom, Term.isTrue, Term.isFalse, Formula.eval]
    intro v
    have hM := htrans (s.matrix body) hmat v
    have hcall : Term.eval ((s.extend body ρ).updateConst .value s.arg v)
        (SpecFn.call s.name s.pvar) = s.funcinterp body ρ v := by
      simp [pvar, Term.eval]
    constructor
    · intro h
      rw [hcall]
      simp only [funcinterp]
      rw [if_pos (hM.mp h)]
      simp [Term.eval]
    · intro h
      rw [hcall]
      simp only [funcinterp]
      rw [if_neg (fun hm => h (hM.mpr hm))]
      simp [Term.eval]

/-- Declaring a validated quantifier symbol preserves the global
relation-assembly invariants: the generic triple declaration
(`SpecFn.declare_correct`) instantiated with the canonical interpretations,
whose graph shape holds by construction. -/
theorem declare_correct (s : Lifting) (body : Skolemize.DefVal) (Δ : Signature) (Γ : FunCtx)
    (st : TransState) (ρ : VerifM.Env) {Q : Unit → TransState → VerifM.Env → Prop}
    (hv : Valid s Δ)
    (hbody : body.wfIn ((Δ.declVar ⟨s.arg, .value⟩).declVar ⟨s.idx, .int⟩))
    (hdecls : st.decls = Δ) (howns : st.owns = []) (hvars : st.decls.vars = [])
    (hwf : Δ.wf) (hΓwf : FunCtx.wfIn Γ Δ)
    (hsplit : FunCtx.splitCompatible Γ ρ.env)
    (hdet : Relation.BinaryRelDet Γ ρ.env ρ.env)
    (heval : VerifM.eval (s.declare body) st ρ Q) :
    ∃ st' ρ',
      st'.decls = s.extendSignature Δ ∧ st'.owns = [] ∧ st'.decls.vars = [] ∧
      st'.decls.wf ∧ st.decls.Subset st'.decls ∧
      VerifM.Env.agreeOn st.decls ρ ρ' ∧
      FunCtx.wfIn (Γ ++ [(s.name, s.name)]) st'.decls ∧
      FunCtx.splitCompatible (Γ ++ [(s.name, s.name)]) ρ'.env ∧
      Relation.BinaryRelDet (Γ ++ [(s.name, s.name)]) ρ'.env ρ'.env ∧
      Q () st' ρ' := by
  have hf : Skolemize.InfoFresh Δ s.name s.arg :=
    { relFresh := hv.relFresh, funFresh := hv.funFresh, defFresh := hv.defFresh,
      argFresh := hv.argFresh, argNeRel := hv.argNeRel,
      argNeFun := hv.argNeFun, argNeDef := hv.argNeDef }
  have hh : Skolemize.HeadFresh Δ s.name s.arg s.idx :=
    Skolemize.headFresh_of_fresh hf hv.idxFresh hv.idxNeRel hv.idxNeFun
      hv.idxNeDef hv.idxNeArg
  have hwfext : (s.extendSignature Δ).wf := hf.wf_addSplit hwf
  have hsub : Δ.Subset (s.extendSignature Δ) :=
    ((Signature.Subset.subset_addBinaryRel _ _).trans
      (Signature.Subset.subset_addUnary _ _)).trans
      (Signature.Subset.subset_addUnaryRel _ _)
  have hargext : s.arg ∉ (s.extendSignature Δ).allNames := hh.argFresh
  have hidxext : s.idx ∉ (s.extendSignature Δ).allNames := by
    intro hmem
    apply hh.resFresh
    show s.idx ∈ ((s.extendSignature Δ).declVar ⟨s.arg, .value⟩).allNames
    rw [Signature.allNames_declVar_of_not_in hargext]
    exact List.mem_cons_of_mem _ hmem
  have hbodyext : body.wfIn
      (((s.extendSignature Δ).declVar ⟨s.arg, .value⟩).declVar ⟨s.idx, .int⟩) := by
    have hsubpi := Signature.Subset.declVar
      (Signature.Subset.declVar hsub ⟨s.arg, .value⟩) ⟨s.idx, .int⟩
    have hwfpi :
        (((s.extendSignature Δ).declVar ⟨s.arg, .value⟩).declVar ⟨s.idx, .int⟩).wf :=
      Signature.wf_declVar (Signature.wf_declVar hwfext)
    exact ⟨Term.wfIn_mono body.value hbody.1 hsubpi hwfpi,
      Formula.wfIn_mono body.defined hbody.2 hsubpi hwfpi⟩
  have haxwf : ∀ ax ∈ s.axioms body, ax.formula.wfIn (s.extendSignature Δ) :=
    s.axioms_wfIn hwfext hbodyext (List.Mem.head _) (List.Mem.head _)
      hargext hidxext hv.idxNeArg
  have haxeval : ∀ ax ∈ s.axioms body,
      ax.formula.eval (Skolemize.relSplitEnv ρ.env s.name
        (s.relinterp body ρ.env) (s.definterp body ρ.env) (s.funcinterp body ρ.env)) :=
    s.axioms_eval (Δ := Δ)
      (s.matrix_wfIn hwf hbody hv.argFresh hv.idxFresh hv.idxNeArg)
      (s.defMatrix_wfIn hwf hbody hv.argFresh hv.idxFresh hv.idxNeArg)
      hv.relFresh hv.funFresh hv.defFresh
  exact SpecFn.declare_correct s.name s.name (s.axioms body)
    (s.relinterp body ρ.env) (s.funcinterp body ρ.env) (s.definterp body ρ.env) Δ Γ st ρ
    hv.relFresh hv.funFresh hv.defFresh (fun _ _ => Iff.rfl)
    hdecls howns hvars hwfext hΓwf hsplit hdet haxwf haxeval heval

end Lifting

end Verifier.BoundedQuantifier

-- SUMMARY: Declaration of spec functions: the solver symbols of `[@@fn]` functions, their defining axioms, and the checks of their measures.
import Mica.Verifier.Context
import Mica.Pure

open Verifier (State)

open Iris Iris.BI

open PureEncoding (FunCtx PrimEncodings encode)
open PureEncoding.Skolemize (DefVal)

/-!
# Spec functions

A spec function is declared to the solver as three symbols: a relation, a value
function, and a definedness predicate. This file declares them for `[@@fn]`
declarations and checks their `[@@decreases]` measures.
-/

/-! ## Declaring a spec-function symbol triple

Shared by `[@@fn]` functions below and by the lifted bounded quantifiers in
`BoundedQuantifier.lean`: declaring the three solver symbols of a spec function whose relation
interpretation is the graph of its value function on its definedness domain,
and assuming its valid defining axioms, preserves the spec-function declaration
invariants. -/

namespace SpecFn
open PureEncoding

/-- Declare the solver-facing triple of `L` and assume its defining axioms. -/
def declare (L : SpecFn) (axs : List Axiom) : SeqM Unit := do
  SeqM.declBinaryRel (SpecFn.rel L)
  SeqM.declUnary (SpecFn.func L)
  SeqM.declUnaryRel (SpecFn.defined L)
  SeqM.assumeAxioms axs

/-- Declaring the triple of a fresh symbol `L` — with interpretations whose
relation is the graph of the value function on the definedness domain, and
defining axioms that are well-formed and valid in the extended
signature/environment — preserves the spec-function declaration invariants and
extends the function context by `(f, L)`. -/
theorem declare_correct (L : SpecFn) (f : TinyML.Var) (axs : List Axiom)
    (R : Srt.value.denote → Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote)
    (D : Srt.value.denote → Prop)
    (Δ : Signature) (Γ : FunCtx) (st : State) (ρ : Env)
    {Q : Unit → State → Env → Prop}
    (hrelFresh : relName L ∉ Δ.allNames)
    (hfuncFresh : funcName L ∉ Δ.allNames)
    (hdefFresh : defName L ∉ Δ.allNames)
    (hgraph : ∀ a b, R a b ↔ D a ∧ F a = b)
    (hdecls : st.decls = Δ) (howns : st.owns = []) (hvars : st.decls.vars = [])
    (hwfext : (((Δ.addBinaryRel (rel L)).addUnary (func L)).addUnaryRel (defined L)).wf)
    (hΓwf : FunCtx.wfIn Γ Δ)
    (hΓagree : FunCtx.Agreement Γ ρ)
    (haxwf : ∀ ax ∈ axs, ax.formula.wfIn
      (((Δ.addBinaryRel (rel L)).addUnary (func L)).addUnaryRel (defined L)))
    (haxeval : ∀ ax ∈ axs, ax.formula.eval (SpecFn.Env.both ρ L R D F))
    (heval : SeqM.eval (declare L axs) st ρ Q) :
    ∃ st' ρ', ρ' = SpecFn.Env.both ρ L R D F ∧
      st'.decls = ((Δ.addBinaryRel (rel L)).addUnary (func L)).addUnaryRel (defined L) ∧
      st'.owns = [] ∧ st'.decls.vars = [] ∧ st'.decls.wf ∧
      st.decls.Subset st'.decls ∧
      Env.agreeOn st.decls ρ ρ' ∧
      FunCtx.wfIn (Γ ++ [(f, L)]) st'.decls ∧
      FunCtx.Agreement (Γ ++ [(f, L)]) ρ' ∧ Q () st' ρ' := by
  simp only [declare] at heval
  obtain ⟨_, h1⟩ := SeqM.eval_declBinaryRel (SeqM.eval_bind heval)
  obtain ⟨_, h2⟩ := SeqM.eval_declUnary (SeqM.eval_bind (h1 R))
  obtain ⟨_, h3⟩ := SeqM.eval_declUnaryRel (SeqM.eval_bind (h2 F))
  have h4 := h3 D
  set Δext : Signature :=
    ((Δ.addBinaryRel (rel L)).addUnary (func L)).addUnaryRel (defined L)
  set st3 : State :=
    { st with decls := ((st.decls.addBinaryRel (rel L)).addUnary
        (func L)).addUnaryRel (defined L) }
  set ρ3 : Env :=
    ((ρ.updateBinaryRel .value .value (relName L) R).updateUnary
        .value .value (funcName L) F).updateUnaryRel
      .value (defName L) D
  have hst3 : st3.decls = Δext := by
    simp only [st3, Δext, hdecls]
  have hρ3 : ρ3 = SpecFn.Env.both ρ L R D F := by
    rfl
  have hsub : Δ.Subset Δext :=
    ((Signature.Subset.subset_addBinaryRel _ _).trans
      (Signature.Subset.subset_addUnary _ _)).trans
      (Signature.Subset.subset_addUnaryRel _ _)
  obtain ⟨st4, hst4, howns4, _, hQ4⟩ :=
    SeqM.eval_assumeAxioms h4 (fun ax hax => hst3 ▸ haxwf ax hax)
      (fun ax hax => by simpa [SpecFn.Env.both] using haxeval ax hax)
  have howns4' : st4.owns = [] := by rw [howns4]; exact howns
  have hvars4 : st4.decls.vars = [] := by
    rw [hst4, hst3]
    show Δ.vars = []
    rw [← hdecls]
    exact hvars
  have hwf4 : st4.decls.wf := by rw [hst4, hst3]; exact hwfext
  have hagree : Env.agreeOn Δ ρ ρ3 := by
    rw [hρ3]
    exact SpecFn.Env.both_agreeOn hrelFresh hfuncFresh hdefFresh
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
      · obtain ⟨hu, hr⟩ := hΓwf.func x rel hold
        exact ⟨hsub.unary _ hu, hsub.unaryRel _ hr⟩
      · simp at hnew; obtain ⟨_, rfl⟩ := hnew
        exact ⟨List.Mem.head _, List.Mem.head _⟩
  have hΓagree' : FunCtx.Agreement (Γ ++ [(f, L)]) ρ3 := by
    intro g rel hgr x y
    rcases List.mem_append.mp hgr with hold | hnew
    · obtain ⟨hu, hr⟩ := hΓwf.func g rel hold
      obtain ⟨her, hec, hed⟩ := SpecFn.eval_of_agreeOn hagree (hΓwf.rel g rel hold) hu hr
      rw [← her, ← hec, ← hed]
      exact hΓagree g rel hold x y
    · simp at hnew; obtain ⟨_, rfl⟩ := hnew
      rw [hρ3]
      exact SpecFn.Env.both_agreement rel ρ hgraph x y
  have hsub4 : st.decls.Subset st4.decls := by
    rw [hst4, hst3, hdecls]
    exact hsub
  have hagree4 : Env.agreeOn st.decls ρ ρ3 := by
    rw [hdecls]
    exact hagree
  exact ⟨st4, ρ3, hρ3, by rw [hst4, hst3], howns4', hvars4, hwf4, hsub4,
    hagree4, hΓwf', hΓagree', hQ4⟩

end SpecFn

/-! ## Termination check -/

namespace PureEncoding.Termination

/-- Prove total definedness from the body, without recursive definedness
axioms. The quantified induction hypothesis belongs only to this query. The
caller records the totality this establishes, outside the query's scope. -/
def check (fn : SpecFn) (x : String) (m : Typed.Measure)
    (body : Skolemize.DefVal) : VerifM Unit := do
  let Δ ← VerifM.decls
  let rank := Fresh.freshName (x :: Δ.allNames) "rank"
  let φ := obligation fn x rank m body
  match m.term.checkWf (Δ.declVar ⟨x, .value⟩),
      body.defined.checkWf (Δ.declVar ⟨x, .value⟩), φ.checkWf Δ, (total fn x).checkWf Δ with
  | .ok (), .ok (), .ok (), .ok () => do
    if ← VerifM.check .high φ then pure ()
    else VerifM.failed s!"termination check failed for {fn}"
  | .error msg, _, _, _ | _, .error msg, _, _ | _, _, .error msg, _ | _, _, _, .error msg =>
    VerifM.fatal msg

theorem check_correct {fn : SpecFn} {x : String} {m : Typed.Measure}
    {body : Skolemize.DefVal} {st : State} {ρ : Env}
    {Q : Unit → State → Env → Prop}
    (hclose : ∀ v, body.defined.eval (ρ.updateConst .value x v) →
      (fn.isDefined (.var .value x)).eval (ρ.updateConst .value x v))
    (h : VerifM.eval (check fn x m body) st ρ Q) :
    (total fn x).wfIn st.decls ∧ (total fn x).eval ρ ∧ Q () st ρ := by
  simp only [check] at h
  have h := VerifM.eval_decls (VerifM.eval_bind h)
  split at h
  · rename_i hm hb hφ ht
    obtain ⟨b, hb', h⟩ := VerifM.eval_check (VerifM.eval_bind h) (Formula.checkWf_ok hφ)
    cases b with
    | false => exact (VerifM.eval_failed h).elim
    | true =>
      have hfresh := Fresh.freshName_not_in_avoid (x :: st.decls.allNames) "rank"
      simp only [List.mem_cons, not_or] at hfresh
      have htotal := obligation_correct hfresh.2 hfresh.1 (Term.checkWf_ok hm)
        (Formula.checkWf_ok hb) hclose (hb' rfl)
      exact ⟨Formula.checkWf_ok ht, htotal, VerifM.eval_ret h⟩
  all_goals exact (VerifM.eval_fatal h).elim

end PureEncoding.Termination

/-! ## `[@@fn]` declarations -/

namespace Verifier.Env

open PureEncoding

/-- A specification on the literal is `[@@impl]`'s, which states the result
against this very axiomatization; the frontend rejects every other pairing of
`[@@fn]` with a specification. -/
private def validateDecl (d : Typed.ValDecl) :
    Except String (TinyML.Var × TinyML.Var × Typed.Expr) := do
  let f ← match d.name.name with
    | some f => .ok f
    | none => .error s!"[@@fn] requires a named declaration"
  match d.body with
  | .fix _ [arg] _ _ body =>
    match arg.name with
    | some x => .ok (f, x, body)
    | none => .error s!"[@@fn] requires a named unary argument"
  | .fix _ _ _ _ _ => .error s!"[@@fn] requires a unary function"
  | _ => .error s!"[@@fn] requires a function body"

/-- The spec function `rel` that the `[@@fn]` declaration `d` defines. Its
symbols and its argument must be fresh for the signature of `env`. -/
private def specDef (env : Env) (d : Typed.ValDecl) (rel : SpecFn) : Except String SpecDef := do
  let (f, arg, body) ← validateDecl d
  let relName := SpecFn.relName rel
  let funName := SpecFn.funcName rel
  let defName := SpecFn.defName rel
  if relName ∈ env.signature.allNames then
    .error s!"derived relation name '{relName}' for [@@fn] conflicts with an existing symbol"
  else if funName ∈ env.signature.allNames then
    .error s!"derived value-function name '{funName}' for [@@fn] conflicts with an existing symbol"
  else if defName ∈ env.signature.allNames then
    .error s!"derived definedness name '{defName}' for [@@fn] conflicts with an existing symbol"
  else if arg ∈ env.signature.allNames then
    .error s!"[@@fn] argument name '{arg}' conflicts with a global symbol"
  else if arg = relName then
    .error s!"[@@fn] argument name '{arg}' clashes with derived relation name"
  else if arg = funName then
    .error s!"[@@fn] argument name '{arg}' clashes with derived value-function name"
  else if arg = defName then
    .error s!"[@@fn] argument name '{arg}' clashes with derived definedness name"
  else
    .ok { primitives := env.registry.primitives, Γ := env.specFunctions, Δ := env.signature,
          f, fn := rel, x := arg, e := body }

/-- An opaque spec function also records its defining equation as a lemma. -/
private def extend (env : Env) (sd : SpecDef) (bv : Skolemize.DefVal)
    (t : TinyML.Transparency) : Env :=
  let lemmas := match t with
    | .transparent => env.lemmas
    | .opaque => env.lemmas ++
        [{ kind := .definingEquation sd.f,
           fact := Skolemize.SpecFn.Axioms.equation sd.fn sd.x bv }]
  { env with
    lemmas,
    specFunctions := env.specFunctions ++ [(sd.f, sd.fn)],
    signature := ((env.signature.addBinaryRel (SpecFn.rel sd.fn)).addUnary
                   (SpecFn.func sd.fn)).addUnaryRel (SpecFn.defined sd.fn) }

/-- With a measure the definedness axioms are replaced by a proof: the
termination check establishes definedness at every input. The check is one of
the declaration's own proofs, so it runs with the withheld fact. Only the
totality survives the bracket. -/
private def declareRelation (sd : SpecDef) (bv : Skolemize.DefVal) (t : TinyML.Transparency) :
    Option Typed.Measure → SeqM Unit
  | none =>
    SpecFn.declare sd.fn
      (Skolemize.SpecFn.Axioms.persistent false t sd.fn sd.x bv)
  | some m => do
    SpecFn.declare sd.fn
      (Skolemize.SpecFn.Axioms.persistent true t sd.fn sd.x bv)
    SeqM.check do
      VerifM.assumeAxioms (Skolemize.SpecFn.Axioms.withheld t sd.fn sd.x bv)
      Termination.check sd.fn sd.x m bv
    SeqM.assume (Termination.total sd.fn sd.x)

def declareAndAssume (env : Env) (d : Typed.ValDecl) : SeqM Env := do
  match d.relation with
  | none => pure env
  | some r =>
      match specDef env d r.name with
      | .error msg => SeqM.fatal msg
      | .ok sd =>
          match Skolemize.encode sd with
          | .error msg => SeqM.fatal msg
          | .ok (bv, _) => do
              declareRelation sd bv r.transparency d.decreases
              pure (extend env sd bv r.transparency)

/-- The invariant threaded through the declaration of spec functions: the signature mirrors the declared
one, the state is spec-level (no owned locations, no variables), and the spec
functions are well-formed and interpreted in agreement with their func-form
reading. -/
structure SpecInv (reg : Registry) (Θ : TinyML.TypeEnv) (env : Env) (st : State)
    (ρ : _root_.Env) : Prop where
  registry : env.registry = reg
  types : env.typeDeclarations = Θ
  signature : env.signature = st.decls
  owns : st.owns = []
  vars : st.decls.vars = []
  wf : st.decls.wf
  Γwf : FunCtx.wfIn env.specFunctions st.decls
  Γagree : FunCtx.Agreement env.specFunctions ρ
  lemmas : env.lemmas.Sound st.decls ρ

/-- Declaring one relation-marked declaration preserves `SpecInv`; the signature
only grows and the environment is only extended with fresh interpretations. -/
theorem declareAndAssume_correct {reg : Registry} {Θ : TinyML.TypeEnv}
    (hlaw : reg.primitives.Lawful) (d : Typed.ValDecl)
    (env : Env) (st : State) (ρ : _root_.Env)
    {Q : Env → State → _root_.Env → Prop}
    (hinv : SpecInv reg Θ env st ρ)
    (heval : SeqM.eval (declareAndAssume env d) st ρ Q) :
    ∃ env' st' ρ', SpecInv reg Θ env' st' ρ' ∧
      st.decls.Subset st'.decls ∧ Env.agreeOn st.decls ρ ρ' ∧
      Q env' st' ρ' := by
  obtain ⟨hreg, htypes, hacc, howns, hvars, hwf, hΓwf, hΓagree, hu⟩ := hinv
  simp only [declareAndAssume] at heval
  cases hrel : d.relation with
  | none =>
    simp only [hrel] at heval
    exact ⟨env, st, ρ, ⟨hreg, htypes, hacc, howns, hvars, hwf, hΓwf, hΓagree, hu⟩,
      Signature.Subset.refl _, Env.agreeOn_refl, SeqM.eval_ret heval⟩
  | some rel =>
    simp only [hrel] at heval
    cases hsd : specDef env d rel.name with
    | error msg => simp only [hsd] at heval; exact (SeqM.eval_fatal heval).elim
    | ok sd =>
      simp only [hsd] at heval
      obtain ⟨⟨bv, axs₀⟩, henc⟩ : ∃ r, Skolemize.encode sd = .ok r := by
        cases h : Skolemize.encode sd with
        | error msg => simp only [h] at heval; exact (SeqM.eval_fatal heval).elim
        | ok r => exact ⟨r, rfl⟩
      simp only [henc] at heval
      obtain ⟨hprimsd, hΓsd, hΔsd, hfnsd, hf⟩ :
          sd.primitives = env.registry.primitives ∧
          sd.Γ = env.specFunctions ∧ sd.Δ = env.signature ∧ sd.fn = rel.name ∧
          SpecFnFresh env.signature rel.name sd.x := by
        unfold specDef at hsd
        simp only [bind, Except.bind] at hsd
        split at hsd
        · cases hsd
        rename_i validated _
        obtain ⟨f, arg, body⟩ := validated
        split_ifs at hsd with
          hrel_in hfun_in hdef_in harg_in harg_eq_rel harg_eq_fun harg_eq_def
        case neg =>
          cases hsd
          refine ⟨rfl, rfl, rfl, rfl, { symFresh := ?_, argFresh := ?_ }⟩
          · intro n hn
            simp only [SpecFn.names, List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl | rfl
            exacts [hrel_in, hfun_in, hdef_in]
          · simp [SpecFn.names, harg_in, harg_eq_rel, harg_eq_fun, harg_eq_def]
      have hspec_lemmas : ∀ l ∈ (extend env sd bv rel.transparency).lemmas, l ∈ env.lemmas ∨
          l.fact = Skolemize.SpecFn.Axioms.equation sd.fn sd.x bv := by
        cases rel.transparency with
        | transparent => exact fun l hl => Or.inl hl
        | «opaque» =>
          intro l hl
          rcases List.mem_append.mp hl with hl | hl
          · exact Or.inl hl
          · simp only [List.mem_singleton] at hl
            subst hl
            exact Or.inr rfl
      have hΓwf_acc : FunCtx.wfIn env.specFunctions env.signature := hacc ▸ hΓwf
      have hΔwf_acc : env.signature.wf := hacc ▸ hwf
      -- The chosen interpretations: the ground-truth relation and its func-form reading.
      set R : ValRel := SpecFn.Semantics.rel sd ρ
      set F := ValRel.toFunc R
      set D : Srt.value.denote → Prop := SpecFn.Semantics.defined sd ρ bv
      have hsdFresh : sd.Fresh :=
        SpecDef.fresh (hΔsd ▸ hfnsd ▸ hf)
      have hlaw' : env.registry.primitives.Lawful := hreg ▸ hlaw
      have hlawsd : sd.primitives.Lawful := hprimsd ▸ hlaw'
      have hgraph : ∀ a b, R a b ↔ D a ∧ F a = b := fun a b =>
        Skolemize.encode_agreement hlawsd henc (hΓsd ▸ hΓagree)
          (hΓsd ▸ hΔsd ▸ hΓwf_acc) (hΔsd ▸ hΔwf_acc) hsdFresh a b
      have henv : SpecFn.Env.both ρ rel.name R D F
          = (SpecFn.Semantics.env sd ρ bv).updateBinaryRel
            .value .value (SpecFn.relName rel.name) R := by
        simp only [SpecFn.Semantics.env, hfnsd]
        exact SpecFn.Env.both_updateBinaryRel.symm
      have haxeval : ∀ ax ∈ axs₀,
          ax.formula.eval (SpecFn.Env.both ρ rel.name R D F) := by
        rw [henv]
        rw [← hfnsd]
        exact Skolemize.encode_eval_updateBinaryRel hlawsd henc (hΓsd ▸ hΓagree)
          (hΓsd ▸ hΔsd ▸ hΓwf_acc) (hΔsd ▸ hΔwf_acc) hsdFresh R
      have hdecl (axs : List Axiom) (hsub : ∀ ax ∈ axs, ax ∈ axs₀)
          {Q' : Unit → State → _root_.Env → Prop}
          (h : SeqM.eval (SpecFn.declare sd.fn axs) st ρ Q') :=
        SpecFn.declare_correct rel.name sd.f axs R F D env.signature env.specFunctions st ρ
          hf.relFresh hf.funcFresh hf.defFresh hgraph hacc.symm howns hvars
          (hf.sigBoth_wf hΔwf_acc) hΓwf_acc hΓagree
          (fun ax hax => by
            have := Skolemize.encode_wfIn hlawsd henc (hΔsd ▸ hΔwf_acc)
              (hΓsd ▸ hΔsd ▸ hΓwf_acc) hsdFresh ax (hsub ax hax)
            rwa [hΔsd, hfnsd] at this)
          (fun ax hax => haxeval ax (hsub ax hax)) (hfnsd ▸ h)
      -- Every encoded axiom holds once the three symbols are declared, whether
      -- or not it stays in the context.
      have hcurrent {st' : State} {ρ' : _root_.Env}
          (hd : st'.decls = ((env.signature.addBinaryRel (SpecFn.rel rel.name)).addUnary
            (SpecFn.func rel.name)).addUnaryRel (SpecFn.defined rel.name))
          (hρ : ρ' = SpecFn.Env.both ρ rel.name R D F) :
          ∀ ax ∈ axs₀, ax.formula.wfIn st'.decls ∧ ax.formula.eval ρ' := by
        intro ax hax
        refine ⟨?_, hρ ▸ haxeval ax hax⟩
        rw [hd, ← hΔsd, ← hfnsd]
        exact Skolemize.encode_wfIn hlawsd henc (hΔsd ▸ hΔwf_acc)
          (hΓsd ▸ hΔsd ▸ hΓwf_acc) hsdFresh ax hax
      -- Either form declares a sublist of the encoded axioms. A measure then
      -- adds the totality assertion, which touches no field the invariant reads.
      have hrun : ∃ axs, (∀ ax ∈ axs, ax ∈ axs₀) ∧
          SeqM.eval (SpecFn.declare sd.fn axs) st ρ
            (fun _ st' ρ' =>
              st'.decls = ((env.signature.addBinaryRel (SpecFn.rel rel.name)).addUnary
                (SpecFn.func rel.name)).addUnaryRel (SpecFn.defined rel.name) →
              ρ' = SpecFn.Env.both ρ rel.name R D F →
              ∃ st'', st''.decls = st'.decls ∧ st''.owns = st'.owns ∧
                Q (extend env sd bv rel.transparency) st'' ρ') := by
        have h := SeqM.eval_bind heval
        cases hm : d.decreases with
        | none =>
          simp only [declareRelation, hm] at h
          exact ⟨_, Skolemize.encode_persistent henc,
            SeqM.eval_mono h fun _ st' _ hQ _ _ => ⟨st', rfl, rfl, SeqM.eval_ret hQ⟩⟩
        | some m =>
          simp only [declareRelation, hm] at h
          refine ⟨_, Skolemize.encode_persistent henc, SeqM.eval_mono (SeqM.eval_bind h) ?_⟩
          intro _ st' ρ' hc hd' hρ'
          have hclose : ∀ v, bv.defined.eval (ρ'.updateConst .value sd.x v) →
              (sd.fn.isDefined (.var .value sd.x)).eval
                (ρ'.updateConst .value sd.x v) := by
            rw [hρ']; exact Skolemize.encode_closed henc haxeval
          obtain ⟨hproof, hcont⟩ := SeqM.eval_check (SeqM.eval_bind hc)
          have hlocal := fun ax (hax : ax ∈ Skolemize.SpecFn.Axioms.withheld
              rel.transparency sd.fn sd.x bv) =>
            hcurrent hd' hρ' ax (Skolemize.encode_withheld henc ax hax)
          obtain ⟨st₀, hd₀, _, _, hcheck⟩ := VerifM.eval_assumeAxioms
            (VerifM.eval_bind hproof) (fun ax hax => (hlocal ax hax).1)
            (fun ax hax => (hlocal ax hax).2)
          obtain ⟨hwt, ht, _⟩ := Termination.check_correct hclose hcheck
          exact ⟨{ st' with asserts := Termination.total sd.fn sd.x :: st'.asserts },
            rfl, rfl, SeqM.eval_ret (SeqM.eval_assume hcont (hd₀ ▸ hwt) ht)⟩
      obtain ⟨axs, hsub, hrun⟩ := hrun
      obtain ⟨st4, ρ4, hρ4, hst4_decls, howns4, hvars4, hwf4, hsub4, hagree4,
        hΓwf4, hΓagree4, hcont⟩ := hdecl axs hsub hrun
      obtain ⟨st5, hst5_decls, howns5, hQ5⟩ := hcont hst4_decls hρ4
      refine ⟨(extend env sd bv rel.transparency), st5, ρ4, ⟨hreg, htypes, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hagree4,
        hQ5⟩
      · simp only [extend, hfnsd]; rw [hst5_decls, hst4_decls]
      · rw [howns5, howns4]
      · rw [hst5_decls]; exact hvars4
      · rw [hst5_decls]; exact hwf4
      · simp only [extend, hfnsd]; rw [hst5_decls]; exact hΓwf4
      · simp only [extend, hfnsd]; exact hΓagree4
      · rw [hst5_decls]
        intro l hl
        rcases hspec_lemmas l hl with hl' | hfact
        · exact (hu l hl').mono hsub4 hagree4 hwf4
        · simp only [Lemma.Sound, hfact]
          exact hcurrent hst4_decls hρ4 _ (Skolemize.encode_equation henc)
      · rw [hst5_decls]; exact hsub4

end Verifier.Env

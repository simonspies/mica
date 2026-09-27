-- SUMMARY: Declaration of spec functions: the solver symbols of `[@@fn]` functions, their defining axioms, and the checks of their measures.
import Mica.Verifier.Context
import Mica.Verifier.RelationalEncoding

open Iris Iris.BI

open Verifier.RelationalEncoding (FunCtx PrimEncodings encode)
open Verifier.RelationalEncoding.Skolemize (DefVal)

/-! ## Declaring a spec-function symbol triple

Generic infrastructure, shared with the declaration of `[@@fn]` functions in `Declaration.lean`:
declaring the three solver symbols of a spec function whose relation
interpretation is the graph of its value function on its definedness domain,
and assuming its valid defining axioms, preserves the spec-function declaration
invariants. -/

namespace SpecFn
open Verifier.RelationalEncoding

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
    (Δ : Signature) (Γ : FunCtx) (st : TransState) (ρ : Env)
    {Q : Unit → TransState → Env → Prop}
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
  set st3 : TransState :=
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

namespace Verifier.Env

open Verifier.RelationalEncoding

private structure RelationDecl where
  env : Env
  sd : SpecDef
  axs : List Axiom
  bv : Skolemize.DefVal

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

private def extend (env : Env) (d : Typed.ValDecl) : Except String RelationDecl := do
  match d.relation with
  | none => .error "internal error: expected relation declaration"
  | some r => do
      let rel := r.name
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
        let sd : SpecDef :=
          { primitives := env.registry.primitives, Γ := env.specFunctions, Δ := env.signature,
            f, fn := rel, x := arg, e := body }
        let (bv, axs) ← Skolemize.encode sd
        let lemmas := match r.transparency with
          | .transparent => env.lemmas
          | .opaque => env.lemmas ++
              [{ kind := .definingEquation f,
                 fact := Skolemize.SpecFn.Axioms.equation rel arg bv }]
        let env' := { env with
                       lemmas,
                       specFunctions := env.specFunctions ++ [(f, rel)],
                       signature := ((env.signature.addBinaryRel (SpecFn.rel rel)).addUnary
                                      (SpecFn.func rel)).addUnaryRel (SpecFn.defined rel) }
        .ok { env := env', sd, axs, bv }

/-- With a measure the definedness axioms are replaced by a proof: the
termination check establishes definedness at every input. The check is one of
the declaration's own proofs, so it runs with the withheld fact. Only the
totality survives the bracket. -/
private def RelationDecl.declare (info : RelationDecl) (t : TinyML.Transparency) :
    Option Typed.Measure → SeqM Unit
  | none =>
    SpecFn.declare info.sd.fn
      (Skolemize.SpecFn.Axioms.persistent false t info.sd.fn info.sd.x info.bv)
  | some m => do
    SpecFn.declare info.sd.fn
      (Skolemize.SpecFn.Axioms.persistent true t info.sd.fn info.sd.x info.bv)
    SeqM.check do
      VerifM.assumeAxioms (Skolemize.SpecFn.Axioms.withheld t info.sd.fn info.sd.x info.bv)
      Termination.check info.sd.fn info.sd.x m info.bv
    SeqM.assume (Termination.total info.sd.fn info.sd.x)

def declareAndAssume (env : Env) (d : Typed.ValDecl) : SeqM Env := do
  match d.relation with
  | none => pure env
  | some r =>
      match extend env d with
      | .error msg => SeqM.fatal msg
      | .ok info => do
          info.declare r.transparency d.decreases
          pure info.env

/-- The invariant threaded through the declaration of spec functions: the signature mirrors the declared
one, the state is spec-level (no owned locations, no variables), and the spec
functions are well-formed and interpreted in agreement with their func-form
reading. -/
structure SpecInv (reg : Registry) (Θ : TinyML.TypeEnv) (env : Env) (st : TransState)
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
    (env : Env) (st : TransState) (ρ : _root_.Env)
    {Q : Env → TransState → _root_.Env → Prop}
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
    cases hext : extend env d with
    | error msg => simp only [hext] at heval; exact (SeqM.eval_fatal heval).elim
    | ok info =>
      simp only [hext] at heval
      -- Unfold `extend` once to expose its construction facts about `info`.
      obtain ⟨hprimsd, hΓsd, hΔsd, hfnsd, hf, hspec_delta, hspec_fm, hspec_reg, hspec_types,
          hspec_lemmas, hinfoEq⟩ :
          info.sd.primitives = env.registry.primitives ∧
          info.sd.Γ = env.specFunctions ∧ info.sd.Δ = env.signature ∧ info.sd.fn = rel.name ∧
          SpecFnFresh env.signature rel.name info.sd.x ∧
          info.env.signature = ((env.signature.addBinaryRel (SpecFn.rel rel.name)).addUnary
              (SpecFn.func rel.name)).addUnaryRel (SpecFn.defined rel.name) ∧
          info.env.specFunctions = env.specFunctions ++ [(info.sd.f, rel.name)] ∧
          info.env.registry = env.registry ∧
          info.env.typeDeclarations = env.typeDeclarations ∧
          (∀ l ∈ info.env.lemmas, l ∈ env.lemmas ∨
            l.fact = Skolemize.SpecFn.Axioms.equation info.sd.fn info.sd.x info.bv) ∧
          Skolemize.encode info.sd = .ok (info.bv, info.axs) := by
        unfold extend at hext
        simp only [hrel, bind, Except.bind] at hext
        split at hext
        · cases hext
        rename_i validated _
        obtain ⟨f, arg, body⟩ := validated
        split_ifs at hext with
          hrel_in hfun_in hdef_in harg_in harg_eq_rel harg_eq_fun harg_eq_def
        case neg =>
          split at hext
          · cases hext
          rename_i tup hinfoTuple
          obtain ⟨bv, axs⟩ := tup
          cases hext
          refine ⟨rfl, rfl, rfl, rfl, { symFresh := ?_, argFresh := ?_ }, rfl, rfl, rfl, rfl, ?_,
            hinfoTuple⟩
          · intro n hn
            simp only [SpecFn.names, List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl | rfl
            exacts [hrel_in, hfun_in, hdef_in]
          · simp [SpecFn.names, harg_in, harg_eq_rel, harg_eq_fun, harg_eq_def]
          · cases rel.transparency with
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
      set R : ValRel := SpecFn.Semantics.rel info.sd ρ
      set F := ValRel.toFunc R
      set D : Srt.value.denote → Prop := SpecFn.Semantics.defined info.sd ρ info.bv
      have hsdFresh : info.sd.Fresh :=
        SpecDef.fresh (hΔsd ▸ hfnsd ▸ hf)
      have hlaw' : env.registry.primitives.Lawful := hreg ▸ hlaw
      have hlawsd : info.sd.primitives.Lawful := hprimsd ▸ hlaw'
      have hgraph : ∀ a b, R a b ↔ D a ∧ F a = b := fun a b =>
        Skolemize.encode_agreement hlawsd hinfoEq (hΓsd ▸ hΓagree)
          (hΓsd ▸ hΔsd ▸ hΓwf_acc) (hΔsd ▸ hΔwf_acc) hsdFresh a b
      have henv : SpecFn.Env.both ρ rel.name R D F
          = (SpecFn.Semantics.env info.sd ρ info.bv).updateBinaryRel
            .value .value (SpecFn.relName rel.name) R := by
        simp only [SpecFn.Semantics.env, hfnsd]
        exact SpecFn.Env.both_updateBinaryRel.symm
      have haxeval : ∀ ax ∈ info.axs,
          ax.formula.eval (SpecFn.Env.both ρ rel.name R D F) := by
        rw [henv]
        rw [← hfnsd]
        exact Skolemize.encode_eval_updateBinaryRel hlawsd hinfoEq (hΓsd ▸ hΓagree)
          (hΓsd ▸ hΔsd ▸ hΓwf_acc) (hΔsd ▸ hΔwf_acc) hsdFresh R
      have hdecl (axs : List Axiom) (hsub : ∀ ax ∈ axs, ax ∈ info.axs)
          {Q' : Unit → TransState → _root_.Env → Prop}
          (h : SeqM.eval (SpecFn.declare info.sd.fn axs) st ρ Q') :=
        SpecFn.declare_correct rel.name info.sd.f axs R F D env.signature env.specFunctions st ρ
          hf.relFresh hf.funcFresh hf.defFresh hgraph hacc.symm howns hvars
          (hf.sigBoth_wf hΔwf_acc) hΓwf_acc hΓagree
          (fun ax hax => by
            have := Skolemize.encode_wfIn hlawsd hinfoEq (hΔsd ▸ hΔwf_acc)
              (hΓsd ▸ hΔsd ▸ hΓwf_acc) hsdFresh ax (hsub ax hax)
            rwa [hΔsd, hfnsd] at this)
          (fun ax hax => haxeval ax (hsub ax hax)) (hfnsd ▸ h)
      -- Every encoded axiom holds once the three symbols are declared, whether
      -- or not it stays in the context.
      have hcurrent {st' : TransState} {ρ' : _root_.Env}
          (hd : st'.decls = ((env.signature.addBinaryRel (SpecFn.rel rel.name)).addUnary
            (SpecFn.func rel.name)).addUnaryRel (SpecFn.defined rel.name))
          (hρ : ρ' = SpecFn.Env.both ρ rel.name R D F) :
          ∀ ax ∈ info.axs, ax.formula.wfIn st'.decls ∧ ax.formula.eval ρ' := by
        intro ax hax
        refine ⟨?_, hρ ▸ haxeval ax hax⟩
        rw [hd, ← hΔsd, ← hfnsd]
        exact Skolemize.encode_wfIn hlawsd hinfoEq (hΔsd ▸ hΔwf_acc)
          (hΓsd ▸ hΔsd ▸ hΓwf_acc) hsdFresh ax hax
      -- Either form declares a sublist of the encoded axioms. A measure then
      -- adds the totality assertion, which touches no field the invariant reads.
      have hrun : ∃ axs, (∀ ax ∈ axs, ax ∈ info.axs) ∧
          SeqM.eval (SpecFn.declare info.sd.fn axs) st ρ
            (fun _ st' ρ' =>
              st'.decls = ((env.signature.addBinaryRel (SpecFn.rel rel.name)).addUnary
                (SpecFn.func rel.name)).addUnaryRel (SpecFn.defined rel.name) →
              ρ' = SpecFn.Env.both ρ rel.name R D F →
              ∃ st'', st''.decls = st'.decls ∧ st''.owns = st'.owns ∧
                Q info.env st'' ρ') := by
        have h := SeqM.eval_bind heval
        cases hm : d.decreases with
        | none =>
          simp only [RelationDecl.declare, hm] at h
          exact ⟨_, Skolemize.encode_persistent hinfoEq,
            SeqM.eval_mono h fun _ st' _ hQ _ _ => ⟨st', rfl, rfl, SeqM.eval_ret hQ⟩⟩
        | some m =>
          simp only [RelationDecl.declare, hm] at h
          refine ⟨_, Skolemize.encode_persistent hinfoEq, SeqM.eval_mono (SeqM.eval_bind h) ?_⟩
          intro _ st' ρ' hc hd' hρ'
          have hclose : ∀ v, info.bv.defined.eval (ρ'.updateConst .value info.sd.x v) →
              (info.sd.fn.isDefined (.var .value info.sd.x)).eval
                (ρ'.updateConst .value info.sd.x v) := by
            rw [hρ']; exact Skolemize.encode_closed hinfoEq haxeval
          obtain ⟨hproof, hcont⟩ := SeqM.eval_check (SeqM.eval_bind hc)
          have hlocal := fun ax (hax : ax ∈ Skolemize.SpecFn.Axioms.withheld
              rel.transparency info.sd.fn info.sd.x info.bv) =>
            hcurrent hd' hρ' ax (Skolemize.encode_withheld hinfoEq ax hax)
          obtain ⟨st₀, hd₀, _, _, hcheck⟩ := VerifM.eval_assumeAxioms
            (VerifM.eval_bind hproof) (fun ax hax => (hlocal ax hax).1)
            (fun ax hax => (hlocal ax hax).2)
          obtain ⟨hwt, ht, _⟩ := Termination.check_correct hclose hcheck
          exact ⟨{ st' with asserts := Termination.total info.sd.fn info.sd.x :: st'.asserts },
            rfl, rfl, SeqM.eval_ret (SeqM.eval_assume hcont (hd₀ ▸ hwt) ht)⟩
      obtain ⟨axs, hsub, hrun⟩ := hrun
      obtain ⟨st4, ρ4, hρ4, hst4_decls, howns4, hvars4, hwf4, hsub4, hagree4,
        hΓwf4, hΓagree4, hcont⟩ := hdecl axs hsub hrun
      obtain ⟨st5, hst5_decls, howns5, hQ5⟩ := hcont hst4_decls hρ4
      refine ⟨info.env, st5, ρ4, ⟨hspec_reg.trans hreg, hspec_types.trans htypes, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hagree4,
        hQ5⟩
      · rw [hspec_delta, hst5_decls, hst4_decls]
      · rw [howns5, howns4]
      · rw [hst5_decls]; exact hvars4
      · rw [hst5_decls]; exact hwf4
      · rw [hspec_fm, hst5_decls]; exact hΓwf4
      · rw [hspec_fm]; exact hΓagree4
      · rw [hst5_decls]
        intro l hl
        rcases hspec_lemmas l hl with hl' | hfact
        · exact (hu l hl').mono hsub4 hagree4 hwf4
        · simp only [Lemma.Sound, hfact]
          exact hcurrent hst4_decls hρ4 _ (Skolemize.encode_equation hinfoEq)
      · rw [hst5_decls]; exact hsub4

end Verifier.Env

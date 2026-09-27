-- SUMMARY: One declaration at a time: elaborate it, declare the spec functions it defines, check it, and bind what it defines for the declarations after it.
import Mica.SourceTinyML.Typing
import Mica.SourceTinyML.Erasure
import Mica.Verifier.PrimitiveLaws
import Mica.Verifier.RelationalEncoding
import Mica.Verifier.Intrinsic
import Mica.Verifier.BoundedQuantifier
import Mica.Verifier.Expressions
import Mica.Verifier.Ghost

/-!
# Declarations

The verifier handles a program one declaration at a time. `Decl.declare`
elaborates a declaration against the environment of the declarations before it,
and declares the spec functions it defines and the bounded quantifiers its
specifications lift. `Decl.check` checks the typed declaration in the scope of
the values before it, and binds what it defines. `Decl.declareAndCheck` does
both.

Each declaration extends the world: it adds type declarations and spec symbols.
The scope carries over (`Scope.supportedBy_mono`): its types are well formed in
the world it was built in, so they mean the same in the larger one
(`ValHasType.agreeOn`).
-/

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Verifier.RelationalEncoding (FunCtx PrimEncodings encode)
open Verifier.RelationalEncoding.Skolemize (DefVal)

/-! ## Spec functions -/

/-- Encode one typechecked specification leaf into its value term and definedness
condition. The encoder environment is the identity over the spec-level names in
scope: `δ` carries real terms only *inside* a leaf — for let-expressions and
match payloads — so the names alone determine it. -/
private def translateLeaf (primitives : PrimEncodings) (Δ : Signature)
    (Γfn : FunCtx) (names : List String)
    (e : Typed.Expr) : Except String (Term .value × Formula) := do
  let c ← encode primitives Δ Γfn (names.map (fun n => (n, .var .value n))) e
    (Δ.allNames ++ names)
  let dv := Verifier.RelationalEncoding.Expr.toDefVal .id c
  .ok (dv.value, dv.defined)

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

private def declareAndAssume (env : Env) (d : Typed.ValDecl) : SeqM Env := do
  match d.relation with
  | none => pure env
  | some r =>
      match extend env d with
      | .error msg => SeqM.fatal msg
      | .ok info => do
          info.declare r.transparency d.decreases
          pure info.env

/-- Declare a bounded quantifier's solver-facing triple and its defining
axioms. All freshness and membership conditions needed by the soundness proof
are checked operationally by `validate`. -/
private def declareLifting (env : Env) (s : Verifier.BoundedQuantifier.Lifting) : SeqM Env :=
  match s.validate env.signature with
  | .error msg => SeqM.fatal msg
  | .ok _ =>
      match s.compile env.registry.primitives env.specFunctions env.signature with
      | .error msg => SeqM.fatal msg
      | .ok body => do
          s.declare body
          pure { env with
                 specFunctions := env.specFunctions ++ [(s.name, s.name)],
                 signature := s.extendSignature env.signature }

/-- Compile and declare the lifted bounded quantifiers in lift order. Earlier
symbols are available while compiling later bodies, which supports nesting. -/
private def declareLiftings : Env → List Verifier.BoundedQuantifier.Lifting → SeqM Env
  | env, [] => pure env
  | env, s :: ss => do
      let env' ← declareLifting env s
      declareLiftings env' ss

/-- The invariant threaded through the declaration of spec functions: the signature mirrors the declared
one, the state is spec-level (no owned locations, no variables), and the spec
functions are well-formed and interpreted in agreement with their func-form
reading. -/
private structure SpecInv (reg : Registry) (Θ : TinyML.TypeEnv) (env : Env) (st : TransState)
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

omit [MicaGS HasLC.hasLC Sig] in
/-- Declaring one relation-marked declaration preserves `SpecInv`; the signature
only grows and the environment is only extended with fresh interpretations. -/
private theorem declareAndAssume_correct {reg : Registry} {Θ : TinyML.TypeEnv}
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

omit [MicaGS HasLC.hasLC Sig] in
/-- Compiling and declaring one lifted bounded quantifier preserves `SpecInv`. -/
private theorem declareLifting_correct {reg : Registry} {Θ : TinyML.TypeEnv}
    (hlaw : reg.primitives.Lawful) (s : Verifier.BoundedQuantifier.Lifting)
    (env : Env) (st : TransState) (ρ : _root_.Env)
    {Q : Env → TransState → _root_.Env → Prop}
    (hinv : SpecInv reg Θ env st ρ)
    (heval : SeqM.eval (declareLifting env s) st ρ Q) :
    ∃ env' st' ρ', SpecInv reg Θ env' st' ρ' ∧
      st.decls.Subset st'.decls ∧ Env.agreeOn st.decls ρ ρ' ∧
      Q env' st' ρ' := by
  obtain ⟨hreg, htypes, hacc, howns, hvars, hwf, hΓwf, hΓagree, hu⟩ := hinv
  simp only [declareLifting] at heval
  cases hvalid : s.validate env.signature with
  | error msg =>
    simp only [hvalid] at heval
    exact (SeqM.eval_fatal heval).elim
  | ok v =>
    simp only [hvalid] at heval
    cases hcompile : s.compile env.registry.primitives env.specFunctions env.signature with
    | error msg =>
      simp only [hcompile] at heval
      exact (SeqM.eval_fatal heval).elim
    | ok body =>
      simp only [hcompile] at heval
      have hbody := Verifier.BoundedQuantifier.Lifting.compile_wfIn (hreg ▸ hlaw)
        v.down (hacc ▸ hwf) (hacc ▸ hΓwf) hcompile
      obtain ⟨st4, ρ4, hdelta, howns4, hvars4, hwf4, hsub4, hagree4,
        hΓwf4, hΓagree4, hcont⟩ :=
        Verifier.BoundedQuantifier.Lifting.declare_correct s body env.signature
          env.specFunctions st ρ v.down hbody hacc.symm howns hvars
          (hacc ▸ hwf) (hacc ▸ hΓwf) hΓagree (SeqM.eval_bind heval)
      exact ⟨{ env with
               specFunctions := env.specFunctions ++ [(s.name, s.name)],
               signature := s.extendSignature env.signature }, st4, ρ4,
        ⟨hreg, htypes, hdelta.symm, howns4, hvars4, hwf4, hΓwf4, hΓagree4, hu.mono hsub4 hagree4 hwf4⟩,
        hsub4, hagree4, SeqM.eval_ret hcont⟩

omit [MicaGS HasLC.hasLC Sig] in
private theorem declareLiftings_correct {reg : Registry} {Θ : TinyML.TypeEnv}
    (hlaw : reg.primitives.Lawful) (ss : List Verifier.BoundedQuantifier.Lifting) :
    ∀ (env : Env) (st : TransState) (ρ : _root_.Env)
      {Q : Env → TransState → _root_.Env → Prop},
      SpecInv reg Θ env st ρ →
      SeqM.eval (declareLiftings env ss) st ρ Q →
      ∃ result stRel ρRel, SpecInv reg Θ result stRel ρRel ∧
        st.decls.Subset stRel.decls ∧ Env.agreeOn st.decls ρ ρRel ∧
        Q result stRel ρRel := by
  induction ss with
  | nil =>
    intro env st ρ Q hinv heval
    simp only [declareLiftings] at heval
    exact ⟨env, st, ρ, hinv, Signature.Subset.refl _, Env.agreeOn_refl,
      SeqM.eval_ret heval⟩
  | cons s ss ih =>
    intro env st ρ Q hinv heval
    simp only [declareLiftings] at heval
    obtain ⟨env1, st1, ρ1, hinv1, hsub1, hag1, hcont1⟩ :=
      declareLifting_correct hlaw s env st ρ hinv (SeqM.eval_bind heval)
    obtain ⟨result, stRel, ρRel, hinvRel, hsubRel, hagRel, hQ⟩ :=
      ih env1 st1 ρ1 hinv1 hcont1
    exact ⟨result, stRel, ρRel, hinvRel, hsub1.trans hsubRel,
      Env.agreeOn_trans hag1 (Env.agreeOn_mono hsub1 hagRel), hQ⟩

end Verifier.Env

namespace Verifier

open Typed (SpecEnv)

/-! ## Elaboration -/

/-- The environment elaboration resolves specifications against: the registry's
primitives, and leaf translation through bounded-quantifier lifting followed by
the relational FOL encoding. Lifting a leaf turns its quantifier occurrences
into calls of the lifted symbols, so the rewritten leaf resolves against the
spec functions extended by every lifting so far. `own` are the spec functions
the declaration itself defines, which its specification may call. -/
def Env.specEnv (env : Env) (own : FunCtx) : SpecEnv BoundedQuantifier.LiftState where
  primitive := env.registry.sigs
  -- `Typed.Decl.elaborate` sets the globals and the type variables.
  globals := TinyML.TyCtx.empty
  translate names e := fun st =>
    match BoundedQuantifier.rewriteLeaf e st with
    | .error msg => .error (.spec msg)
    | .ok (e', st') =>
      let Γ := env.specFunctions ++ own ++ st'.syms.map (fun s => (s.name, s.name))
      match translateLeaf env.registry.primitives (Intrinsic.sigOf env.registry) Γ names e' with
      | .error msg => .error (.spec msg)
      | .ok r => .ok (r, st')
  tvars := []

/-- The spec function a `[@@fn]` declaration defines. `Env.declareAndAssume`
re-derives it from the typed declaration and validates it, so nothing here is
trusted. -/
private def ownSpecFunctions : Untyped.Decl Untyped.SpecBody → FunCtx
  | .val_ d =>
    match d.name, d.relation with
    | .named f _, some rel => [(f, rel.name)]
    | _, _ => []
  | .type_ _ => []

/-- The payloads of the type `d` declares are well formed. -/
private def checkTypeDeclaration (Δ : Signature) (Θ : TinyML.TypeEnv) :
    Untyped.Decl Untyped.SpecBody → Except String Unit
  | .type_ dty =>
    match Θ dty.name with
    | some d => TinyML.Typ.checkWfList Δ Θ d.payloads
    | none => .ok ()
  | .val_ _ => .ok ()

/-- Elaborate `d` against `env`, and declare the spec functions it defines and
the bounded quantifiers its specifications lift. The spec functions come first,
because a lifted body may call them. -/
def Decl.declare (env : Env) (d : Untyped.Decl Untyped.SpecBody) :
    SeqM (Env × Option Typed.ValDecl) := do
  match Typed.Decl.elaborate (env.specEnv (ownSpecFunctions d)) env.typeDeclarations env.globals d
      { syms := env.liftings } with
  | .error err => SeqM.fatal (toString err)
  | .ok ((Θ, Γ, d'), lifted) => do
    SeqM.ofExcept (checkTypeDeclaration env.signature Θ d)
    let env' := { env with typeDeclarations := Θ, globals := Γ }
    let env' ← match d' with
      | some d' => env'.declareAndAssume d'
      | none => pure env'
    let env' ← env'.declareLiftings (lifted.syms.drop env.liftings.length)
    pure ({ env' with liftings := lifted.syms }, d')

/-! ## Checking -/

/-- Compile the body of `d` for safety. -/
def ValDecl.checkBody (env : Env) (S : Scope) (d : Typed.ValDecl) : VerifM Unit := do
  let _ ← compile env S d.body
  pure ()

/-- Check a typed declaration in the scope `S` of the values before it, and bind
what it defines. A specified function gets a constant, so the declarations after
it can use its name as a value. -/
def Decl.check (env : Env) (S : Scope) (d : Typed.ValDecl) : SeqM (Env × Scope) := do
  -- The entries are added after the handling below, because that handling
  -- drops the name from the ghost table when it binds a run-time value of it.
  let fn ← ValDecl.ghostEntries env S.ghostFns d
  match d.mode with
  | .ghost =>
    -- A ghost declaration binds no run-time value: it only becomes callable
    -- from the ghost code of the declarations that follow it.
    let entry ← ValDecl.checkGhost env S.ghostFns d
    pure (env, { S with ghostFns := fn ++ entry :: S.ghostFns,
                        runtimeBindings := S.runtimeBindings.remove entry.1 })
  | .runtime =>
    match d.name.name, d.body.spec? with
    | none, _ =>
      SeqM.check (ValDecl.checkBody env S d)
      pure (env, { S with ghostFns := fn ++ S.ghostFns })
    | some n, none => do
      -- A function definition runs no code. The new binding shadows any
      -- earlier one of the same name, which is therefore dropped: nothing here
      -- gives the new value a specification.
      if !d.body.isFunc then SeqM.check (ValDecl.checkBody env S d)
      pure (env, { S with ghostFns := fn ++ S.ghostFns.remove n,
                          runtimeBindings := S.runtimeBindings.remove n })
    | some n, some _ => do
      -- The value is a specified function: bind the name at the arrow it was
      -- verified at. The arrow's type variables are generalized, the
      -- verification having gone through at every assignment of them.
      SeqM.check (ValDecl.checkBody env S d)
      SeqM.ofExcept (TinyML.Typ.checkWf env.signature env.typeDeclarations d.body.ty)
      let fv : Decl.Const := ⟨Fresh.freshNumbers n env.signature.allNames, .value⟩
      SeqM.declConst fv
      pure ({ env with signature := env.signature.addConst fv },
            { S with ghostFns := fn ++ S.ghostFns.remove n,
                     runtimeBindings := (n, fv) :: S.runtimeBindings,
                     typingContext := S.typingContext.extendScheme n
                       (TinyML.Scheme.gen d.body.ty) })

/-- Elaborate and declare `d`, then check it. -/
def Decl.declareAndCheck (env : Env) (S : Scope) (d : Untyped.Decl Untyped.SpecBody) :
    SeqM (Env × Scope) := do
  let (env', d') ← Decl.declare env d
  match d' with
  | some d' => Decl.check env' S d'
  | none => pure (env', S)

end Verifier

namespace Verifier

variable {env env' : Env} {S : Scope} {st st' : TransState} {ρ ρ' : _root_.Env}
  {γ : Runtime.Subst}

/-! ## Declaring -/

omit [MicaGS HasLC.hasLC Sig] in
private theorem checkTypeDeclaration_ok {Δ : Signature} {Θ : TinyML.TypeEnv}
    {dty : Untyped.TypeDecl} (h : checkTypeDeclaration Δ Θ (.type_ dty) = .ok ()) :
    ∀ dd, Θ dty.name = some dd → ∀ p ∈ dd.payloads, TinyML.Typ.wfIn Δ Θ p := by
  intro dd hT
  simp only [checkTypeDeclaration, hT] at h
  exact TinyML.Typ.checkWfList_ok _ h

theorem Decl.declare_correct {d : Untyped.Decl Untyped.SpecBody}
    {Q : Env × Option Typed.ValDecl → TransState → _root_.Env → Prop}
    (henv : env.supportedBy st ρ) (hS : S.supportedBy env st ρ γ)
    (howns : st.owns = []) (hvars : st.decls.vars = [])
    (heval : SeqM.eval (Decl.declare env d) st ρ Q) :
    ∃ env' d' st' ρ', env'.supportedBy st' ρ' ∧ S.supportedBy env' st' ρ' γ ∧
      st'.owns = [] ∧ st'.decls.vars = [] ∧ env'.registry = env.registry ∧ (env.world ρ).Subset (env'.world ρ') ∧
      d'.bind Typed.ValDecl.runtime? = d.runtime ∧ Q (env', d') st' ρ' := by
  have hst := SeqM.eval_wf heval
  cases helab : Typed.Decl.elaborate (env.specEnv (ownSpecFunctions d)) env.typeDeclarations
      env.globals d { syms := env.liftings } with
  | error err =>
    simp only [Decl.declare, helab] at heval
    exact (SeqM.eval_fatal heval).elim
  | ok r =>
    obtain ⟨⟨Θ, Γ, d'⟩, lifted⟩ := r
    simp only [Decl.declare, helab] at heval
    obtain ⟨hΘext, hΘsame⟩ := Typed.Decl.elaborate_types helab
    have hrt := Typed.Decl.elaborate_runtime _ _ _ d helab
    -- The type declaration's own payloads are checked; the others were before.
    obtain ⟨u, hcheck, h2⟩ := SeqM.eval_ofExcept (SeqM.eval_bind heval)
    cases u
    have htypes : TinyML.TypeEnv.wfIn st.decls Θ := by
      intro T dd hT p hp
      by_cases hnew : ∃ dty, d = .type_ dty ∧ T = dty.name
      · obtain ⟨dty, rfl, rfl⟩ := hnew
        have := checkTypeDeclaration_ok hcheck dd hT p hp
        rwa [henv.signature] at this
      · have hold : Θ T = env.typeDeclarations T :=
          hΘsame T fun dty hd hT' => hnew ⟨dty, hd, hT'⟩
        rw [hold] at hT
        exact TinyML.Typ.wfIn_mono (Signature.Subset.refl _) hst.namesDisjoint hΘext
          (henv.types T dd hT p hp)
    have hlaw := Registry.primitives_lawful henv.sound
    have hinv0 : Env.SpecInv env.registry Θ { env with typeDeclarations := Θ, globals := Γ } st ρ :=
      ⟨rfl, rfl, henv.signature, howns, hvars, hst.namesDisjoint, henv.specFunctionsWf,
        henv.specFunctionsAgree, henv.lemmas⟩
    obtain ⟨env1, st1, ρ1, hinv1, hsub1, hag1, h4⟩ : ∃ env1 st1 ρ1,
        Env.SpecInv env.registry Θ env1 st1 ρ1 ∧ st.decls.Subset st1.decls ∧
        Env.agreeOn st.decls ρ ρ1 ∧
        SeqM.eval (do
          let env' ← env1.declareLiftings (lifted.syms.drop env.liftings.length)
          pure ({ env' with liftings := lifted.syms }, d')) st1 ρ1 Q := by
      cases d' with
      | none => exact ⟨_, st, ρ, hinv0, Signature.Subset.refl _, Env.agreeOn_refl, h2⟩
      | some dd => exact Env.declareAndAssume_correct hlaw dd _ st ρ hinv0 (SeqM.eval_bind h2)
    obtain ⟨env2, st2, ρ2, hinv2, hsub2, hag2, h5⟩ :=
      Env.declareLiftings_correct hlaw _ env1 st1 ρ1 hinv1 (SeqM.eval_bind h4)
    have hsub := hsub1.trans hsub2
    have hag := Env.agreeOn_trans hag1 (Env.agreeOn_mono hsub1 hag2)
    have hreg : env2.registry = env.registry := hinv2.registry
    have hΘ2 : env2.typeDeclarations = Θ := hinv2.types
    have hW : (env.world ρ).Subset ({ env2 with liftings := lifted.syms }.world ρ2) :=
      ⟨by simp [Env.world, hreg], rfl, fun T dd hT => by simpa [Env.world, hΘ2] using hΘext T dd hT,
        by simpa [Env.world, henv.signature, hinv2.signature] using hsub,
        by simpa [Env.world, henv.signature] using hag⟩
    refine ⟨{ env2 with liftings := lifted.syms }, d', st2, ρ2, ?_, ?_, hinv2.owns, hinv2.vars,
      hreg, hW, hrt,
      SeqM.eval_ret h5⟩
    · exact
        { sound := hreg ▸ henv.sound
          signature := hinv2.signature
          specFunctionsWf := hinv2.Γwf
          specFunctionsAgree := hinv2.Γagree
          lemmas := hinv2.lemmas
          symbols := hreg ▸ Registry.symSubset_mono henv.symbols hsub
          interpretations := hreg ▸ Registry.symAgree_agreeOn henv.interpretations henv.symbols hag
          types := by
            rw [show ({ env2 with liftings := lifted.syms } : Env).typeDeclarations = Θ from hΘ2]
            intro T dd hT p hp
            exact TinyML.Typ.wfIn_mono hsub hinv2.wf (fun _ _ h => h) (htypes T dd hT p hp) }
    · exact Scope.supportedBy_mono hS henv hinv2.wf hsub hag
        (fun T dd hT => by simpa [hΘ2] using hΘext T dd hT) hW

/-! ## Checking -/

/-- The body runs safely, and a frame `Φ` survives it. -/
theorem ValDecl.checkBody_correct (env : Env) (W : TinyML.World) (henv : env.wf W)
    (Gf : GhostFns) (B : Bindings) (Γ : TinyML.TyCtx) (d : Typed.ValDecl) (γ : Runtime.Subst)
    (st : TransState) (ρ : _root_.Env)
    (hS : (⟨Gf, Bindings.empty, B, Γ⟩ : Scope).wfIn W st.decls ρ Runtime.Subst.id γ)
    {Q : Unit → TransState → _root_.Env → Prop}
    (heval : VerifM.eval (ValDecl.checkBody env ⟨Gf, Bindings.empty, B, Γ⟩ d) st ρ Q) (Φ : iProp) :
    □ st.sl W ρ ∗ Bindings.typedSubst W B Γ γ ∗ Φ ⊢
      wp W.pctx (d.body.runtime.subst γ) (fun _ => Φ) := by
  simp only [ValDecl.checkBody] at heval
  have hcomp := compile_correct d.body env W _ _ _ (R := iprop(□ st.sl W ρ ∗ Φ))
    (Φ := fun _ => Φ) henv hS (VerifM.eval_bind heval)
    (fun _ _ _ _ _ _ _ => by
      istart
      iintro ⟨_, _, Hctx⟩
      icases Hctx with ⟨_, HΦ⟩
      iexact HΦ)
  refine (BIBase.Entails.trans ?_ hcomp)
  istart
  iintro ⟨#Hsl, #HT, HΦ⟩
  isplitl []
  · iexact Hsl
  · isplitl []
    · iapply Scope.typed_runtimeBindings
      iexact HT
    · isplitl []
      · iexact Hsl
      · iexact HΦ

/-- A specified function's value is typed at the arrow it was verified at.
    Stated without a `wp` for the same reason as `compileFix_typed`: the caller
    needs it once per assignment. -/
theorem ValDecl.checkBody_typed (env : Env) (W : TinyML.World) (henv : env.wf W)
    (Gf : GhostFns) (B : Bindings) (Γ : TinyML.TyCtx) (d : Typed.ValDecl) (γ : Runtime.Subst)
    (self : Typed.Binder) (args : List Typed.Binder) (retTy : TinyML.Typ)
    (s : Spec TinyML.Typ) (body : Typed.Expr)
    (hbody : d.body = .fix self args retTy (some s) body)
    (st : TransState) (ρ : _root_.Env)
    (hS : (⟨Gf, Bindings.empty, B, Γ⟩ : Scope).wfIn W st.decls ρ Runtime.Subst.id γ)
    {Q : Unit → TransState → _root_.Env → Prop}
    (heval : VerifM.eval (ValDecl.checkBody env ⟨Gf, Bindings.empty, B, Γ⟩ d) st ρ Q) :
    Bindings.typedSubst W B Γ γ ⊢
      TinyML.ValHasType W
        (Runtime.Val.fix self.runtime (args.map (·.runtime))
          (body.runtime.subst ((γ.remove' self.runtime).removeAll' (args.map (·.runtime)))))
        d.body.ty := by
  simp only [ValDecl.checkBody] at heval
  have hty : d.body.ty = .arrow (args.map Typed.Binder.WithTypeVars.ty) retTy (some s) := by
    rw [hbody]; simp [Typed.Expr.WithTypeVars.ty]
  rw [hty]
  have hc := VerifM.eval_bind heval
  rw [hbody] at hc
  exact Scope.typed_runtimeBindings.trans
    (compileFix_typed env W henv _ Runtime.Subst.id γ self args retTy s body
      (compile_correct body) hS hc)

theorem Decl.check_correct {d : Typed.ValDecl} {Q : Env × Scope → TransState → _root_.Env → Prop}
    (henv : env.supportedBy st ρ) (hS : S.supportedBy env st ρ γ) (hG : S.ghostBindings = [])
    (howns : st.owns = []) (hvars : st.decls.vars = [])
    (heval : SeqM.eval (Decl.check env S d) st ρ Q) (P : Runtime.Program)
    (hk : ∀ env' S' st' ρ' γ', env'.supportedBy st' ρ' → S'.supportedBy env' st' ρ' γ' →
      S'.ghostBindings = [] → st'.owns = [] → st'.decls.vars = [] →
      env'.registry = env.registry → Q (env', S') st' ρ' →
      S'.runtimeBindings.schemeSubst (env'.world ρ') S'.typingContext γ' ⊢
        pwp env.registry.primCtx (P.subst γ')) :
    S.runtimeBindings.schemeSubst (env.world ρ) S.typingContext γ ⊢
      pwp env.registry.primCtx (Runtime.Program.subst (d.runtime?.toList ++ P) γ) := by
  obtain ⟨Gf, G, B, Γ⟩ := S
  obtain rfl : G = [] := hG
  have hst := SeqM.eval_wf heval
  have hW := Env.wf_of_supportedBy henv hst hvars
  have hag := Env.agrees_of_supportedBy henv
  have hSwf := Scope.wfIn_of_supportedBy henv hS rfl Runtime.Subst.id
  have hsig : env.signature = st.decls := henv.signature
  simp only [Decl.check] at heval
  obtain ⟨fn, hfnwf, hfn, heval⟩ :=
    ValDecl.ghostEntries_correct env _ hW Gf d hag hS.ghostFns (SeqM.eval_bind heval)
  replace hfnwf : fn.wfIn st.decls env.typeDeclarations :=
    hsig ▸ (hfnwf : fn.wfIn env.signature env.typeDeclarations)
  have hsl : ⊢ □ st.sl (env.world ρ) ρ := TransState.sl_of_owns_nil howns
  cases hmode : d.mode with
  | ghost =>
    simp only [hmode] at heval
    obtain ⟨entry, hentrywf, hentry, heval⟩ :=
      ValDecl.checkGhost_correct env _ hW Gf d hag hS.ghostFns (SeqM.eval_bind heval)
    replace hentrywf : GhostFns.wfIn st.decls env.typeDeclarations [entry] :=
      hsig ▸ (hentrywf : GhostFns.wfIn env.signature env.typeDeclarations [entry])
    have hk' := hk env ⟨fn ++ entry :: Gf, [], B.remove entry.1, Γ⟩ st ρ γ henv
      { closed := hS.closed
        types := hS.types
        ghostFnsWf := GhostFns.wfIn_append hfnwf (GhostFns.wfIn_append hentrywf hS.ghostFnsWf)
        ghostFns := hfn.append (hentry.append hS.ghostFns)
        runtimeLinked := Bindings.agreeOnLinked_remove hS.runtimeLinked entry.1
        runtimeDeclared := Bindings.wfIn_remove hS.runtimeDeclared entry.1 }
      rfl howns hvars rfl (SeqM.eval_ret heval)
    simpa [Typed.ValDecl.runtime?, hmode] using Bindings.schemeSubst_remove.trans hk'
  | runtime =>
    have hunfold :
        wp (env.world ρ).pctx (d.body.runtime.subst γ) (fun v =>
          pwp env.registry.primCtx
            (P.subst (Runtime.Subst.updateBinder d.name.runtime v γ)))
        ⊢ pwp env.registry.primCtx (Runtime.Program.subst (d.runtime?.toList ++ P) γ) := by
      simp only [Typed.ValDecl.runtime?, hmode, Typed.ValDecl.runtime, Option.toList_some,
        List.singleton_append, Runtime.Program.subst, Runtime.Decl.subst]
      refine BIBase.Entails.trans (wp.mono fun v => ?_) pwp_cons
      rw [Runtime.Program.subst_remove_update]
      exact .rfl
    refine BIBase.Entails.trans ?_ hunfold
    simp only [hmode] at heval
    cases hname : d.name.name with
    | none =>
      simp only [hname] at heval
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ := by
        intro v; simp [Typed.Binder.runtime_of_name_none hname, Runtime.Subst.updateBinder]
      obtain ⟨hchk, heval⟩ := SeqM.eval_check (SeqM.eval_bind heval)
      have hk' := hk env ⟨fn ++ Gf, [], B, Γ⟩ st ρ γ henv
        { closed := hS.closed
          types := hS.types
          ghostFnsWf := GhostFns.wfIn_append hfnwf hS.ghostFnsWf
          ghostFns := hfn.append hS.ghostFns
          runtimeLinked := hS.runtimeLinked
          runtimeDeclared := hS.runtimeDeclared }
        rfl howns hvars rfl (SeqM.eval_ret heval)
      have hwp := ValDecl.checkBody_correct env _ hW Gf B Γ d γ st ρ hSwf hchk
        (pwp env.registry.primCtx (P.subst γ))
      simp only [hupd]
      refine BIBase.Entails.trans ?_ hwp
      istart
      iintro #H
      isplitl []
      · iapply hsl
      · isplitl []
        · iapply Bindings.typedSubst_of_schemeSubst
          iexact H
        · iapply hk'
          iexact H
    | some n =>
      have hname_rt : d.name.runtime = .named n := Typed.Binder.runtime_of_name_some hname
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ.update n v := by
        intro v; simp [hname_rt, Runtime.Subst.updateBinder]
      simp only [hupd]
      cases hspec : d.body.spec? with
      | none =>
        simp only [hname, hspec] at heval
        have hS' : ∀ v, Scope.supportedBy ⟨fn ++ Gf.remove n, [], B.remove n, Γ⟩
            env st ρ (γ.update n v) := fun v =>
          { closed := hS.closed
            types := hS.types
            ghostFnsWf := GhostFns.wfIn_append hfnwf (GhostFns.wfIn_remove hS.ghostFnsWf n)
            ghostFns := hfn.append (hS.ghostFns.remove n)
            runtimeLinked := Bindings.agreeOnLinked_remove_update hS.runtimeLinked n v
            runtimeDeclared := Bindings.wfIn_remove hS.runtimeDeclared n }
        by_cases hf : d.body.isFunc
        · rw [if_neg (by simp [hf])] at heval
          have hQ := SeqM.eval_ret (SeqM.eval_ret (SeqM.eval_bind heval))
          obtain ⟨self, args, retTy, spec, body, hbody⟩ := Typed.Expr.isFunc_elim hf
          have hbody_rt : d.body.runtime.subst γ =
              Runtime.Expr.fix self.runtime (args.map (·.runtime))
                (body.runtime.subst ((γ.remove' self.runtime).removeAll'
                  (args.map (·.runtime)))) := by
            rw [hbody]; conv_lhs => unfold Typed.Expr.WithTypeVars.runtime
            simp only [Runtime.Expr.subst_fix]
          rw [hbody_rt]
          apply SpatialContext.wp_func
          exact Bindings.schemeSubst_remove_update.trans
            (hk env ⟨fn ++ Gf.remove n, [], B.remove n, Γ⟩ st ρ _ henv (hS' _) rfl howns hvars rfl hQ)
        · rw [if_pos (by simpa using hf)] at heval
          obtain ⟨hchk, heval⟩ := SeqM.eval_check (SeqM.eval_bind heval)
          have hwp := ValDecl.checkBody_correct env _ hW Gf B Γ d γ st ρ hSwf hchk iprop(emp)
          refine SpatialContext.wp_strengthen_persistent (P := fun _ => iprop(emp)) (hwp := ?_)
            (hpost := fun v => ?_)
          · istart
            iintro #H
            iapply hwp
            isplitl []
            · iapply hsl
            · isplitl []
              · iapply Bindings.typedSubst_of_schemeSubst
                iexact H
              · iempintro
          · exact wand_intro (sep_elim_left.trans (Bindings.schemeSubst_remove_update.trans
              (hk env ⟨fn ++ Gf.remove n, [], B.remove n, Γ⟩ st ρ (γ.update n v) henv (hS' v)
                rfl howns hvars rfl (SeqM.eval_ret heval))))
      | some sp =>
        simp only [hname, hspec] at heval
        obtain ⟨self, args, retTy, body, hbody⟩ := Typed.Expr.spec?_elim hspec
        obtain ⟨hchk, heval⟩ := SeqM.eval_check (SeqM.eval_bind heval)
        obtain ⟨u, hwfty, heval⟩ := SeqM.eval_ofExcept (SeqM.eval_bind heval)
        obtain ⟨hfresh, heval⟩ := SeqM.eval_declConst (SeqM.eval_bind heval)
        set fv : Decl.Const := ⟨Fresh.freshNumbers n env.signature.allNames, .value⟩
        set v := Runtime.Val.fix self.runtime (args.map (·.runtime))
          (body.runtime.subst ((γ.remove' self.runtime).removeAll' (args.map (·.runtime))))
        set ρ₁ := ρ.updateConst .value fv.name v
        set st₁ : TransState := { st with decls := st.decls.addConst fv }
        set env₁ : Env := { env with signature := env.signature.addConst fv }
        have hwf₁ : st₁.decls.wf := Signature.wf_addConst hst.namesDisjoint hfresh
        have hsub₁ : st.decls.Subset st₁.decls := Signature.Subset.subset_addConst _ _
        have hag₁ : Env.agreeOn st.decls ρ ρ₁ := Env.agreeOn_update_fresh_const hfresh
        have hty : TinyML.Typ.wfIn st.decls env.typeDeclarations d.body.ty :=
          hsig ▸ TinyML.Typ.checkWf_ok _ hwfty
        have hW₁ : (env.world ρ).Subset (env₁.world ρ₁) :=
          ⟨rfl, rfl, fun _ _ h => h, by simpa [Env.world, env₁, hsig] using hsub₁,
            by simpa [Env.world, hsig] using hag₁⟩
        have henv₁ : env₁.supportedBy st₁ ρ₁ :=
          { sound := henv.sound
            signature := by simp [env₁, st₁, hsig]
            specFunctionsWf := FunCtx.wfIn_mono henv.specFunctionsWf hsub₁
            specFunctionsAgree := henv.specFunctionsAgree.updateConst _ _ _
            lemmas := henv.lemmas.mono hsub₁ hag₁ hwf₁
            symbols := Registry.symSubset_mono henv.symbols hsub₁
            interpretations := Registry.symAgree_agreeOn henv.interpretations henv.symbols hag₁
            types := fun T dd hT p hp =>
              TinyML.Typ.wfIn_mono hsub₁ hwf₁ (fun _ _ h => h) (henv.types T dd hT p hp) }
        have hfnwf' := GhostFns.wfIn_append hfnwf (GhostFns.wfIn_remove hS.ghostFnsWf n)
        have hS₁ : Scope.supportedBy ⟨fn ++ Gf.remove n, [], (n, fv) :: B,
            Γ.extendScheme n (TinyML.Scheme.gen d.body.ty)⟩ env₁ st₁ ρ₁ (γ.update n v) :=
          { closed := hS.closed.extendScheme n (TinyML.Scheme.gen_free _)
            types := fun x s hx => by
              by_cases hxn : x = n
              · subst hxn
                simp [TinyML.TyCtx.extendScheme] at hx
                subst hx
                exact TinyML.Typ.wfIn_mono hsub₁ hwf₁ (fun _ _ h => h) hty
              · have hx' : Γ x = some s := by
                  simpa [TinyML.TyCtx.extendScheme, hxn] using hx
                exact TinyML.Typ.wfIn_mono hsub₁ hwf₁ (fun _ _ h => h) (hS.types x s hx')
            ghostFnsWf := GhostFns.wfIn_mono hfnwf' hsub₁ hwf₁ fun _ _ h => h
            ghostFns := GhostFns.wellTyped_of_subset hW₁ (Env.typesWf_of_supportedBy henv)
              (by simpa [Env.world, hsig] using hfnwf') (hfn.append (hS.ghostFns.remove n))
            runtimeLinked := Bindings.agreeOnLinked_cons_update
              (Bindings.agreeOnLinked_agreeOn hS.runtimeLinked hag₁ hS.runtimeDeclared) rfl
              (by simp [ρ₁, Env.updateConst])
            runtimeDeclared := Bindings.wfIn_cons hS.runtimeDeclared }
        have hk' := hk env₁ _ st₁ ρ₁ _ henv₁ hS₁ rfl howns hvars rfl (SeqM.eval_ret (heval v))
        -- The value has its scheme: the check went through at every assignment.
        have hval : Bindings.schemeSubst (env.world ρ) B Γ γ ⊢
            TinyML.ValHasScheme (env₁.world ρ₁) v (TinyML.Scheme.gen d.body.ty) := by
          unfold TinyML.ValHasScheme
          refine forall_intro fun η => ?_
          set η' := TinyML.SemTypeAssign.override (env.world ρ).eta
            (TinyML.Scheme.gen d.body.ty).tparams η
          have htyped := ValDecl.checkBody_typed env _ (hW.eta η') Gf B Γ d γ self args retTy sp
            body hbody st ρ (hSwf.eta η') hchk
          refine (Bindings.schemeSubst_eta hS.closed η').trans
            (Bindings.typedSubst_of_schemeSubst.trans (htyped.trans ?_))
          exact (TinyML.ValueRelation.agreeOn_iff (TinyML.ValHasType.agreeOn
            (TinyML.World.subset_refl _) (TinyML.World.subset_withEta hW₁ η')
            (Env.typesWf_of_supportedBy henv)) (by simpa [Env.world, hsig] using hty) v).1
        rw [Typed.Expr.runtime_subst_of_fix hbody]
        refine SpatialContext.wp_func ?_
        refine BIBase.Entails.trans ?_ hk'
        istart
        iintro #H
        iapply Bindings.schemeSubst_cons
        · iapply (Bindings.schemeSubst_of_subset hW₁ (Env.typesWf_of_supportedBy henv)
            (fun x s hx => by simpa [Env.world, hsig] using hS.types x s hx))
          iexact H
        · iapply hval
          iexact H

theorem Decl.declareAndCheck_correct {d : Untyped.Decl Untyped.SpecBody}
    {Q : Env × Scope → TransState → _root_.Env → Prop}
    (henv : env.supportedBy st ρ) (hS : S.supportedBy env st ρ γ) (hG : S.ghostBindings = [])
    (howns : st.owns = []) (hvars : st.decls.vars = [])
    (heval : SeqM.eval (Decl.declareAndCheck env S d) st ρ Q) (P : Runtime.Program)
    (hk : ∀ env' S' st' ρ' γ', env'.supportedBy st' ρ' → S'.supportedBy env' st' ρ' γ' →
      S'.ghostBindings = [] → st'.owns = [] → st'.decls.vars = [] →
      env'.registry = env.registry → Q (env', S') st' ρ' →
      S'.runtimeBindings.schemeSubst (env'.world ρ') S'.typingContext γ' ⊢
        pwp env.registry.primCtx (P.subst γ')) :
    S.runtimeBindings.schemeSubst (env.world ρ) S.typingContext γ ⊢
      pwp env.registry.primCtx (Runtime.Program.subst (d.runtime.toList ++ P) γ) := by
  simp only [Decl.declareAndCheck] at heval
  obtain ⟨env', d', st', ρ', henv', hS', howns', hvars', hreg, hW, hrt, heval⟩ :=
    Decl.declare_correct henv hS howns hvars (SeqM.eval_bind heval)
  refine (Bindings.schemeSubst_of_subset hW (Env.typesWf_of_supportedBy henv)
    (fun x s hx => by simpa [Env.world, henv.signature] using hS.types x s hx)).trans ?_
  rw [← hrt]
  cases d' with
  | none =>
    simpa using hk env' S st' ρ' γ henv' hS' hG howns' hvars' hreg (SeqM.eval_ret heval)
  | some dd =>
    have h := Decl.check_correct henv' hS' hG howns' hvars' heval P
      (fun env'' S'' st'' ρ'' γ'' h1 h2 hG'' ho hv h3 h4 =>
        hreg ▸ hk env'' S'' st'' ρ'' γ'' h1 h2 hG'' ho hv (h3.trans hreg) h4)
    rw [hreg] at h
    simpa using h

end Verifier

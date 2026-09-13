-- SUMMARY: End-to-end preparation and verification of programs, from typed elaboration to program-level soundness.
import Mica.SourceTinyML.Typed
import Mica.SourceTinyML.Untyped
import Mica.SourceTinyML.Typing
import Mica.SourceTinyML.Erasure
import Mica.Verifier.PrimitiveLaws
import Mica.SeparationLogic.Adequacy
import Mica.Verifier.RelationalEncoding
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Engine.Driver
import Mica.Verifier.Intrinsic
import Mica.Verifier.BoundedQuantifier
import Mica.Verifier.Expressions
import Mica.Verifier.Lemma

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Typed
open Verifier.RelationalEncoding (FunCtx PrimEncodings encode)
open Verifier.RelationalEncoding.Skolemize (DefVal)

/-! ## Program-level verification

Iterates over a list of declarations, verifying each one against its spec
and accumulating the spec map for use by subsequent declarations. -/

/-- The `[@@fn]` function map, read off the *untyped* program. Specification
leaves are translated during elaboration, so the map that resolves their calls
has to be available before elaboration starts; the declaration name and relation
name it needs are both untyped metadata. `RelationSpec.assemble` re-derives the
same map from the typed program and validates every entry, so nothing here is
trusted. -/
def Program.relationMap (prog : Untyped.Program Untyped.SpecBody) : FunCtx :=
  prog.filterMap fun
    | .val_ d =>
      match d.name, d.relation with
      | .named f _, some rel => some (f, rel.name)
      | _, _ => none
    | .type_ _ => none

/-- Encode one typechecked specification leaf into its value term and definedness
condition. The encoder environment is the identity over the spec-level names in
scope: `δ` carries real terms only *inside* a leaf — for let-expressions and
match payloads — so the names alone determine it. -/
private def Program.translateLeaf (primitives : PrimEncodings) (Δ : Signature)
    (Γfn : FunCtx) (names : List String)
    (e : Typed.Expr) : Except String (Term .value × Formula) := do
  let c ← encode primitives Δ Γfn (names.map (fun n => (n, .var .value n))) e
    (Δ.allNames ++ names)
  let dv := Verifier.RelationalEncoding.Expr.toDefVal .id c
  .ok (dv.value, dv.defined)

/-- The environment elaboration resolves specifications against: the registry's
primitives, and leaf translation through bounded-quantifier lifting followed by
the relational FOL encoding. The lifted symbols accumulate in the elaboration
state, and lifting a leaf turns its quantifier occurrences into calls of those
symbols, so encoding the rewritten leaf resolves against `Γfn` extended by every
lifting so far — the same list, in the same order, that `assembleLiftings`
appends to the function map. -/
def Program.specEnv (reg : Verifier.Registry) (Γfn : FunCtx) :
    Typed.SpecEnv Verifier.BoundedQuantifier.LiftState where
  primitive := reg.sigs
  -- No declaration is in scope yet; `Program.elaborate` sets the globals of
  -- each declaration as it reaches it.
  globals := TinyML.TyCtx.empty
  translate names e := fun st =>
    match Verifier.BoundedQuantifier.rewriteLeaf e st with
    | .error msg => .error (.spec msg)
    | .ok (e', st') =>
      let Γ := Γfn ++ st'.syms.map (fun s => (s.name, s.name))
      match Program.translateLeaf reg.primitives (Verifier.Intrinsic.sigOf reg) Γ names e' with
      | .error msg => .error (.spec msg)
      | .ok r => .ok (r, st')
  tvars := []

/-- Elaborate a program, returning the type environment, the typed program with
its specifications already translated, and the final elaboration state (which
carries the lifted bounded quantifiers). -/
def Program.prepare (env : Typed.SpecEnv σ) (s : σ)
    (prog : Untyped.Program Untyped.SpecBody) :
    VerifM (TinyML.TypeEnv × Typed.Program × σ) :=
  match Typed.Program.elaborate env TinyML.TypeEnv.empty TinyML.TyCtx.empty prog s with
  | .ok ((Θ, typed), s') => .ret (Θ, typed, s')
  | .error err => .fatal (toString err)

/-- Globally assembled metadata for declarations marked with `[@@fn]`. -/
structure RelationSpec where
  symbols : List FOL.BinaryRel
  /-- The facts opaque declarations withhold. -/
  lemmas : Lemmas
  functionMap : List (TinyML.Var × String)
  delta : Signature

namespace RelationSpec

open Verifier.RelationalEncoding

def empty : RelationSpec :=
  { symbols := [], lemmas := [], functionMap := [], delta := Signature.empty }

private structure RelationDecl where
  spec : RelationSpec
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

private def extend (primitives : PrimEncodings) (acc : RelationSpec) (d : Typed.ValDecl) :
    Except String RelationDecl := do
  match d.relation with
  | none => .error "internal error: expected relation declaration"
  | some r => do
      let rel := r.name
      let (f, arg, body) ← validateDecl d
      let relName := SpecFn.relName rel
      let funName := SpecFn.funcName rel
      let defName := SpecFn.defName rel
      if relName ∈ acc.delta.allNames then
        .error s!"derived relation name '{relName}' for [@@fn] conflicts with an existing symbol"
      else if funName ∈ acc.delta.allNames then
        .error s!"derived value-function name '{funName}' for [@@fn] conflicts with an existing symbol"
      else if defName ∈ acc.delta.allNames then
        .error s!"derived definedness name '{defName}' for [@@fn] conflicts with an existing symbol"
      else if arg ∈ acc.delta.allNames then
        .error s!"[@@fn] argument name '{arg}' conflicts with a global symbol"
      else if arg = relName then
        .error s!"[@@fn] argument name '{arg}' clashes with derived relation name"
      else if arg = funName then
        .error s!"[@@fn] argument name '{arg}' clashes with derived value-function name"
      else if arg = defName then
        .error s!"[@@fn] argument name '{arg}' clashes with derived definedness name"
      else
        let sd : SpecDef :=
          { primitives, Γ := acc.functionMap, Δ := acc.delta, f, fn := rel, x := arg, e := body }
        let (bv, axs) ← Skolemize.encode sd
        let lemmas := match r.transparency with
          | .transparent => acc.lemmas
          | .opaque => acc.lemmas ++
              [{ kind := .definingEquation f,
                 fact := Skolemize.SpecFn.Axioms.equation rel arg bv }]
        let spec := { symbols := acc.symbols ++ [SpecFn.rel rel],
                      lemmas,
                      functionMap := acc.functionMap ++ [(f, rel)],
                      delta := ((acc.delta.addBinaryRel (SpecFn.rel rel)).addUnary
                                  (SpecFn.func rel)).addUnaryRel (SpecFn.defined rel) }
        .ok { spec, sd, axs, bv }

/-- With a measure the definedness axioms are replaced by a proof: the
termination check establishes definedness at every input. The check is one of
the declaration's own proofs, so it runs with the withheld fact. Only the
totality survives the bracket. -/
private def RelationDecl.declare (info : RelationDecl) (t : TinyML.Transparency) :
    Option Typed.Measure → VerifM Unit
  | none =>
    SpecFn.declare info.sd.fn
      (Skolemize.SpecFn.Axioms.persistent false t info.sd.fn info.sd.x info.bv)
  | some m => do
    SpecFn.declare info.sd.fn
      (Skolemize.SpecFn.Axioms.persistent true t info.sd.fn info.sd.x info.bv)
    VerifM.seq
      (do
        VerifM.assumeAxioms (Skolemize.SpecFn.Axioms.withheld t info.sd.fn info.sd.x info.bv)
        Termination.check info.sd.fn info.sd.x m info.bv)
      (VerifM.assume (.pure (Termination.total info.sd.fn info.sd.x)))

private def declareAndAssume (primitives : PrimEncodings) (acc : RelationSpec)
    (d : Typed.ValDecl) : VerifM RelationSpec := do
  match d.relation with
  | none => pure acc
  | some r =>
      match extend primitives acc d with
      | .error msg => VerifM.fatal msg
      | .ok info => do
          info.declare r.transparency d.decreases
          pure info.spec

/-- Declare a bounded quantifier's solver-facing triple and its defining
axioms on top of the accumulated relation spec. All freshness and membership
conditions needed by the soundness proof are checked operationally by
`validate`. -/
private def declareLifting (primitives : PrimEncodings) (acc : RelationSpec)
    (s : Verifier.BoundedQuantifier.Lifting) :
    VerifM RelationSpec :=
  match s.validate acc.delta with
  | .error msg => VerifM.fatal msg
  | .ok _ =>
      match s.compile primitives acc.functionMap acc.delta with
      | .error msg => VerifM.fatal msg
      | .ok body => do
          s.declare body
          pure { symbols := acc.symbols ++ [SpecFn.rel s.name],
                 lemmas := acc.lemmas,
                 functionMap := acc.functionMap ++ [(s.name, s.name)],
                 delta := s.extendSignature acc.delta }

private def assembleFrom (primitives : PrimEncodings) :
    RelationSpec → Typed.Program → VerifM RelationSpec
  | acc, [] => pure acc
  | acc, d :: ds => do
      let acc' ← declareAndAssume primitives acc d
      assembleFrom primitives acc' ds

/-- Compile and declare the lifted bounded quantifiers in lift order. Earlier
symbols are available while compiling later bodies, which supports nesting. -/
private def assembleLiftings (primitives : PrimEncodings) :
    RelationSpec → List Verifier.BoundedQuantifier.Lifting → VerifM RelationSpec
  | acc, [] => pure acc
  | acc, s :: ss => do
      let acc' ← declareLifting primitives acc s
      assembleLiftings primitives acc' ss

/-- Assemble the global relation signature and function-name map for a typed
program together with the bounded quantifiers its specifications lifted.
Quantifier symbols are declared after all program declarations: assembly never
consults specs, and the only cross-references between lifted bodies — inner
occurrences captured by outer ones — respect the lift order, which elaboration
preserves. -/
def assemble (primitives : PrimEncodings) (prog : Typed.Program)
    (liftings : List Verifier.BoundedQuantifier.Lifting) : VerifM RelationSpec := do
  let Δ ← VerifM.ctx (fun st => (st.decls, st.owns))
  let acc ← assembleFrom primitives { RelationSpec.empty with delta := Δ } prog
  assembleLiftings primitives acc liftings

/-- The invariant pack threaded through relation assembly: the accumulated
delta mirrors the declared signature, the state is spec-level (no owned
locations, no variables), and the accumulated function map is well-formed and
interpreted in agreement with its func-form reading. -/
private structure Inv (acc : RelationSpec) (st : TransState) (ρ : Env) : Prop where
  delta : acc.delta = st.decls
  owns : st.owns = []
  vars : st.decls.vars = []
  wf : st.decls.wf
  Γwf : FunCtx.wfIn acc.functionMap st.decls
  Γagree : FunCtx.Agreement acc.functionMap ρ
  lemmas : acc.lemmas.Sound st.decls ρ

omit [MicaGS HasLC.hasLC Sig] in
/-- Declaring one relation-marked declaration preserves the assembly
invariants; the signature only grows and the environment is only extended
with fresh interpretations. -/
private theorem declareAndAssume_correct {primitives : PrimEncodings}
    (hlaw : primitives.Lawful) (d : Typed.ValDecl)
    (acc : RelationSpec) (st : TransState) (ρ : Env)
    {Q : RelationSpec → TransState → Env → Prop}
    (hinv : Inv acc st ρ)
    (heval : VerifM.eval (declareAndAssume primitives acc d) st ρ Q) :
    ∃ acc' st' ρ', Inv acc' st' ρ' ∧
      st.decls.Subset st'.decls ∧ Env.agreeOn st.decls ρ ρ' ∧
      Q acc' st' ρ' := by
  obtain ⟨hacc, howns, hvars, hwf, hΓwf, hΓagree, hu⟩ := hinv
  simp only [declareAndAssume] at heval
  cases hrel : d.relation with
  | none =>
    simp only [hrel] at heval
    exact ⟨acc, st, ρ, ⟨hacc, howns, hvars, hwf, hΓwf, hΓagree, hu⟩,
      Signature.Subset.refl _, Env.agreeOn_refl, VerifM.eval_ret heval⟩
  | some rel =>
    simp only [hrel] at heval
    cases hext : extend primitives acc d with
    | error msg => simp only [hext] at heval; exact (VerifM.eval_fatal heval).elim
    | ok info =>
      simp only [hext] at heval
      -- Unfold `extend` once to expose its construction facts about `info`.
      obtain ⟨hprimsd, hΓsd, hΔsd, hfnsd, hf, hspec_delta, hspec_fm, hspec_lemmas, hinfoEq⟩ :
          info.sd.primitives = primitives ∧
          info.sd.Γ = acc.functionMap ∧ info.sd.Δ = acc.delta ∧ info.sd.fn = rel.name ∧
          SpecFnFresh acc.delta rel.name info.sd.x ∧
          info.spec.delta = ((acc.delta.addBinaryRel (SpecFn.rel rel.name)).addUnary
              (SpecFn.func rel.name)).addUnaryRel (SpecFn.defined rel.name) ∧
          info.spec.functionMap = acc.functionMap ++ [(info.sd.f, rel.name)] ∧
          (∀ l ∈ info.spec.lemmas, l ∈ acc.lemmas ∨
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
          refine ⟨rfl, rfl, rfl, rfl, { symFresh := ?_, argFresh := ?_ }, rfl, rfl, ?_,
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
      have hΓwf_acc : FunCtx.wfIn acc.functionMap acc.delta := hacc ▸ hΓwf
      have hΔwf_acc : acc.delta.wf := hacc ▸ hwf
      -- The chosen interpretations: the ground-truth relation and its func-form reading.
      set R : ValRel := SpecFn.Semantics.rel info.sd ρ
      set F := ValRel.toFunc R
      set D : Srt.value.denote → Prop := SpecFn.Semantics.defined info.sd ρ info.bv
      have hsdFresh : info.sd.Fresh :=
        SpecDef.fresh (hΔsd ▸ hfnsd ▸ hf)
      have hlawsd : info.sd.primitives.Lawful := hprimsd ▸ hlaw
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
          {Q' : Unit → TransState → Env → Prop}
          (h : VerifM.eval (SpecFn.declare info.sd.fn axs) st ρ Q') :=
        SpecFn.declare_correct rel.name info.sd.f axs R F D acc.delta acc.functionMap st ρ
          hf.relFresh hf.funcFresh hf.defFresh hgraph hacc.symm howns hvars
          (hf.sigBoth_wf hΔwf_acc) hΓwf_acc hΓagree
          (fun ax hax => by
            have := Skolemize.encode_wfIn hlawsd hinfoEq (hΔsd ▸ hΔwf_acc)
              (hΓsd ▸ hΔsd ▸ hΓwf_acc) hsdFresh ax (hsub ax hax)
            rwa [hΔsd, hfnsd] at this)
          (fun ax hax => haxeval ax (hsub ax hax)) (hfnsd ▸ h)
      -- Every encoded axiom holds once the three symbols are declared, whether
      -- or not it stays in the context.
      have hcurrent {st' : TransState} {ρ' : Env}
          (hd : st'.decls = ((acc.delta.addBinaryRel (SpecFn.rel rel.name)).addUnary
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
          VerifM.eval (SpecFn.declare info.sd.fn axs) st ρ
            (fun _ st' ρ' =>
              st'.decls = ((acc.delta.addBinaryRel (SpecFn.rel rel.name)).addUnary
                (SpecFn.func rel.name)).addUnaryRel (SpecFn.defined rel.name) →
              ρ' = SpecFn.Env.both ρ rel.name R D F →
              ∃ st'', st''.decls = st'.decls ∧ st''.owns = st'.owns ∧
                Q info.spec st'' ρ') := by
        have h := VerifM.eval_bind heval
        cases hm : d.decreases with
        | none =>
          simp only [RelationDecl.declare, hm] at h
          exact ⟨_, Skolemize.encode_persistent hinfoEq,
            h.mono fun _ st' _ hQ _ _ => ⟨st', rfl, rfl, VerifM.eval_ret hQ⟩⟩
        | some m =>
          simp only [RelationDecl.declare, hm] at h
          refine ⟨_, Skolemize.encode_persistent hinfoEq, (VerifM.eval_bind h).mono ?_⟩
          intro _ st' ρ' hc hd' hρ'
          have hclose : ∀ v, info.bv.defined.eval (ρ'.updateConst .value info.sd.x v) →
              (info.sd.fn.isDefined (.var .value info.sd.x)).eval
                (ρ'.updateConst .value info.sd.x v) := by
            rw [hρ']; exact Skolemize.encode_closed hinfoEq haxeval
          obtain ⟨hproof, hcont⟩ := VerifM.eval_seq hc
          have hlocal := fun ax (hax : ax ∈ Skolemize.SpecFn.Axioms.withheld
              rel.transparency info.sd.fn info.sd.x info.bv) =>
            hcurrent hd' hρ' ax (Skolemize.encode_withheld hinfoEq ax hax)
          obtain ⟨st₀, hd₀, _, _, hcheck⟩ := VerifM.eval_assumeAxioms
            (VerifM.eval_bind hproof) (fun ax hax => (hlocal ax hax).1)
            (fun ax hax => (hlocal ax hax).2)
          obtain ⟨hwt, ht, _⟩ := Termination.check_correct hclose hcheck
          exact ⟨{ st' with asserts := Termination.total info.sd.fn info.sd.x :: st'.asserts },
            rfl, rfl, VerifM.eval_ret (VerifM.eval_assumePure hcont (hd₀ ▸ hwt) ht)⟩
      obtain ⟨axs, hsub, hrun⟩ := hrun
      obtain ⟨st4, ρ4, hρ4, hst4_decls, howns4, hvars4, hwf4, hsub4, hagree4,
        hΓwf4, hΓagree4, hcont⟩ := hdecl axs hsub hrun
      obtain ⟨st5, hst5_decls, howns5, hQ5⟩ := hcont hst4_decls hρ4
      refine ⟨info.spec, st5, ρ4, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hagree4, hQ5⟩
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
private theorem assembleFrom_correct {primitives : PrimEncodings}
    (hlaw : primitives.Lawful) (prog : Typed.Program) :
    ∀ (acc : RelationSpec) (st : TransState) (ρ : Env)
      {Q : RelationSpec → TransState → Env → Prop},
      Inv acc st ρ →
      VerifM.eval (assembleFrom primitives acc prog) st ρ Q →
      ∃ result stRel ρRel, Inv result stRel ρRel ∧
        st.decls.Subset stRel.decls ∧ Env.agreeOn st.decls ρ ρRel ∧
        Q result stRel ρRel := by
  induction prog with
  | nil =>
    intro acc st ρ Q hinv heval
    simp only [assembleFrom] at heval
    exact ⟨acc, st, ρ, hinv, Signature.Subset.refl _, Env.agreeOn_refl,
      VerifM.eval_ret heval⟩
  | cons d ds ih =>
    intro acc st ρ Q hinv heval
    simp only [assembleFrom] at heval
    obtain ⟨acc', st', ρ', hinv', hsub', hag', hcont⟩ :=
      declareAndAssume_correct hlaw d acc st ρ hinv (VerifM.eval_bind heval)
    obtain ⟨result, stRel, ρRel, hinvRel, hsubRel, hagRel, hQ⟩ := ih acc' st' ρ' hinv' hcont
    exact ⟨result, stRel, ρRel, hinvRel, hsub'.trans hsubRel,
      Env.agreeOn_trans hag' (Env.agreeOn_mono hsub' hagRel), hQ⟩

omit [MicaGS HasLC.hasLC Sig] in
/-- Compiling and declaring one lifted bounded quantifier preserves the
assembly invariants. -/
private theorem declareLifting_correct {primitives : PrimEncodings}
    (hlaw : primitives.Lawful) (s : Verifier.BoundedQuantifier.Lifting)
    (acc : RelationSpec) (st : TransState) (ρ : Env)
    {Q : RelationSpec → TransState → Env → Prop}
    (hinv : Inv acc st ρ)
    (heval : VerifM.eval (declareLifting primitives acc s) st ρ Q) :
    ∃ acc' st' ρ', Inv acc' st' ρ' ∧
      st.decls.Subset st'.decls ∧ Env.agreeOn st.decls ρ ρ' ∧
      Q acc' st' ρ' := by
  obtain ⟨hacc, howns, hvars, hwf, hΓwf, hΓagree, hu⟩ := hinv
  simp only [declareLifting] at heval
  cases hvalid : s.validate acc.delta with
  | error msg =>
    simp only [hvalid] at heval
    exact (VerifM.eval_fatal heval).elim
  | ok v =>
    simp only [hvalid] at heval
    cases hcompile : s.compile primitives acc.functionMap acc.delta with
    | error msg =>
      simp only [hcompile] at heval
      exact (VerifM.eval_fatal heval).elim
    | ok body =>
      simp only [hcompile] at heval
      have hbody := Verifier.BoundedQuantifier.Lifting.compile_wfIn hlaw
        v.down (hacc ▸ hwf) (hacc ▸ hΓwf) hcompile
      obtain ⟨st4, ρ4, hdelta, howns4, hvars4, hwf4, hsub4, hagree4,
        hΓwf4, hΓagree4, hcont⟩ :=
        Verifier.BoundedQuantifier.Lifting.declare_correct s body acc.delta
          acc.functionMap st ρ v.down hbody hacc.symm howns hvars
          (hacc ▸ hwf) (hacc ▸ hΓwf) hΓagree (VerifM.eval_bind heval)
      exact ⟨{ symbols := acc.symbols ++ [SpecFn.rel s.name],
               lemmas := acc.lemmas,
               functionMap := acc.functionMap ++ [(s.name, s.name)],
               delta := s.extendSignature acc.delta }, st4, ρ4,
        ⟨hdelta.symm, howns4, hvars4, hwf4, hΓwf4, hΓagree4, hu.mono hsub4 hagree4 hwf4⟩,
        hsub4, hagree4, VerifM.eval_ret hcont⟩

omit [MicaGS HasLC.hasLC Sig] in
private theorem assembleLiftings_correct {primitives : PrimEncodings}
    (hlaw : primitives.Lawful) (ss : List Verifier.BoundedQuantifier.Lifting) :
    ∀ (acc : RelationSpec) (st : TransState) (ρ : Env)
      {Q : RelationSpec → TransState → Env → Prop},
      Inv acc st ρ →
      VerifM.eval (assembleLiftings primitives acc ss) st ρ Q →
      ∃ result stRel ρRel, Inv result stRel ρRel ∧
        st.decls.Subset stRel.decls ∧ Env.agreeOn st.decls ρ ρRel ∧
        Q result stRel ρRel := by
  induction ss with
  | nil =>
    intro acc st ρ Q hinv heval
    simp only [assembleLiftings] at heval
    exact ⟨acc, st, ρ, hinv, Signature.Subset.refl _, Env.agreeOn_refl,
      VerifM.eval_ret heval⟩
  | cons s ss ih =>
    intro acc st ρ Q hinv heval
    simp only [assembleLiftings] at heval
    obtain ⟨acc1, st1, ρ1, hinv1, hsub1, hag1, hcont1⟩ :=
      declareLifting_correct hlaw s acc st ρ hinv (VerifM.eval_bind heval)
    obtain ⟨result, stRel, ρRel, hinvRel, hsubRel, hagRel, hQ⟩ :=
      ih acc1 st1 ρ1 hinv1 hcont1
    exact ⟨result, stRel, ρRel, hinvRel, hsub1.trans hsubRel,
      Env.agreeOn_trans hag1 (Env.agreeOn_mono hsub1 hagRel), hQ⟩

omit [MicaGS HasLC.hasLC Sig] in
theorem assemble_correct (primitives : PrimEncodings) (hlaw : primitives.Lawful)
    (prog : Typed.Program)
    (liftings : List Verifier.BoundedQuantifier.Lifting)
    {st : TransState} {ρ : Env}
    {Q : RelationSpec → TransState → Env → Prop}
    (hvars0 : st.decls.vars = [])
    (howns0 : st.owns = [])
    (hwf0 : st.decls.wf)
    (heval : VerifM.eval (RelationSpec.assemble primitives prog liftings) st ρ Q) :
    ∃ spec0 : RelationSpec, ∃ stRel ρRel,
      stRel.decls.vars = [] ∧
      stRel.owns = [] ∧
      st.decls.Subset stRel.decls ∧
      Env.agreeOn st.decls ρ ρRel ∧
      spec0.lemmas.Sound stRel.decls ρRel ∧
      Q { spec0 with delta := stRel.decls } stRel ρRel := by
  unfold RelationSpec.assemble at heval
  have hctx := VerifM.eval_bind heval
  obtain ⟨hassembleFrom, hownsWf, _, _⟩ := VerifM.eval_ctx hctx
  have hrest := hassembleFrom hownsWf
  have hempty_Γwf : FunCtx.wfIn empty.functionMap st.decls :=
    ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim⟩
  have hempty_Γagree : FunCtx.Agreement empty.functionMap ρ :=
    fun _ _ h => (List.not_mem_nil h).elim
  obtain ⟨acc, st1, ρ1, hinv1, hsub1, hag1, hcont⟩ :=
    assembleFrom_correct hlaw prog { empty with delta := st.decls } st ρ
      ⟨rfl, howns0, hvars0, hwf0, hempty_Γwf, hempty_Γagree, by simp [empty, Lemmas.Sound]⟩
      (VerifM.eval_bind hrest)
  obtain ⟨result, stRel, ρRel, hinvRel, hsubRel, hagRel, hQ⟩ :=
    assembleLiftings_correct hlaw liftings acc st1 ρ1 hinv1 hcont
  refine ⟨result, stRel, ρRel, hinvRel.vars, hinvRel.owns, hsub1.trans hsubRel,
    Env.agreeOn_trans hag1 (Env.agreeOn_mono hsub1 hagRel), hinvRel.lemmas, ?_⟩
  have hresD := hinvRel.delta
  obtain ⟨_, _, _, _⟩ := result
  simp only at hresD; subst hresD
  exact hQ

end RelationSpec

/-- Check an individual declaration by compiling its body, which is a specified
    function literal and so takes exactly the path a `let`-bound one does. The
    compilation and its axioms run inside a `seq` bracket, so neither reaches
    the verifications that follow. Returns the specified arrow
    the declaration was verified at, which is what binds its name for the
    declarations that follow. -/
def ValDecl.check (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
    (Γfn : FunCtx) (Gf : GhostFns) (B : Bindings) (Γ : TinyML.TyCtx)
    (axs : List Axiom) (d : Typed.ValDecl) : VerifM TinyML.Typ :=
  VerifM.seq
    (do
      VerifM.assumeAxioms axs
      let _ ← compile reg Θ Δ_spec Γfn Gf Bindings.empty B Γ d.body
      pure ())
    (pure d.body.ty)

/-- Check a `let _ = e` declaration: just compile `e` for safety, no spec. -/
def ValDecl.checkExpr (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
    (Γfn : FunCtx) (Gf : GhostFns) (B : Bindings) (Γ : TinyML.TyCtx)
    (d : Typed.ValDecl) : VerifM Unit :=
  VerifM.seq (do let _ ← compile reg Θ Δ_spec Γfn Gf Bindings.empty B Γ d.body; pure ()) (pure ())

/-- Verify all declarations in a program, binding each verified one so later
    declarations can use it as a value. -/
def Program.check (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
    (ls : Lemmas) (Γfn : FunCtx) (Gf : GhostFns) :
    Bindings → TinyML.TyCtx → Typed.Program → VerifM Unit
  | _, _, [] => pure ()
  | B, Γ, d :: ds => do
    -- The entries are added after the handling below, because that handling
    -- drops the name from the ghost table when it binds a run-time value of it.
    let fn ← ValDecl.ghostEntries reg Θ Δ_spec Gf ls d
    match d.mode with
    | .ghost =>
      -- A ghost declaration binds no run-time value: it only becomes callable
      -- from the ghost code of the declarations that follow it.
      let entry ← ValDecl.checkGhost reg Θ Δ_spec Gf d
      Program.check reg Θ Δ_spec ls Γfn (fn ++ entry :: Gf) (B.remove entry.1) Γ ds
    | .runtime =>
    match d.name.name, d.body.spec? with
    | none, none =>
      ValDecl.checkExpr reg Θ Δ_spec Γfn Gf B Γ d
      Program.check reg Θ Δ_spec ls Γfn (fn ++ Gf) B Γ ds
    | some n, none =>
    -- Named declaration without a spec: skip if it's a function definition
    -- (no code executes), otherwise check it. The new binding shadows any
    -- earlier one of the same name, which is therefore dropped: nothing here
    -- gives the new value a specification.
      if d.body.isFunc then
        Program.check reg Θ Δ_spec ls Γfn (fn ++ Gf.remove n) (B.remove n) Γ ds
      else
        ValDecl.checkExpr reg Θ Δ_spec Γfn Gf B Γ d
        Program.check reg Θ Δ_spec ls Γfn (fn ++ Gf.remove n) (B.remove n) Γ ds
    | _, _ =>
      let ty ← ValDecl.check reg Θ Δ_spec Γfn Gf B Γ (ls.enterDeclaration d.name.name) d
      match d.name.name with
      | some n =>
        -- The declaration's value is a specified function: declare a constant
        -- for it and bind the name at the arrow it was verified at, so later
        -- declarations can apply it through its type or pass it as a value.
        -- The arrow's type variables are generalized, the verification having
        -- gone through at every assignment of them.
        let fv ← VerifM.decl (some n) .value
        Program.check reg Θ Δ_spec ls Γfn (fn ++ Gf.remove n) ((n, fv) :: B)
          (Γ.extendScheme n (TinyML.Scheme.gen ty)) ds
      | none => Program.check reg Θ Δ_spec ls Γfn (fn ++ Gf) B Γ ds

def Program.verify (reg : Verifier.Registry) (prog : Untyped.Program Untyped.SpecBody) : Smt.Strategy Smt.Strategy.Outcome :=
  VerifM.strategy do
    let (Θ, typed, liftSt) ← Program.prepare (Program.specEnv reg (Program.relationMap prog)) {} prog
    Verifier.Registry.introduceRegistry reg
    let relations ← RelationSpec.assemble reg.primitives typed liftSt.syms
    Program.check reg Θ relations.delta relations.lemmas relations.functionMap
      GhostFns.empty Bindings.empty TinyML.TyCtx.empty typed

/-! ## Correctness -/

omit [MicaGS HasLC.hasLC Sig] in
theorem Program.prepare_correct (env : Typed.SpecEnv σ) (s : σ)
    (prog : Untyped.Program Untyped.SpecBody)
    (st : TransState) (ρ : Env)
    {Q : (TinyML.TypeEnv × Typed.Program × σ) → TransState → Env → Prop}
    (heval : VerifM.eval (Program.prepare env s prog) st ρ Q) :
    ∃ Θ typed s', Typed.Program.runtime typed = Untyped.Program.runtime prog ∧
      Q (Θ, typed, s') st ρ := by
  unfold Program.prepare at heval
  cases helab : Typed.Program.elaborate env TinyML.TypeEnv.empty TinyML.TyCtx.empty prog s with
  | error err =>
    simp [helab] at heval
    exact (VerifM.eval_fatal heval).elim
  | ok prepared =>
    rcases prepared with ⟨⟨Θ, typed⟩, s'⟩
    refine ⟨Θ, typed, s',
      Typed.Program.elaborate_runtime env TinyML.TypeEnv.empty TinyML.TyCtx.empty prog helab, ?_⟩
    simp [helab] at heval
    exact VerifM.eval_ret heval

theorem ValDecl.checkExpr_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (W : TinyML.World) (hW : W.pctx = reg.primCtx)
    (B : Bindings) (Γ : TinyML.TyCtx)
    (d : Typed.ValDecl) (γ : Runtime.Subst)
    (hwf : W.wf)
    (st : TransState) (ρ : Env)
    (hag : W.agrees st.decls ρ)
    (hagree : B.agreeOnLinked ρ γ) (hbwf : B.wfIn st.decls)
    (hΔreg : Verifier.Registry.symSubset reg W.Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg W.ρ_spec)
    (hGf : GhostFns.wellTyped W st.decls ρ Gf)
    {Q : Unit → TransState → Env → Prop}
    (heval : VerifM.eval (ValDecl.checkExpr reg W.Θ W.Δ_spec Γfn Gf B Γ d) st ρ Q) :
    (□ st.sl W ρ ∗ Bindings.typedSubst W B Γ γ ⊢ Φ) →
    □ st.sl W ρ ∗ Bindings.typedSubst W B Γ γ ⊢
      wp W.pctx (d.body.runtime.subst γ) (fun _ => Φ) := by
  intro Hent
  simp only [ValDecl.checkExpr] at heval
  have ⟨hinner, _⟩ := VerifM.eval_seq heval
  have hcompile := VerifM.eval_bind hinner
  have hcomp :=
    compile_correct reg hSound d.body W iprop(□ st.sl W ρ ∗ Φ) Γfn Gf Bindings.empty B Γ st ρ
    Runtime.Subst.id γ
    (fun x st' ρ' => VerifM.eval (pure ()) st' ρ' (fun _ _ _ => True))
    (fun _ => Φ)
    hW
    hcompile
    (Bindings.agreeOnLinked_empty ρ _)
    (Bindings.wfIn_empty st.decls)
    hGf
    hagree
    hbwf
    hwf
    hag
    hΔreg
    hρreg
    (fun _ _ _ _ _ _ _ => by
      istart
      iintro ⟨_, _, Hctx⟩
      icases Hctx with ⟨_, HΦ⟩
      iexact HΦ)
  refine (BIBase.Entails.trans ?_ hcomp)
  istart
  iintro ⟨#Hsl, #HT⟩
  isplitl [Hsl]
  · iexact Hsl
  · isplitl []
    · iapply (Bindings.typedScope_of_typedSubst W Runtime.Subst.id)
      iexact HT
    · isplitl [Hsl]
      · iexact Hsl
      · iapply Hent
        isplitl [Hsl]
        · iexact Hsl
        · iexact HT

/-- A specified declaration's value is typed at the arrow it was verified at,
    and the check runs on. Stated without a `wp` for the same reason as
    `compileFix_typed`: `Program.check_correct` needs it once per assignment. -/
theorem ValDecl.check_correct (reg : Verifier.Registry)
    (hSound : Verifier.Registry.Sound reg)
    (W : TinyML.World) (hW : W.pctx = reg.primCtx)
    (B : Bindings) (Γ : TinyML.TyCtx) (axs : List Axiom)
    (haxs : ∀ ax ∈ axs, ax.formula.wfIn W.Δ_spec ∧ ax.formula.eval W.ρ_spec)
    (d : Typed.ValDecl) (γ : Runtime.Subst)
    (self : Typed.Binder) (args : List Typed.Binder) (retTy : TinyML.Typ)
    (s : Spec TinyML.Typ) (body : Typed.Expr)
    (hbody : d.body = .fix self args retTy (some s) body)
    (hwf : W.wf)
    (st : TransState) (ρ : Env)
    (hag : W.agrees st.decls ρ)
    (hagree : B.agreeOnLinked ρ γ) (hbwf : B.wfIn st.decls)
    (hΔreg : Verifier.Registry.symSubset reg W.Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg W.ρ_spec)
    (hGf : GhostFns.wellTyped W st.decls ρ Gf)
    {Q : TinyML.Typ → TransState → Env → Prop}
    (heval : VerifM.eval (ValDecl.check reg W.Θ W.Δ_spec Γfn Gf B Γ axs d) st ρ Q) :
    (Bindings.typedSubst W B Γ γ ⊢
        TinyML.ValHasType W
          (Runtime.Val.fix self.runtime (args.map (·.runtime))
            (body.runtime.subst ((γ.remove' self.runtime).removeAll' (args.map (·.runtime)))))
          d.body.ty) ∧
      Q d.body.ty st ρ := by
  simp only [ValDecl.check] at heval
  obtain ⟨hcompileSeq, hpure⟩ := VerifM.eval_seq heval
  refine ⟨?_, VerifM.eval_ret hpure⟩
  have hty : d.body.ty = .arrow (args.map Typed.Binder.WithTypeVars.ty) retTy (some s) := by
    rw [hbody]; simp [Typed.Expr.WithTypeVars.ty]
  rw [hty]
  obtain ⟨st₀, hd₀, _, _, hcompile⟩ := VerifM.eval_assumeAxioms
    (VerifM.eval_bind hcompileSeq)
    (fun ax ha => Formula.wfIn_mono _ (haxs ax ha).1 hag.subset hcompileSeq.1.namesDisjoint)
    (fun ax ha => (Formula.eval_env_agree (haxs ax ha).1 hag.agree).mp (haxs ax ha).2)
  have hc := VerifM.eval_bind hcompile
  rw [hbody] at hc
  exact (Bindings.typedScope_of_typedSubst W Runtime.Subst.id).trans
    (compileFix_typed reg W hW Γfn Gf Bindings.empty B Γ Runtime.Subst.id γ
      self args retTy s body (compile_correct reg hSound body) hwf (hd₀ ▸ hag)
      (Bindings.agreeOnLinked_empty ρ _) (Bindings.wfIn_empty st₀.decls) (hd₀ ▸ hGf)
      hagree (hd₀ ▸ hbwf) hΔreg hρreg hc)

theorem Program.check_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (W : TinyML.World) (hW : W.pctx = reg.primCtx)
    (ls : Lemmas) (hls : ls.Sound W.Δ_spec W.ρ_spec)
    (B : Bindings) (Γ : TinyML.TyCtx)
    (prog : Typed.Program) (γ : Runtime.Subst)
    (hwf : W.wf)
    (st : TransState) (ρ : Env)
    (hag : W.agrees st.decls ρ)
    (hagree : B.agreeOnLinked ρ γ) (hbwf : B.wfIn st.decls)
    (hΔreg : Verifier.Registry.symSubset reg W.Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg W.ρ_spec)
    (hGf : GhostFns.wellTyped W st.decls ρ Gf) :
    Γ.Closed →
    VerifM.eval (Program.check reg W.Θ W.Δ_spec ls Γfn Gf B Γ prog) st ρ (fun _ _ _ => True) →
    □ st.sl W ρ ∗ Bindings.typedSubst W B Γ γ ⊢
      pwp W.pctx ((Typed.Program.runtime prog).subst γ) := by
  induction prog generalizing B Γ γ st ρ Gf with
  | nil =>
    intro _ _
    simp only [Typed.Program.runtime, List.filterMap_nil, Runtime.Program.subst]
    refine BIBase.Entails.trans ?_ pwp_nil
    istart
    iintro _
    iempintro
  | cons d ds ih =>
    intro hΓ heval
    simp only [Program.check] at heval
    have haxs := Lemmas.enterDeclaration_sound hls
    obtain ⟨fn, hfn, heval⟩ :=
      ValDecl.ghostEntries_correct reg hSound W Gf hwf hΔreg hρreg _ d hag hls hGf (VerifM.eval_bind heval)
    cases hmode : d.mode with
    | ghost =>
      simp only [hmode] at heval
      obtain ⟨entry, hGf_entry, hcont⟩ :=
        ValDecl.checkGhost_correct reg hSound W Gf hwf hΔreg hρreg d hag hGf (VerifM.eval_bind heval)
      have hih := ih (Gf := fn ++ entry :: Gf) (B.remove entry.1) Γ γ st ρ hag
        (Bindings.agreeOnLinked_remove hagree entry.1) (Bindings.wfIn_remove hbwf entry.1)
        (hfn.append (hGf_entry.append hGf)) hΓ hcont
      have hscope : □ st.sl W ρ ∗ Bindings.typedSubst W B Γ γ ⊢
          □ st.sl W ρ ∗ Bindings.typedSubst W (B.remove entry.1) Γ γ :=
        sep_mono .rfl (Bindings.typedSubst_remove (fun _ _ => rfl))
      have hih := hscope.trans hih
      simpa [Typed.Program.runtime, Typed.ValDecl.runtime?, hmode] using hih
    | runtime =>
    have hpwp_unfold :
        wp W.pctx (d.body.runtime.subst γ) (fun v =>
          pwp W.pctx ((Typed.Program.runtime ds).subst (Runtime.Subst.updateBinder d.name.runtime v γ)))
        ⊢ pwp W.pctx ((Typed.Program.runtime (d :: ds)).subst γ) := by
      simp only [Typed.Program.runtime, Typed.ValDecl.runtime?, hmode, Typed.ValDecl.runtime,
        Runtime.Program.subst, Runtime.Decl.subst, List.filterMap_cons]
      refine BIBase.Entails.trans (wp.mono fun v => ?_) pwp_cons
      rw [Runtime.Program.subst_remove_update]
      exact .rfl
    refine BIBase.Entails.trans ?_ hpwp_unfold
    simp only [hmode] at heval
    cases hname : d.name.name with
    | none =>
      -- unnamed: pwp continuation does not depend on `v`
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ := by
        intro v; simp [Binder.runtime_of_name_none hname, Runtime.Subst.updateBinder]
      cases hspec : d.body.spec? with
      | none =>
        -- unnamed, no spec
        simp only [hname, hspec] at heval
        have hbind := VerifM.eval_bind heval
        have ⟨_, hcont⟩ := VerifM.eval_seq hbind
        have hih := ih (Gf := fn ++ Gf) B Γ γ st ρ hag hagree hbwf (hfn.append hGf) hΓ
          (VerifM.eval_ret hcont)
        have hwp := ValDecl.checkExpr_correct reg hSound W hW B Γ d γ hwf st ρ hag
          hagree hbwf hΔreg hρreg hGf hbind hih
        refine hwp.trans (wp.mono ?_)
        intro v; rw [hupd v]; exact .rfl
      | some sp =>
        -- unnamed, with spec
        simp only [hname, hspec] at heval
        obtain ⟨self, args, retTy, body, hbody⟩ := Typed.Expr.spec?_elim hspec
        obtain ⟨_, hcont⟩ := ValDecl.check_correct reg hSound W hW B Γ _ (haxs none) d γ
          self args retTy sp body hbody hwf st ρ hag hagree hbwf hΔreg hρreg hGf
          (VerifM.eval_bind heval)
        have hih := ih (Gf := fn ++ Gf) B Γ γ st ρ hag hagree hbwf (hfn.append hGf) hΓ hcont
        rw [Typed.Expr.runtime_subst_of_fix hbody]
        refine SpatialContext.wp_func ?_
        rw [hupd _]
        exact hih
    | some n =>
      have hname_rt : d.name.runtime = .named n := Binder.runtime_of_name_some hname
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ.update n v := by
        intro v; simp [hname_rt, Runtime.Subst.updateBinder]
      cases hspec : d.body.spec? with
      | none =>
        simp only [hname, hspec] at heval
        split at heval
        · -- named, no spec, function value
          rename_i hfunc
          obtain ⟨self, args, retTy, spec, body, hbody⟩ := Expr.isFunc_elim hfunc
          have hbody_rt : d.body.runtime.subst γ =
              Runtime.Expr.fix self.runtime (args.map (·.runtime))
                (body.runtime.subst ((γ.remove' self.runtime).removeAll'
                  (args.map (·.runtime)))) := by
            rw [hbody]; conv_lhs => unfold Expr.WithTypeVars.runtime
            simp only [Runtime.Expr.subst_fix]
          rw [hbody_rt]
          set fval := Runtime.Val.fix self.runtime (args.map (·.runtime))
            (body.runtime.subst ((γ.remove' self.runtime).removeAll'
              (args.map (·.runtime))))
          apply SpatialContext.wp_func
          rw [hupd fval]
          have heval' : VerifM.eval
              (Program.check reg W.Θ W.Δ_spec ls Γfn (fn ++ Gf.remove n) (B.remove n) Γ ds) st ρ
              (fun _ _ _ => True) := by
            convert heval
          have hih := ih (Gf := fn ++ Gf.remove n) (B.remove n) Γ (γ.update n fval) st ρ hag
            (Bindings.agreeOnLinked_remove_update hagree n fval) (Bindings.wfIn_remove hbwf n)
            (hfn.append (hGf.remove n)) hΓ heval'
          refine BIBase.Entails.trans ?_ hih
          istart
          iintro ⟨#Hsl, #HT⟩
          isplitl [Hsl]
          · iexact Hsl
          · iapply Bindings.typedSubst_remove_update
            iexact HT
        · -- named, no spec, not a function
          have hbind := VerifM.eval_bind heval
          have ⟨_, hcont⟩ := VerifM.eval_seq hbind
          have hcont' : VerifM.eval
              (Program.check reg W.Θ W.Δ_spec ls Γfn (fn ++ Gf.remove n) (B.remove n) Γ ds) st ρ
              (fun _ _ _ => True) :=
            VerifM.eval_ret hcont
          have hwp := ValDecl.checkExpr_correct reg hSound W hW B Γ d γ hwf st ρ hag
            hagree hbwf hΔreg hρreg hGf hbind
            (Φ := iprop(emp)) (by istart; iintro _; iempintro)
          refine SpatialContext.wp_strengthen_persistent hwp ?_
          intro v
          rw [hupd v]
          have hih := ih (Gf := fn ++ Gf.remove n) (B.remove n) Γ (γ.update n v)
            st ρ hag (Bindings.agreeOnLinked_remove_update hagree n v)
            (Bindings.wfIn_remove hbwf n) (hfn.append (hGf.remove n)) hΓ
            hcont'
          exact wand_intro (sep_elim_left.trans <| by
            refine BIBase.Entails.trans ?_ hih
            istart
            iintro ⟨#Hsl, #HT⟩
            isplitl [Hsl]
            · iexact Hsl
            · iapply Bindings.typedSubst_remove_update
              iexact HT)
      | some sp =>
        simp only [hname, hspec] at heval
        obtain ⟨self, args, retTy, body, hbody⟩ := Typed.Expr.spec?_elim hspec
        set selfTy := d.body.ty
        set v := Runtime.Val.fix self.runtime (args.map (·.runtime))
          (body.runtime.subst ((γ.remove' self.runtime).removeAll'
            (args.map (·.runtime))))
        have hval : ∀ σ, Bindings.typedSubst W B Γ γ ⊢
            TinyML.ValHasType W v ((TinyML.Scheme.gen selfTy).instantiate σ) := by
          intro σ
          rw [TinyML.Scheme.gen_instantiate]
          refine BIBase.Entails.trans (Bindings.typedSubst_afterInstantiating W σ hΓ) ?_
          refine BIBase.Entails.trans ?_ (TinyML.ValHasType.subst W σ v selfTy).1
          exact (ValDecl.check_correct reg hSound (W.afterInstantiating σ) hW B Γ _
            (haxs (some n)) d γ
            self args retTy sp body hbody (hwf.afterInstantiating σ) st ρ
            (hag.afterInstantiating σ) hagree hbwf hΔreg hρreg hGf (VerifM.eval_bind heval)).1
        have hcont :=
          (ValDecl.check_correct reg hSound W hW B Γ _ (haxs (some n)) d γ self args retTy sp body
            hbody hwf st ρ hag hagree hbwf hΔreg hρreg hGf (VerifM.eval_bind heval)).2
        have hcont' : VerifM.eval
            (do let fv ← VerifM.decl (some n) .value
                Program.check reg W.Θ W.Δ_spec ls Γfn (fn ++ Gf.remove n) ((n, fv) :: B)
                  (Γ.extendScheme n (TinyML.Scheme.gen selfTy)) ds) st ρ
            (fun _ _ _ => True) := by
          convert hcont
        rw [Typed.Expr.runtime_subst_of_fix hbody]
        refine SpatialContext.wp_func ?_
        rw [hupd v]
        -- The declaration's value gets a constant of its own, so later
        -- declarations can use the name as a value.
        set fv := st.freshConst (some n) .value with hfv_def
        set st₁ : TransState := { st with decls := st.decls.addConst fv } with hst₁_def
        set ρ₁ := ρ.updateConst .value fv.name v with hρ₁_def
        have hdecl := VerifM.eval_decl (VerifM.eval_bind hcont') v
        have hfresh : fv.name ∉ st.decls.allNames := st.freshConst_fresh (some n) .value
        have hρ_st₁ : Env.agreeOn st.decls ρ ρ₁ := Env.agreeOn_update_fresh_const hfresh
        have hst_sub₁ : st.decls.Subset st₁.decls := Signature.Subset.subset_addConst _ _
        have hag₁ : W.agrees st₁.decls ρ₁ := hag.step hst_sub₁ hρ_st₁
        have hval₁ : ρ₁.consts .value fv.name = v := by
          simp [hρ₁_def, Env.updateConst]
        have hagree₁ : Bindings.agreeOnLinked ((n, fv) :: B) ρ₁ (γ.update n v) :=
          Bindings.agreeOnLinked_cons_update
            (Bindings.agreeOnLinked_env_agree hagree hρ_st₁ hbwf) rfl hval₁
        have hbwf₁ : Bindings.wfIn ((n, fv) :: B) st₁.decls := Bindings.wfIn_cons hbwf
        have hGf₁ := hGf.step hst_sub₁ hρ_st₁ (VerifM.eval.wf hdecl).namesDisjoint
        have hih := ih (Gf := fn ++ Gf.remove n) ((n, fv) :: B)
          (Γ.extendScheme n (TinyML.Scheme.gen selfTy))
          (γ.update n v) st₁ ρ₁ hag₁ hagree₁ hbwf₁
          ((hfn.step hst_sub₁ hρ_st₁ (VerifM.eval.wf hdecl).namesDisjoint).append
            (hGf₁.remove n))
          (hΓ.extendScheme n (TinyML.Scheme.gen_free selfTy)) hdecl
        have hsl₁ : st.sl W ρ ⊢ st₁.sl W ρ₁ := by
          simp only [TransState.sl_eq, hst₁_def]
          exact (SpatialContext.interp_env_agree W (VerifM.eval.wf heval).ownsWf hρ_st₁).1
        refine BIBase.Entails.trans ?_ hih
        istart
        iintro ⟨#Hsl, #HT⟩
        isplitl [Hsl]
        · imodintro
          iapply hsl₁
          iexact Hsl
        · iapply (Bindings.typedSubst_cons_scheme (W := W) (B := B) (Γ := Γ) (γ := γ)
            (x := n) (v := fv) (s := TinyML.Scheme.gen selfTy) (w := v))
          · iexact HT
          · iapply (forall_intro hval)
            iexact HT


omit [MicaGS HasLC.hasLC Sig] in
theorem Program.verify_correct (reg : Verifier.Registry)
    (hSound : Verifier.Registry.Sound reg) (p : Untyped.Program Untyped.SpecBody) :
    Smt.Strategy.checks (Program.verify reg p)
      (∀ [MicaGS HasLC.hasLC Sig], ⊢ pwp reg.primCtx (Untyped.Program.runtime p)) := by
  simp only [Smt.Strategy.checks, Program.verify, VerifM.strategy]
  intro st' heval _inst
  obtain ⟨_, h1⟩ := ScopedM.strategy_eval_initial_implies_ScopedM_eval heval
  obtain ⟨a, ctx_mid, hverif, hcont⟩ := ScopedM.eval_bind h1
  match a with
  | .error e =>
    cases e with
    | failed _ =>
        have hret := (ScopedM.eval_ret.mp hcont).1
        cases hret
    | fatal _ =>
        have hret := (ScopedM.eval_ret.mp hcont).1
        cases hret
  | .ok () =>
    have hverifM := VerifM.eval_of_translate
                      (do
                        let (Θ, typed, liftSt) ←
                          Program.prepare (Program.specEnv reg (Program.relationMap p)) {} p
                        Verifier.Registry.introduceRegistry reg
                        let relations ← RelationSpec.assemble reg.primitives typed liftSt.syms
                        Program.check reg Θ relations.delta relations.lemmas
                          relations.functionMap GhostFns.empty
                          Bindings.empty TinyML.TyCtx.empty typed)
                      TransState.init Env.init ctx_mid
                      (ScopedM.eval_declareConst hverif)
                      TransState.init_holdsFor TransState.init_wf
    have hbind := VerifM.eval_bind hverifM
    obtain ⟨Θ, typed, liftSt, hrt, hrest⟩ :=
      Program.prepare_correct (Program.specEnv reg (Program.relationMap p)) {} p
        TransState.init Env.init hbind
    dsimp only at hrest
    -- Peel the registry setup from the continuation generically.
    have hsetup_bind := VerifM.eval_bind hrest
    obtain ⟨st_setup, ρ_setup, _hΔsub, hdep_setup, hvars_setup_eq, howns_setup,
      _hasserts, hstable_setup, _hρagree, hcheck_eval⟩ :=
      Verifier.Registry.eval_introduceRegistry reg hSound hsetup_bind
    have hassemble := VerifM.eval_bind hcheck_eval
    have hvars_setup : st_setup.decls.vars = [] := by
      rw [hvars_setup_eq]
      rfl
    obtain ⟨spec0, stRel, ρRel, hvars, howns, hsub_setup_rel, hag_setup_rel, hlem,
      hcheck_eval⟩ :=
      RelationSpec.assemble_correct reg.primitives (Verifier.Registry.primitives_lawful hSound)
        typed liftSt.syms hvars_setup howns_setup
        hcheck_eval.1.namesDisjoint hassemble
    have hΔreg : Verifier.Registry.symSubset reg stRel.decls := by
      intro i hi
      exact (Verifier.Registry.extendWithSym_subset_sigOf_of_mem hi).trans
        (hdep_setup.trans hsub_setup_rel)
    have hρreg : Verifier.Registry.symAgree reg ρRel := by
      intro i hi
      exact hstable_setup ρRel hag_setup_rel i hi
    -- The meta-level world: the registry's operational context, the type
    -- environment the elaborator produced, and the specification model the
    -- relational declarations left in the state.
    let W : TinyML.World :=
      { pctx := reg.primCtx, Θ, Δ_spec := stRel.decls, ρ_spec := ρRel,
        eta := TinyML.SemTypeAssign.empty }
    have hcorrect := Program.check_correct reg hSound W rfl spec0.lemmas hlem
                       Bindings.empty TinyML.TyCtx.empty typed Runtime.Subst.id
                       ⟨hcheck_eval.1.namesDisjoint, hvars⟩
                       stRel ρRel
                       ⟨Signature.Subset.refl _, Env.agreeOn_refl⟩
                       (by intro x x' h; simp at h)
                       (by intro p hp; simp at hp)
                       hΔreg
                       hρreg
                       (GhostFns.wellTyped.empty W _ _)
                       TinyML.TyCtx.empty_closed
                       hcheck_eval
    rw [Runtime.Program.subst_id] at hcorrect
    have hctx0 : (⊢ □ stRel.sl W ρRel ∗
        Bindings.typedSubst W Bindings.empty TinyML.TyCtx.empty Runtime.Subst.id) := by
      istart
      isplitl []
      · simp [TransState.sl, howns]
        imodintro
        iempintro
      · iapply Bindings.typedSubst_empty
    simpa [hrt] using hctx0.trans hcorrect

omit [MicaGS HasLC.hasLC Sig] in
/-- End-to-end adequacy: a successful verifier run guarantees that executions
    of the program — folded into a single expression by `Runtime.Program.expr`,
    starting from the empty heap — never get stuck: every reachable expression
    is a value or can step. Derived from `Program.verify_correct` through the
    `pwp`-to-`wp` bridge and `Runtime.Program.adequacy`. -/
theorem Program.verify_adequate (reg : Verifier.Registry)
    (hSound : Verifier.Registry.Sound reg) (p : Untyped.Program Untyped.SpecBody) :
    Smt.Strategy.checks (Program.verify reg p)
      (∀ {e' : Runtime.Expr} {μ' : TinyML.Heap},
        TinyML.Steps reg.primCtx (Untyped.Program.runtime p).expr ∅ e' μ' →
        (∃ v, e' = .val v) ∨ ∃ e'' μ'', TinyML.Step reg.primCtx e' μ' e'' μ'') :=
  (Program.verify_correct reg hSound p).imp fun Hpwp _ _ hsteps =>
    (Runtime.Program.adequacy (φ := fun _ => True)
      (by intro inst; exact Hpwp.trans (pwp.wp_expr _)) hsteps).1

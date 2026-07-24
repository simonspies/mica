-- SUMMARY: End-to-end preparation and verification of programs, from typed elaboration to program-level soundness.
import Mica.TinyML.Typed
import Mica.TinyML.Untyped
import Mica.TinyML.Typing
import Mica.SeparationLogic.PrimitiveLaws
import Mica.SeparationLogic.Adequacy
import Mica.Verifier.Functions
import Mica.Verifier.SpecTranslation
import Mica.Verifier.RelationalEncoding
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Engine.Driver
import Mica.Verifier.Intrinsic
import Mica.Verifier.BoundedQuantifier

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Typed
open Verifier.RelationalEncoding (FunCtx)

private def parseSpec (reg : Verifier.Registry) (Γfn : FunCtx) (cb : (Spec.Body Typed.Expr)) :
    Except String SpecPredicate :=
  SpecTranslation.translate (Verifier.Intrinsic.sigOf reg) Γfn cb

/-- Extract typed argument names from a function's argument list. -/
private def extractArgs : List Binder → List String → Except String (List (String × TinyML.Typ))
  | [], names =>
    if names.isEmpty then .ok []
    else .error s!"spec has more arguments than function"
  | _ :: _, [] => .ok []
  | b :: rest, n :: ns => do
    let tail ← extractArgs rest ns
    .ok ((n, b.ty) :: tail)

/-- Complete a raw spec predicate with type information from a function expression. -/
def Spec.complete (sp : SpecPredicate) (e : Expr) : Except String Spec :=
  match e with
  | .fix _ argBinders retTy _ => do
    let args ← extractArgs argBinders sp.1
    .ok { args, retTy, pred := sp.2 }
  | _ => .error "Spec.complete: expected function"

/-! ## Program-level verification

Iterates over a list of declarations, verifying each one against its spec
and accumulating the spec map for use by subsequent declarations. -/

def Program.prepare (prims : Typed.Prims) (prog : Untyped.Program (Spec.Body Untyped.Expr)) :
    VerifM (TinyML.TypeEnv × Typed.Program (Spec.Body Typed.Expr)) :=
  match Typed.Program.elaborate prims TinyML.TypeEnv.empty TinyML.TyCtx.empty prog with
  | .ok prepared => .ret prepared
  | .error err => .fatal (toString err)

/-- Globally assembled metadata for declarations marked with `[@@fn]`. -/
structure RelationSpec where
  symbols : List FOL.BinaryRel
  axioms : List Axiom
  functionMap : List (TinyML.Var × String)
  delta : Signature

namespace RelationSpec

open Verifier.RelationalEncoding

def empty : RelationSpec :=
  { symbols := [], axioms := [], functionMap := [], delta := Signature.empty }

private structure RelationDecl where
  spec : RelationSpec
  res : TinyML.Var
  axs : List Axiom
  f : TinyML.Var
  rel : String
  arg : TinyML.Var
  body : Typed.Expr
  bv : Skolemize.DefVal

private def validateDecl (d : Typed.ValDecl (Spec.Body Typed.Expr)) :
    Except String (TinyML.Var × TinyML.Var × Typed.Expr) := do
  if d.declMeta.spec.isSome then
    .error s!"declaration cannot have both [@@spec] and [@@fn]"
  let f ← match d.name.name with
    | some f => .ok f
    | none => .error s!"[@@fn] requires a named declaration"
  match d.body with
  | .fix _ [arg] _ body =>
    match arg.name with
    | some x => .ok (f, x, body)
    | none => .error s!"[@@fn] requires a named unary argument"
  | .fix _ _ _ _ => .error s!"[@@fn] requires a unary function"
  | _ => .error s!"[@@fn] requires a function body"

private def extend (acc : RelationSpec) (d : Typed.ValDecl (Spec.Body Typed.Expr)) :
    Except String RelationDecl := do
  match d.declMeta.relation with
  | none => .error "internal error: expected relation declaration"
  | some rel => do
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
        let (res, bv, axs) ← Skolemize.bundle acc.functionMap acc.delta f rel arg body
        let spec := { symbols := acc.symbols ++ [SpecFn.rel rel],
                      axioms := acc.axioms ++ axs,
                      functionMap := acc.functionMap ++ [(f, rel)],
                      delta := ((acc.delta.addBinaryRel (SpecFn.rel rel)).addUnary
                                  (SpecFn.func rel)).addUnaryRel (SpecFn.defined rel) }
        .ok { spec, res, axs, f, rel, arg, body, bv }

private def declareAndAssume (acc : RelationSpec) (d : Typed.ValDecl (Spec.Body Typed.Expr)) :
    VerifM RelationSpec := do
  match d.declMeta.relation with
  | none => pure acc
  | some rel =>
      match extend acc d with
      | .error msg => VerifM.fatal msg
      | .ok info => do
          SpecFn.declare rel info.axs
          pure info.spec

/-- Declare a bounded quantifier's solver-facing triple and its defining
axioms on top of the accumulated relation spec. All freshness and membership
conditions needed by the soundness proof are checked operationally by
`validate`. -/
private def declareLifting (acc : RelationSpec) (s : Verifier.BoundedQuantifier.Lifting) :
    VerifM RelationSpec :=
  match s.validate acc.delta with
  | .error msg => VerifM.fatal msg
  | .ok _ =>
      match s.compile acc.functionMap acc.delta with
      | .error msg => VerifM.fatal msg
      | .ok body => do
          s.declare body
          pure { symbols := acc.symbols ++ [SpecFn.rel s.name],
                 axioms := acc.axioms ++ s.axioms body,
                 functionMap := acc.functionMap ++ [(s.name, s.name)],
                 delta := s.extendSignature acc.delta }

private def assembleFrom : RelationSpec → Typed.Program (Spec.Body Typed.Expr) → VerifM RelationSpec
  | acc, [] => pure acc
  | acc, d :: ds => do
      let acc' ← declareAndAssume acc d
      assembleFrom acc' ds

/-- Compile and declare the lifted bounded quantifiers in lift order. Earlier
symbols are available while compiling later bodies, which supports nesting. -/
private def assembleLiftings : RelationSpec → List Verifier.BoundedQuantifier.Lifting → VerifM RelationSpec
  | acc, [] => pure acc
  | acc, s :: ss => do
      let acc' ← declareLifting acc s
      assembleLiftings acc' ss

/-- Assemble the global relation signature and function-name map for a typed
program paired with its lifted bounded quantifiers. Quantifier symbols are
declared after all program declarations: assembly never consults specs, and
the only cross-references between lifted bodies — inner occurrences captured
by outer ones — respect the lift order, which `flatMap` preserves. -/
def assemble (pairs : List (Typed.ValDecl (Spec.Body Typed.Expr) × List Verifier.BoundedQuantifier.Lifting)) :
    VerifM RelationSpec := do
  let Δ ← VerifM.ctx (fun st => (st.decls, st.owns))
  let acc ← assembleFrom { RelationSpec.empty with delta := Δ } (pairs.map Prod.fst)
  assembleLiftings acc (pairs.flatMap Prod.snd)

/-- The invariant pack threaded through relation assembly: the accumulated
delta mirrors the declared signature, the state is spec-level (no owned
locations, no variables), and the accumulated function map is well-formed
with deterministic, split-compatible interpretations. -/
private structure Inv (acc : RelationSpec) (st : TransState) (ρ : VerifM.Env) : Prop where
  delta : acc.delta = st.decls
  owns : st.owns = []
  vars : st.decls.vars = []
  wf : st.decls.wf
  Γwf : FunCtx.wfIn acc.functionMap st.decls
  split : FunCtx.splitCompatible acc.functionMap ρ.env
  det : Relation.BinaryRelDet acc.functionMap ρ.env ρ.env

omit [MicaGS HasLC.hasLC Sig] in
/-- Declaring one relation-marked declaration preserves the assembly
invariants; the signature only grows and the environment is only extended
with fresh interpretations. -/
private theorem declareAndAssume_correct (d : Typed.ValDecl (Spec.Body Typed.Expr))
    (acc : RelationSpec) (st : TransState) (ρ : VerifM.Env)
    {Q : RelationSpec → TransState → VerifM.Env → Prop}
    (hinv : Inv acc st ρ)
    (heval : VerifM.eval (declareAndAssume acc d) st ρ Q) :
    ∃ acc' st' ρ', Inv acc' st' ρ' ∧
      st.decls.Subset st'.decls ∧ VerifM.Env.agreeOn st.decls ρ ρ' ∧
      Q acc' st' ρ' := by
  obtain ⟨hacc, howns, hvars, hwf, hΓwf, hsplit, hdet⟩ := hinv
  simp only [declareAndAssume] at heval
  cases hrel : d.declMeta.relation with
  | none =>
    simp only [hrel] at heval
    exact ⟨acc, st, ρ, ⟨hacc, howns, hvars, hwf, hΓwf, hsplit, hdet⟩,
      Signature.Subset.refl _, VerifM.Env.agreeOn_refl, VerifM.eval_ret heval⟩
  | some rel_name =>
    simp only [hrel] at heval
    cases hext : extend acc d with
    | error msg => simp only [hext] at heval; exact (VerifM.eval_fatal heval).elim
    | ok info =>
      simp only [hext] at heval
      -- Unfold `extend` once to expose its construction facts about `info`.
      obtain ⟨hf, hspec_delta, hspec_fm, hinfoEq⟩ :
          Skolemize.InfoFresh acc.delta rel_name info.arg ∧
          info.spec.delta = ((acc.delta.addBinaryRel (SpecFn.rel rel_name)).addUnary
              (SpecFn.func rel_name)).addUnaryRel (SpecFn.defined rel_name) ∧
          info.spec.functionMap = acc.functionMap ++ [(info.f, rel_name)] ∧
          Skolemize.bundle acc.functionMap acc.delta info.f rel_name info.arg info.body
            = .ok (info.res, info.bv, info.axs) := by
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
          obtain ⟨res, bv, axs⟩ := tup
          cases hext
          exact ⟨{ relFresh := hrel_in, funFresh := hfun_in, defFresh := hdef_in,
                   argFresh := harg_in, argNeRel := harg_eq_rel,
                   argNeFun := harg_eq_fun, argNeDef := harg_eq_def }, rfl, rfl, hinfoTuple⟩
      have hΓwf_acc : FunCtx.wfIn acc.functionMap acc.delta := hacc ▸ hΓwf
      have hΔwf_acc : acc.delta.wf := hacc ▸ hwf
      -- The chosen interpretations: the ground-truth relation and its split.
      set R : Relation.ValRel :=
        Relation.semrel acc.functionMap acc.delta ρ.env
          info.f rel_name info.arg info.res info.body
      set F := Skolemize.semFunc R
      set D : Srt.value.denote → Prop :=
        Skolemize.semdef acc.functionMap acc.delta ρ.env
          info.f rel_name info.arg info.res info.body info.bv
      have hgraph : ∀ a b, R a b ↔ D a ∧ F a = b := fun a b =>
        Skolemize.bundle_semrel_compatible hinfoEq hsplit hΓwf_acc hΔwf_acc hf hdet a b
      have henv : Skolemize.relSplitEnv ρ.env rel_name R D F
          = (Skolemize.defInterpEnv acc.functionMap acc.delta ρ.env
              info.f rel_name info.arg info.res info.body info.bv).updateBinaryRel
            .value .value (SpecFn.relName rel_name) R := by
        simp only [Skolemize.relSplitEnv, Skolemize.defInterpEnv, Skolemize.splitEnv]
        apply Env.ext <;> rfl
      have haxeval : ∀ ax ∈ info.axs,
          ax.formula.eval (Skolemize.relSplitEnv ρ.env rel_name R D F) := by
        rw [henv]
        exact Skolemize.bundle_eval_updateBinaryRel
          hinfoEq hsplit hΓwf_acc hΔwf_acc hf hdet R
      obtain ⟨st4, ρ4, hst4_decls, howns4, hvars4, hwf4, hsub4, hagree4,
        hΓwf4, hsplit4, hdet4, hcont⟩ :=
        SpecFn.declare_correct rel_name info.f info.axs R F D acc.delta acc.functionMap st ρ
          hf.relFresh hf.funFresh hf.defFresh hgraph hacc.symm howns hvars
          (hf.wf_addSplit hΔwf_acc) hΓwf_acc hsplit hdet
          (Skolemize.bundle_wfIn hinfoEq hΔwf_acc hΓwf_acc hf) haxeval
          (VerifM.eval_bind heval)
      have hdelta4 : info.spec.delta = st4.decls := by rw [hspec_delta, hst4_decls]
      have hΓwf4' : FunCtx.wfIn info.spec.functionMap st4.decls := by
        rw [hspec_fm]; exact hΓwf4
      have hsplit4' : FunCtx.splitCompatible info.spec.functionMap ρ4.env := by
        rw [hspec_fm]; exact hsplit4
      have hdet4' : Relation.BinaryRelDet info.spec.functionMap ρ4.env ρ4.env := by
        rw [hspec_fm]; exact hdet4
      exact ⟨info.spec, st4, ρ4,
        ⟨hdelta4, howns4, hvars4, hwf4, hΓwf4', hsplit4', hdet4'⟩,
        hsub4, hagree4, VerifM.eval_ret hcont⟩

omit [MicaGS HasLC.hasLC Sig] in
private theorem assembleFrom_correct (prog : Typed.Program (Spec.Body Typed.Expr)) :
    ∀ (acc : RelationSpec) (st : TransState) (ρ : VerifM.Env)
      {Q : RelationSpec → TransState → VerifM.Env → Prop},
      Inv acc st ρ →
      VerifM.eval (assembleFrom acc prog) st ρ Q →
      ∃ result stRel ρRel, Inv result stRel ρRel ∧
        st.decls.Subset stRel.decls ∧ VerifM.Env.agreeOn st.decls ρ ρRel ∧
        Q result stRel ρRel := by
  induction prog with
  | nil =>
    intro acc st ρ Q hinv heval
    simp only [assembleFrom] at heval
    exact ⟨acc, st, ρ, hinv, Signature.Subset.refl _, VerifM.Env.agreeOn_refl,
      VerifM.eval_ret heval⟩
  | cons d ds ih =>
    intro acc st ρ Q hinv heval
    simp only [assembleFrom] at heval
    obtain ⟨acc', st', ρ', hinv', hsub', hag', hcont⟩ :=
      declareAndAssume_correct d acc st ρ hinv (VerifM.eval_bind heval)
    obtain ⟨result, stRel, ρRel, hinvRel, hsubRel, hagRel, hQ⟩ := ih acc' st' ρ' hinv' hcont
    exact ⟨result, stRel, ρRel, hinvRel, hsub'.trans hsubRel,
      VerifM.Env.agreeOn_trans hag' (VerifM.Env.agreeOn_mono hsub' hagRel), hQ⟩

omit [MicaGS HasLC.hasLC Sig] in
/-- Compiling and declaring one lifted bounded quantifier preserves the
assembly invariants. -/
private theorem declareLifting_correct (s : Verifier.BoundedQuantifier.Lifting)
    (acc : RelationSpec) (st : TransState) (ρ : VerifM.Env)
    {Q : RelationSpec → TransState → VerifM.Env → Prop}
    (hinv : Inv acc st ρ)
    (heval : VerifM.eval (declareLifting acc s) st ρ Q) :
    ∃ acc' st' ρ', Inv acc' st' ρ' ∧
      st.decls.Subset st'.decls ∧ VerifM.Env.agreeOn st.decls ρ ρ' ∧
      Q acc' st' ρ' := by
  obtain ⟨hacc, howns, hvars, hwf, hΓwf, hsplit, hdet⟩ := hinv
  simp only [declareLifting] at heval
  cases hvalid : s.validate acc.delta with
  | error msg =>
    simp only [hvalid] at heval
    exact (VerifM.eval_fatal heval).elim
  | ok v =>
    simp only [hvalid] at heval
    cases hcompile : s.compile acc.functionMap acc.delta with
    | error msg =>
      simp only [hcompile] at heval
      exact (VerifM.eval_fatal heval).elim
    | ok body =>
      simp only [hcompile] at heval
      have hbody := Verifier.BoundedQuantifier.Lifting.compile_wfIn
        v.down (hacc ▸ hwf) (hacc ▸ hΓwf) hcompile
      obtain ⟨st4, ρ4, hdelta, howns4, hvars4, hwf4, hsub4, hagree4,
        hΓwf4, hsplit4, hdet4, hcont⟩ :=
        Verifier.BoundedQuantifier.Lifting.declare_correct s body acc.delta
          acc.functionMap st ρ v.down hbody hacc.symm howns hvars
          (hacc ▸ hwf) (hacc ▸ hΓwf) hsplit hdet (VerifM.eval_bind heval)
      exact ⟨{ symbols := acc.symbols ++ [SpecFn.rel s.name],
               axioms := acc.axioms ++ s.axioms body,
               functionMap := acc.functionMap ++ [(s.name, s.name)],
               delta := s.extendSignature acc.delta }, st4, ρ4,
        ⟨hdelta.symm, howns4, hvars4, hwf4, hΓwf4, hsplit4, hdet4⟩,
        hsub4, hagree4, VerifM.eval_ret hcont⟩

omit [MicaGS HasLC.hasLC Sig] in
private theorem assembleLiftings_correct (ss : List Verifier.BoundedQuantifier.Lifting) :
    ∀ (acc : RelationSpec) (st : TransState) (ρ : VerifM.Env)
      {Q : RelationSpec → TransState → VerifM.Env → Prop},
      Inv acc st ρ →
      VerifM.eval (assembleLiftings acc ss) st ρ Q →
      ∃ result stRel ρRel, Inv result stRel ρRel ∧
        st.decls.Subset stRel.decls ∧ VerifM.Env.agreeOn st.decls ρ ρRel ∧
        Q result stRel ρRel := by
  induction ss with
  | nil =>
    intro acc st ρ Q hinv heval
    simp only [assembleLiftings] at heval
    exact ⟨acc, st, ρ, hinv, Signature.Subset.refl _, VerifM.Env.agreeOn_refl,
      VerifM.eval_ret heval⟩
  | cons s ss ih =>
    intro acc st ρ Q hinv heval
    simp only [assembleLiftings] at heval
    obtain ⟨acc1, st1, ρ1, hinv1, hsub1, hag1, hcont1⟩ :=
      declareLifting_correct s acc st ρ hinv (VerifM.eval_bind heval)
    obtain ⟨result, stRel, ρRel, hinvRel, hsubRel, hagRel, hQ⟩ :=
      ih acc1 st1 ρ1 hinv1 hcont1
    exact ⟨result, stRel, ρRel, hinvRel, hsub1.trans hsubRel,
      VerifM.Env.agreeOn_trans hag1 (VerifM.Env.agreeOn_mono hsub1 hagRel), hQ⟩

omit [MicaGS HasLC.hasLC Sig] in
theorem assemble_correct
    (pairs : List (Typed.ValDecl (Spec.Body Typed.Expr) × List Verifier.BoundedQuantifier.Lifting))
    {st : TransState} {ρ : VerifM.Env}
    {Q : RelationSpec → TransState → VerifM.Env → Prop}
    (hvars0 : st.decls.vars = [])
    (howns0 : st.owns = [])
    (hwf0 : st.decls.wf)
    (heval : VerifM.eval (RelationSpec.assemble pairs) st ρ Q) :
    ∃ spec0 : RelationSpec, ∃ stRel ρRel,
      stRel.decls.vars = [] ∧
      stRel.owns = [] ∧
      st.decls.Subset stRel.decls ∧
      VerifM.Env.agreeOn st.decls ρ ρRel ∧
      Q { spec0 with delta := stRel.decls } stRel ρRel := by
  unfold RelationSpec.assemble at heval
  have hctx := VerifM.eval_bind heval
  obtain ⟨hassembleFrom, hownsWf, _, _⟩ := VerifM.eval_ctx hctx
  have hrest := hassembleFrom hownsWf
  have hempty_Γwf : FunCtx.wfIn empty.functionMap st.decls :=
    ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim⟩
  have hempty_split : FunCtx.splitCompatible empty.functionMap ρ.env :=
    fun _ _ h => (List.not_mem_nil h).elim
  have hempty_det : Relation.BinaryRelDet
      empty.functionMap ρ.env ρ.env :=
    fun _ _ h => (List.not_mem_nil h).elim
  obtain ⟨acc, st1, ρ1, hinv1, hsub1, hag1, hcont⟩ :=
    assembleFrom_correct (pairs.map Prod.fst) { empty with delta := st.decls } st ρ
      ⟨rfl, howns0, hvars0, hwf0, hempty_Γwf, hempty_split, hempty_det⟩
      (VerifM.eval_bind hrest)
  obtain ⟨result, stRel, ρRel, hinvRel, hsubRel, hagRel, hQ⟩ :=
    assembleLiftings_correct (pairs.flatMap Prod.snd) acc st1 ρ1 hinv1 hcont
  refine ⟨result, stRel, ρRel, hinvRel.vars, hinvRel.owns, hsub1.trans hsubRel,
    VerifM.Env.agreeOn_trans hag1 (VerifM.Env.agreeOn_mono hsub1 hagRel), ?_⟩
  have hresD := hinvRel.delta
  obtain ⟨_, _, _, _⟩ := result
  simp only at hresD; subst hresD
  exact hQ

end RelationSpec

/-- Check an individual declaration. Each declaration's `checkSpec` runs inside a `seq` bracket so its
    declarations and assertions don't pollute subsequent verifications. -/
def ValDecl.check (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (Γfn : FunCtx)
    (S : SpecMap) (d : Typed.ValDecl (Spec.Body Typed.Expr)) : VerifM Spec := do
  let specExpr ← match d.declMeta.spec with
    | some e => .ret e
    | none => .fatal "declaration has no spec"
  let sp ← match parseSpec reg Γfn specExpr with
  | .ok a => .ret a
  | .error msg => .fatal msg
  let spec ← match Spec.complete sp d.body with
    | .ok s => .ret s
    | .error e => .fatal e
  let () ← match Spec.checkWf spec Δ_spec with
    | .ok () => .ret ()
    | .error msg => .fatal msg
  VerifM.seq (checkSpec reg Θ Δ_spec S d.body spec) (pure spec)

/-- Check a `let _ = e` declaration: just compile `e` for safety, no spec. -/
def ValDecl.checkExpr (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (d : Typed.ValDecl (Spec.Body Typed.Expr)) : VerifM Unit :=
  VerifM.seq (do let _ ← compile reg Θ Δ_spec S [] TinyML.TyCtx.empty d.body; pure ()) (pure ())

/-- Verify all declarations in a program, accumulating specs as we go. -/
def Program.check (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (Γfn : FunCtx) :
    SpecMap → Typed.Program (Spec.Body Typed.Expr) → VerifM Unit
  | _, [] => pure ()
  | S, d :: ds => do
    match d.name.name, d.declMeta.spec with
    | none, none =>
      ValDecl.checkExpr reg Θ Δ_spec S d
      Program.check reg Θ Δ_spec Γfn S ds
    | some n, none =>
    -- Named declaration without a spec: skip if it's a function definition
    -- (no code executes), otherwise check it. Erase any old spec for this
    -- name since the new binding shadows it.
      if d.body.isFunc then
        Program.check reg Θ Δ_spec Γfn (S.erase n) ds
      else
        ValDecl.checkExpr reg Θ Δ_spec S d
        Program.check reg Θ Δ_spec Γfn (S.erase n) ds
    | _, _ =>
      let spec ← ValDecl.check reg Θ Δ_spec Γfn S d
      let S' := match d.name.name with
        | some name => S.insert name spec
        | none => S
      Program.check reg Θ Δ_spec Γfn S' ds

def Program.verify (reg : Verifier.Registry) (prog : Untyped.Program (Spec.Body Untyped.Expr)) : Smt.Strategy Smt.Strategy.Outcome :=
  VerifM.strategy do
    let (Θ, typed) ← Program.prepare reg.sigs prog
    match Verifier.BoundedQuantifier.run typed with
    | .error msg => VerifM.fatal msg
    | .ok pairs => do
        Verifier.Registry.introduceRegistry reg
        let relations ← RelationSpec.assemble pairs
        Program.check reg Θ relations.delta relations.functionMap ∅ (pairs.map Prod.fst)

/-! ## Correctness -/

omit [MicaGS HasLC.hasLC Sig] in
theorem Program.prepare_correct (prims : Typed.Prims)
    (prog : Untyped.Program (Spec.Body Untyped.Expr))
    (st : TransState) (ρ : VerifM.Env)
    {Q : (TinyML.TypeEnv × Typed.Program (Spec.Body Typed.Expr)) → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (Program.prepare prims prog) st ρ Q) :
    ∃ Θ typed, Typed.Program.runtime typed = Untyped.Program.runtime prog ∧ Q (Θ, typed) st ρ := by
  unfold Program.prepare at heval
  cases helab : Typed.Program.elaborate prims TinyML.TypeEnv.empty TinyML.TyCtx.empty prog with
  | error err =>
    simp [helab] at heval
    exact (VerifM.eval_fatal heval).elim
  | ok prepared =>
    rcases prepared with ⟨Θ, typed⟩
    refine ⟨Θ, typed, Typed.Program.elaborate_runtime prims TinyML.TypeEnv.empty TinyML.TyCtx.empty prog helab, ?_⟩
    simp [helab] at heval
    exact VerifM.eval_ret heval

theorem ValDecl.checkExpr_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (W : TinyML.World) (hW : W.pctx = reg.primCtx)
    (S : SpecMap) (d : Typed.ValDecl (Spec.Body Typed.Expr)) (γ : Runtime.Subst)
    (hSwf : S.wfIn W.Δ_spec) (hwf : W.wf)
    (st : TransState) (ρ : VerifM.Env)
    (hag : W.agrees st.decls ρ.env)
    (hΔreg : Verifier.Registry.symSubset reg W.Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg W.ρ_spec)
    {Q : Unit → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (ValDecl.checkExpr reg W.Θ W.Δ_spec S d) st ρ Q) :
    (□ st.sl W ρ ∗ S.satisfiedBy W γ ⊢ Φ) →
    □ st.sl W ρ ∗ S.satisfiedBy W γ ⊢ wp W.pctx (d.body.runtime.subst γ) (fun _ => Φ) := by
  intro Hent
  simp only [ValDecl.checkExpr] at heval
  have ⟨hinner, _⟩ := VerifM.eval_seq heval
  have hcompile := VerifM.eval_bind hinner
  have hcomp :=
    compile_correct reg hSound d.body W iprop(□ st.sl W ρ ∗ Φ) S [] TinyML.TyCtx.empty st ρ γ
    (fun x st' ρ' => VerifM.eval (pure ()) st' ρ' (fun _ _ _ => True))
    (fun _ => Φ)
    hW
    hcompile
    (fun _ _ h => by simp at h)
    (fun _ h => by simp at h)
    hSwf hwf
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
  iintro ⟨#Hsl, #Hspec⟩
  isplitl [Hsl]
  · iexact Hsl
  · isplitl []
    · iexact Hspec
    · isplitl []
      · iapply Bindings.typedSubst_nil
      · isplitl [Hsl]
        · iexact Hsl
        · iapply Hent
          isplitl [Hsl]
          · iexact Hsl
          · iexact Hspec

theorem ValDecl.check_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (W : TinyML.World) (hW : W.pctx = reg.primCtx) (Γfn : FunCtx)
    (S : SpecMap) (d : Typed.ValDecl (Spec.Body Typed.Expr)) (γ : Runtime.Subst)
    (hSwf : S.wfIn W.Δ_spec) (hwf : W.wf)
    (st : TransState) (ρ : VerifM.Env)
    (hag : W.agrees st.decls ρ.env)
    (hΔreg : Verifier.Registry.symSubset reg W.Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg W.ρ_spec)
    {Q : Spec → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (ValDecl.check reg W.Θ W.Δ_spec Γfn S d) st ρ Q) :
    ∃ spec, spec.wfIn W.Δ_spec ∧
            (□ st.sl W ρ ∗ S.satisfiedBy W γ ⊢ wp W.pctx (d.body.runtime.subst γ) (fun v => spec.isPrecondFor W v)) ∧
            Q spec st ρ := by
  simp only [ValDecl.check] at heval
  cases hspec : d.declMeta.spec with
  | none =>
    simp only [hspec] at heval
    exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim
  | some specExpr =>
    simp only [hspec] at heval
    have h1 := VerifM.eval_ret (VerifM.eval_bind heval)
    cases hparse : parseSpec reg Γfn specExpr with
    | error msg =>
      simp only [hparse] at h1
      exact (VerifM.eval_fatal (VerifM.eval_bind h1)).elim
    | ok sp =>
      simp only [hparse] at h1
      have h2 := VerifM.eval_ret (VerifM.eval_bind h1)
      cases hcomplete : Spec.complete sp d.body with
      | error msg =>
        simp only [hcomplete] at h2
        exact (VerifM.eval_fatal (VerifM.eval_bind h2)).elim
      | ok spec =>
        simp only [hcomplete] at h2
        have h3 := VerifM.eval_ret (VerifM.eval_bind h2)
        cases hcheckWf : Spec.checkWf spec W.Δ_spec with
        | error msg =>
          simp only [hcheckWf] at h3
          exact (VerifM.eval_fatal (VerifM.eval_bind h3)).elim
        | ok u =>
          simp only [hcheckWf] at h3
          have h4 := VerifM.eval_ret (VerifM.eval_bind h3)
          have hswf : spec.wfIn W.Δ_spec := Spec.checkWf_ok (by cases u; exact hcheckWf)
          have ⟨hcheckSpec, hpure⟩ := VerifM.eval_seq h4
          exact ⟨spec, hswf,
            by
              have hcheck :=
                checkSpec_correct reg hSound W hW S d.body spec γ
                  hswf hSwf hwf st ρ hag hΔreg hρreg hcheckSpec
              refine BIBase.Entails.trans ?_ hcheck
              istart
              iintro ⟨#Hsl, #Hspec⟩
              isplitl [Hsl]
              · iexact Hsl
              · iexact Hspec,
                 VerifM.eval_ret hpure⟩

theorem Program.check_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (W : TinyML.World) (hW : W.pctx = reg.primCtx) (Γfn : FunCtx)
    (S : SpecMap) (prog : Typed.Program (Spec.Body Typed.Expr)) (γ : Runtime.Subst)
    (hSwf : S.wfIn W.Δ_spec) (hwf : W.wf)
    (st : TransState) (ρ : VerifM.Env)
    (hag : W.agrees st.decls ρ.env)
    (hΔreg : Verifier.Registry.symSubset reg W.Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg W.ρ_spec) :
    VerifM.eval (Program.check reg W.Θ W.Δ_spec Γfn S prog) st ρ (fun _ _ _ => True) →
    □ st.sl W ρ ∗ S.satisfiedBy W γ ⊢ pwp W.pctx ((Typed.Program.runtime prog).subst γ) := by
  induction prog generalizing S γ st ρ with
  | nil =>
    intro _
    simp only [Typed.Program.runtime, List.map_nil, Runtime.Program.subst]
    refine BIBase.Entails.trans ?_ pwp_nil
    istart
    iintro _
    iempintro
  | cons d ds ih =>
    intro heval
    have hpwp_unfold :
        wp W.pctx (d.body.runtime.subst γ) (fun v =>
          pwp W.pctx ((Typed.Program.runtime ds).subst (Runtime.Subst.updateBinder d.name.runtime v γ)))
        ⊢ pwp W.pctx ((Typed.Program.runtime (d :: ds)).subst γ) := by
      simp only [Typed.Program.runtime, Typed.ValDecl.runtime,
        Runtime.Program.subst, Runtime.Decl.subst, List.map_cons]
      refine BIBase.Entails.trans (wp.mono fun v => ?_) pwp_cons
      rw [Runtime.Program.subst_remove_update]
      exact .rfl
    refine BIBase.Entails.trans ?_ hpwp_unfold
    simp only [Program.check] at heval
    cases hname : d.name.name with
    | none =>
      -- unnamed: pwp continuation does not depend on `v`
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ := by
        intro v; simp [Binder.runtime_of_name_none hname, Runtime.Subst.updateBinder]
      cases hspec : d.declMeta.spec with
      | none =>
        -- unnamed, no spec
        simp only [hname, hspec] at heval
        have hbind := VerifM.eval_bind heval
        have ⟨_, hcont⟩ := VerifM.eval_seq hbind
        have hih := ih S γ hSwf st ρ hag (VerifM.eval_ret hcont)
        have hwp := ValDecl.checkExpr_correct reg hSound W hW S d γ hSwf hwf st ρ hag hΔreg hρreg hbind hih
        refine hwp.trans (wp.mono ?_)
        intro v; rw [hupd v]; exact .rfl
      | some _ =>
        -- unnamed, with spec
        simp only [hname, hspec] at heval
        obtain ⟨spec, _, hwp, hcont⟩ :=
          ValDecl.check_correct reg hSound W hW Γfn S d γ hSwf hwf st ρ hag hΔreg hρreg (VerifM.eval_bind heval)
        have hih := ih S γ hSwf st ρ hag hcont
        refine SpatialContext.wp_strengthen_persistent hwp ?_
        intro v
        rw [hupd v]
        exact wand_intro (sep_elim_left.trans hih)
    | some n =>
      have hname_rt : d.name.runtime = .named n := Binder.runtime_of_name_some hname
      have herase : S.eraseBinder d.name = S.erase n := by simp [SpecMap.eraseBinder, hname]
      have hinsert : ∀ s, S.insertBinder d.name s = S.insert n s := by
        intro s; simp [SpecMap.insertBinder, hname]
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ.update n v := by
        intro v; simp [hname_rt, Runtime.Subst.updateBinder]
      cases hspec : d.declMeta.spec with
      | none =>
        simp only [hname, hspec] at heval
        split at heval
        · -- named, no spec, function value
          rename_i hfunc
          obtain ⟨self, args, retTy, body, hbody⟩ := Expr.isFunc_elim hfunc
          have hbody_rt : d.body.runtime.subst γ =
              Runtime.Expr.fix self.runtime (args.map (·.runtime))
                (body.runtime.subst ((γ.remove' self.runtime).removeAll'
                  (args.map (·.runtime)))) := by
            rw [hbody]; conv_lhs => unfold Expr.runtime
            simp only [Runtime.Expr.subst_fix]
          rw [hbody_rt]
          set fval := Runtime.Val.fix self.runtime (args.map (·.runtime))
            (body.runtime.subst ((γ.remove' self.runtime).removeAll'
              (args.map (·.runtime))))
          apply SpatialContext.wp_func
          rw [hupd fval]
          have heval' : VerifM.eval (Program.check reg W.Θ W.Δ_spec Γfn (S.erase n) ds) st ρ (fun _ _ _ => True) := by
            convert heval
          have hih := ih (S.erase n) (γ.update n fval)
            (SpecMap.wfIn_erase hSwf) st ρ hag heval'
          refine BIBase.Entails.trans ?_ hih
          istart
          iintro ⟨#Hsl, #Hspec⟩
          isplitl [Hsl]
          · iexact Hsl
          · iapply SpecMap.satisfiedBy_erase
            iexact Hspec
        · -- named, no spec, not a function
          have hbind := VerifM.eval_bind heval
          have ⟨_, hcont⟩ := VerifM.eval_seq hbind
          have hcont' : VerifM.eval (Program.check reg W.Θ W.Δ_spec Γfn (S.erase n) ds) st ρ (fun _ _ _ => True) :=
            VerifM.eval_ret hcont
          have hwp := ValDecl.checkExpr_correct reg hSound W hW S d γ hSwf hwf st ρ hag hΔreg hρreg hbind
            (Φ := iprop(emp)) (by istart; iintro _; iempintro)
          refine SpatialContext.wp_strengthen_persistent hwp ?_
          intro v
          rw [hupd v]
          have hih := ih (S.erase n) (γ.update n v) (SpecMap.wfIn_erase hSwf) st ρ hag hcont'
          exact wand_intro (sep_elim_left.trans <| by
            refine BIBase.Entails.trans ?_ hih
            istart
            iintro ⟨#Hsl, #Hspec⟩
            isplitl [Hsl]
            · iexact Hsl
            · iapply SpecMap.satisfiedBy_erase
              iexact Hspec)
      | some _ =>
        simp only [hname, hspec] at heval
        obtain ⟨spec, hswf, hwp, hcont⟩ :=
          ValDecl.check_correct reg hSound W hW Γfn S d γ hSwf hwf st ρ hag hΔreg hρreg (VerifM.eval_bind heval)
        have hcont' : VerifM.eval (Program.check reg W.Θ W.Δ_spec Γfn (S.insert n spec) ds) st ρ (fun _ _ _ => True) := by
          convert hcont
        refine SpatialContext.wp_strengthen_persistent hwp ?_
        intro v
        rw [hupd v]
        have hih := ih (S.insert n spec) (γ.update n v)
          (SpecMap.wfIn_insert hSwf hswf) st ρ hag hcont'
        have hstep : (□ st.sl W ρ ∗ S.satisfiedBy W γ) ∗ spec.isPrecondFor W v ⊢
            pwp W.pctx ((Typed.Program.runtime ds).subst (γ.update n v)) := by
          refine BIBase.Entails.trans ?_ hih
          istart
          iintro ⟨Hctx, Hpre⟩
          icases Hctx with ⟨#Hsl, #Hspec⟩
          isplitl [Hsl]
          · iexact Hsl
          · iapply SpecMap.satisfiedBy_insert_update
            isplitl [Hspec]
            · iexact Hspec
            · iexact Hpre
        exact wand_intro hstep


omit [MicaGS HasLC.hasLC Sig] in
theorem Program.verify_correct (reg : Verifier.Registry)
    (hSound : Verifier.Registry.Sound reg) (p : Untyped.Program (Spec.Body Untyped.Expr)) :
    Smt.Strategy.checks (Program.verify reg p)
      (∀ [MicaGS HasLC.hasLC Sig], ⊢ pwp reg.primCtx (Untyped.Program.runtime p)) := by
  simp only [Smt.Strategy.checks, Program.verify, VerifM.strategy]
  intro st' heval _inst
  have h1 := ScopedM.strategy_eval_initial_implies_ScopedM_eval heval
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
                        let (Θ, typed) ← Program.prepare reg.sigs p
                        match Verifier.BoundedQuantifier.run typed with
                        | .error msg => VerifM.fatal msg
                        | .ok pairs => do
                            Verifier.Registry.introduceRegistry reg
                            let relations ← RelationSpec.assemble pairs
                            Program.check reg Θ relations.delta relations.functionMap ∅
                              (pairs.map Prod.fst))
                      TransState.init VerifM.Env.init ctx_mid
                      (ScopedM.eval_declareConst hverif)
                      TransState.init_holdsFor TransState.init_wf
    have hbind := VerifM.eval_bind hverifM
    obtain ⟨Θ, typed, hrt, hrest⟩ :=
      Program.prepare_correct reg.sigs p TransState.init VerifM.Env.init hbind
    -- Peel the bounded-quantifier pass: a rewrite failure is fatal, and a success
    -- leaves the program's runtime erasure unchanged.
    dsimp only at hrest
    cases hrun : Verifier.BoundedQuantifier.run typed with
    | error msg =>
      rw [hrun] at hrest
      exact (VerifM.eval_fatal hrest).elim
    | ok pairs =>
    rw [hrun] at hrest
    have hrt : Typed.Program.runtime (pairs.map Prod.fst) = Untyped.Program.runtime p :=
      (Verifier.BoundedQuantifier.run_runtime hrun).trans hrt
    -- Peel the registry setup from the continuation generically.
    have hsetup_bind := VerifM.eval_bind hrest
    obtain ⟨st_setup, ρ_setup, _hΔsub, hdep_setup, hvars_setup_eq, howns_setup,
      _hasserts, hstable_setup, _hρagree, hcheck_eval⟩ :=
      Verifier.Registry.eval_introduceRegistry reg hSound hsetup_bind
    have hassemble := VerifM.eval_bind hcheck_eval
    have hvars_setup : st_setup.decls.vars = [] := by
      rw [hvars_setup_eq]
      rfl
    obtain ⟨spec0, stRel, ρRel, hvars, howns, hsub_setup_rel, hag_setup_rel, hcheck_eval⟩ :=
      RelationSpec.assemble_correct pairs hvars_setup howns_setup hcheck_eval.1.namesDisjoint hassemble
    have hΔreg : Verifier.Registry.symSubset reg stRel.decls := by
      intro i hi
      exact (Verifier.Registry.extendWithSym_subset_sigOf_of_mem hi).trans
        (hdep_setup.trans hsub_setup_rel)
    have hρreg : Verifier.Registry.symAgree reg ρRel.env := by
      intro i hi
      exact hstable_setup ρRel hag_setup_rel i hi
    -- The meta-level world: the registry's operational context, the type
    -- environment the elaborator produced, and the specification model the
    -- relational declarations left in the state.
    let W : TinyML.World :=
      { pctx := reg.primCtx, Θ, Δ_spec := stRel.decls, ρ_spec := ρRel.env }
    have hcorrect := Program.check_correct reg hSound W rfl spec0.functionMap
                       ∅ (pairs.map Prod.fst) Runtime.Subst.id
                       (SpecMap.empty_wfIn _)
                       ⟨hcheck_eval.1.namesDisjoint, hvars⟩
                       stRel ρRel
                       ⟨Signature.Subset.refl _, VerifM.Env.agreeOn_refl⟩
                       hΔreg
                       hρreg
                       hcheck_eval
    rw [Runtime.Program.subst_id] at hcorrect
    have hctx0 : (⊢ □ stRel.sl W ρRel ∗
        SpecMap.satisfiedBy W (∅ : SpecMap) Runtime.Subst.id) := by
      istart
      isplitl []
      · simp [TransState.sl, howns]
        imodintro
        iempintro
      · iapply SpecMap.empty_satisfiedBy
    simpa [hrt] using hctx0.trans hcorrect

omit [MicaGS HasLC.hasLC Sig] in
/-- End-to-end adequacy: a successful verifier run guarantees that executions
    of the program — folded into a single expression by `Runtime.Program.expr`,
    starting from the empty heap — never get stuck: every reachable expression
    is a value or can step. Derived from `Program.verify_correct` through the
    `pwp`-to-`wp` bridge and `Runtime.Program.adequacy`. -/
theorem Program.verify_adequate (reg : Verifier.Registry)
    (hSound : Verifier.Registry.Sound reg) (p : Untyped.Program (Spec.Body Untyped.Expr)) :
    Smt.Strategy.checks (Program.verify reg p)
      (∀ {e' : Runtime.Expr} {μ' : TinyML.Heap},
        TinyML.Steps reg.primCtx (Untyped.Program.runtime p).expr ∅ e' μ' →
        (∃ v, e' = .val v) ∨ ∃ e'' μ'', TinyML.Step reg.primCtx e' μ' e'' μ'') :=
  (Program.verify_correct reg hSound p).imp fun Hpwp _ _ hsteps =>
    (Runtime.Program.adequacy (φ := fun _ => True)
      (by intro inst; exact Hpwp.trans (pwp.wp_expr _)) hsteps).1

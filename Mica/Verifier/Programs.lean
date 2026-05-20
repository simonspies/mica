-- SUMMARY: End-to-end preparation and verification of programs, from typed elaboration to program-level soundness.
import Mica.TinyML.Typed
import Mica.TinyML.Untyped
import Mica.TinyML.Typing
import Mica.SeparationLogic.PrimitiveLaws
import Mica.Verifier.Functions
import Mica.Frontend.SpecParser
import Mica.Verifier.SpecTranslation
import Mica.Verifier.RelationalEncoding
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Engine.Driver

open Iris Iris.BI
open Typed

private def parseSpec (Δ_spec : Signature) (e : Untyped.Expr) :
    Except String SpecPredicate := do
  let spec ← Spec.parse e
  SpecTranslation.translate Δ_spec.binaryRel spec

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

def Program.prepare (prog : Untyped.Program Untyped.Expr) :
    VerifM (TinyML.TypeEnv × Typed.Program Untyped.Expr) :=
  match Typed.Program.elaborate TinyML.TypeEnv.empty TinyML.TyCtx.empty prog with
  | .ok prepared => .ret prepared
  | .error err => .fatal (toString err)

/-- Globally assembled metadata for declarations marked with `[@@fn fn]`. -/
structure RelationSpec where
  symbols : List FOL.BinaryRel
  axioms : List Formula
  functionMap : List (TinyML.Var × String)
  delta : Signature

namespace RelationSpec

open Verifier.RelationalEncoding

def empty : RelationSpec :=
  { symbols := [], axioms := [], functionMap := [], delta := Signature.empty }

private structure RelationDecl where
  spec : RelationSpec
  res : TinyML.Var
  axs : List Formula
  f : TinyML.Var
  rel : String
  arg : TinyML.Var
  body : Typed.Expr
  bv : Skolemize.DefVal

private def validateDecl (d : Typed.ValDecl Untyped.Expr) (rel : String) :
    Except String (TinyML.Var × TinyML.Var × Typed.Expr) := do
  if d.declMeta.spec.isSome then
    .error s!"declaration cannot have both [@@spec] and [@@fn {rel}]"
  let f ← match d.name.name with
    | some f => .ok f
    | none => .error s!"[@@fn {rel}] requires a named declaration"
  match d.body with
  | .fix _ [arg] _ body =>
    match arg.name with
    | some x => .ok (f, x, body)
    | none => .error s!"[@@fn {rel}] requires a named unary argument"
  | .fix _ _ _ _ => .error s!"[@@fn {rel}] requires a unary function"
  | _ => .error s!"[@@fn {rel}] requires a function body"

private def extend (acc : RelationSpec) (d : Typed.ValDecl Untyped.Expr) :
    Except String RelationDecl := do
  match d.declMeta.relation with
  | none => .error "internal error: expected relation declaration"
  | some rel => do
      let (f, arg, body) ← validateDecl d rel
      let relName := SpecFn.relName rel
      let funName := SpecFn.funcName rel
      let defName := SpecFn.defName rel
      if relName ∈ acc.delta.allNames then
        .error s!"derived relation name '{relName}' for [@@fn {rel}] conflicts with an existing symbol"
      else if funName ∈ acc.delta.allNames then
        .error s!"derived value-function name '{funName}' for [@@fn {rel}] conflicts with an existing symbol"
      else if defName ∈ acc.delta.allNames then
        .error s!"derived definedness name '{defName}' for [@@fn {rel}] conflicts with an existing symbol"
      else if arg ∈ acc.delta.allNames then
        .error s!"[@@fn {rel}] argument name '{arg}' conflicts with a global symbol"
      else if arg = relName then
        .error s!"[@@fn {rel}] argument name '{arg}' clashes with derived relation name"
      else if arg = funName then
        .error s!"[@@fn {rel}] argument name '{arg}' clashes with derived value-function name"
      else if arg = defName then
        .error s!"[@@fn {rel}] argument name '{arg}' clashes with derived definedness name"
      else
        let (res, bv, axs) ← Skolemize.bundle acc.functionMap acc.delta f rel arg body
        let spec := { symbols := acc.symbols ++ [SpecFn.rel rel],
                      axioms := acc.axioms ++ axs,
                      functionMap := acc.functionMap ++ [(f, rel)],
                      delta := ((acc.delta.addBinaryRel (SpecFn.rel rel)).addUnary
                                  (SpecFn.func rel)).addUnaryRel (SpecFn.defined rel) }
        .ok { spec, res, axs, f, rel, arg, body, bv }

private def addDecl (acc : RelationSpec) (d : Typed.ValDecl Untyped.Expr) :
    Except String RelationSpec := do
  match d.declMeta.relation with
  | none => .ok acc
  | some _ => return (← extend acc d).spec

private def declareAndAssume (acc : RelationSpec) (d : Typed.ValDecl Untyped.Expr) :
    VerifM RelationSpec := do
  match d.declMeta.relation with
  | none => pure acc
  | some rel =>
      match extend acc d with
      | .error msg => VerifM.fatal msg
      | .ok info => do
          VerifM.declBinaryRelExact (SpecFn.rel rel)
          VerifM.declUnaryExact (SpecFn.func rel)
          VerifM.declUnaryRelExact (SpecFn.defined rel)
          VerifM.assumeAll info.axs
          pure info.spec

private def assembleFrom : RelationSpec → Typed.Program Untyped.Expr → VerifM RelationSpec
  | acc, [] => pure acc
  | acc, d :: ds => do
      let acc' ← declareAndAssume acc d
      assembleFrom acc' ds

/-- Assemble the global relation signature and function-name map for a typed program. -/
def assemble (prog : Typed.Program Untyped.Expr) : VerifM RelationSpec :=
  assembleFrom RelationSpec.empty prog

private theorem assembleFrom_correct (prog : Typed.Program Untyped.Expr) :
    ∀ (acc : RelationSpec) (st : TransState) (ρ : VerifM.Env)
      {Q : RelationSpec → TransState → VerifM.Env → Prop},
      acc.delta = st.decls →
      st.owns = [] →
      st.decls.vars = [] →
      st.decls.wf →
      FunCtx.wfIn acc.functionMap st.decls →
      FunCtx.splitCompatible acc.functionMap ρ.env →
      Relation.BinaryRelDet acc.functionMap ρ.env ρ.env →
      VerifM.eval (assembleFrom acc prog) st ρ Q →
      ∃ result stRel ρRel,
        stRel.decls.vars = [] ∧ stRel.owns = [] ∧
        result.delta = stRel.decls ∧ Q result stRel ρRel := by
  induction prog with
  | nil =>
    intro acc st ρ Q hacc howns hvars _ _ _ _ heval
    simp only [assembleFrom] at heval
    exact ⟨acc, st, ρ, hvars, howns, hacc, VerifM.eval_ret heval⟩
  | cons d ds ih =>
    intro acc st ρ Q hacc howns hvars hwf hΓwf hsplit hdet heval
    simp only [assembleFrom] at heval
    have hbind := VerifM.eval_bind _ _ _ _ heval
    simp only [declareAndAssume] at hbind
    cases hrel : d.declMeta.relation with
    | none =>
      simp only [hrel] at hbind
      exact ih acc st ρ hacc howns hvars hwf hΓwf hsplit hdet (VerifM.eval_ret hbind)
    | some rel_name =>
      simp only [hrel] at hbind
      cases hext : extend acc d with
      | error msg => simp only [hext] at hbind; exact (VerifM.eval_fatal hbind).elim
      | ok info =>
        simp only [hext] at hbind
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
        -- Three declaration steps; introduce the chosen interpretations.
        set R : Relation.ValRel :=
          Relation.semrel acc.functionMap acc.delta ρ.env
            info.f rel_name info.arg info.res info.body
        set F := Skolemize.semFunc R
        set D : Srt.value.denote → Prop :=
          Skolemize.semdef acc.functionMap acc.delta ρ.env
            info.f rel_name info.arg info.res info.body info.bv
        obtain ⟨_, hbcont⟩ := VerifM.eval_declBinaryRelExact (VerifM.eval_bind _ _ _ _ hbind)
        obtain ⟨_, hbcont3⟩ := VerifM.eval_declUnaryExact (VerifM.eval_bind _ _ _ _ (hbcont R))
        obtain ⟨_, hbcont5⟩ := VerifM.eval_declUnaryRelExact (VerifM.eval_bind _ _ _ _ (hbcont3 F))
        have hbind7 := VerifM.eval_bind _ _ _ _ (hbcont5 D)
        -- Δ after the three declarations.
        set Δext : Signature :=
          ((acc.delta.addBinaryRel (SpecFn.rel rel_name)).addUnary
            (SpecFn.func rel_name)).addUnaryRel (SpecFn.defined rel_name)
        set st3 : TransState :=
          { st with decls := ((st.decls.addBinaryRel (SpecFn.rel rel_name)).addUnary
              (SpecFn.func rel_name)).addUnaryRel (SpecFn.defined rel_name) }
        set ρ3 : VerifM.Env :=
          ((ρ.updateBinaryRel .value .value (SpecFn.relName rel_name) R).updateUnary
              .value .value (SpecFn.funcName rel_name) F).updateUnaryRel
            .value (SpecFn.defName rel_name) D
        have hst3_decls : st3.decls = Δext := by simp only [st3, Δext, hacc]
        -- Axiom well-formedness via bundle_wfIn.
        have hax_wf_acc := Skolemize.bundle_wfIn hinfoEq hΔwf_acc hΓwf_acc hf
        have hax_wf : ∀ ax ∈ info.axs, ax.wfIn st3.decls :=
          fun ax hmem => hst3_decls ▸ hax_wf_acc ax hmem
        -- ρ3.env vs (defInterpEnv ...).updateBinaryRel R.
        have hρ3_env_eq :
            ρ3.env = (Skolemize.defInterpEnv acc.functionMap acc.delta ρ.env
                info.f rel_name info.arg info.res info.body info.bv).updateBinaryRel
                  .value .value (SpecFn.relName rel_name) R := by
          simp only [ρ3, VerifM.Env.updateUnaryRel_env, VerifM.Env.updateUnary_env,
            VerifM.Env.updateBinaryRel_env, Skolemize.defInterpEnv, Skolemize.splitEnv]
          apply Env.ext <;> rfl
        have hax_eval : ∀ ax ∈ info.axs, ax.eval ρ3.env := fun ax hmem => by
          rw [hρ3_env_eq]
          exact Skolemize.bundle_eval_updateBinaryRel
            hinfoEq hsplit hΓwf_acc hΔwf_acc hf hdet R ax hmem
        obtain ⟨st4, hst4_decls, hst4_owns, hpure_pre⟩ :=
          VerifM.eval_assumeAll hbind7 hax_wf hax_eval
        -- Reestablish invariants and apply IH.
        have hst4_owns_eq : st4.owns = [] := by rw [hst4_owns]; exact howns
        have hst4_vars : st4.decls.vars = [] := by
          rw [hst4_decls, hst3_decls]; show acc.delta.vars = []; rw [hacc]; exact hvars
        have hst4_wf : st4.decls.wf := by
          rw [hst4_decls, hst3_decls]; exact hf.wf_addSplit hΔwf_acc
        have hnewAcc_delta : info.spec.delta = st4.decls := by
          rw [hspec_delta, hst4_decls, hst3_decls]
        -- Agreement on acc.delta: the three new symbols are fresh.
        have hagree_old : Env.agreeOn acc.delta ρ.env ρ3.env := by
          rw [hρ3_env_eq]
          unfold Skolemize.defInterpEnv Skolemize.splitEnv
          refine Env.agreeOn_trans
            (Env.agreeOn_update_fresh_unary (ρ := ρ.env) (u := SpecFn.func rel_name)
              (f := F) hf.funFresh) ?_
          refine Env.agreeOn_trans
            (Env.agreeOn_update_fresh_unaryRel (u := SpecFn.defined rel_name)
              (f := D) hf.defFresh) ?_
          exact Env.agreeOn_update_fresh_binaryRel (b := SpecFn.rel rel_name) (f := R) hf.relFresh
        have hΔext_sub : acc.delta.Subset Δext :=
          ((Signature.Subset.subset_addBinaryRel _ _).trans
            (Signature.Subset.subset_addUnary _ _)).trans
            (Signature.Subset.subset_addUnaryRel _ _)
        -- FunCtx.wfIn on the extended map.
        have hnewΓwf : FunCtx.wfIn info.spec.functionMap st4.decls := by
          rw [hst4_decls, hst3_decls, hspec_fm]
          refine ⟨?_, ?_⟩
          · intro x rel hxr
            rcases List.mem_append.mp hxr with hold | hnew
            · exact hΔext_sub.binaryRel _ (hΓwf_acc.rel x rel hold)
            · simp at hnew; obtain ⟨_, rfl⟩ := hnew
              show SpecFn.rel rel ∈ Δext.binaryRel
              exact List.Mem.head _
          · intro x rel hxr
            rcases List.mem_append.mp hxr with hold | hnew
            · obtain ⟨hu, hr⟩ := hΓwf_acc.split x rel hold
              exact ⟨hΔext_sub.unary _ hu, hΔext_sub.unaryRel _ hr⟩
            · simp at hnew; obtain ⟨_, rfl⟩ := hnew
              exact ⟨List.Mem.head _, List.Mem.head _⟩
        -- New invariants on ρ3.
        have hsplit_new : FunCtx.splitCompatible info.spec.functionMap ρ3.env := by
          rw [hspec_fm]
          intro f rel hxr x y
          rcases List.mem_append.mp hxr with hold | hnew
          · obtain ⟨hu_mem, hr_mem⟩ := hΓwf_acc.split f rel hold
            obtain ⟨her, hec, hed⟩ :=
              SpecFn.agreeOn hagree_old (hΓwf_acc.rel f rel hold) hu_mem hr_mem
            rw [← her, ← hec, ← hed]; exact hsplit f rel hold x y
          · simp at hnew; obtain ⟨_, rfl⟩ := hnew
            rw [hρ3_env_eq]
            have hgraph := Skolemize.bundle_semrel_compatible
              hinfoEq hsplit hΓwf_acc hΔwf_acc hf hdet x y
            simp only [SpecFn.evalRelates, SpecFn.evalCall, SpecFn.evalDefined,
              SpecFn.rel, SpecFn.func, SpecFn.defined,
              Skolemize.defInterpEnv, Skolemize.splitEnv,
              Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel]
            exact hgraph
        have hdet_new : Relation.BinaryRelDet info.spec.functionMap ρ3.env ρ3.env := by
          rw [hspec_fm]
          intro f rel hxr vin y₁ y₂ h₁ h₂
          rcases List.mem_append.mp hxr with hold | hnew
          · obtain ⟨hu_mem, hr_mem⟩ := hΓwf_acc.split f rel hold
            obtain ⟨her, _, _⟩ :=
              SpecFn.agreeOn hagree_old (hΓwf_acc.rel f rel hold) hu_mem hr_mem
            rw [← her] at h₁ h₂
            exact hdet f rel hold vin y₁ y₂ h₁ h₂
          · simp at hnew; obtain ⟨_, rfl⟩ := hnew
            rw [hρ3_env_eq] at h₁ h₂
            simp only [SpecFn.evalRelates, SpecFn.rel, Env.updateBinaryRel] at h₁ h₂
            exact Skolemize.bundle_semrel_functional
              hinfoEq hΓwf_acc hΔwf_acc hf ρ.env hdet vin y₁ y₂ h₁ h₂
        exact ih info.spec st4 ρ3 hnewAcc_delta hst4_owns_eq hst4_vars hst4_wf
          hnewΓwf hsplit_new hdet_new (VerifM.eval_ret hpure_pre)

theorem assemble_correct (typed : Typed.Program Untyped.Expr)
    {Q : RelationSpec → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (RelationSpec.assemble typed) TransState.empty VerifM.Env.empty Q) :
    ∃ spec0 : RelationSpec, ∃ stRel ρRel,
      stRel.decls.vars = [] ∧
      stRel.owns = [] ∧
      Q { spec0 with delta := stRel.decls } stRel ρRel := by
  unfold RelationSpec.assemble at heval
  have hempty_Γwf : FunCtx.wfIn empty.functionMap TransState.empty.decls :=
    ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim⟩
  have hempty_split : FunCtx.splitCompatible empty.functionMap VerifM.Env.empty.env :=
    fun _ _ h => (List.not_mem_nil h).elim
  have hempty_det : Relation.BinaryRelDet
      empty.functionMap VerifM.Env.empty.env VerifM.Env.empty.env :=
    fun _ _ h => (List.not_mem_nil h).elim
  obtain ⟨result, stRel, ρRel, hvars, howns, hresD, hQ⟩ :=
    assembleFrom_correct typed empty TransState.empty VerifM.Env.empty
      rfl rfl rfl Signature.wf_empty hempty_Γwf hempty_split hempty_det heval
  refine ⟨result, stRel, ρRel, hvars, howns, ?_⟩
  obtain ⟨_, _, _, _⟩ := result
  simp only at hresD; subst hresD
  exact hQ

end RelationSpec

/-- Check an individual declaration. Each declaration's `checkSpec` runs inside a `seq` bracket so its
    declarations and assertions don't pollute subsequent verifications. -/
def ValDecl.check (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
    (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) : VerifM Spec := do
  let specExpr ← match d.declMeta.spec with
    | some e => .ret e
    | none => .fatal "declaration has no spec"
  let sp ← match parseSpec Δ_spec specExpr with
  | .ok a => .ret a
  | .error msg => .fatal msg
  let spec ← match Spec.complete sp d.body with
    | .ok s => .ret s
    | .error e => .fatal e
  let () ← match Spec.checkWf spec Δ_spec with
    | .ok () => .ret ()
    | .error msg => .fatal msg
  VerifM.seq (checkSpec Θ Δ_spec S d.body spec) (pure spec)

/-- Check a `let _ = e` declaration: just compile `e` for safety, no spec. -/
def ValDecl.checkExpr (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) : VerifM Unit :=
  VerifM.seq (do let _ ← compile Θ Δ_spec S [] TinyML.TyCtx.empty d.body; pure ()) (pure ())

/-- Verify all declarations in a program, accumulating specs as we go. -/
def Program.check (Θ : TinyML.TypeEnv) (Δ_spec : Signature) :
    SpecMap → Typed.Program Untyped.Expr → VerifM Unit
  | _, [] => pure ()
  | S, d :: ds => do
    match d.name.name, d.declMeta.spec with
    | none, none =>
      ValDecl.checkExpr Θ Δ_spec S d
      Program.check Θ Δ_spec S ds
    | some n, none =>
    -- Named declaration without a spec: skip if it's a function definition
    -- (no code executes), otherwise check it. Erase any old spec for this
    -- name since the new binding shadows it.
      if d.body.isFunc then
        Program.check Θ Δ_spec (S.erase n) ds
      else
        ValDecl.checkExpr Θ Δ_spec S d
        Program.check Θ Δ_spec (S.erase n) ds
    | _, _ =>
      let spec ← ValDecl.check Θ Δ_spec S d
      let S' := match d.name.name with
        | some name => S.insert name spec
        | none => S
      Program.check Θ Δ_spec S' ds

/-- Empty relation signature used before global relation assembly. -/
def Δ_spec : Signature := Signature.empty

/-- Initial verifier environment threaded through program verification.
    Proper relation support must populate this with relation interpretations. -/
def ρ_spec : VerifM.Env := VerifM.Env.empty

def Program.verify (prog : Untyped.Program Untyped.Expr) : Smt.Strategy Smt.Strategy.Outcome :=
  VerifM.strategy do
    let (Θ, typed) ← Program.prepare prog
    let relations ← RelationSpec.assemble typed
    Program.check Θ relations.delta ∅ typed

/-! ## Correctness -/

theorem Program.prepare_correct (prog : Untyped.Program Untyped.Expr)
    (st : TransState) (ρ : VerifM.Env)
    {Q : (TinyML.TypeEnv × Typed.Program Untyped.Expr) → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (Program.prepare prog) st ρ Q) :
    ∃ Θ typed, Typed.Program.runtime typed = Untyped.Program.runtime prog ∧ Q (Θ, typed) st ρ := by
  unfold Program.prepare at heval
  cases helab : Typed.Program.elaborate TinyML.TypeEnv.empty TinyML.TyCtx.empty prog with
  | error err =>
    simp [helab] at heval
    exact (VerifM.eval_fatal heval).elim
  | ok prepared =>
    rcases prepared with ⟨Θ, typed⟩
    refine ⟨Θ, typed, Typed.Program.elaborate_runtime TinyML.TypeEnv.empty TinyML.TyCtx.empty prog helab, ?_⟩
    simp [helab] at heval
    exact VerifM.eval_ret heval

theorem ValDecl.checkExpr_correct (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) (γ : Runtime.Subst)
    (hSwf : S.wfIn Δ_spec) (hΔwf : Δ_spec.wf) (hΔvars : Δ_spec.vars = [])
    (st : TransState) (ρ : VerifM.Env)
    (hΔspec : Δ_spec.Subset st.decls) (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec ρ)
    {Q : Unit → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (ValDecl.checkExpr Θ Δ_spec S d) st ρ Q) :
    (□ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ ⊢ Φ) →
    □ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ ⊢ wp (d.body.runtime.subst γ) (fun _ => Φ) := by
  intro Hent
  simp only [ValDecl.checkExpr] at heval
  have ⟨hinner, _⟩ := VerifM.eval_seq heval
  have hcompile := VerifM.eval_bind _ _ _ _ hinner
  have hcomp :=
    compile_correct d.body Θ iprop(□ st.sl ρ ∗ Φ) S [] TinyML.TyCtx.empty st ρ γ Δ_spec ρ_spec
    (fun x st' ρ' => VerifM.eval (pure ()) st' ρ' (fun _ _ _ => True))
    (fun _ => Φ)
    hcompile
    (fun _ _ h => by simp at h)
    (fun _ h => by simp at h)
    hSwf hΔwf hΔvars
    hΔspec
    hρspec
    (fun _ _ _ _ _ _ _ => by
      istart
      iintro ⟨_, _, Hctx⟩
      icases Hctx with ⟨_, HΦ⟩
      iexact HΦ)
  refine (BIBase.Entails.trans ?_ hcomp)
  istart
  iintro ⟨□Hsl, □Hspec⟩
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

theorem ValDecl.check_correct (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (d : Typed.ValDecl Untyped.Expr) (γ : Runtime.Subst)
    (hSwf : S.wfIn Δ_spec) (hΔwf : Δ_spec.wf) (hΔvars : Δ_spec.vars = [])
    (st : TransState) (ρ : VerifM.Env)
    (hΔspec : Δ_spec.Subset st.decls) (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec ρ)
    {Q : Spec → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (ValDecl.check Θ Δ_spec S d) st ρ Q) :
    ∃ spec, spec.wfIn Δ_spec ∧
            (□ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ ⊢ wp (d.body.runtime.subst γ) (fun v => spec.isPrecondFor Θ Δ_spec ρ_spec v)) ∧
            Q spec st ρ := by
  simp only [ValDecl.check] at heval
  cases hspec : d.declMeta.spec with
  | none =>
    simp only [hspec] at heval
    exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
  | some specExpr =>
    simp only [hspec] at heval
    have h1 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ heval)
    cases hparse : parseSpec Δ_spec specExpr with
    | error msg =>
      simp only [hparse] at h1
      exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ h1)).elim
    | ok sp =>
      simp only [hparse] at h1
      have h2 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ h1)
      cases hcomplete : Spec.complete sp d.body with
      | error msg =>
        simp only [hcomplete] at h2
        exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ h2)).elim
      | ok spec =>
        simp only [hcomplete] at h2
        have h3 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ h2)
        cases hwf : Spec.checkWf spec Δ_spec with
        | error msg =>
          simp only [hwf] at h3
          exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ h3)).elim
        | ok u =>
          simp only [hwf] at h3
          have h4 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ h3)
          have hswf : spec.wfIn Δ_spec := Spec.checkWf_ok (by cases u; exact hwf)
          have ⟨hcheckSpec, hpure⟩ := VerifM.eval_seq h4
          exact ⟨spec, hswf,
            by
              have hcheck :=
                checkSpec_correct Θ S d.body spec γ Δ_spec ρ_spec
                  hswf hSwf hΔwf hΔvars st ρ hΔspec hρspec hcheckSpec
              refine BIBase.Entails.trans ?_ hcheck
              istart
              iintro ⟨□Hsl, □Hspec⟩
              isplitl [Hsl]
              · iexact Hsl
              · iexact Hspec,
                 VerifM.eval_ret hpure⟩

theorem Program.check_correct (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (prog : Typed.Program Untyped.Expr) (γ : Runtime.Subst)
    (hSwf : S.wfIn Δ_spec) (hΔwf : Δ_spec.wf) (hΔvars : Δ_spec.vars = [])
    (st : TransState) (ρ : VerifM.Env)
    (hΔspec : Δ_spec.Subset st.decls) (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec ρ) :
    VerifM.eval (Program.check Θ Δ_spec S prog) st ρ (fun _ _ _ => True) →
    □ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ ⊢ pwp ((Typed.Program.runtime prog).subst γ) := by
  induction prog generalizing S γ st ρ with
  | nil =>
    intro _
    simp only [Typed.Program.runtime, List.map_nil, Runtime.Program.subst, pwp]
    istart
    iintro _
    iemp_intro
  | cons d ds ih =>
    intro heval
    have hpwp_unfold : pwp ((Typed.Program.runtime (d :: ds)).subst γ) ⊣⊢
        wp (d.body.runtime.subst γ) (fun v =>
          pwp ((Typed.Program.runtime ds).subst (Runtime.Subst.updateBinder d.name.runtime v γ))) := by
      simp [Typed.Program.runtime, Typed.ValDecl.runtime,
        Runtime.Program.subst, Runtime.Decl.subst, Runtime.Program.subst_remove_update]
    refine BIBase.Entails.trans ?_ hpwp_unfold.2
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
        have hbind := VerifM.eval_bind _ _ _ _ heval
        have ⟨_, hcont⟩ := VerifM.eval_seq hbind
        have hih := ih S γ hSwf st ρ hΔspec hρspec (VerifM.eval_ret hcont)
        have hwp := ValDecl.checkExpr_correct Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec hbind hih
        refine hwp.trans (wp.mono ?_)
        intro v; rw [hupd v]; exact .rfl
      | some _ =>
        -- unnamed, with spec
        simp only [hname, hspec] at heval
        obtain ⟨spec, _, hwp, hcont⟩ :=
          ValDecl.check_correct Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec (VerifM.eval_bind _ _ _ _ heval)
        have hih := ih S γ hSwf st ρ hΔspec hρspec hcont
        refine SpatialContext.wp_strengthen_persistent hwp ?_
        intro v
        rw [hupd v]
        exact wand_intro (sep_elim_l.trans hih)
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
          have heval' : VerifM.eval (Program.check Θ Δ_spec (S.erase n) ds) st ρ (fun _ _ _ => True) := by
            convert heval
          have hih := ih (S.erase n) (γ.update n fval)
            (SpecMap.wfIn_erase hSwf) st ρ hΔspec hρspec heval'
          refine BIBase.Entails.trans ?_ hih
          istart
          iintro ⟨□Hsl, □Hspec⟩
          isplitl [Hsl]
          · iexact Hsl
          · iapply SpecMap.satisfiedBy_erase
            iexact Hspec
        · -- named, no spec, not a function
          have hbind := VerifM.eval_bind _ _ _ _ heval
          have ⟨_, hcont⟩ := VerifM.eval_seq hbind
          have hcont' : VerifM.eval (Program.check Θ Δ_spec (S.erase n) ds) st ρ (fun _ _ _ => True) :=
            VerifM.eval_ret hcont
          have hwp := ValDecl.checkExpr_correct Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec hbind
            (Φ := iprop(emp)) (by istart; iintro _; iemp_intro)
          refine SpatialContext.wp_strengthen_persistent hwp ?_
          intro v
          rw [hupd v]
          have hih := ih (S.erase n) (γ.update n v) (SpecMap.wfIn_erase hSwf) st ρ hΔspec hρspec hcont'
          exact wand_intro (sep_elim_l.trans <| by
            refine BIBase.Entails.trans ?_ hih
            istart
            iintro ⟨□Hsl, □Hspec⟩
            isplitl [Hsl]
            · iexact Hsl
            · iapply SpecMap.satisfiedBy_erase
              iexact Hspec)
      | some _ =>
        simp only [hname, hspec] at heval
        obtain ⟨spec, hswf, hwp, hcont⟩ :=
          ValDecl.check_correct Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec (VerifM.eval_bind _ _ _ _ heval)
        have hcont' : VerifM.eval (Program.check Θ Δ_spec (S.insert n spec) ds) st ρ (fun _ _ _ => True) := by
          convert hcont
        refine SpatialContext.wp_strengthen_persistent hwp ?_
        intro v
        rw [hupd v]
        have hih := ih (S.insert n spec) (γ.update n v)
          (SpecMap.wfIn_insert hSwf hswf) st ρ hΔspec hρspec hcont'
        have hstep : (□ st.sl ρ ∗ S.satisfiedBy Θ Δ_spec ρ_spec γ) ∗ spec.isPrecondFor Θ Δ_spec ρ_spec v ⊢
            pwp ((Typed.Program.runtime ds).subst (γ.update n v)) := by
          refine BIBase.Entails.trans ?_ hih
          istart
          iintro ⟨Hctx, Hpre⟩
          icases Hctx with ⟨□Hsl, □Hspec⟩
          isplitl [Hsl]
          · iexact Hsl
          · iapply SpecMap.satisfiedBy_insert_update
            isplitl [Hspec]
            · iexact Hspec
            · iexact Hpre
        exact wand_intro hstep


theorem Program.verify_correct (p : Untyped.Program Untyped.Expr) :
  Smt.Strategy.checks (Program.verify p) (⊢ pwp (Untyped.Program.runtime p)) := by
  simp only [Smt.Strategy.checks, Program.verify, VerifM.strategy]
  intro st' heval
  have h1 := ScopedM.strategy_eval_initial_implies_ScopedM_eval heval
  obtain ⟨a, ctx_mid, hverif, hcont⟩ := ScopedM.eval_bind h1
  match a with
  | .error e =>
    cases e <;> simp [ScopedM.eval_ret] at hcont
  | .ok () =>
    have hholdsFor : TransState.holdsFor TransState.empty VerifM.Env.empty :=
      fun φ hφ => by simp [TransState.empty] at hφ
    have hwf : TransState.wf TransState.empty :=
      ⟨fun φ hφ => by simp [TransState.empty] at hφ,
       by simp [TransState.empty, Signature.empty, Signature.allNames],
       fun a ha => by simp [TransState.empty] at ha⟩
    have hverifM := VerifM.eval_of_translate
                      (do
                        let (Θ, typed) ← Program.prepare p
                        let relations ← RelationSpec.assemble typed
                        Program.check Θ relations.delta ∅ typed)
                      TransState.empty VerifM.Env.empty ctx_mid hverif hholdsFor hwf
    have hbind := VerifM.eval_bind _ _ _ _ hverifM
    obtain ⟨Θ, typed, hrt, hrest⟩ := Program.prepare_correct p TransState.empty VerifM.Env.empty hbind
    have hassemble := VerifM.eval_bind _ _ _ _ hrest
    obtain ⟨spec0, stRel, ρRel, hvars, howns, hcheck⟩ :=
      RelationSpec.assemble_correct typed hassemble
    have hcorrect := Program.check_correct Θ stRel.decls ρRel
                       ∅ typed Runtime.Subst.id
                       (SpecMap.empty_wfIn _)
                       hcheck.1.namesDisjoint
                       hvars
                       stRel ρRel
                       (Signature.Subset.refl _)
                       VerifM.Env.agreeOn_refl
                       hcheck
    rw [Runtime.Program.subst_id] at hcorrect
    have hctx0 : (⊢ □ stRel.sl ρRel ∗
        SpecMap.satisfiedBy Θ stRel.decls ρRel (∅ : SpecMap) Runtime.Subst.id) := by
      istart
      isplitl []
      · simp [TransState.sl, howns]
        imodintro
        iemp_intro
      · iapply SpecMap.empty_satisfiedBy
    simpa [hrt] using hctx0.trans hcorrect

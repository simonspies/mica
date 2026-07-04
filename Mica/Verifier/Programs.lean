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

def Program.prepare (prog : Untyped.Program (Spec.Body Untyped.Expr)) :
    VerifM (TinyML.TypeEnv × Typed.Program (Spec.Body Typed.Expr)) :=
  match Typed.Program.elaborate TinyML.TypeEnv.empty TinyML.TyCtx.empty prog with
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

private def addDecl (acc : RelationSpec) (d : Typed.ValDecl (Spec.Body Typed.Expr)) :
    Except String RelationSpec := do
  match d.declMeta.relation with
  | none => .ok acc
  | some _ => return (← extend acc d).spec

private def declareAndAssume (acc : RelationSpec) (d : Typed.ValDecl (Spec.Body Typed.Expr)) :
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
          VerifM.assumeAxioms info.axs
          pure info.spec

private def assembleFrom : RelationSpec → Typed.Program (Spec.Body Typed.Expr) → VerifM RelationSpec
  | acc, [] => pure acc
  | acc, d :: ds => do
      let acc' ← declareAndAssume acc d
      assembleFrom acc' ds

/-- Assemble the global relation signature and function-name map for a typed program. -/
def assemble (prog : Typed.Program (Spec.Body Typed.Expr)) : VerifM RelationSpec := do
  let Δ ← VerifM.ctx (fun st => (st.decls, st.owns))
  assembleFrom { RelationSpec.empty with delta := Δ } prog

omit [MicaGS HasLC.hasLC Sig] in
private theorem assembleFrom_correct (prog : Typed.Program (Spec.Body Typed.Expr)) :
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
        st.decls.Subset stRel.decls ∧ VerifM.Env.agreeOn st.decls ρ ρRel ∧
        result.delta = stRel.decls ∧ Q result stRel ρRel := by
  induction prog with
  | nil =>
    intro acc st ρ Q hacc howns hvars _ _ _ _ heval
    simp only [assembleFrom] at heval
    exact ⟨acc, st, ρ, hvars, howns, Signature.Subset.refl _, VerifM.Env.agreeOn_refl,
      hacc, VerifM.eval_ret heval⟩
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
        have hax_wf : ∀ ax ∈ info.axs, ax.formula.wfIn st3.decls :=
          fun ax hmem => hst3_decls ▸ hax_wf_acc ax hmem
        -- ρ3.env vs (defInterpEnv ...).updateBinaryRel R.
        have hρ3_env_eq :
            ρ3.env = (Skolemize.defInterpEnv acc.functionMap acc.delta ρ.env
                info.f rel_name info.arg info.res info.body info.bv).updateBinaryRel
                  .value .value (SpecFn.relName rel_name) R := by
          simp only [ρ3, VerifM.Env.updateUnaryRel_env, VerifM.Env.updateUnary_env,
            VerifM.Env.updateBinaryRel_env, Skolemize.defInterpEnv, Skolemize.splitEnv]
          apply Env.ext <;> rfl
        have hax_eval : ∀ ax ∈ info.axs, ax.formula.eval ρ3.env := fun ax hmem => by
          rw [hρ3_env_eq]
          exact Skolemize.bundle_eval_updateBinaryRel
            hinfoEq hsplit hΓwf_acc hΔwf_acc hf hdet R ax hmem
        obtain ⟨st4, hst4_decls, hst4_owns, _, hpure_pre⟩ :=
          VerifM.eval_assumeAxioms hbind7 hax_wf hax_eval
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
        obtain ⟨result, stRel, ρRel, hvarsRel, hownsRel, hsubRel, hagRel, hresD, hQ⟩ :=
          ih info.spec st4 ρ3 hnewAcc_delta hst4_owns_eq hst4_vars hst4_wf
          hnewΓwf hsplit_new hdet_new (VerifM.eval_ret hpure_pre)
        have hsub_old : st.decls.Subset st4.decls := by
          rw [hst4_decls, hst3_decls, ← hacc]
          exact hΔext_sub
        have hag_old : VerifM.Env.agreeOn st.decls ρ ρ3 := by
          rw [← hacc]
          exact hagree_old
        exact ⟨result, stRel, ρRel, hvarsRel, hownsRel, hsub_old.trans hsubRel,
          VerifM.Env.agreeOn_trans hag_old (VerifM.Env.agreeOn_mono hsub_old hagRel),
          hresD, hQ⟩

omit [MicaGS HasLC.hasLC Sig] in
theorem assemble_correct (typed : Typed.Program (Spec.Body Typed.Expr))
    {st : TransState} {ρ : VerifM.Env}
    {Q : RelationSpec → TransState → VerifM.Env → Prop}
    (hvars0 : st.decls.vars = [])
    (howns0 : st.owns = [])
    (hwf0 : st.decls.wf)
    (heval : VerifM.eval (RelationSpec.assemble typed) st ρ Q) :
    ∃ spec0 : RelationSpec, ∃ stRel ρRel,
      stRel.decls.vars = [] ∧
      stRel.owns = [] ∧
      st.decls.Subset stRel.decls ∧
      VerifM.Env.agreeOn st.decls ρ ρRel ∧
      Q { spec0 with delta := stRel.decls } stRel ρRel := by
  unfold RelationSpec.assemble at heval
  have hctx := VerifM.eval_bind _ _ _ _ heval
  obtain ⟨hassembleFrom, hownsWf, _, _⟩ := VerifM.eval_ctx hctx
  have hrest := hassembleFrom hownsWf
  have hempty_Γwf : FunCtx.wfIn empty.functionMap st.decls :=
    ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim⟩
  have hempty_split : FunCtx.splitCompatible empty.functionMap ρ.env :=
    fun _ _ h => (List.not_mem_nil h).elim
  have hempty_det : Relation.BinaryRelDet
      empty.functionMap ρ.env ρ.env :=
    fun _ _ h => (List.not_mem_nil h).elim
  obtain ⟨result, stRel, ρRel, hvars, howns, hsub, hag, hresD, hQ⟩ :=
    assembleFrom_correct typed { empty with delta := st.decls } st ρ
      rfl howns0 hvars0 hwf0 hempty_Γwf hempty_split hempty_det hrest
  refine ⟨result, stRel, ρRel, hvars, howns, hsub, hag, ?_⟩
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

/-- Empty relation signature used before global relation assembly. -/
def Δ_spec : Signature := Signature.empty

/-- Initial verifier environment threaded through program verification.
    Proper relation support must populate this with relation interpretations. -/
def ρ_spec : VerifM.Env := VerifM.Env.empty

def Program.verify (reg : Verifier.Registry) (prog : Untyped.Program (Spec.Body Untyped.Expr)) : Smt.Strategy Smt.Strategy.Outcome :=
  VerifM.strategy do
    let (Θ, typed) ← Program.prepare prog
    Verifier.Registry.introduceRegistry reg
    let relations ← RelationSpec.assemble typed
    Program.check reg Θ relations.delta relations.functionMap ∅ typed

/-! ## Correctness -/

omit [MicaGS HasLC.hasLC Sig] in
theorem Program.prepare_correct (prog : Untyped.Program (Spec.Body Untyped.Expr))
    (st : TransState) (ρ : VerifM.Env)
    {Q : (TinyML.TypeEnv × Typed.Program (Spec.Body Typed.Expr)) → TransState → VerifM.Env → Prop}
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

theorem ValDecl.checkExpr_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (d : Typed.ValDecl (Spec.Body Typed.Expr)) (γ : Runtime.Subst)
    (hSwf : S.wfIn Δ_spec) (hΔwf : Δ_spec.wf) (hΔvars : Δ_spec.vars = [])
    (st : TransState) (ρ : VerifM.Env)
    (hΔspec : Δ_spec.Subset st.decls) (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec ρ)
    (hΔreg : Verifier.Registry.symSubset reg Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg ρ_spec.env)
    {Q : Unit → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (ValDecl.checkExpr reg Θ Δ_spec S d) st ρ Q) :
    (□ st.sl Θ ρ ∗ S.satisfiedBy reg.primCtx Θ Δ_spec ρ_spec γ ⊢ Φ) →
    □ st.sl Θ ρ ∗ S.satisfiedBy reg.primCtx Θ Δ_spec ρ_spec γ ⊢ wp reg.primCtx (d.body.runtime.subst γ) (fun _ => Φ) := by
  intro Hent
  simp only [ValDecl.checkExpr] at heval
  have ⟨hinner, _⟩ := VerifM.eval_seq heval
  have hcompile := VerifM.eval_bind _ _ _ _ hinner
  have hcomp :=
    compile_correct reg hSound d.body Θ iprop(□ st.sl Θ ρ ∗ Φ) S [] TinyML.TyCtx.empty st ρ γ Δ_spec ρ_spec
    (fun x st' ρ' => VerifM.eval (pure ()) st' ρ' (fun _ _ _ => True))
    (fun _ => Φ)
    hcompile
    (fun _ _ h => by simp at h)
    (fun _ h => by simp at h)
    hSwf hΔwf hΔvars
    hΔspec
    hρspec
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
    (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (Γfn : FunCtx)
    (ρ_spec : VerifM.Env)
    (S : SpecMap) (d : Typed.ValDecl (Spec.Body Typed.Expr)) (γ : Runtime.Subst)
    (hSwf : S.wfIn Δ_spec) (hΔwf : Δ_spec.wf) (hΔvars : Δ_spec.vars = [])
    (st : TransState) (ρ : VerifM.Env)
    (hΔspec : Δ_spec.Subset st.decls) (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec ρ)
    (hΔreg : Verifier.Registry.symSubset reg Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg ρ_spec.env)
    {Q : Spec → TransState → VerifM.Env → Prop}
    (heval : VerifM.eval (ValDecl.check reg Θ Δ_spec Γfn S d) st ρ Q) :
    ∃ spec, spec.wfIn Δ_spec ∧
            (□ st.sl Θ ρ ∗ S.satisfiedBy reg.primCtx Θ Δ_spec ρ_spec γ ⊢ wp reg.primCtx (d.body.runtime.subst γ) (fun v => spec.isPrecondFor reg.primCtx Θ Δ_spec ρ_spec v)) ∧
            Q spec st ρ := by
  simp only [ValDecl.check] at heval
  cases hspec : d.declMeta.spec with
  | none =>
    simp only [hspec] at heval
    exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
  | some specExpr =>
    simp only [hspec] at heval
    have h1 := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ heval)
    cases hparse : parseSpec reg Γfn specExpr with
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
                checkSpec_correct reg hSound Θ S d.body spec γ Δ_spec ρ_spec
                  hswf hSwf hΔwf hΔvars st ρ hΔspec hρspec hΔreg hρreg hcheckSpec
              refine BIBase.Entails.trans ?_ hcheck
              istart
              iintro ⟨#Hsl, #Hspec⟩
              isplitl [Hsl]
              · iexact Hsl
              · iexact Hspec,
                 VerifM.eval_ret hpure⟩

theorem Program.check_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (Γfn : FunCtx)
    (ρ_spec : VerifM.Env)
    (S : SpecMap) (prog : Typed.Program (Spec.Body Typed.Expr)) (γ : Runtime.Subst)
    (hSwf : S.wfIn Δ_spec) (hΔwf : Δ_spec.wf) (hΔvars : Δ_spec.vars = [])
    (st : TransState) (ρ : VerifM.Env)
    (hΔspec : Δ_spec.Subset st.decls) (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec ρ)
    (hΔreg : Verifier.Registry.symSubset reg Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg ρ_spec.env) :
    VerifM.eval (Program.check reg Θ Δ_spec Γfn S prog) st ρ (fun _ _ _ => True) →
    □ st.sl Θ ρ ∗ S.satisfiedBy reg.primCtx Θ Δ_spec ρ_spec γ ⊢ pwp reg.primCtx ((Typed.Program.runtime prog).subst γ) := by
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
        wp reg.primCtx (d.body.runtime.subst γ) (fun v =>
          pwp reg.primCtx ((Typed.Program.runtime ds).subst (Runtime.Subst.updateBinder d.name.runtime v γ)))
        ⊢ pwp reg.primCtx ((Typed.Program.runtime (d :: ds)).subst γ) := by
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
        have hbind := VerifM.eval_bind _ _ _ _ heval
        have ⟨_, hcont⟩ := VerifM.eval_seq hbind
        have hih := ih S γ hSwf st ρ hΔspec hρspec (VerifM.eval_ret hcont)
        have hwp := ValDecl.checkExpr_correct reg hSound Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec hΔreg hρreg hbind hih
        refine hwp.trans (wp.mono ?_)
        intro v; rw [hupd v]; exact .rfl
      | some _ =>
        -- unnamed, with spec
        simp only [hname, hspec] at heval
        obtain ⟨spec, _, hwp, hcont⟩ :=
          ValDecl.check_correct reg hSound Θ Δ_spec Γfn ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec hΔreg hρreg (VerifM.eval_bind _ _ _ _ heval)
        have hih := ih S γ hSwf st ρ hΔspec hρspec hcont
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
          have heval' : VerifM.eval (Program.check reg Θ Δ_spec Γfn (S.erase n) ds) st ρ (fun _ _ _ => True) := by
            convert heval
          have hih := ih (S.erase n) (γ.update n fval)
            (SpecMap.wfIn_erase hSwf) st ρ hΔspec hρspec heval'
          refine BIBase.Entails.trans ?_ hih
          istart
          iintro ⟨#Hsl, #Hspec⟩
          isplitl [Hsl]
          · iexact Hsl
          · iapply SpecMap.satisfiedBy_erase
            iexact Hspec
        · -- named, no spec, not a function
          have hbind := VerifM.eval_bind _ _ _ _ heval
          have ⟨_, hcont⟩ := VerifM.eval_seq hbind
          have hcont' : VerifM.eval (Program.check reg Θ Δ_spec Γfn (S.erase n) ds) st ρ (fun _ _ _ => True) :=
            VerifM.eval_ret hcont
          have hwp := ValDecl.checkExpr_correct reg hSound Θ Δ_spec ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec hΔreg hρreg hbind
            (Φ := iprop(emp)) (by istart; iintro _; iempintro)
          refine SpatialContext.wp_strengthen_persistent hwp ?_
          intro v
          rw [hupd v]
          have hih := ih (S.erase n) (γ.update n v) (SpecMap.wfIn_erase hSwf) st ρ hΔspec hρspec hcont'
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
          ValDecl.check_correct reg hSound Θ Δ_spec Γfn ρ_spec S d γ hSwf hΔwf hΔvars st ρ hΔspec hρspec hΔreg hρreg (VerifM.eval_bind _ _ _ _ heval)
        have hcont' : VerifM.eval (Program.check reg Θ Δ_spec Γfn (S.insert n spec) ds) st ρ (fun _ _ _ => True) := by
          convert hcont
        refine SpatialContext.wp_strengthen_persistent hwp ?_
        intro v
        rw [hupd v]
        have hih := ih (S.insert n spec) (γ.update n v)
          (SpecMap.wfIn_insert hSwf hswf) st ρ hΔspec hρspec hcont'
        have hstep : (□ st.sl Θ ρ ∗ S.satisfiedBy reg.primCtx Θ Δ_spec ρ_spec γ) ∗ spec.isPrecondFor reg.primCtx Θ Δ_spec ρ_spec v ⊢
            pwp reg.primCtx ((Typed.Program.runtime ds).subst (γ.update n v)) := by
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
                        let (Θ, typed) ← Program.prepare p
                        Verifier.Registry.introduceRegistry reg
                        let relations ← RelationSpec.assemble typed
                        Program.check reg Θ relations.delta relations.functionMap ∅ typed)
                      TransState.init VerifM.Env.init ctx_mid
                      (ScopedM.eval_declareConst hverif)
                      TransState.init_holdsFor TransState.init_wf
    have hbind := VerifM.eval_bind _ _ _ _ hverifM
    obtain ⟨Θ, typed, hrt, hrest⟩ := Program.prepare_correct p TransState.init VerifM.Env.init hbind
    -- Peel the registry setup from the continuation generically.
    have hsetup_bind := VerifM.eval_bind _ _ _ _ hrest
    obtain ⟨st_setup, ρ_setup, _hΔsub, hdep_setup, hvars_setup_eq, howns_setup,
      _hasserts, hstable_setup, _hρagree, hcheck_eval⟩ :=
      Verifier.Registry.eval_introduceRegistry reg hSound hsetup_bind
    have hassemble := VerifM.eval_bind _ _ _ _ hcheck_eval
    have hvars_setup : st_setup.decls.vars = [] := by
      rw [hvars_setup_eq]
      rfl
    obtain ⟨spec0, stRel, ρRel, hvars, howns, hsub_setup_rel, hag_setup_rel, hcheck_eval⟩ :=
      RelationSpec.assemble_correct typed hvars_setup howns_setup hcheck_eval.1.namesDisjoint hassemble
    have hΔreg : Verifier.Registry.symSubset reg stRel.decls := by
      intro i hi
      exact (Verifier.Registry.extendWithSym_subset_sigOf_of_mem hi).trans
        (hdep_setup.trans hsub_setup_rel)
    have hρreg : Verifier.Registry.symAgree reg ρRel.env := by
      intro i hi
      exact hstable_setup ρRel hag_setup_rel i hi
    have hcorrect := Program.check_correct reg hSound Θ stRel.decls spec0.functionMap ρRel
                       ∅ typed Runtime.Subst.id
                       (SpecMap.empty_wfIn _)
                       hcheck_eval.1.namesDisjoint
                       hvars
                       stRel ρRel
                       (Signature.Subset.refl _)
                       VerifM.Env.agreeOn_refl
                       hΔreg
                       hρreg
                       hcheck_eval
    rw [Runtime.Program.subst_id] at hcorrect
    have hctx0 : (⊢ □ stRel.sl Θ ρRel ∗
        SpecMap.satisfiedBy reg.primCtx Θ stRel.decls ρRel (∅ : SpecMap) Runtime.Subst.id) := by
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

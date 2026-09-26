-- SUMMARY: The environment and the scope the compilers work in, with the invariants that tie them to a world and a verifier state.
import Mica.Verifier.Lemma
import Mica.Verifier.Intrinsic

open Iris Iris.BI

namespace Verifier

/-! ## Environment -/

structure Env where
  registry         : Registry
  typeDeclarations : TinyML.TypeEnv
  signature        : Signature
  lemmas           : Lemmas
  specFunctions    : RelationalEncoding.FunCtx

structure Env.wf (env : Env) (W : TinyML.World) : Prop where
  sound            : env.registry.Sound
  world            : W.wf
  primitives       : W.pctx = env.registry.primCtx
  typeDeclarations : W.Θ = env.typeDeclarations
  signature        : W.Δ_spec = env.signature
  lemmas           : env.lemmas.Sound W.Δ_spec W.ρ_spec
  symbols          : env.registry.symSubset W.Δ_spec
  interpretations  : env.registry.symAgree W.ρ_spec

/-- None of the conditions mentions the type assignment. -/
theorem Env.wf.eta {env : Env} {W : TinyML.World} (h : env.wf W) (η : TinyML.SemTypeAssign) :
    env.wf { W with eta := η } :=
  { h with world := h.world.eta η }

/-! ## Scope -/

structure Scope where
  ghostFns        : GhostFns
  ghostBindings   : Bindings
  runtimeBindings : Bindings
  typingContext   : TinyML.TyCtx

namespace Scope

def bindRuntime (S : Scope) (x : TinyML.Var) (c : Decl.Const) (ty : TinyML.Typ) : Scope :=
  { ghostFns := S.ghostFns.remove x
    ghostBindings := S.ghostBindings.remove x
    runtimeBindings := (x, c) :: S.runtimeBindings
    typingContext := S.typingContext.extend x ty }

/-- A ghost function of the same name stays: the ghost binding shadows it by
    lookup order. -/
def bindGhost (S : Scope) (x : TinyML.Var) (c : Decl.Const) (ty : TinyML.Typ) : Scope :=
  { S with
    ghostBindings := (x, c) :: S.ghostBindings
    runtimeBindings := S.runtimeBindings.remove x
    typingContext := S.typingContext.extend x ty }

def bind : TinyML.Mode → Scope → TinyML.Var → Decl.Const → TinyML.Typ → Scope
  | .runtime => bindRuntime
  | .ghost => bindGhost

def bindRuntimeBinder (S : Scope) (b : Typed.Binder) (c : Decl.Const) (ty : TinyML.Typ) : Scope :=
  match b.name with
  | some x => S.bindRuntime x c ty
  | none => S

def bindGhostBinder (S : Scope) (b : Typed.Binder) (c : Decl.Const) (ty : TinyML.Typ) : Scope :=
  match b.name with
  | some x => S.bindGhost x c ty
  | none => S

def bindRuntimeAll : Scope → List TinyML.Var → List Decl.Const → List TinyML.Typ → Scope
  | S, x :: xs, c :: cs, ty :: tys => (S.bindRuntime x c ty).bindRuntimeAll xs cs tys
  | S, _, _, _ => S

def bindGhostAll : Scope → List TinyML.Var → List Decl.Const → List TinyML.Typ → Scope
  | S, x :: xs, c :: cs, ty :: tys => (S.bindGhost x c ty).bindGhostAll xs cs tys
  | S, _, _, _ => S

private theorem bindings_wfIn_cons {B : Bindings} {Δ : Signature} {x : TinyML.Var}
    {c : Decl.Const} (h : B.wfIn Δ) (hc : c ∈ Δ.consts) : Bindings.wfIn ((x, c) :: B) Δ :=
  fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hc
    · exact h p hp

/-- A function's arguments, then its ghost parameters. -/
def bindParameters (S : Scope) (names : List TinyML.Var) (vars : List Decl.Const)
    (tys : List TinyML.Typ) (ghost : List (TinyML.Var × TinyML.Typ))
    (ghostVars : List Decl.Const) : Scope :=
  (S.bindRuntimeAll names vars tys).bindGhostAll (ghost.map Prod.fst) ghostVars
    (ghost.map Prod.snd)

variable [MicaGS HasLC.hasLC Sig]

/-- The scope's constants are declared in `Δ`, and `ρ` gives them the values
    `γg` and `γ` give their names. -/
structure wfIn (S : Scope) (W : TinyML.World) (Δ : Signature) (ρ : _root_.Env)
    (γg γ : Runtime.Subst) : Prop where
  agrees          : W.agrees Δ ρ
  ghostFns        : S.ghostFns.wellTyped W Δ ρ
  ghostLinked     : S.ghostBindings.agreeOnLinked ρ γg
  ghostDeclared   : S.ghostBindings.wfIn Δ
  runtimeLinked   : S.runtimeBindings.agreeOnLinked ρ γ
  runtimeDeclared : S.runtimeBindings.wfIn Δ

variable {S : Scope} {W : TinyML.World} {Δ Δ' : Signature} {ρ ρ' : _root_.Env}
  {γg γ : Runtime.Subst}

theorem wfIn.eta (h : S.wfIn W Δ ρ γg γ) (η : TinyML.SemTypeAssign) :
    S.wfIn { W with eta := η } Δ ρ γg γ :=
  { h with agrees := h.agrees.eta η, ghostFns := h.ghostFns.eta }

theorem wfIn_ghostFns {Gf : GhostFns} {Γ : TinyML.TyCtx} (hag : W.agrees Δ ρ)
    (hGf : Gf.wellTyped W Δ ρ) : (⟨Gf, [], [], Γ⟩ : Scope).wfIn W Δ ρ γg γ where
  agrees := hag
  ghostFns := hGf
  ghostLinked := Bindings.agreeOnLinked_empty ρ γg
  ghostDeclared := Bindings.wfIn_empty Δ
  runtimeLinked := Bindings.agreeOnLinked_empty ρ γ
  runtimeDeclared := Bindings.wfIn_empty Δ

theorem wfIn_mono (h : S.wfIn W Δ ρ γg γ) (hΔ : Δ.Subset Δ') (hρ : Env.agreeOn Δ ρ ρ')
    (hwf : Δ'.wf) : S.wfIn W Δ' ρ' γg γ where
  agrees := h.agrees.step hΔ hρ
  ghostFns := h.ghostFns.step hΔ hρ hwf
  ghostLinked := Bindings.agreeOnLinked_agreeOn h.ghostLinked hρ h.ghostDeclared
  ghostDeclared := fun p hp => hΔ.consts _ (h.ghostDeclared p hp)
  runtimeLinked := Bindings.agreeOnLinked_agreeOn h.runtimeLinked hρ h.runtimeDeclared
  runtimeDeclared := fun p hp => hΔ.consts _ (h.runtimeDeclared p hp)

theorem wfIn.bindRuntime (h : S.wfIn W Δ ρ γg γ) {x : TinyML.Var} {c : Decl.Const}
    {ty : TinyML.Typ} {v : Runtime.Val} (hc : c ∈ Δ.consts) (hsort : c.sort = .value)
    (hval : ρ.consts .value c.name = v) :
    (S.bindRuntime x c ty).wfIn W Δ ρ γg (γ.update x v) where
  agrees := h.agrees
  ghostFns := h.ghostFns.remove x
  ghostLinked := Bindings.agreeOnLinked_remove h.ghostLinked x
  ghostDeclared := Bindings.wfIn_remove h.ghostDeclared x
  runtimeLinked := Bindings.agreeOnLinked_cons_update h.runtimeLinked hsort hval
  runtimeDeclared := bindings_wfIn_cons h.runtimeDeclared hc

theorem wfIn.bindGhost (h : S.wfIn W Δ ρ γg γ) {x : TinyML.Var} {c : Decl.Const}
    {ty : TinyML.Typ} {v : Runtime.Val} (hc : c ∈ Δ.consts) (hsort : c.sort = .value)
    (hval : ρ.consts .value c.name = v) :
    (S.bindGhost x c ty).wfIn W Δ ρ (γg.update x v) γ where
  agrees := h.agrees
  ghostFns := h.ghostFns
  ghostLinked := Bindings.agreeOnLinked_cons_update h.ghostLinked hsort hval
  ghostDeclared := bindings_wfIn_cons h.ghostDeclared hc
  runtimeLinked := Bindings.agreeOnLinked_remove h.runtimeLinked x
  runtimeDeclared := Bindings.wfIn_remove h.runtimeDeclared x

theorem wfIn.bindRuntimeBinder (h : S.wfIn W Δ ρ γg γ) {b : Typed.Binder} {c : Decl.Const}
    {ty : TinyML.Typ} {v : Runtime.Val} (hc : c ∈ Δ.consts) (hsort : c.sort = .value)
    (hval : ρ.consts .value c.name = v) :
    (S.bindRuntimeBinder b c ty).wfIn W Δ ρ γg (γ.updateBinder b.runtime v) := by
  unfold Scope.bindRuntimeBinder
  cases hb : b.name with
  | none => simpa [Typed.Binder.runtime_of_name_none hb, Runtime.Subst.updateBinder] using h
  | some x =>
    simpa [Typed.Binder.runtime_of_name_some hb, Runtime.Subst.updateBinder] using
      h.bindRuntime (x := x) (ty := ty) hc hsort hval

theorem wfIn.bindGhostBinder (h : S.wfIn W Δ ρ γg γ) {b : Typed.Binder} {c : Decl.Const}
    {ty : TinyML.Typ} {v : Runtime.Val} (hc : c ∈ Δ.consts) (hsort : c.sort = .value)
    (hval : ρ.consts .value c.name = v) :
    (S.bindGhostBinder b c ty).wfIn W Δ ρ (γg.updateBinder b.runtime v) γ := by
  unfold Scope.bindGhostBinder
  cases hb : b.name with
  | none => simpa [Typed.Binder.runtime_of_name_none hb, Runtime.Subst.updateBinder] using h
  | some x =>
    simpa [Typed.Binder.runtime_of_name_some hb, Runtime.Subst.updateBinder] using
      h.bindGhost (x := x) (ty := ty) hc hsort hval

theorem wfIn.bindRuntimeAll {xs : List TinyML.Var} {cs : List Decl.Const}
    {tys : List TinyML.Typ} {vs : List Runtime.Val} (hxs : xs.length = cs.length)
    (htys : tys.length = cs.length) (h : S.wfIn W Δ ρ γg γ)
    (hc : ∀ c ∈ cs, c ∈ Δ.consts) (hsort : ∀ c ∈ cs, c.sort = .value)
    (hvals : List.Forall₂ (fun c v => ρ.consts .value c.name = v) cs vs) :
    (S.bindRuntimeAll xs cs tys).wfIn W Δ ρ γg
      (γ.updateAllBinder (xs.map Runtime.Binder.named) vs) := by
  induction hvals generalizing S xs tys γ with
  | nil => cases xs <;> cases tys <;> simp_all [Scope.bindRuntimeAll]
  | cons hv _ ih =>
    obtain _ | ⟨x, xs⟩ := xs; · simp at hxs
    obtain _ | ⟨ty, tys⟩ := tys; · simp at htys
    exact ih (by simpa using hxs) (by simpa using htys)
      (h.bindRuntime (hc _ (.head _)) (hsort _ (.head _)) hv)
      (fun c hc' => hc c (.tail _ hc')) (fun c hc' => hsort c (.tail _ hc'))

theorem wfIn.bindGhostAll {xs : List TinyML.Var} {cs : List Decl.Const}
    {tys : List TinyML.Typ} {vs : List Runtime.Val} (hxs : xs.length = cs.length)
    (htys : tys.length = cs.length) (h : S.wfIn W Δ ρ γg γ)
    (hc : ∀ c ∈ cs, c ∈ Δ.consts) (hsort : ∀ c ∈ cs, c.sort = .value)
    (hvals : List.Forall₂ (fun c v => ρ.consts .value c.name = v) cs vs) :
    (S.bindGhostAll xs cs tys).wfIn W Δ ρ
      (γg.updateAllBinder (xs.map Runtime.Binder.named) vs) γ := by
  induction hvals generalizing S xs tys γg with
  | nil => cases xs <;> cases tys <;> simp_all [Scope.bindGhostAll]
  | cons hv _ ih =>
    obtain _ | ⟨x, xs⟩ := xs; · simp at hxs
    obtain _ | ⟨ty, tys⟩ := tys; · simp at htys
    exact ih (by simpa using hxs) (by simpa using htys)
      (h.bindGhost (hc _ (.head _)) (hsort _ (.head _)) hv)
      (fun c hc' => hc c (.tail _ hc')) (fun c hc' => hsort c (.tail _ hc'))

theorem wfIn.bindParameters {names : List TinyML.Var} {vars ghostVars : List Decl.Const}
    {tys : List TinyML.Typ} {ghost : List (TinyML.Var × TinyML.Typ)} {vs gs : List Runtime.Val}
    (h : S.wfIn W Δ ρ γg γ) (hnames : names.length = vars.length)
    (htys : tys.length = vars.length) (hghost : ghost.length = ghostVars.length)
    (hc : ∀ c ∈ vars, c ∈ Δ.consts) (hsort : ∀ c ∈ vars, c.sort = .value)
    (hvals : List.Forall₂ (fun c v => ρ.consts .value c.name = v) vars vs)
    (hgc : ∀ c ∈ ghostVars, c ∈ Δ.consts) (hgsort : ∀ c ∈ ghostVars, c.sort = .value)
    (hgvals : List.Forall₂ (fun c v => ρ.consts .value c.name = v) ghostVars gs) :
    (S.bindParameters names vars tys ghost ghostVars).wfIn W Δ ρ
      (γg.updateAllBinder ((ghost.map Prod.fst).map Runtime.Binder.named) gs)
      (γ.updateAllBinder (names.map Runtime.Binder.named) vs) :=
  (h.bindRuntimeAll hnames htys hc hsort hvals).bindGhostAll (by simpa using hghost)
    (by simpa using hghost) hgc hgsort hgvals

theorem wfIn.lookup (h : S.wfIn W Δ ρ γg γ) {x : TinyML.Var} {c : Decl.Const}
    (hx : S.ghostBindings.lookup x = some c ∨ S.runtimeBindings.lookup x = some c) :
    c ∈ Δ.consts ∧ c.sort = .value := by
  rcases hx with hx | hx
  · obtain ⟨_, _, heq, _⟩ := List.lookup_eq_some_iff.mp hx
    exact ⟨h.ghostDeclared (x, c) (by rw [heq]; simp), (h.ghostLinked x c hx).1⟩
  · obtain ⟨_, _, heq, _⟩ := List.lookup_eq_some_iff.mp hx
    exact ⟨h.runtimeDeclared (x, c) (by rw [heq]; simp), (h.runtimeLinked x c hx).1⟩

/-! ## Typing -/

/-- Every name in scope denotes a value of the type the typing context gives it. -/
def typed (S : Scope) (W : TinyML.World) (γg γ : Runtime.Subst) : iProp :=
  Bindings.typedScope W S.ghostBindings S.runtimeBindings S.typingContext γg γ

instance typed_persistent (S : Scope) (W : TinyML.World) (γg γ : Runtime.Subst) :
    Persistent (S.typed W γg γ) := by
  unfold typed; infer_instance

theorem typed_ghostFns {Gf : GhostFns} {Γ : TinyML.TyCtx} :
    ⊢ (⟨Gf, [], [], Γ⟩ : Scope).typed W γg γ :=
  (Bindings.typedSubst_empty W Γ γ).trans (Bindings.typedScope_of_typedSubst W γg)

theorem typed_runtimeBindings {Gf : GhostFns} {B : Bindings} {Γ : TinyML.TyCtx} :
    B.typedSubst W Γ γ ⊢ (⟨Gf, [], B, Γ⟩ : Scope).typed W γg γ :=
  Bindings.typedScope_of_typedSubst W γg

theorem typed_lookup (h : S.wfIn W Δ ρ γg γ) {x : TinyML.Var} {c : Decl.Const}
    {u : TinyML.Scheme} (σ : TinyML.TyVar → TinyML.Typ)
    (hx : S.ghostBindings.lookup x = some c ∨ S.runtimeBindings.lookup x = some c)
    (hΓ : S.typingContext x = some u) :
    S.typed W γg γ ⊢ TinyML.ValHasType W (ρ.consts .value c.name) (u.instantiate σ) :=
  Bindings.typedScope_valHasType W σ h.ghostLinked h.runtimeLinked hx hΓ

theorem typed_bindRuntime {x : TinyML.Var} {c : Decl.Const} {ty : TinyML.Typ}
    {w : Runtime.Val} :
    S.typed W γg γ ∗ TinyML.ValHasType W w ty ⊢
      (S.bindRuntime x c ty).typed W γg (γ.update x w) := by
  simp only [Scope.typed, Scope.bindRuntime]
  iintro ⟨#HS, #Hw⟩
  iapply (Bindings.typedScope_cons (W := W))
  · iexact HS
  · iexact Hw

theorem typed_bindGhost {x : TinyML.Var} {c : Decl.Const} {ty : TinyML.Typ}
    {w : Runtime.Val} :
    S.typed W γg γ ∗ TinyML.ValHasType W w ty ⊢
      (S.bindGhost x c ty).typed W (γg.update x w) γ := by
  simp only [Scope.typed, Scope.bindGhost]
  iintro ⟨#HS, #Hw⟩
  iapply (Bindings.typedScope_cons_ghost (W := W))
  · iexact HS
  · iexact Hw

theorem typed_bindRuntimeBinder {b : Typed.Binder} {c : Decl.Const} {ty : TinyML.Typ}
    {w : Runtime.Val} :
    S.typed W γg γ ∗ TinyML.ValHasType W w ty ⊢
      (S.bindRuntimeBinder b c ty).typed W γg (γ.updateBinder b.runtime w) := by
  unfold Scope.bindRuntimeBinder
  cases hb : b.name with
  | none =>
    simp only [Typed.Binder.runtime_of_name_none hb, Runtime.Subst.updateBinder]
    exact sep_elim_left
  | some x =>
    simp only [Typed.Binder.runtime_of_name_some hb, Runtime.Subst.updateBinder]
    exact typed_bindRuntime

theorem typed_bindGhostBinder {b : Typed.Binder} {c : Decl.Const} {ty : TinyML.Typ}
    {w : Runtime.Val} :
    S.typed W γg γ ∗ TinyML.ValHasType W w ty ⊢
      (S.bindGhostBinder b c ty).typed W (γg.updateBinder b.runtime w) γ := by
  unfold Scope.bindGhostBinder
  cases hb : b.name with
  | none =>
    simp only [Typed.Binder.runtime_of_name_none hb, Runtime.Subst.updateBinder]
    exact sep_elim_left
  | some x =>
    simp only [Typed.Binder.runtime_of_name_some hb, Runtime.Subst.updateBinder]
    exact typed_bindGhost

theorem typed_bindRuntimeAll {xs : List TinyML.Var} {cs : List Decl.Const}
    {tys : List TinyML.Typ} {vs : List Runtime.Val} (hxs : xs.length = cs.length)
    (hcs : cs.length = vs.length) :
    S.typed W γg γ ∗ TinyML.ValsHaveTypes W vs tys ⊢
      (S.bindRuntimeAll xs cs tys).typed W γg
        (γ.updateAllBinder (xs.map Runtime.Binder.named) vs) := by
  induction xs generalizing S cs tys vs γ with
  | nil => simpa [Scope.bindRuntimeAll] using sep_elim_left
  | cons x xs ih =>
    obtain _ | ⟨c, cs⟩ := cs; · simp at hxs
    obtain _ | ⟨v, vs⟩ := vs; · simp at hcs
    obtain _ | ⟨ty, tys⟩ := tys
    · iintro ⟨_, Hvs⟩
      ihave Hfalse := (TinyML.ValsHaveTypes.cons_nil W v vs).1 $$ Hvs
      iapply false_elim
      iexact Hfalse
    simp only [List.map_cons, Runtime.Subst.updateAllBinder_cons, Runtime.Subst.updateBinder]
    refine BIBase.Entails.trans ?_ (ih (by simpa using hxs) (by simpa using hcs))
    iintro ⟨#HS, Hvs⟩
    ihave Hpair := (TinyML.ValsHaveTypes.cons W v vs ty tys).1 $$ Hvs
    icases Hpair with ⟨#Hv, Hvs⟩
    isplitl []
    · iapply typed_bindRuntime
      isplitl []
      · iexact HS
      · iexact Hv
    · iexact Hvs

theorem typed_bindGhostAll {xs : List TinyML.Var} {cs : List Decl.Const}
    {tys : List TinyML.Typ} {vs : List Runtime.Val} (hxs : xs.length = cs.length)
    (hcs : cs.length = vs.length) :
    S.typed W γg γ ∗ TinyML.ValsHaveTypes W vs tys ⊢
      (S.bindGhostAll xs cs tys).typed W
        (γg.updateAllBinder (xs.map Runtime.Binder.named) vs) γ := by
  induction xs generalizing S cs tys vs γg with
  | nil => simpa [Scope.bindGhostAll] using sep_elim_left
  | cons x xs ih =>
    obtain _ | ⟨c, cs⟩ := cs; · simp at hxs
    obtain _ | ⟨v, vs⟩ := vs; · simp at hcs
    obtain _ | ⟨ty, tys⟩ := tys
    · iintro ⟨_, Hvs⟩
      ihave Hfalse := (TinyML.ValsHaveTypes.cons_nil W v vs).1 $$ Hvs
      iapply false_elim
      iexact Hfalse
    simp only [List.map_cons, Runtime.Subst.updateAllBinder_cons, Runtime.Subst.updateBinder]
    refine BIBase.Entails.trans ?_ (ih (by simpa using hxs) (by simpa using hcs))
    iintro ⟨#HS, Hvs⟩
    ihave Hpair := (TinyML.ValsHaveTypes.cons W v vs ty tys).1 $$ Hvs
    icases Hpair with ⟨#Hv, Hvs⟩
    isplitl []
    · iapply typed_bindGhost
      isplitl []
      · iexact HS
      · iexact Hv
    · iexact Hvs

theorem typed_bindParameters {names : List TinyML.Var} {vars ghostVars : List Decl.Const}
    {tys : List TinyML.Typ} {ghost : List (TinyML.Var × TinyML.Typ)} {vs gs : List Runtime.Val}
    (hnames : names.length = vars.length) (hvars : vars.length = vs.length)
    (hghost : ghost.length = ghostVars.length) (hgvars : ghostVars.length = gs.length) :
    S.typed W γg γ ∗ TinyML.ValsHaveTypes W vs tys ∗
        TinyML.ValsHaveTypes W gs (ghost.map Prod.snd) ⊢
      (S.bindParameters names vars tys ghost ghostVars).typed W
        (γg.updateAllBinder ((ghost.map Prod.fst).map Runtime.Binder.named) gs)
        (γ.updateAllBinder (names.map Runtime.Binder.named) vs) := by
  unfold Scope.bindParameters
  iintro ⟨#HS, #Hvs, #Hgs⟩
  iapply (typed_bindGhostAll (by simpa using hghost) hgvars)
  isplitl []
  · iapply (typed_bindRuntimeAll hnames hvars)
    isplitl []
    · iexact HS
    · iexact Hvs
  · iexact Hgs

end Scope

end Verifier

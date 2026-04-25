-- SUMMARY: Verifier variable-to-constant bindings, their semantic linkage to runtime substitutions, and typing/lookup lemmas.
import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.FOL.Printing
import Mica.FOL.Subst
import Mica.SeparationLogic.LogicalRelation

open Iris Iris.BI

/-! ### Bindings -/

abbrev Bindings := List (TinyML.Var × FOL.Const)

def Bindings.empty : Bindings := []

-- Every variable in Bindings is now declared at sort `.value`.
def Bindings.agreeOnLinked (B : Bindings) (ρ : Env) (γ : Runtime.Subst) :=
  ∀ x x', B.lookup x = some x' →
    x'.sort = .value ∧ γ x = .some (ρ.consts .value x'.name)

def Bindings.wfIn (B : Bindings) (decls : Signature) : Prop :=
  ∀ p ∈ B, p.2 ∈ decls.consts

theorem Bindings.agreeOnLinked_env_agree {B : Bindings} {decls : Signature} {ρ ρ' : Env} {γ : Runtime.Subst}
    (hagr : B.agreeOnLinked ρ γ) (henv : Env.agreeOn decls ρ ρ')
    (hwf : B.wfIn decls) : B.agreeOnLinked ρ' γ := by
  intro x x' hmem
  obtain ⟨hsort, hγ⟩ := hagr x x' hmem
  obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hmem
  have hmem' : (x, x') ∈ B := by rw [heq]; simp
  have hdecl := hwf _ hmem'
  have henv' := henv.2.1 x' hdecl
  rw [hsort] at henv'
  exact ⟨hsort, hγ.trans (congrArg some henv')⟩

theorem Bindings.wfIn_cons {B : Bindings} {decls : Signature} {x : TinyML.Var} {v : FOL.Const}
    (hbwf : B.wfIn decls) :
    Bindings.wfIn ((x, v) :: B) (decls.addConst v) := by
  intro p hp
  simp [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact List.Mem.head _
  · exact List.Mem.tail _ (hbwf p hp)

/-- The substitution `γ` maps every binding to a value well-typed by `Γ`. -/
def Bindings.typedSubst (Θ : TinyML.TypeEnv) (B : Bindings) (Γ : TinyML.TyCtx) (γ : Runtime.Subst) : iProp :=
  iprop(□ ∀ x x' t, ⌜B.lookup x = some x'⌝ -∗ ⌜Γ x = some t⌝ -∗ ∃ v, ⌜γ x = some v⌝ ∗ TinyML.ValHasType Θ v t)

instance Bindings.typedSubst_persistent {B Γ γ} (Θ : TinyML.TypeEnv) : Persistent (Bindings.typedSubst Θ B Γ γ) :=
  by
    unfold Bindings.typedSubst
    infer_instance

theorem Bindings.typedSubst_nil (Θ : TinyML.TypeEnv) (γ : Runtime.Subst) :
    ⊢ Bindings.typedSubst Θ [] TinyML.TyCtx.empty γ := by
  unfold Bindings.typedSubst
  imodintro
  iintro %x %x' %t
  iintro %hlookup
  simp at hlookup

theorem Bindings.typedSubst_cons {B : Bindings} {Γ : TinyML.TyCtx} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : FOL.Const} {te : TinyML.Typ} {w : Runtime.Val}
    : ⊢ B.typedSubst Θ Γ γ -∗ TinyML.ValHasType Θ w te -∗
      Bindings.typedSubst Θ ((x, v) :: B) (Γ.extend x te) (Runtime.Subst.update γ x w) := by
  iintro #Hts #Hw
  unfold Bindings.typedSubst
  imodintro
  iintro %y
  iintro %y'
  iintro %t
  iintro %hmem
  iintro %hΓ
  by_cases hyx : y == x
  · -- head case: y = x
    simp [List.lookup, hyx] at hmem; subst hmem
    simp [TinyML.TyCtx.extend, hyx] at hΓ; subst hΓ
    iexists w
    isplitr
    · ipure_intro
      simp [Runtime.Subst.update, hyx]
    · iexact Hw
  · -- tail case: y ≠ x
    simp [List.lookup, hyx] at hmem
    have hΓ' : Γ y = some t := by simp [TinyML.TyCtx.extend, hyx] at hΓ; exact hΓ
    ispecialize Hts $$ %y %y' %t %hmem %hΓ'
    icases Hts with ⟨%w', %hw', Hw'⟩
    iexists w'
    isplitr
    · ipure_intro
      simp [Runtime.Subst.update, hyx, hw']
    · iexact Hw'

theorem Bindings.agreeOnLinked_cons {B : Bindings} {ρ ρ' : Env} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : FOL.Const}
    (hagree : B.agreeOnLinked ρ γ)
    (hρ_agree : Env.agreeOn (Signature.ofConsts (B.map Prod.snd)) ρ' ρ)
    (hvty : v.sort = .value) :
    Bindings.agreeOnLinked ((x, v) :: B) ρ' (Runtime.Subst.update γ x (ρ'.consts .value v.name)) := by
  intro y y' hmem
  by_cases hyx : y == x
  · simp [List.lookup, hyx] at hmem; subst hmem
    exact ⟨hvty, by simp [Runtime.Subst.update, hyx]⟩
  · simp [List.lookup, hyx] at hmem
    obtain ⟨hsort, hγ⟩ := hagree y y' hmem
    have hmem_snd : y' ∈ B.map Prod.snd := by
      obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hmem
      exact List.mem_map.mpr ⟨(y, y'), by rw [heq]; simp, rfl⟩
    have hρ := hρ_agree.2.1 y' hmem_snd
    rw [hsort] at hρ
    exact ⟨hsort, by simp [Runtime.Subst.update, hyx]; exact hγ.trans (congrArg some hρ.symm)⟩

-- If agreeOnLinked holds and values at each binding are well-typed, then typedSubst holds.
theorem Bindings.typedSubst_of_agreeOnLinked
    {B : Bindings} {Γ : TinyML.TyCtx} {γ : Runtime.Subst} {ρ : Env}
    (hagree : B.agreeOnLinked ρ γ)
    : ⊢ □ (∀ x x' t, ⌜B.lookup x = some x'⌝ -∗ ⌜Γ x = some t⌝ -∗
        TinyML.ValHasType Θ (ρ.consts .value x'.name) t) -∗
      B.typedSubst Θ Γ γ := by
  iintro #Htyped
  unfold Bindings.typedSubst
  imodintro
  iintro %x
  iintro %x'
  iintro %t
  iintro %hmem
  iintro %hΓ
  obtain ⟨_, hval⟩ := hagree x x' hmem
  iexists (ρ.consts .value x'.name)
  isplitr
  · ipure_intro
    exact hval
  · ispecialize Htyped $$ %x %x' %t
    iapply Htyped
    · ipure_intro; exact hmem
    · ipure_intro; exact hΓ

theorem findVal_none_of_not_mem
    (ns : List String) (vs : List Runtime.Val) (x : String)
    (hlen : ns.length = vs.length) (hx : x ∉ ns) :
    Runtime.Binders.findVal (ns.map Runtime.Binder.named) vs x = none := by
  induction ns generalizing vs with
  | nil => simp
  | cons n ns ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp at hlen hx
      simp only [List.map_cons, Runtime.Binders.findVal_cons, ih vs hlen hx.2]
      simp [Runtime.Binder.named_beq, beq_iff_eq, Ne.symm hx.1]

theorem not_mem_of_lookup_zip_reverse_none
    (ns : List String) (avs : List FOL.Const) (x : String)
    (hlen : ns.length = avs.length)
    (h : List.lookup x (ns.zip avs).reverse = none) :
    x ∉ ns := by
  rw [List.lookup_eq_none_iff] at h
  intro hx
  obtain ⟨i, hi, hni⟩ := List.getElem_of_mem hx
  have hi' : i < avs.length := by omega
  have hmem : (ns[i], avs[i]) ∈ ns.zip avs := by
    have hiz : i < (ns.zip avs).length := by simp [List.length_zip]; omega
    have : (ns.zip avs)[i]'hiz = (ns[i], avs[i]) := List.getElem_zip
    rw [← this]; exact List.getElem_mem hiz
  have hmem' : (ns[i], avs[i]) ∈ (ns.zip avs).reverse := List.mem_reverse.mpr hmem
  have := h _ hmem'
  simp [hni] at this

theorem Bindings.agreeOnLinked_zip_reverse
    (names : List String) (vars : List FOL.Const) (vals : List Runtime.Val)
    (γ : Runtime.Subst) (ρ : Env)
    (hlen_nv : names.length = vars.length)
    (hlen_nvl : names.length = vals.length)
    (hsorts : ∀ v ∈ vars, v.sort = .value)
    (hlookups : List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals) :
    Bindings.agreeOnLinked (names.zip vars).reverse ρ
      (γ.updateAll' (names.map Runtime.Binder.named) vals) := by
  induction names generalizing vars vals γ with
  | nil => intro x x' hmem; simp at hmem
  | cons n ns ih =>
    cases vars with
    | nil => simp at hlen_nv
    | cons av avs =>
      cases vals with
      | nil => simp at hlen_nvl
      | cons v vs =>
        simp at hlen_nv hlen_nvl
        cases hlookups with
        | cons hlk htail =>
          simp only [List.map_cons, Runtime.Subst.updateAll'_cons, List.zip_cons_cons, List.reverse_cons]
          have ih' := ih avs vs (γ.update' (.named n) v) (by omega) (by omega)
            (fun v' hv' => hsorts v' (.tail _ hv')) htail
          intro x x' hmem
          rw [List.lookup_append] at hmem
          cases hlk_inner : List.lookup x (ns.zip avs).reverse with
          | some v' =>
            simp [hlk_inner] at hmem; subst hmem
            exact ih' x v' hlk_inner
          | none =>
            simp [hlk_inner] at hmem
            by_cases hxn : x == n
            · simp [List.lookup, hxn] at hmem; subst hmem
              constructor
              · exact hsorts av (.head _)
              · rw [Runtime.Subst.updateAll'_eq _ _ _ _ (by simp; omega)]
                have hx_notin := not_mem_of_lookup_zip_reverse_none ns avs x hlen_nv hlk_inner
                suffices Runtime.Binders.findVal (ns.map Runtime.Binder.named) vs x = none by
                  simp [this, Runtime.Subst.update', hxn, ← hlk]
                exact findVal_none_of_not_mem ns vs x hlen_nvl hx_notin
            · simp [List.lookup, hxn] at hmem

theorem Bindings.lookup_reverse_zip_append {keys : List String} {vars : List FOL.Const} {x : String} (B : Bindings) :
    ((keys.zip vars).reverse ++ B).lookup x =
      ((keys.zip vars).reverse.lookup x).or (B.lookup x) := by
  rw [List.lookup_append]

theorem Bindings.agreeOnLinked_updateAll'
    (B : Bindings) (names : List String) (vars : List FOL.Const) (vals : List Runtime.Val)
    (γ : Runtime.Subst) (ρ : Env)
    (hB : B.agreeOnLinked ρ γ)
    (hlen_nv : names.length = vars.length)
    (hlen_nvl : names.length = vals.length)
    (hsorts : ∀ v ∈ vars, v.sort = .value)
    (hlookups : List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals) :
    Bindings.agreeOnLinked ((names.zip vars).reverse ++ B) ρ
      (γ.updateAll' (names.map Runtime.Binder.named) vals) := by
  intro x x' hmem
  rw [lookup_reverse_zip_append B] at hmem
  cases hlk : (names.zip vars).reverse.lookup x with
  | some x'' =>
    simp [hlk] at hmem; subst hmem
    have hag := agreeOnLinked_zip_reverse names vars vals γ ρ hlen_nv hlen_nvl hsorts hlookups
    exact hag x x'' hlk
  | none =>
    simp [hlk] at hmem
    obtain ⟨hsort, hγ⟩ := hB x x' hmem
    constructor
    · exact hsort
    · rw [Runtime.Subst.updateAll'_eq _ _ _ _ (by simp; omega)]
      have hx_notin := not_mem_of_lookup_zip_reverse_none names vars x hlen_nv hlk
      rw [findVal_none_of_not_mem names vals x (by omega) hx_notin]
      exact hγ

-- For lists with "last wins" semantics: if the reversed-zip lookup finds x' at x,
-- and the foldl-Γ lookup finds type t at x, and Forall₂ relates vars to vals
-- with ValsHaveTypes, then the value at x' has type t.
-- All three structures agree on the "last occurrence" of x.
theorem val_typed_of_last_wins
    (args : List (String × TinyML.Typ))
    (vars : List FOL.Const) (vals : List Runtime.Val)
    (ρ : Env) (Γ₀ : TinyML.TyCtx)
    (x : String) (x' : FOL.Const) (t : TinyML.Typ)
    (hlen_v : (args.map Prod.fst).length = vars.length)
    (hlen_vl : (args.map Prod.fst).length = vals.length)
    (hlookup : List.lookup x ((args.map Prod.fst).zip vars).reverse = some x')
    (hΓ : (args.foldl (fun ctx a => ctx.extend a.1 a.2) Γ₀) x = some t)
    (hlookups : List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals)
    : ⊢ TinyML.ValsHaveTypes Θ vals (args.map Prod.snd) -∗
        TinyML.ValHasType Θ (ρ.consts .value x'.name) t := by
  induction args generalizing vars vals Γ₀ with
  | nil => simp at hlookup
  | cons a as' ih =>
    cases vars with
    | nil => simp at hlen_v
    | cons vr vrs =>
      cases vals with
      | nil => simp at hlen_vl
      | cons vl vls =>
        simp [List.map_cons, List.length_cons] at hlen_v hlen_vl
        cases hlookups with
        | cons hlk_head hlk_tail =>
          exact (show ⊢ TinyML.ValsHaveTypes Θ (vl :: vls) (a.2 :: as'.map Prod.snd) -∗
                TinyML.ValHasType Θ (ρ.consts .value x'.name) t by
              iintro Hvals
              ihave Hpair := (TinyML.ValsHaveTypes.cons Θ vl vls a.2 (as'.map Prod.snd)).1 $$ Hvals
              icases Hpair with ⟨Htype_head, Htype_tail⟩
              simp only [List.map_cons, List.zip_cons_cons, List.reverse_cons] at hlookup
              rw [List.lookup_append] at hlookup
              simp only [List.foldl_cons] at hΓ
              cases hlk_inner : List.lookup x ((as'.map Prod.fst).zip vrs).reverse with
              | some v' =>
                simp [hlk_inner] at hlookup; subst hlookup
                iapply (ih vrs vls (Γ₀.extend a.1 a.2) (by simp; omega) (by simp; omega) hlk_inner hΓ hlk_tail)
                iexact Htype_tail
              | none =>
                simp [hlk_inner] at hlookup
                by_cases hxa : x == a.1
                · simp [List.lookup, hxa] at hlookup; subst hlookup
                  have hx_notin := not_mem_of_lookup_zip_reverse_none
                    (as'.map Prod.fst) vrs x (by simp; omega) hlk_inner
                  simp [List.mem_map] at hx_notin
                  have hΓ_stable : (as'.foldl (fun ctx a => ctx.extend a.1 a.2) (Γ₀.extend a.1 a.2)) x =
                      (Γ₀.extend a.1 a.2) x := by
                    apply TinyML.TyCtx.foldl_extend_stable
                    intro ⟨n, t⟩ hmem heq; exact hx_notin t (heq ▸ hmem)
                  rw [hΓ_stable] at hΓ
                  have hxa' : x = a.1 := by exact beq_iff_eq.mp hxa
                  subst hxa'
                  simp [TinyML.TyCtx.extend] at hΓ; subst hΓ
                  rw [← hlk_head]
                  iexact Htype_head
                · simp [List.lookup, hxa] at hlookup)

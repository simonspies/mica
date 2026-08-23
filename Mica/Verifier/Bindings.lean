-- SUMMARY: Verifier variable-to-constant bindings, their semantic linkage to runtime substitutions, and typing/lookup lemmas.
import Mica.SourceTinyML.Typed
import Mica.SourceTinyML.Typing
import Mica.TinyML.OpSem
import Mica.FOL.Printing
import Mica.FOL.Subst
import Mica.SourceTinyML.LogicalRelation

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]

/-! ### Bindings -/

abbrev Bindings := List (TinyML.Var × FOL.Const)

def Bindings.empty : Bindings := []

/-- Drop a name's binding. A declaration that shadows a bound name without
    binding a value of its own must remove it, or the old constant would stand
    for the new value. -/
def Bindings.remove : Bindings → TinyML.Var → Bindings
  | [], _ => []
  | (y, c) :: B, x => if y == x then Bindings.remove B x else (y, c) :: Bindings.remove B x

omit [MicaGS HasLC.hasLC Sig] in
@[simp] theorem Bindings.lookup_remove (B : Bindings) (x y : TinyML.Var) :
    (B.remove x).lookup y = if y == x then none else B.lookup y := by
  induction B with
  | nil => simp [Bindings.remove]
  | cons p B ih =>
    obtain ⟨z, c⟩ := p
    by_cases hzx : z = x
    · subst hzx
      simp only [Bindings.remove, beq_self_eq_true, if_true, ih]
      by_cases hyz : y = z
      · subst hyz; simp only [List.lookup, beq_self_eq_true, if_true]
      · have hb : (y == z) = false := by simp [hyz]
        simp only [List.lookup, hb, Bool.false_eq_true, if_false]
    · have hzb : (z == x) = false := by simp [hzx]
      simp only [Bindings.remove, hzb, Bool.false_eq_true, if_false]
      by_cases hyz : y = z
      · subst hyz
        have hyx : (y == x) = false := by simp [hzx]
        simp only [List.lookup, beq_self_eq_true, hyx, Bool.false_eq_true, if_false]
      · have hb : (y == z) = false := by simp [hyz]
        simp only [List.lookup, hb, ih]

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.mem_of_mem_remove {B : Bindings} {x : TinyML.Var} {p : TinyML.Var × FOL.Const}
    (h : p ∈ B.remove x) : p ∈ B := by
  induction B with
  | nil => simp [Bindings.remove] at h
  | cons q B ih =>
    obtain ⟨z, c⟩ := q
    by_cases hzx : z = x
    · simp [Bindings.remove, hzx] at h
      exact List.mem_cons_of_mem _ (ih h)
    · simp [Bindings.remove, hzx, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · exact .inl rfl
      · exact .inr (ih h)

-- Every variable in Bindings is now declared at sort `.value`.
def Bindings.agreeOnLinked (B : Bindings) (ρ : Env) (γ : Runtime.Subst) :=
  ∀ x x', B.lookup x = some x' →
    x'.sort = .value ∧ γ x = .some (ρ.consts .value x'.name)

def Bindings.wfIn (B : Bindings) (decls : Signature) : Prop :=
  ∀ p ∈ B, p.2 ∈ decls.consts

omit [MicaGS HasLC.hasLC Sig] in
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

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.wfIn_cons {B : Bindings} {decls : Signature} {x : TinyML.Var} {v : FOL.Const}
    (hbwf : B.wfIn decls) :
    Bindings.wfIn ((x, v) :: B) (decls.addConst v) := by
  intro p hp
  simp [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact List.Mem.head _
  · exact List.Mem.tail _ (hbwf p hp)

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.wfIn_remove {B : Bindings} {decls : Signature} (h : B.wfIn decls)
    (x : TinyML.Var) : (B.remove x).wfIn decls :=
  fun _ hp => h _ (Bindings.mem_of_mem_remove hp)

omit [MicaGS HasLC.hasLC Sig] in
/-- Dropping a name's binding survives that name being rebound at runtime: the
    remaining bindings are all for other names. -/
theorem Bindings.agreeOnLinked_remove {B : Bindings} {ρ : Env} {γ : Runtime.Subst}
    (hagree : B.agreeOnLinked ρ γ) (x : TinyML.Var) (v : Runtime.Val) :
    (B.remove x).agreeOnLinked ρ (Runtime.Subst.update γ x v) := by
  intro y y' hmem
  rw [Bindings.lookup_remove] at hmem
  by_cases hyx : y == x
  · simp [hyx] at hmem
  · simp only [hyx, Bool.false_eq_true, if_false] at hmem
    obtain ⟨hsort, hγ⟩ := hagree y y' hmem
    exact ⟨hsort, by simp [Runtime.Subst.update, hyx, hγ]⟩

/-- The substitution `γ` maps every binding to a value well-typed by `Γ`, at
every instantiation of the scheme the context binds it at. A binding that
quantifies nothing has exactly one instantiation, so this says of it what it
said before schemes existed. -/
def Bindings.typedSubst (W : TinyML.World) (B : Bindings) (Γ : TinyML.TyCtx) (γ : Runtime.Subst) : iProp :=
  iprop(□ ∀ x x' s, ⌜B.lookup x = some x'⌝ -∗ ⌜Γ x = some s⌝ -∗
    ∃ v, ⌜γ x = some v⌝ ∗ ∀ σ, TinyML.ValHasType W v (TinyML.Scheme.instantiate s σ))

instance Bindings.typedSubst_persistent {B Γ γ} (W : TinyML.World) : Persistent (Bindings.typedSubst W B Γ γ) :=
  by
    unfold Bindings.typedSubst
    infer_instance

theorem Bindings.typedSubst_nil (W : TinyML.World) (γ : Runtime.Subst) :
    ⊢ Bindings.typedSubst W [] TinyML.TyCtx.empty γ := by
  unfold Bindings.typedSubst
  imodintro
  iintro %x %x' %t
  iintro %hlookup
  simp at hlookup

/-- Extend by a binding whose uses may instantiate it: the value is typed at
every instantiation of the scheme. -/
theorem Bindings.typedSubst_cons_scheme {B : Bindings} {Γ : TinyML.TyCtx} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : FOL.Const} {s : TinyML.Scheme} {w : Runtime.Val}
    : ⊢ B.typedSubst W Γ γ -∗ (∀ σ, TinyML.ValHasType W w (s.instantiate σ)) -∗
      Bindings.typedSubst W ((x, v) :: B) (Γ.extendScheme x s) (Runtime.Subst.update γ x w) := by
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
    simp [TinyML.TyCtx.extendScheme, hyx] at hΓ; subst hΓ
    iexists w
    isplitr
    · ipureintro
      simp [Runtime.Subst.update, hyx]
    · iexact Hw
  · -- tail case: y ≠ x
    simp [List.lookup, hyx] at hmem
    have hΓ' : Γ y = some t := by simp [TinyML.TyCtx.extendScheme, hyx] at hΓ; exact hΓ
    ispecialize Hts $$ %y %y' %t %hmem %hΓ'
    icases Hts with ⟨%w', %hw', Hw'⟩
    iexists w'
    isplitr
    · ipureintro
      simp [Runtime.Subst.update, hyx, hw']
    · iexact Hw'

/-- Extend by a binding nothing may instantiate. -/
theorem Bindings.typedSubst_cons {B : Bindings} {Γ : TinyML.TyCtx} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : FOL.Const} {te : TinyML.Typ} {w : Runtime.Val}
    : ⊢ B.typedSubst W Γ γ -∗ TinyML.ValHasType W w te -∗
      Bindings.typedSubst W ((x, v) :: B) (Γ.extend x te) (Runtime.Subst.update γ x w) := by
  iintro #Hts #Hw
  rw [TinyML.TyCtx.extend_def]
  iapply (Bindings.typedSubst_cons_scheme (s := TinyML.Scheme.mono te))
  · iexact Hts
  · iintro %σ
    simp only [TinyML.Scheme.instantiate_mono]
    iexact Hw

/-- Typing survives dropping a name's binding and rebinding that name at
    runtime: no claim is made about the dropped name, and every other binding
    reads the same value. -/
theorem Bindings.typedSubst_remove {B : Bindings} {Γ : TinyML.TyCtx} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : Runtime.Val} :
    B.typedSubst W Γ γ ⊢ (B.remove x).typedSubst W Γ (Runtime.Subst.update γ x v) := by
  unfold Bindings.typedSubst
  iintro #Hts
  imodintro
  iintro %y %y' %t %hmem %hΓ
  rw [Bindings.lookup_remove] at hmem
  by_cases hyx : y == x
  · simp [hyx] at hmem
  · simp only [hyx, Bool.false_eq_true, if_false] at hmem
    ispecialize Hts $$ %y %y' %t %hmem %hΓ
    icases Hts with ⟨%w, %hw, Hw⟩
    iexists w
    isplitr
    · ipureintro
      simp [Runtime.Subst.update, hyx, hw]
    · iexact Hw

/-- Typedness transports to every type assignment. This is what makes a
declaration's verification parametric: the same bindings re-derive its typing at
every `σ`, so its value can be installed at a scheme rather than at one type. -/
theorem Bindings.typedSubst_afterInstantiating {B : Bindings} {Γ : TinyML.TyCtx}
    {γ : Runtime.Subst} (W : TinyML.World) (σ : TinyML.TyVar → TinyML.Typ)
    (hΓ : Γ.Closed) :
    B.typedSubst W Γ γ ⊢ B.typedSubst (W.afterInstantiating σ) Γ γ := by
  unfold Bindings.typedSubst
  iintro #Hts
  imodintro
  iintro %y %y' %s %hmem %hΓy
  ispecialize Hts $$ %y %y' %s %hmem %hΓy
  icases Hts with ⟨%w, %hw, Hw⟩
  iexists w
  isplitr
  · ipureintro; exact hw
  · iintro %σ'
    iapply (TinyML.ValHasType.subst W σ w (s.instantiate σ')).2
    rw [TinyML.Scheme.subst_instantiate (fun a ha => by simp [hΓ y s hΓy] at ha) σ']
    ispecialize Hw $$ %(fun a => TinyML.Typ.subst σ (σ' a))
    iexact Hw

omit [MicaGS HasLC.hasLC Sig] in
/-- Bind a name to a constant that already denotes the value the name is being
    bound to. -/
theorem Bindings.agreeOnLinked_cons_update {B : Bindings} {ρ : Env} {γ : Runtime.Subst}
    {x : TinyML.Var} {c : FOL.Const} {v : Runtime.Val}
    (hagree : B.agreeOnLinked ρ γ) (hsort : c.sort = .value)
    (hval : ρ.consts .value c.name = v) :
    Bindings.agreeOnLinked ((x, c) :: B) ρ (Runtime.Subst.update γ x v) := by
  intro y y' hmem
  by_cases hyx : y == x
  · simp [List.lookup, hyx] at hmem; subst hmem
    exact ⟨hsort, by simp [Runtime.Subst.update, hyx, hval]⟩
  · simp [List.lookup, hyx] at hmem
    obtain ⟨hsort', hγ⟩ := hagree y y' hmem
    exact ⟨hsort', by simp [Runtime.Subst.update, hyx, hγ]⟩

omit [MicaGS HasLC.hasLC Sig] in
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
    : ⊢ □ (∀ x x' s σ, ⌜B.lookup x = some x'⌝ -∗ ⌜Γ x = some s⌝ -∗
        TinyML.ValHasType W (ρ.consts .value x'.name) (TinyML.Scheme.instantiate s σ)) -∗
      B.typedSubst W Γ γ := by
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
  · ipureintro
    exact hval
  · iintro %σ
    ispecialize Htyped $$ %x %x' %t %σ
    iapply Htyped
    · ipureintro; exact hmem
    · ipureintro; exact hΓ

omit [MicaGS HasLC.hasLC Sig] in
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
      simp [BEq.beq, Runtime.instBEqBinder.beq, Ne.symm hx.1]

omit [MicaGS HasLC.hasLC Sig] in
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

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.agreeOnLinked_zip_reverse
    (names : List String) (vars : List FOL.Const) (vals : List Runtime.Val)
    (γ : Runtime.Subst) (ρ : Env)
    (hlen_nv : names.length = vars.length)
    (hlen_nvl : names.length = vals.length)
    (hsorts : ∀ v ∈ vars, v.sort = .value)
    (hlookups : List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals) :
    Bindings.agreeOnLinked (names.zip vars).reverse ρ
      (γ.updateAllBinder (names.map Runtime.Binder.named) vals) := by
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
          simp only [List.map_cons, Runtime.Subst.updateAllBinder_cons, List.zip_cons_cons, List.reverse_cons]
          have ih' := ih avs vs (γ.updateBinder (.named n) v) (by omega) (by omega)
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
              · rw [Runtime.Subst.updateAllBinder_eq _ _ _ _ (by simp; omega)]
                have hx_notin := not_mem_of_lookup_zip_reverse_none ns avs x hlen_nv hlk_inner
                suffices Runtime.Binders.findVal (ns.map Runtime.Binder.named) vs x = none by
                  simp [this, Runtime.Subst.updateBinder, hxn, ← hlk]
                exact findVal_none_of_not_mem ns vs x hlen_nvl hx_notin
            · simp [List.lookup, hxn] at hmem

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.agreeOnLinked_updateAllBinder
    (B : Bindings) (names : List String) (vars : List FOL.Const) (vals : List Runtime.Val)
    (γ : Runtime.Subst) (ρ : Env)
    (hB : B.agreeOnLinked ρ γ)
    (hlen_nv : names.length = vars.length)
    (hlen_nvl : names.length = vals.length)
    (hsorts : ∀ v ∈ vars, v.sort = .value)
    (hlookups : List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals) :
    Bindings.agreeOnLinked ((names.zip vars).reverse ++ B) ρ
      (γ.updateAllBinder (names.map Runtime.Binder.named) vals) := by
  intro x x' hmem
  rw [List.lookup_append] at hmem
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
    · rw [Runtime.Subst.updateAllBinder_eq _ _ _ _ (by simp; omega)]
      have hx_notin := not_mem_of_lookup_zip_reverse_none names vars x hlen_nv hlk
      rw [findVal_none_of_not_mem names vals x (by omega) hx_notin]
      exact hγ

-- For lists with "last wins" semantics: if the reversed-zip lookup finds x' at x,
-- and the foldl-Γ lookup finds type t at x, and Forall₂ relates vars to vals
-- with ValsHaveTypes, then the value at x' has type t.
-- All three structures agree on the "last occurrence" of x.
theorem valHasType_lookup_zip_reverse
    (args : List (String × TinyML.Typ))
    (vars : List FOL.Const) (vals : List Runtime.Val)
    (ρ : Env) (Γ₀ : TinyML.TyCtx)
    (x : String) (x' : FOL.Const) (s : TinyML.Scheme) (σ : TinyML.TyVar → TinyML.Typ)
    (hlen_v : (args.map Prod.fst).length = vars.length)
    (hlen_vl : (args.map Prod.fst).length = vals.length)
    (hlookup : List.lookup x ((args.map Prod.fst).zip vars).reverse = some x')
    (hΓ : (args.foldl (fun ctx a => ctx.extend a.1 a.2) Γ₀) x = some s)
    (hlookups : List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals)
    : ⊢ TinyML.ValsHaveTypes W vals (args.map Prod.snd) -∗
        TinyML.ValHasType W (ρ.consts .value x'.name) (s.instantiate σ) := by
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
          exact (show ⊢ TinyML.ValsHaveTypes W (vl :: vls) (a.2 :: as'.map Prod.snd) -∗
                TinyML.ValHasType W (ρ.consts .value x'.name) (s.instantiate σ) by
              iintro Hvals
              ihave Hpair := (TinyML.ValsHaveTypes.cons W vl vls a.2 (as'.map Prod.snd)).1 $$ Hvals
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
                  simp at hΓ; subst hΓ
                  rw [← hlk_head]
                  simp only [TinyML.Scheme.instantiate_mono]
                  iexact Htype_head
                · simp [List.lookup, hxa] at hlookup)

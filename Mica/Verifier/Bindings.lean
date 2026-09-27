-- SUMMARY: Verifier variable-to-constant bindings, their semantic linkage to runtime substitutions, and typing/lookup lemmas.
import Mica.SourceTinyML.Typed
import Mica.SourceTinyML.Typing
import Mica.TinyML.OpSem
import Mica.FirstOrderLogic.Subst
import Mica.SourceTinyML.LogicalRelation

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]

/-! ### Bindings -/

abbrev Bindings := List (TinyML.Var × Decl.Const)

/-- The bindings a program starts with, paired with `TinyML.TyCtx.empty`. -/
abbrev Bindings.empty : Bindings := []

/-- A declaration that shadows a bound name without binding a value of its own
    must drop it, or the old constant would stand for the new value. -/
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
theorem Bindings.mem_of_mem_remove {B : Bindings} {x : TinyML.Var} {p : TinyML.Var × Decl.Const}
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

/-- The runtime substitution reads each bound name as the value its verifier
    constant denotes. Bindings are always at sort `.value`. -/
def Bindings.agreeOnLinked (B : Bindings) (ρ : Env) (γ : Runtime.Subst) :=
  ∀ x x', B.lookup x = some x' →
    x'.sort = .value ∧ γ x = .some (ρ.consts .value x'.name)

def Bindings.wfIn (B : Bindings) (decls : Signature) : Prop :=
  ∀ p ∈ B, p.2 ∈ decls.consts

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.agreeOnLinked_agreeOn {B : Bindings} {decls : Signature} {ρ ρ' : Env} {γ : Runtime.Subst}
    (hagr : B.agreeOnLinked ρ γ) (henv : Env.agreeOn decls ρ ρ')
    (hwf : B.wfIn decls) : B.agreeOnLinked ρ' γ := by
  intro x x' hmem
  obtain ⟨hsort, hγ⟩ := hagr x x' hmem
  obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hmem
  have hmem' : (x, x') ∈ B := by rw [heq]; simp
  have hdecl := hwf _ hmem'
  have henv' := henv.consts x' hdecl
  rw [hsort] at henv'
  exact ⟨hsort, hγ.trans (congrArg some henv')⟩

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.wfIn_cons {B : Bindings} {decls : Signature} {x : TinyML.Var} {v : Decl.Const}
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
theorem Bindings.agreeOnLinked_remove_update {B : Bindings} {ρ : Env} {γ : Runtime.Subst}
    (hagree : B.agreeOnLinked ρ γ) (x : TinyML.Var) (v : Runtime.Val) :
    (B.remove x).agreeOnLinked ρ (Runtime.Subst.update γ x v) := by
  intro y y' hmem
  rw [Bindings.lookup_remove] at hmem
  by_cases hyx : y == x
  · simp [hyx] at hmem
  · simp only [hyx, Bool.false_eq_true, if_false] at hmem
    obtain ⟨hsort, hγ⟩ := hagree y y' hmem
    exact ⟨hsort, by simp [Runtime.Subst.update, hyx, hγ]⟩

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.agreeOnLinked_remove {B : Bindings} {ρ : Env} {γ : Runtime.Subst}
    (hagree : B.agreeOnLinked ρ γ) (x : TinyML.Var) : (B.remove x).agreeOnLinked ρ γ := by
  intro y y' hmem
  rw [Bindings.lookup_remove] at hmem
  split at hmem
  · contradiction
  · exact hagree y y' hmem

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.agreeOnLinked_empty (ρ : Env) (γ : Runtime.Subst) :
    Bindings.empty.agreeOnLinked ρ γ := fun _ _ h => by simp [Bindings.empty] at h

omit [MicaGS HasLC.hasLC Sig] in
theorem Bindings.wfIn_empty (decls : Signature) : Bindings.empty.wfIn decls :=
  fun _ h => by simp [Bindings.empty] at h

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

theorem Bindings.typedSubst_empty (W : TinyML.World) (Γ : TinyML.TyCtx) (γ : Runtime.Subst) :
    ⊢ Bindings.typedSubst W Bindings.empty Γ γ := by
  unfold Bindings.typedSubst
  imodintro
  iintro %x %x' %t
  iintro %hlookup
  simp at hlookup

/-- Extend by a binding whose uses may instantiate it: the value is typed at
every instantiation of the scheme. -/
theorem Bindings.typedSubst_cons_scheme {B : Bindings} {Γ : TinyML.TyCtx} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : Decl.Const} {s : TinyML.Scheme} {w : Runtime.Val}
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
    {x : TinyML.Var} {v : Decl.Const} {te : TinyML.Typ} {w : Runtime.Val}
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
theorem Bindings.typedSubst_remove_update {B : Bindings} {Γ : TinyML.TyCtx} {γ : Runtime.Subst}
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

/-- Carries the invariant across a binder of the other kind: the new context can
    differ from the old only at the removed name. -/
theorem Bindings.typedSubst_remove {B : Bindings} {Γ Γ' : TinyML.TyCtx}
    {γ : Runtime.Subst} {x : TinyML.Var} (hΓ : ∀ y ≠ x, Γ' y = Γ y) :
    B.typedSubst W Γ γ ⊢ (B.remove x).typedSubst W Γ' γ := by
  unfold Bindings.typedSubst
  iintro #Hts
  imodintro
  iintro %y %y' %t %hmem %hΓy
  rw [Bindings.lookup_remove] at hmem
  by_cases hyx : y = x
  · simp [hyx] at hmem
  · simp only [beq_iff_eq, hyx, if_false] at hmem
    rw [hΓ y hyx] at hΓy
    ispecialize Hts $$ %y %y' %t %hmem %hΓy
    iexact Hts

/-! ### Values at their schemes

Between declarations a value has its scheme parametrically (`ValHasScheme`),
not just at every syntactic instantiation. Only the parametric reading
carries over to a larger world: an instantiation may name a type the smaller
world does not know. -/

/-- Every name in `B` denotes a value that has the scheme `Γ` gives it. -/
def Bindings.schemeSubst (W : TinyML.World) (B : Bindings) (Γ : TinyML.TyCtx)
    (γ : Runtime.Subst) : iProp :=
  iprop(□ ∀ x x' s, ⌜B.lookup x = some x'⌝ -∗ ⌜Γ x = some s⌝ -∗
    ∃ v, ⌜γ x = some v⌝ ∗ TinyML.ValHasScheme W v s)

instance Bindings.schemeSubst_persistent {B Γ γ} (W : TinyML.World) :
    Persistent (Bindings.schemeSubst W B Γ γ) := by
  unfold Bindings.schemeSubst
  infer_instance

theorem Bindings.schemeSubst_empty (W : TinyML.World) (Γ : TinyML.TyCtx) (γ : Runtime.Subst) :
    ⊢ Bindings.schemeSubst W Bindings.empty Γ γ := by
  unfold Bindings.schemeSubst
  imodintro
  iintro %x %x' %t %hlookup
  simp at hlookup

theorem Bindings.typedSubst_of_schemeSubst {W : TinyML.World} {B : Bindings}
    {Γ : TinyML.TyCtx} {γ : Runtime.Subst} :
    B.schemeSubst W Γ γ ⊢ B.typedSubst W Γ γ := by
  unfold Bindings.schemeSubst Bindings.typedSubst
  iintro #H
  imodintro
  iintro %x %x' %s %hl %hΓ
  icases H $$ %x %x' %s %hl %hΓ with ⟨%v, %hv, #Hv⟩
  iexists v
  isplitr
  · ipureintro; exact hv
  · iintro %σ
    iapply TinyML.ValHasScheme.instantiate
    iexact Hv

/-- Closed schemes do not read the assignment of the world. -/
theorem Bindings.schemeSubst_eta {W : TinyML.World} {B : Bindings} {Γ : TinyML.TyCtx}
    {γ : Runtime.Subst} (hΓ : Γ.Closed) (η : TinyML.SemTypeAssign) :
    B.schemeSubst W Γ γ ⊢ B.schemeSubst { W with eta := η } Γ γ := by
  unfold Bindings.schemeSubst
  iintro #H
  imodintro
  iintro %x %x' %s %hl %hΓx
  icases H $$ %x %x' %s %hl %hΓx with ⟨%v, %hv, #Hv⟩
  iexists v
  isplitr
  · ipureintro; exact hv
  · iapply (TinyML.ValHasScheme.eta_closed W v (hΓ x s hΓx) η).1
    iexact Hv

theorem Bindings.schemeSubst_of_subset {W₀ W : TinyML.World} (h : W₀.Subset W)
    (hΘ : TinyML.TypeEnv.wfIn W₀.Δ_spec W₀.Θ) {B : Bindings} {Γ : TinyML.TyCtx}
    {γ : Runtime.Subst} (hΓ : ∀ x s, Γ x = some s → TinyML.Typ.wfIn W₀.Δ_spec W₀.Θ s.ty) :
    B.schemeSubst W₀ Γ γ ⊢ B.schemeSubst W Γ γ := by
  unfold Bindings.schemeSubst
  iintro #H
  imodintro
  iintro %x %x' %s %hl %hΓx
  icases H $$ %x %x' %s %hl %hΓx with ⟨%v, %hv, #Hv⟩
  iexists v
  isplitr
  · ipureintro; exact hv
  · iapply (TinyML.ValHasScheme.of_subset h hΘ (hΓ x s hΓx) v)
    iexact Hv

theorem Bindings.schemeSubst_cons {W : TinyML.World} {B : Bindings} {Γ : TinyML.TyCtx}
    {γ : Runtime.Subst} {x : TinyML.Var} {c : Decl.Const} {s : TinyML.Scheme}
    {w : Runtime.Val} :
    ⊢ B.schemeSubst W Γ γ -∗ TinyML.ValHasScheme W w s -∗
      Bindings.schemeSubst W ((x, c) :: B) (Γ.extendScheme x s) (Runtime.Subst.update γ x w) := by
  iintro #H #Hw
  unfold Bindings.schemeSubst
  imodintro
  iintro %y %y' %t %hl %hΓ
  by_cases hyx : y == x
  · simp [List.lookup, hyx] at hl; subst hl
    simp [TinyML.TyCtx.extendScheme, hyx] at hΓ; subst hΓ
    iexists w
    isplitr
    · ipureintro
      simp [Runtime.Subst.update, hyx]
    · iexact Hw
  · simp [List.lookup, hyx] at hl
    have hΓ' : Γ y = some t := by simpa [TinyML.TyCtx.extendScheme, hyx] using hΓ
    icases H $$ %y %y' %t %hl %hΓ' with ⟨%w', %hw', #Hw'⟩
    iexists w'
    isplitr
    · ipureintro
      simp [Runtime.Subst.update, hyx, hw']
    · iexact Hw'

theorem Bindings.schemeSubst_remove_update {W : TinyML.World} {B : Bindings}
    {Γ : TinyML.TyCtx} {γ : Runtime.Subst} {x : TinyML.Var} {v : Runtime.Val} :
    B.schemeSubst W Γ γ ⊢ (B.remove x).schemeSubst W Γ (Runtime.Subst.update γ x v) := by
  unfold Bindings.schemeSubst
  iintro #H
  imodintro
  iintro %y %y' %t %hl %hΓ
  rw [Bindings.lookup_remove] at hl
  by_cases hyx : y == x
  · simp [hyx] at hl
  · simp only [hyx, Bool.false_eq_true, if_false] at hl
    icases H $$ %y %y' %t %hl %hΓ with ⟨%w, %hw, #Hw⟩
    iexists w
    isplitr
    · ipureintro
      simp [Runtime.Subst.update, hyx, hw]
    · iexact Hw

theorem Bindings.schemeSubst_remove {W : TinyML.World} {B : Bindings} {Γ : TinyML.TyCtx}
    {γ : Runtime.Subst} {x : TinyML.Var} :
    B.schemeSubst W Γ γ ⊢ (B.remove x).schemeSubst W Γ γ := by
  unfold Bindings.schemeSubst
  iintro #H
  imodintro
  iintro %y %y' %t %hl %hΓ
  rw [Bindings.lookup_remove] at hl
  by_cases hyx : y = x
  · simp [hyx] at hl
  · simp only [beq_iff_eq, hyx, if_false] at hl
    ispecialize H $$ %y %y' %t %hl %hΓ
    iexact H

/-! ### The typing of a whole scope -/

/-- Every name in scope denotes a value of the type `Γ` assigns it. `G` and `B`
are disjoint and `Γ` types their union, so one context serves both. Only a
run-time name stands for what the program substitutes; `γg` reads a ghost name
as its verifier constant denotes it. -/
def Bindings.typedScope (W : TinyML.World) (G B : Bindings) (Γ : TinyML.TyCtx)
    (γg γ : Runtime.Subst) : iProp :=
  iprop(G.typedSubst W Γ γg ∗ B.typedSubst W Γ γ)

instance Bindings.typedScope_persistent {G B Γ γg γ} (W : TinyML.World) :
    Persistent (Bindings.typedScope W G B Γ γg γ) := by
  unfold Bindings.typedScope
  infer_instance

/-- Until ghost code binds a name the run-time typing is the whole invariant. -/
theorem Bindings.typedScope_of_typedSubst {B : Bindings} {Γ : TinyML.TyCtx}
    {γ : Runtime.Subst} (W : TinyML.World) (γg : Runtime.Subst) :
    B.typedSubst W Γ γ ⊢ Bindings.typedScope W Bindings.empty B Γ γg γ := by
  unfold Bindings.typedScope
  iintro #HT
  isplitl []
  · iapply Bindings.typedSubst_empty
  · iexact HT

/-- A run-time binder: the name joins `B` at the type the context now gives it,
and leaves `G`, where the same context would otherwise type it wrongly. -/
theorem Bindings.typedScope_cons {G B : Bindings} {Γ : TinyML.TyCtx} {γg γ : Runtime.Subst}
    {x : TinyML.Var} {v : Decl.Const} {w : Runtime.Val} {te : TinyML.Typ}
    : ⊢ Bindings.typedScope W G B Γ γg γ -∗ TinyML.ValHasType W w te -∗
      Bindings.typedScope W (G.remove x) ((x, v) :: B) (Γ.extend x te) γg
        (Runtime.Subst.update γ x w) := by
  unfold Bindings.typedScope
  iintro ⟨#Hg, #Hb⟩ #Hw
  isplitl []
  · iapply (Bindings.typedSubst_remove (W := W) (B := G) (Γ := Γ) (Γ' := Γ.extend x te)
      (γ := γg) (x := x) (fun y hy => TinyML.TyCtx.extend_ne Γ x y te hy))
    iexact Hg
  · iapply (Bindings.typedSubst_cons (W := W))
    · iexact Hb
    · iexact Hw

/-- A ghost binder: the mirror of `typedScope_cons`. Only the ghost reading of
the name changes, because no run-time substitution ever reaches it. -/
theorem Bindings.typedScope_cons_ghost {G B : Bindings} {Γ : TinyML.TyCtx}
    {γg γ : Runtime.Subst} {x : TinyML.Var} {v : Decl.Const} {w : Runtime.Val}
    {te : TinyML.Typ}
    : ⊢ Bindings.typedScope W G B Γ γg γ -∗ TinyML.ValHasType W w te -∗
      Bindings.typedScope W ((x, v) :: G) (B.remove x) (Γ.extend x te)
        (Runtime.Subst.update γg x w) γ := by
  unfold Bindings.typedScope
  iintro ⟨#Hg, #Hb⟩ #Hw
  isplitl []
  · iapply (Bindings.typedSubst_cons (W := W))
    · iexact Hg
    · iexact Hw
  · iapply (Bindings.typedSubst_remove (W := W) (B := B) (Γ := Γ) (Γ' := Γ.extend x te)
      (γ := γ) (x := x) (fun y hy => TinyML.TyCtx.extend_ne Γ x y te hy))
    iexact Hb

omit [MicaGS HasLC.hasLC Sig] in
/-- Bind a name to a constant that already denotes the value the name is being
    bound to. -/
theorem Bindings.agreeOnLinked_cons_update {B : Bindings} {ρ : Env} {γ : Runtime.Subst}
    {x : TinyML.Var} {c : Decl.Const} {v : Runtime.Val}
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

/-- Read one bound name's typing out of the substitution. -/
theorem Bindings.valHasType_of_typedSubst {B : Bindings} {Γ : TinyML.TyCtx}
    {γ : Runtime.Subst} {ρ : Env} (hagree : B.agreeOnLinked ρ γ)
    {y : TinyML.Var} {y' : Decl.Const} {u : TinyML.Scheme} (σ : TinyML.TyVar → TinyML.Typ)
    (hy : B.lookup y = some y') (hΓ : Γ y = some u) :
    B.typedSubst W Γ γ ⊢ TinyML.ValHasType W (ρ.consts .value y'.name) (u.instantiate σ) := by
  unfold Bindings.typedSubst
  iintro #Hts
  ispecialize Hts $$ %y %y' %u %hy %hΓ
  icases Hts with ⟨%w, %hw, Hw⟩
  obtain ⟨_, hγy⟩ := hagree y y' hy
  rw [hγy] at hw
  injection hw with hw
  rw [← hw]
  ispecialize Hw $$ %σ
  iexact Hw


/-- Read one name's typing out of the scope, whichever half of it binds the
name. -/
theorem Bindings.typedScope_valHasType (W : TinyML.World) {G B : Bindings}
    {Γ : TinyML.TyCtx} {γg γ : Runtime.Subst} {ρ : Env}
    {x : TinyML.Var} {x' : Decl.Const} {u : TinyML.Scheme}
    (σ : TinyML.TyVar → TinyML.Typ)
    (hgagree : G.agreeOnLinked ρ γg) (hagree : B.agreeOnLinked ρ γ)
    (hx : G.lookup x = some x' ∨ B.lookup x = some x') (hΓ : Γ x = some u) :
    Bindings.typedScope W G B Γ γg γ ⊢
      TinyML.ValHasType W (ρ.consts .value x'.name) (u.instantiate σ) := by
  unfold Bindings.typedScope
  rcases hx with hx | hx
  · iintro ⟨#Hg, -⟩
    iapply (Bindings.valHasType_of_typedSubst (W := W) hgagree σ hx hΓ)
    iexact Hg
  · iintro ⟨-, #Hb⟩
    iapply (Bindings.valHasType_of_typedSubst (W := W) hagree σ hx hΓ)
    iexact Hb

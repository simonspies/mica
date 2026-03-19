import Mica.TinyML.Expr
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.FOL.Printing
import Mica.FOL.Subst
import Mica.Base.Fresh
import Mica.Base.Except
import Mathlib.Data.Finmap

/-! ### Bindings -/

abbrev Bindings := List (TinyML.Var × Var)

def Bindings.empty : Bindings := []

-- Every variable in Bindings is now declared at sort `.value`.
def Bindings.agreeOnLinked (B : Bindings) (ρ : Env) (γ : TinyML.Subst) :=
  ∀ x x', B.lookup x = some x' →
    x'.sort = .value ∧ γ x = .some (ρ.lookup .value x'.name)

def Bindings.wf (B : Bindings) (decls : VarCtx) : Prop :=
  ∀ p ∈ B, p.2 ∈ decls

theorem Bindings.agreeOnLinked_env_agree {B : Bindings} {decls : VarCtx} {ρ ρ' : Env} {γ : TinyML.Subst}
    (hagr : B.agreeOnLinked ρ γ) (henv : Env.agreeOn decls ρ ρ')
    (hwf : B.wf decls) : B.agreeOnLinked ρ' γ := by
  intro x x' hmem
  obtain ⟨hsort, hγ⟩ := hagr x x' hmem
  obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hmem
  have hmem' : (x, x') ∈ B := by rw [heq]; simp
  have hdecl := hwf _ hmem'
  have henv' := henv x' hdecl
  rw [hsort] at henv'
  exact ⟨hsort, hγ.trans (congrArg some henv')⟩

theorem Bindings.wf_cons {B : Bindings} {decls : VarCtx} {x : TinyML.Var} {v : Var}
    (hbwf : B.wf decls) :
    Bindings.wf ((x, v) :: B) (v :: decls) := by
  intro p hp
  simp [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact List.Mem.head _
  · exact List.Mem.tail _ (hbwf p hp)

/-- The substitution `γ` maps every binding to a value well-typed by `Γ`. -/
def Bindings.typedSubst (B : Bindings) (Γ : TinyML.TyCtx) (γ : TinyML.Subst) : Prop :=
  ∀ x x' t, B.lookup x = some x' → Γ x = some t → ∃ v, γ x = some v ∧ TinyML.ValHasType v t

/-! ### Term List Evaluation -/

/-- Pack a list of value-sorted terms into a `vallist`-sorted term using `.vcons` and `.vnil`. -/
def Terms.toValList : List (Term .value) → Term .vallist
  | [] => .const .vnil
  | t :: ts => .binop .vcons t (toValList ts)

@[simp] theorem Terms.toValList_nil : toValList [] = .const .vnil := rfl
@[simp] theorem Terms.toValList_cons (t : Term .value) (ts : List (Term .value)) :
    toValList (t :: ts) = .binop .vcons t (toValList ts) := rfl

/-- If all terms in `ts` are well-formed in `Δ`, then `toValList ts` is well-formed in `Δ`. -/
theorem Terms.toValList_wfIn {ts : List (Term .value)} {Δ : VarCtx}
    (h : ∀ t ∈ ts, t.wfIn Δ) : (toValList ts).wfIn Δ := by
  induction ts with
  | nil => intro w hw; simp [toValList, Term.freeVars] at hw
  | cons t ts ih =>
    simp only [toValList]
    intro w hw; simp [Term.freeVars] at hw
    rcases hw with hw | hw
    · exact h t (.head _) w hw
    · exact ih (fun q hq => h q (.tail _ hq)) w hw

/-- A list of terms evaluates to a list of values. -/
def Terms.Eval (ρ : Env) (ts : List (Term .value)) (vs : List TinyML.Val) : Prop :=
  List.Forall₂ (fun t v => t.eval ρ = v) ts vs

theorem Terms.Eval.map_eval {ρ : Env} {ts : List (Term .value)} {vs : List TinyML.Val}
    (h : Terms.Eval ρ ts vs) : ts.map (fun t => t.eval ρ) = vs := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

theorem Terms.toValList_eval {ρ : Env} {ts : List (Term .value)} {vs : List TinyML.Val}
    (h : Terms.Eval ρ ts vs) : (Terms.toValList ts).eval ρ = vs := by
  induction h with
  | nil => simp [Terms.toValList, Term.eval, Const.denote]
  | cons hhead _ ih => simp [Terms.toValList, Term.eval, BinOp.eval, hhead, ih]

theorem Terms.Eval.env_agree {ρ ρ' : Env} {Δ : VarCtx}
    {ts : List (Term .value)} {vs : List TinyML.Val}
    (hwf : ∀ t ∈ ts, t.wfIn Δ)
    (hagree : Env.agreeOn Δ ρ ρ')
    (h : Terms.Eval ρ ts vs) : Terms.Eval ρ' ts vs := by
  induction h with
  | nil => exact .nil
  | @cons t v ts' vs' htv _ ih =>
    constructor
    · rw [Term.eval_env_agree (hwf t (.head _)) (Env.agreeOn_symm hagree)]; exact htv
    · exact ih (fun q hq => hwf q (.tail _ hq))

theorem Terms.Eval.cons {ρ : Env} {t : Term .value} {v : TinyML.Val}
    {ts : List (Term .value)} {vs : List TinyML.Val}
    (hhead : t.eval ρ = v)
    (htail : Terms.Eval ρ ts vs) :
    Terms.Eval ρ (t :: ts) (v :: vs) :=
  List.Forall₂.cons hhead htail

theorem Terms.Eval.of_pairs {ρ : Env} {pairs : List (TinyML.Type_ × Term .value)} {vs : List TinyML.Val}
    (h : List.Forall₂ (fun p v => p.2.eval ρ = v) pairs vs) :
    Terms.Eval ρ (pairs.map Prod.snd) vs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

theorem Terms.Eval.lookup_var {ρ : Env} {avs : List Var} {vs : List TinyML.Val}
    (h : Terms.Eval ρ (avs.map (fun av => .var .value av.name)) vs) :
    List.Forall₂ (fun av val => ρ.lookup .value av.name = val) avs vs := by
  generalize hts : avs.map (fun av => Term.var .value av.name) = ts at h
  induction h generalizing avs with
  | nil =>
    cases avs with
    | nil => exact .nil
    | cons _ _ => simp at hts
  | cons hhead htail ih =>
    cases avs with
    | nil => simp at hts
    | cons av avs' =>
      simp only [List.map_cons, List.cons.injEq] at hts
      obtain ⟨rfl, rfl⟩ := hts
      constructor
      · exact hhead
      · exact ih rfl

/-! ### Helpers for Multi-Argument Bindings -/

theorem Bindings.typedSubst_cons {B : Bindings} {Γ : TinyML.TyCtx} {γ : TinyML.Subst}
    {x : TinyML.Var} {v : Var} {te : TinyML.Type_} {w : TinyML.Val}
    (hts  : B.typedSubst Γ γ)
    (hval : TinyML.ValHasType w te) :
    Bindings.typedSubst ((x, v) :: B) (Γ.extend x te) (TinyML.Subst.update γ x w) := by
  intro y y' t hmem hΓ
  by_cases hyx : y == x
  · -- head case: y = x
    simp [List.lookup, hyx] at hmem; subst hmem
    simp [TinyML.TyCtx.extend, hyx] at hΓ; subst hΓ
    exact ⟨w, by simp [TinyML.Subst.update, hyx], hval⟩
  · -- tail case: y ≠ x
    simp [List.lookup, hyx] at hmem
    have hΓ' : Γ y = some t := by simp [TinyML.TyCtx.extend, hyx] at hΓ; exact hΓ
    obtain ⟨w', hw', hwt'⟩ := hts y y' t hmem hΓ'
    exact ⟨w', by simp [TinyML.Subst.update, hyx, hw'], hwt'⟩

theorem Bindings.agreeOnLinked_cons {B : Bindings} {ρ ρ' : Env} {γ : TinyML.Subst}
    {x : TinyML.Var} {v : Var}
    (hagree : B.agreeOnLinked ρ γ)
    (hρ_agree : Env.agreeOn (B.map Prod.snd) ρ' ρ)
    (hvty : v.sort = .value) :
    Bindings.agreeOnLinked ((x, v) :: B) ρ' (TinyML.Subst.update γ x (ρ'.lookup .value v.name)) := by
  intro y y' hmem
  by_cases hyx : y == x
  · simp [List.lookup, hyx] at hmem; subst hmem
    exact ⟨hvty, by simp [TinyML.Subst.update, hyx]⟩
  · simp [List.lookup, hyx] at hmem
    obtain ⟨hsort, hγ⟩ := hagree y y' hmem
    have hmem_snd : y' ∈ B.map Prod.snd := by
      obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hmem
      exact List.mem_map.mpr ⟨(y, y'), by rw [heq]; simp, rfl⟩
    have hρ := hρ_agree y' hmem_snd
    rw [hsort] at hρ
    exact ⟨hsort, by simp [TinyML.Subst.update, hyx]; exact hγ.trans (congrArg some hρ.symm)⟩

-- If agreeOnLinked holds and values at each binding are well-typed, then typedSubst holds.
theorem Bindings.typedSubst_of_agreeOnLinked
    {B : Bindings} {Γ : TinyML.TyCtx} {γ : TinyML.Subst} {ρ : Env}
    (hagree : B.agreeOnLinked ρ γ)
    (htyped_vals : ∀ x x' t, B.lookup x = some x' → Γ x = some t →
      TinyML.ValHasType (ρ.lookup .value x'.name) t) :
    B.typedSubst Γ γ := by
  intro x x' t hmem hΓ
  obtain ⟨_, hval⟩ := hagree x x' hmem
  exact ⟨_, hval, htyped_vals x x' t hmem hΓ⟩

theorem findVal_none_of_not_mem
    (ns : List String) (vs : List TinyML.Val) (x : String)
    (hlen : ns.length = vs.length) (hx : x ∉ ns) :
    TinyML.Binders.findVal (ns.map TinyML.Binder.named) vs x = none := by
  induction ns generalizing vs with
  | nil => simp
  | cons n ns ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp at hlen hx
      simp only [List.map_cons, TinyML.Binders.findVal_cons, ih vs hlen hx.2]
      simp [TinyML.Binder.named_beq, beq_iff_eq, Ne.symm hx.1]

theorem not_mem_of_lookup_zip_reverse_none
    (ns : List String) (avs : List Var) (x : String)
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

theorem argVars_cons_perm {name : String}
    {rest : List (String × TinyML.Type_)} {dom : List Var} {x : Var}
    (hx : x ∈ (⟨name, .value⟩ :: rest.map (fun (name, _) => ⟨name, .value⟩) ++ dom)) :
    x ∈ (rest.map (fun (name, _) => ⟨name, .value⟩) ++ ⟨name, .value⟩ :: dom) := by
  simp only [List.cons_append, List.mem_cons,
    List.mem_append, List.mem_map] at hx ⊢
  rcases hx with rfl | ⟨a, ha, rfl⟩ | hmem
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl ⟨a, ha, rfl⟩
  · exact Or.inr (Or.inr hmem)

/-- Extract argument names from binders, pairing with spec arg info.
    Requires exact length match. -/
def extractArgNames : List (TinyML.Binder × Option TinyML.Type_) → List (String × TinyML.Type_) →
    Except String (List String)
  | [], [] => .ok []
  | (.named x, _) :: rest, _ :: specRest => do
    let tail ← extractArgNames rest specRest
    .ok (x :: tail)
  | _, _ => .error "argument mismatch"

theorem extractArgNames_spec {argBinders : List (TinyML.Binder × Option TinyML.Type_)}
    {specArgs : List (String × TinyML.Type_)} {names : List String}
    (h : extractArgNames argBinders specArgs = .ok names) :
    names.length = specArgs.length ∧
    argBinders.length = specArgs.length ∧
    argBinders.map Prod.fst = names.map TinyML.Binder.named := by
  induction specArgs generalizing argBinders names with
  | nil =>
    cases argBinders with
    | nil => simp [extractArgNames] at h; subst h; simp
    | cons _ _ => simp [extractArgNames] at h
  | cons sa sas ih =>
    cases argBinders with
    | nil => simp [extractArgNames] at h
    | cons ab abs =>
      obtain ⟨b, ty⟩ := ab
      cases b with
      | none => simp [extractArgNames] at h
      | named x =>
        unfold extractArgNames at h
        cases hrec : extractArgNames abs sas with
        | error => rw [hrec] at h; exact absurd h (by intro hc; cases hc)
        | ok tail =>
          rw [hrec] at h
          have h' : names = x :: tail := by cases h; rfl
          subst h'
          obtain ⟨h1, h2, h3⟩ := ih hrec
          exact ⟨by simp [h1], by simp [h2], by simp [h3]⟩

theorem Bindings.agreeOnLinked_zip_reverse
    (names : List String) (vars : List Var) (vals : List TinyML.Val)
    (γ : TinyML.Subst) (ρ : Env)
    (hlen_nv : names.length = vars.length)
    (hlen_nvl : names.length = vals.length)
    (hsorts : ∀ v ∈ vars, v.sort = .value)
    (hlookups : List.Forall₂ (fun av val => ρ.lookup .value av.name = val) vars vals) :
    Bindings.agreeOnLinked (names.zip vars).reverse ρ
      (γ.updateAll' (names.map TinyML.Binder.named) vals) := by
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
          simp only [List.map_cons, TinyML.Subst.updateAll'_cons, List.zip_cons_cons, List.reverse_cons]
          have ih' := ih avs vs (γ.update' (.named n) v) (by omega) (by omega)
            (fun v' hv' => hsorts v' (.tail _ hv')) htail
          intro x x' hmem
          -- hmem : List.lookup x ((ns.zip avs).reverse ++ [(n, av)]) = some x'
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
              · -- Need: updateAll' (ns.map .named) vs (update' (.named n) v γ) x = some v
                rw [TinyML.Subst.updateAll'_eq _ _ _ _ (by simp; omega)]
                have hx_notin := not_mem_of_lookup_zip_reverse_none ns avs x hlen_nv hlk_inner
                suffices TinyML.Binders.findVal (ns.map TinyML.Binder.named) vs x = none by
                  simp [this, TinyML.Subst.update', hxn, ← hlk]
                exact findVal_none_of_not_mem ns vs x hlen_nvl hx_notin
            · simp [List.lookup, hxn] at hmem

theorem Bindings.lookup_reverse_zip_append {keys : List String} {vars : List Var} {x : String} (B : Bindings) :
    ((keys.zip vars).reverse ++ B).lookup x =
      ((keys.zip vars).reverse.lookup x).or (B.lookup x) := by
  rw [List.lookup_append]

theorem Bindings.agreeOnLinked_updateAll'
    (B : Bindings) (names : List String) (vars : List Var) (vals : List TinyML.Val)
    (γ : TinyML.Subst) (ρ : Env)
    (hB : B.agreeOnLinked ρ γ)
    (hlen_nv : names.length = vars.length)
    (hlen_nvl : names.length = vals.length)
    (hsorts : ∀ v ∈ vars, v.sort = .value)
    (hlookups : List.Forall₂ (fun av val => ρ.lookup .value av.name = val) vars vals) :
    Bindings.agreeOnLinked ((names.zip vars).reverse ++ B) ρ
      (γ.updateAll' (names.map TinyML.Binder.named) vals) := by
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
    · rw [TinyML.Subst.updateAll'_eq _ _ _ _ (by simp; omega)]
      have hx_notin := not_mem_of_lookup_zip_reverse_none names vars x hlen_nv hlk
      rw [findVal_none_of_not_mem names vals x (by omega) hx_notin]
      exact hγ

-- For lists with "last wins" semantics: if the reversed-zip lookup finds x' at x,
-- and the foldl-Γ lookup finds type t at x, and Forall₂ relates vars to vals
-- with ValsHaveTypes, then the value at x' has type t.
-- All three structures agree on the "last occurrence" of x.
theorem val_typed_of_last_wins
    (args : List (String × TinyML.Type_))
    (vars : List Var) (vals : List TinyML.Val)
    (ρ : Env) (Γ₀ : TinyML.TyCtx)
    (x : String) (x' : Var) (t : TinyML.Type_)
    (hlen_v : (args.map Prod.fst).length = vars.length)
    (hlen_vl : (args.map Prod.fst).length = vals.length)
    (hlookup : List.lookup x ((args.map Prod.fst).zip vars).reverse = some x')
    (hΓ : (args.foldl (fun ctx a => ctx.extend a.1 a.2) Γ₀) x = some t)
    (hlookups : List.Forall₂ (fun av val => ρ.lookup .value av.name = val) vars vals)
    (htyped : TinyML.ValsHaveTypes vals (args.map Prod.snd))
    -- If x is not found in args, Γ₀ is irrelevant because hlookup guarantees x IS in args.
    : TinyML.ValHasType (ρ.lookup .value x'.name) t := by
  induction args generalizing vars vals Γ₀ with
  | nil => simp at hlookup
  | cons a as ih =>
    cases vars with
    | nil => simp at hlen_v
    | cons vr vrs =>
      cases vals with
      | nil => simp at hlen_vl
      | cons vl vls =>
        simp [List.map_cons, List.length_cons] at hlen_v hlen_vl
        cases hlookups with
        | cons hlk_head hlk_tail =>
          cases htyped with
          | cons htype_head htype_tail =>
            simp only [List.map_cons, List.zip_cons_cons, List.reverse_cons] at hlookup
            rw [List.lookup_append] at hlookup
            simp only [List.foldl_cons] at hΓ
            cases hlk_inner : List.lookup x ((as.map Prod.fst).zip vrs).reverse with
            | some v' =>
              -- Found in the tail — IH handles it
              simp [hlk_inner] at hlookup; subst hlookup
              exact ih vrs vls (Γ₀.extend a.1 a.2) (by simp; omega) (by simp; omega) hlk_inner hΓ hlk_tail htype_tail
            | none =>
              -- Not in the tail — must be from the head entry [(a.1, vr)]
              simp [hlk_inner] at hlookup
              by_cases hxa : x == a.1
              · simp [List.lookup, hxa] at hlookup; subst hlookup
                -- x = a.1, x' = vr, t comes from foldl extend.
                -- Since x not in tail (hlk_inner = none), and the tail's foldl
                -- doesn't add x back, Γ x = a.2 (from the initial extend of a).
                -- Need: foldl extend (Γ₀.extend a.1 a.2) as x = some t
                -- and x ∉ as.map fst (from hlk_inner), so foldl doesn't overwrite.
                have hx_notin := not_mem_of_lookup_zip_reverse_none
                  (as.map Prod.fst) vrs x (by simp; omega) hlk_inner
                simp [List.mem_map] at hx_notin
                -- hΓ : (as.foldl ... (Γ₀.extend a.1 a.2)) x = some t
                -- Since x ∉ as.map fst, foldl doesn't overwrite the initial extend.
                -- So t = a.2 and we need ValHasType (ρ.lookup .value vr.name) a.2.
                have hΓ_stable : (as.foldl (fun ctx a => ctx.extend a.1 a.2) (Γ₀.extend a.1 a.2)) x =
                    (Γ₀.extend a.1 a.2) x := by
                  apply TinyML.TyCtx.foldl_extend_stable
                  intro ⟨n, t⟩ hmem heq; exact hx_notin t (heq ▸ hmem)
                rw [hΓ_stable] at hΓ
                have hxa' : x = a.1 := by exact beq_iff_eq.mp hxa
                subst hxa'
                simp [TinyML.TyCtx.extend] at hΓ; subst hΓ
                rw [← hlk_head] at htype_head; exact htype_head
              · simp [List.lookup, hxa] at hlookup

-- ---------------------------------------------------------------------------
-- FiniteSubst
-- ---------------------------------------------------------------------------

structure FiniteSubst where
  subst : Subst
  dom   : List Var
  range : List Var

def FiniteSubst.id : FiniteSubst where
  subst := Subst.id
  dom   := []
  range := []

def FiniteSubst.wf (σ : FiniteSubst) (decls : List Var) : Prop :=
  σ.subst.wfIn σ.dom σ.range ∧ σ.range ⊆ decls

def FiniteSubst.rename (σ : FiniteSubst) (v : Var) (name' : String) : FiniteSubst where
  subst := σ.subst.update v.sort v.name (.var v.sort name')
  dom   := v :: σ.dom
  range := ⟨name', v.sort⟩ :: σ.range

theorem agreeOn_update_fresh {ρ : Env} {v : Var} {u : v.sort.denote}
    {decls : List Var} (hfresh : v.name ∉ decls.map Var.name) :
    Env.agreeOn decls ρ (ρ.update v.sort v.name u) := by
  intro w hw
  have hne : w.name ≠ v.name := by
    intro heq; exact hfresh (heq ▸ List.mem_map.mpr ⟨w, hw, rfl⟩)
  exact (Env.lookup_update_ne (Or.inl hne)).symm

theorem FiniteSubst.rename_wf {σ : FiniteSubst} {v : Var} {name' : String} {decls : List Var}
    (hσ : σ.wf decls) (_hfresh : ⟨name', v.sort⟩ ∉ σ.range) :
    (σ.rename v name').wf (⟨name', v.sort⟩ :: decls) := by
  refine ⟨?_, List.cons_subset_cons _ hσ.2⟩
  -- (σ.rename v name').subst.wfIn (v :: σ.dom) (⟨name', v.sort⟩ :: σ.range)
  apply Subst.wfIn_update (Subst.wfIn_mono hσ.1 (List.subset_cons_of_subset _ (List.Subset.refl _)))
  intro w hw
  simp [Term.freeVars] at hw
  exact hw ▸ List.mem_cons_self ..

theorem FiniteSubst.rename_agreeOn {σ : FiniteSubst} {v : Var} {name' : String}
    {ρ : Env} {u : v.sort.denote}
    (hσwf : σ.subst.wfIn σ.dom σ.range) (hfresh : ⟨name', v.sort⟩ ∉ σ.range) :
    Env.agreeOn (v :: σ.dom)
      ((σ.rename v name').subst.eval (ρ.update v.sort name' u))
      ((σ.subst.eval ρ).update v.sort v.name u) :=
  Subst.eval_update_agreeOn hσwf hfresh

theorem FiniteSubst.eval_update_fresh {σ : FiniteSubst} {ρ : Env} {τ : Srt} {name' : String}
    {u : τ.denote} (hσ : σ.subst.wfIn σ.dom σ.range) (hfresh : ⟨name', τ⟩ ∉ σ.range) :
    Env.agreeOn σ.dom (σ.subst.eval ρ) (σ.subst.eval (ρ.update τ name' u)) := by
  intro w hw
  simp only [Subst.eval_lookup]
  exact (Term.eval_update_fresh (fun hfv => hfresh (hσ w hw _ hfv))).symm

theorem FiniteSubst.subst_wfIn_formula {σ : FiniteSubst} {φ : Formula} {decls : List Var}
    (hσ : σ.wf decls) (hφ : φ.wfIn σ.dom) : (φ.subst σ.subst σ.range).wfIn decls := by
  have h1 : σ.subst.wfIn σ.dom σ.range := hσ.1
  have h2 : (φ.subst σ.subst σ.range).wfIn σ.range := Formula.subst_wfIn hφ h1
  exact Formula.wfIn_mono _ h2 hσ.2

theorem FiniteSubst.eval_subst_formula {σ : FiniteSubst} {φ : Formula} {ρ : Env}
    (hφ : φ.wfIn σ.dom) (hσ : σ.subst.wfIn σ.dom σ.range) :
    (φ.subst σ.subst σ.range).eval ρ ↔ φ.eval (σ.subst.eval ρ) :=
  Formula.eval_subst hφ hσ

theorem FiniteSubst.id_wf (decls : List Var) : FiniteSubst.id.wf decls := by
  constructor
  · intro v hv; simp [FiniteSubst.id] at hv
  · intro v hv; simp [FiniteSubst.id] at hv

theorem FiniteSubst.eval_agreeOn {σ : FiniteSubst} {ρ ρ' : Env}
    (hσ : σ.subst.wfIn σ.dom σ.range) (hagree : Env.agreeOn σ.range ρ ρ') :
    Env.agreeOn σ.dom (σ.subst.eval ρ) (σ.subst.eval ρ') := by
  intro v hv
  simp only [Subst.eval_lookup]
  exact Term.eval_env_agree (hσ v hv) hagree

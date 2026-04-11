import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.FOL.Printing
import Mica.FOL.Subst
import Mica.Base.Fresh
import Mica.Base.Except
import Mathlib.Data.Finmap

/-! ### Bindings -/

abbrev Bindings := List (TinyML.Var × FOL.Const)

def Bindings.empty : Bindings := []

-- Every variable in Bindings is now declared at sort `.value`.
def Bindings.agreeOnLinked (B : Bindings) (ρ : Env) (γ : Runtime.Subst) :=
  ∀ x x', B.lookup x = some x' →
    x'.sort = .value ∧ γ x = .some (ρ.consts .value x'.name)

def Bindings.wf (B : Bindings) (decls : Signature) : Prop :=
  ∀ p ∈ B, p.2 ∈ decls.consts

theorem Bindings.agreeOnLinked_env_agree {B : Bindings} {decls : Signature} {ρ ρ' : Env} {γ : Runtime.Subst}
    (hagr : B.agreeOnLinked ρ γ) (henv : Env.agreeOn decls ρ ρ')
    (hwf : B.wf decls) : B.agreeOnLinked ρ' γ := by
  intro x x' hmem
  obtain ⟨hsort, hγ⟩ := hagr x x' hmem
  obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hmem
  have hmem' : (x, x') ∈ B := by rw [heq]; simp
  have hdecl := hwf _ hmem'
  have henv' := henv.2.1 x' hdecl
  rw [hsort] at henv'
  exact ⟨hsort, hγ.trans (congrArg some henv')⟩

theorem Bindings.wf_cons {B : Bindings} {decls : Signature} {x : TinyML.Var} {v : FOL.Const}
    (hbwf : B.wf decls) :
    Bindings.wf ((x, v) :: B) (decls.addConst v) := by
  intro p hp
  simp [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact List.Mem.head _
  · exact List.Mem.tail _ (hbwf p hp)

/-- The substitution `γ` maps every binding to a value well-typed by `Γ`. -/
def Bindings.typedSubst (Θ : TinyML.TypeEnv) (B : Bindings) (Γ : TinyML.TyCtx) (γ : Runtime.Subst) : Prop :=
  ∀ x x' t, B.lookup x = some x' → Γ x = some t → ∃ v, γ x = some v ∧ TinyML.ValHasType Θ v t

/-! ### Term List Evaluation -/

/-- Pack a list of value-sorted terms into a `vallist`-sorted term using `.vcons` and `.vnil`. -/
def Terms.toValList : List (Term .value) → Term .vallist
  | [] => .const .vnil
  | t :: ts => .binop .vcons t (toValList ts)

@[simp] theorem Terms.toValList_nil : toValList [] = .const .vnil := rfl
@[simp] theorem Terms.toValList_cons (t : Term .value) (ts : List (Term .value)) :
    toValList (t :: ts) = .binop .vcons t (toValList ts) := rfl

/-- If all terms in `ts` are well-formed in `Δ`, then `toValList ts` is well-formed in `Δ`. -/
theorem Terms.toValList_wfIn {ts : List (Term .value)} {Δ : Signature}
    (h : ∀ t ∈ ts, t.wfIn Δ) : (toValList ts).wfIn Δ := by
  induction ts with
  | nil => trivial
  | cons t ts ih =>
    simp only [toValList, Term.wfIn]
    exact ⟨trivial, h t (.head _), ih (fun q hq => h q (.tail _ hq))⟩

/-- A list of terms evaluates to a list of values. -/
def Terms.Eval (ρ : Env) (ts : List (Term .value)) (vs : List Runtime.Val) : Prop :=
  List.Forall₂ (fun t v => t.eval ρ = v) ts vs

theorem Terms.Eval.map_eval {ρ : Env} {ts : List (Term .value)} {vs : List Runtime.Val}
    (h : Terms.Eval ρ ts vs) : ts.map (fun t => t.eval ρ) = vs := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

theorem Terms.toValList_eval {ρ : Env} {ts : List (Term .value)} {vs : List Runtime.Val}
    (h : Terms.Eval ρ ts vs) : (Terms.toValList ts).eval ρ = vs := by
  induction h with
  | nil => simp [Terms.toValList, Term.eval, Const.denote]
  | cons hhead _ ih => simp [Terms.toValList, Term.eval, BinOp.eval, hhead, ih]

theorem Terms.Eval.env_agree {ρ ρ' : Env} {Δ : Signature}
    {ts : List (Term .value)} {vs : List Runtime.Val}
    (hwf : ∀ t ∈ ts, t.wfIn Δ)
    (hagree : Env.agreeOn Δ ρ ρ')
    (h : Terms.Eval ρ ts vs) : Terms.Eval ρ' ts vs := by
  induction h with
  | nil => exact .nil
  | @cons t v ts' vs' htv _ ih =>
    constructor
    · rw [Term.eval_env_agree (hwf t (.head _)) (Env.agreeOn_symm hagree)]; exact htv
    · exact ih (fun q hq => hwf q (.tail _ hq))

theorem Terms.Eval.cons {ρ : Env} {t : Term .value} {v : Runtime.Val}
    {ts : List (Term .value)} {vs : List Runtime.Val}
    (hhead : t.eval ρ = v)
    (htail : Terms.Eval ρ ts vs) :
    Terms.Eval ρ (t :: ts) (v :: vs) :=
  List.Forall₂.cons hhead htail

theorem Terms.Eval.of_pairs {ρ : Env} {pairs : List (TinyML.Typ × Term .value)} {vs : List Runtime.Val}
    (h : List.Forall₂ (fun p v => p.2.eval ρ = v) pairs vs) :
    Terms.Eval ρ (pairs.map Prod.snd) vs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

theorem Terms.Eval.lookup_var {ρ : Env} {avs : List Var} {vs : List Runtime.Val}
    (h : Terms.Eval ρ (avs.map (fun av => .var .value av.name)) vs) :
    List.Forall₂ (fun av val => ρ.lookupConst .value av.name = val) avs vs := by
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

theorem Terms.Eval.lookup_const {ρ : Env} {avs : List FOL.Const} {vs : List Runtime.Val}
    (h : Terms.Eval ρ (avs.map (fun av => .const (.uninterpreted av.name .value))) vs) :
    List.Forall₂ (fun av val => ρ.consts .value av.name = val) avs vs := by
  generalize hts : avs.map (fun av => Term.const (.uninterpreted av.name .value)) = ts at h
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
      · simp [Term.eval, Const.denote] at hhead; exact hhead
      · exact ih rfl

/-! ### Helpers for Multi-Argument Bindings -/

theorem Bindings.typedSubst_cons {B : Bindings} {Γ : TinyML.TyCtx} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : FOL.Const} {te : TinyML.Typ} {w : Runtime.Val}
    (hts  : B.typedSubst Θ Γ γ)
    (hval : TinyML.ValHasType Θ w te) :
    Bindings.typedSubst Θ ((x, v) :: B) (Γ.extend x te) (Runtime.Subst.update γ x w) := by
  intro y y' t hmem hΓ
  by_cases hyx : y == x
  · -- head case: y = x
    simp [List.lookup, hyx] at hmem; subst hmem
    simp [TinyML.TyCtx.extend, hyx] at hΓ; subst hΓ
    exact ⟨w, by simp [Runtime.Subst.update, hyx], hval⟩
  · -- tail case: y ≠ x
    simp [List.lookup, hyx] at hmem
    have hΓ' : Γ y = some t := by simp [TinyML.TyCtx.extend, hyx] at hΓ; exact hΓ
    obtain ⟨w', hw', hwt'⟩ := hts y y' t hmem hΓ'
    exact ⟨w', by simp [Runtime.Subst.update, hyx, hw'], hwt'⟩

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
    (htyped_vals : ∀ x x' t, B.lookup x = some x' → Γ x = some t →
      TinyML.ValHasType Θ (ρ.consts .value x'.name) t) :
    B.typedSubst Θ Γ γ := by
  intro x x' t hmem hΓ
  obtain ⟨_, hval⟩ := hagree x x' hmem
  exact ⟨_, hval, htyped_vals x x' t hmem hΓ⟩

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

theorem argVars_cons_perm {name : String}
    {rest : List (String × TinyML.Typ)} {dom : List Var} {x : Var}
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
def extractArgNames : List Typed.Binder → List (String × TinyML.Typ) →
    Except String (List String)
  | [], [] => .ok []
  | ⟨some x, _⟩ :: rest, _ :: specRest => do
      let tail ← extractArgNames rest specRest
      .ok (x :: tail)
  | _, _ => .error "argument mismatch"

theorem extractArgNames_spec {argBinders : List Typed.Binder}
    {specArgs : List (String × TinyML.Typ)} {names : List String}
    (h : extractArgNames argBinders specArgs = .ok names) :
    names.length = specArgs.length ∧
    argBinders.length = specArgs.length ∧
    argBinders.map Typed.Binder.runtime = names.map Runtime.Binder.named := by
  induction specArgs generalizing argBinders names with
  | nil =>
    cases argBinders with
    | nil => simp [extractArgNames] at h; subst h; simp
    | cons _ _ => simp [extractArgNames] at h
  | cons sa sas ih =>
    cases argBinders with
    | nil => simp [extractArgNames] at h
    | cons ab abs =>
      cases ab with
      | mk name ty =>
        cases name with
        | none =>
          simp [extractArgNames] at h
        | some x =>
          simp [extractArgNames] at h
          cases hrec : extractArgNames abs sas with
          | error =>
              simp [hrec] at h
              cases h
          | ok tail =>
              simp [hrec] at h
              cases h
              obtain ⟨h1, h2, h3⟩ := ih hrec
              exact ⟨by simp [h1], by simp [h2], by simp [Typed.Binder.runtime, h3]⟩

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
                rw [Runtime.Subst.updateAll'_eq _ _ _ _ (by simp; omega)]
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
    (htyped : TinyML.ValsHaveTypes Θ vals (args.map Prod.snd))
    : TinyML.ValHasType Θ (ρ.consts .value x'.name) t := by
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
              simp [hlk_inner] at hlookup; subst hlookup
              exact ih vrs vls (Γ₀.extend a.1 a.2) (by simp; omega) (by simp; omega) hlk_inner hΓ hlk_tail htype_tail
            | none =>
              simp [hlk_inner] at hlookup
              by_cases hxa : x == a.1
              · simp [List.lookup, hxa] at hlookup; subst hlookup
                have hx_notin := not_mem_of_lookup_zip_reverse_none
                  (as.map Prod.fst) vrs x (by simp; omega) hlk_inner
                simp [List.mem_map] at hx_notin
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
  range : Signature

def FiniteSubst.id : FiniteSubst where
  subst := Subst.id
  dom   := []
  range := Signature.empty

def FiniteSubst.wf (σ : FiniteSubst) (Δ : Signature) : Prop :=
  σ.subst.wfIn σ.dom σ.range ∧ σ.range.Subset Δ ∧ σ.range.wf

def FiniteSubst.rename (σ : FiniteSubst) (v : Var) (name' : String) : FiniteSubst where
  subst := (σ.subst.eraseName v.name).update v.sort v.name (.const (.uninterpreted name' v.sort))
  dom   := v :: σ.dom.filter (·.name != v.name)
  range := σ.range.addConst ⟨name', v.sort⟩

theorem FiniteSubst.rename_dom_wf {σ : FiniteSubst} {v : Var} {name' : String}
    (hdomwf : (Signature.ofVars σ.dom).wf) :
    (Signature.ofVars (σ.rename v name').dom).wf := by
  simpa [FiniteSubst.rename, Signature.ofVars, Signature.declVar, Signature.remove] using
    (Signature.wf_declVar (Δ := Signature.ofVars σ.dom) (v := v) hdomwf)

theorem agreeOn_update_fresh {ρ : Env} {v : Var} {u : v.sort.denote}
    {Δ : Signature} (hfresh : v.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateConst v.sort v.name u) := by
  constructor
  · intro w hw
    have hne : w.name ≠ v.name := by
      intro heq
      apply hfresh
      rw [← heq]
      exact Signature.mem_allNames_of_var hw
    exact (Env.lookupConst_updateConst_ne (Or.inl hne)).symm
  · constructor
    · intro c hc
      have hne : c.name ≠ v.name := by
        intro heq
        apply hfresh
        rw [← heq]
        exact Signature.mem_allNames_of_const hc
      exact (Env.lookupConst_updateConst_ne (Or.inl hne)).symm
    · constructor
      · intro u' hu'
        rw [Env.updateConst_unary]
      · intro b' hb'
        rw [Env.updateConst_binary]

theorem FiniteSubst.rename_wf {σ : FiniteSubst} {v : Var} {name' : String} {Δ : Signature}
    (hσ : σ.wf Δ) (hfresh : name' ∉ σ.range.allNames) :
    (σ.rename v name').wf (Δ.addConst ⟨name', v.sort⟩) := by
  rcases hσ with ⟨hsubst, hrange, hwfRange⟩
  constructor
  · have hrangeWf : (σ.range.addConst ⟨name', v.sort⟩).wf :=
      Signature.wf_addConst hwfRange hfresh
    have hsubst' : σ.subst.wfIn σ.dom (σ.range.addConst ⟨name', v.sort⟩) :=
      Subst.wfIn_mono hsubst (Signature.Subset.subset_addConst _ _) hrangeWf
    have herase :
        (σ.subst.eraseName v.name).wfIn (σ.dom.filter (fun w => w.name != v.name))
          (σ.range.addConst ⟨name', v.sort⟩) :=
      Subst.wfIn_eraseName hsubst'
    have hconstwf : (Term.const (.uninterpreted name' v.sort)).wfIn (σ.range.addConst ⟨name', v.sort⟩) := by
      refine ⟨List.Mem.head _, ?_, ?_⟩
      · intro τ' hvar
        exact Signature.wf_no_var_of_const hrangeWf (List.Mem.head _) hvar
      · intro τ' hc'
        exact Signature.wf_unique_const hrangeWf (List.Mem.head _) hc'
    simpa [FiniteSubst.rename] using
      (Subst.wfIn_update (σ := σ.subst.eraseName v.name)
        (dom := σ.dom.filter (fun w => w.name != v.name))
        (τ := v.sort) (x := v.name) herase hconstwf)
  · constructor
    · constructor
      · intro x hx
        exact hrange.vars x hx
      · intro c hc
        cases hc with
        | head => exact List.Mem.head _
        | tail _ hc => exact List.Mem.tail _ (hrange.consts c hc)
      · intro u hu
        exact hrange.unary u hu
      · intro b hb
        exact hrange.binary b hb
    · exact Signature.wf_addConst hwfRange hfresh

theorem FiniteSubst.rename_agreeOn {σ : FiniteSubst} {v : Var} {c : FOL.Const}
    {ρ : Env} {u : v.sort.denote}
    (hσwf : σ.subst.wfIn σ.dom σ.range) (hfresh : c.name ∉ σ.range.allNames)
    (hsort : c.sort = v.sort) :
    Env.agreeOn (Signature.ofVars (σ.rename v c.name).dom)
      ((σ.rename v c.name).subst.eval (ρ.updateConst v.sort c.name u))
      ((σ.subst.eval ρ).updateConst v.sort v.name u) := by
  constructor
  · intro w hw
    simp [FiniteSubst.rename, Signature.ofVars] at hw
    rcases hw with rfl | ⟨hwdom, hneq⟩
    · change
        Term.eval (ρ.updateConst w.sort c.name u)
          (((σ.subst.eraseName w.name).update w.sort w.name
            (Term.const (Const.uninterpreted c.name w.sort))).apply w.sort w.name) =
          (((σ.subst.eval ρ).updateConst w.sort w.name u).lookupConst w.sort w.name)
      simp [Subst.eval, Env.updateConst, Env.lookupConst, Subst.apply, Subst.update,
        Term.eval, Const.denote]
    · have hne : w.name ≠ v.name := hneq
      change
        Term.eval (ρ.updateConst v.sort c.name u)
            (((σ.subst.eraseName v.name).update v.sort v.name
              (Term.const (Const.uninterpreted c.name v.sort))).apply w.sort w.name) =
          ((σ.subst.eval ρ).updateConst v.sort v.name u).lookupConst w.sort w.name
      rw [Subst.apply_update_ne (Or.inl hne), Subst.apply_eraseName_ne hne,
        Env.lookupConst_updateConst_ne (Or.inl hne), Subst.eval_lookup]
      exact (Term.eval_env_agree (hσwf.1 w hwdom)
        (agreeOn_update_fresh_const (c := ⟨c.name, v.sort⟩) hfresh)).symm
  · simp [Signature.ofVars]

theorem FiniteSubst.rename_dom_declVar {σ : FiniteSubst} {Δ : Signature} {v : Var} {name' : String}
    (hdom : Δ.vars ⊆ σ.dom) :
    (Δ.declVar v).vars ⊆ (σ.rename v name').dom := by
  intro w hw
  simp [Signature.declVar, Signature.addVar, FiniteSubst.rename] at hw ⊢
  rcases hw with rfl | ⟨hw, hneq⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hdom hw, hneq⟩

theorem FiniteSubst.rename_agreeOn_declVar {σ : FiniteSubst} {decls : Signature}
    {v : Var} {c : FOL.Const} {ρ : Env} {u : v.sort.denote}
    (hσwf : σ.wf decls)
    (hfresh : c.name ∉ decls.allNames) (hsort : c.sort = v.sort) :
    Env.agreeOn ((Signature.ofVars σ.dom).declVar v)
      ((σ.rename v c.name).subst.eval (ρ.updateConst v.sort c.name u))
      ((σ.subst.eval ρ).updateConst v.sort v.name u) := by
  have hfresh_range : c.name ∉ σ.range.allNames := by
    intro h
    exact hfresh (Signature.allNames_subset hσwf.2.1 _ h)
  have hrename := FiniteSubst.rename_agreeOn (σ := σ) (v := v) (c := c) (ρ := ρ) (u := u)
    hσwf.1 hfresh_range hsort
  constructor
  · intro w hw
    exact hrename.1 w (FiniteSubst.rename_dom_declVar (σ := σ) (Δ := Signature.ofVars σ.dom) (v := v) (name' := c.name) (by intro x hx; exact hx) hw)
  · simp [Signature.declVar, Signature.ofVars, Signature.addVar, Signature.remove]

theorem FiniteSubst.eval_update_fresh {σ : FiniteSubst} {ρ : Env} {τ : Srt} {name' : String}
    {u : τ.denote} (hσ : σ.subst.wfIn σ.dom σ.range) (hfresh : name' ∉ σ.range.allNames) :
    Env.agreeOn (Signature.ofVars σ.dom) (σ.subst.eval ρ) (σ.subst.eval (ρ.updateConst τ name' u)) := by
  constructor
  · intro v hv
    exact Term.eval_env_agree (hσ.1 v hv) (agreeOn_update_fresh_const (c := ⟨name', τ⟩) hfresh)
  · simp [Signature.ofVars]

theorem FiniteSubst.subst_wfIn_formula {σ : FiniteSubst} {φ : Formula} {Δ : Signature}
    (hσ : σ.wf Δ) (hφ : φ.wfIn (Signature.ofVars σ.dom)) (hwfΔ : Δ.wf) :
    (φ.subst σ.subst σ.range.allNames).wfIn Δ := by
  rcases hσ with ⟨hsubst, hrange, hwfRange⟩
  have hwf_range : (φ.subst σ.subst σ.range.allNames).wfIn σ.range := by
    simpa using
      (Formula.subst_wfIn (Δ := Signature.ofVars σ.dom) (Δ' := σ.range) hφ hsubst
        (Signature.SymbolSubset.ofVars _ _) hwfRange)
  exact Formula.wfIn_mono _ hwf_range hrange hwfΔ

theorem FiniteSubst.eval_subst_formula {σ : FiniteSubst} {φ : Formula} {ρ : Env}
    (hφ : φ.wfIn (Signature.ofVars σ.dom)) (hσ : σ.subst.wfIn σ.dom σ.range)
    (hdomwf : (Signature.ofVars σ.dom).wf) :
    σ.range.wf →
    ((φ.subst σ.subst σ.range.allNames).eval ρ ↔ φ.eval (σ.subst.eval ρ)) := by
  intro hwf
  exact Formula.eval_subst (ρ := ρ) hφ hσ (Signature.SymbolSubset.ofVars _ _) hdomwf hwf

theorem FiniteSubst.id_wf (Δ : Signature) : FiniteSubst.id.wf Δ := by
  constructor
  · apply Subst.id_wfIn
    · intro x hx; cases hx
    · exact Signature.wf_empty
  · constructor
    · constructor
      · intro _ h; cases h
      · intro _ h; cases h
      · intro _ h; cases h
      · intro _ h; cases h
    · exact Signature.wf_empty

theorem FiniteSubst.eval_agreeOn {σ : FiniteSubst} {ρ ρ' : Env}
    (hσ : σ.subst.wfIn σ.dom σ.range) (hagree : Env.agreeOn σ.range ρ ρ') :
    Env.agreeOn (Signature.ofVars σ.dom) (σ.subst.eval ρ) (σ.subst.eval ρ') := by
  constructor
  · intro v hv
    exact Term.eval_env_agree (hσ.1 v hv) hagree
  · simp [Signature.ofVars]

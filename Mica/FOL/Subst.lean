-- SUMMARY: Capture-avoiding substitution for first-order syntax and its well-formedness conditions.
import Mica.FOL.Terms
import Mica.FOL.Formulas
import Mica.Base.Fresh

def Subst := (τ : Srt) → String → Term τ

def Subst.id : Subst := fun τ x => .var τ x

def Subst.apply (σ : Subst) (τ : Srt) (x : String) : Term τ := σ τ x

def Subst.update (σ : Subst) (τ : Srt) (x : String) (s : Term τ) : Subst := fun τ' y =>
  if h : τ' = τ ∧ y = x then h.1 ▸ s else σ τ' y

def Subst.remove (σ : Subst) (x : String) : Subst := fun τ y =>
  if y = x then .var τ y else σ τ y

def Subst.bind (σ : Subst) (y : String) (τ : Srt) (y' : String) : Subst :=
  (σ.remove y).update τ y (.var τ y')

def Term.subst (σ : Subst) : Term τ → Term τ
  | .var τ y   => σ.apply τ y
  | .const c   => .const c
  | .unop op a => .unop op (a.subst σ)
  | .binop op a b => .binop op (a.subst σ) (b.subst σ)
  | .terop op a b c => .terop op (a.subst σ) (b.subst σ) (c.subst σ)
  | .ite c t e => .ite (c.subst σ) (t.subst σ) (e.subst σ)

def Pattern.subst (σ : Subst) : Pattern → Pattern
  | .term t => .term (t.subst σ)
  | .unpred p t => .unpred p (t.subst σ)
  | .binpred p t₁ t₂ => .binpred p (t₁.subst σ) (t₂.subst σ)

def Subst.wfIn (σ : Subst) (dom : VarCtx) (Δ : Signature) : Prop :=
  (∀ v ∈ dom, (σ.apply v.sort v.name).wfIn Δ) ∧
  (∀ v, v ∉ dom → σ.apply v.sort v.name = .var v.sort v.name)

theorem Subst.wfIn_mono {σ : Subst} {dom : VarCtx} {Δ Δ' : Signature}
    (hσ : σ.wfIn dom Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    σ.wfIn dom Δ' :=
  ⟨fun v hv => Term.wfIn_mono _ (hσ.1 v hv) hsub hwf, hσ.2⟩

private theorem Subst.apply_update_same {σ : Subst} {τ : Srt} {x : String} {t : Term τ} :
    (σ.update τ x t).apply τ x = t := by
  simp [Subst.update, Subst.apply]

theorem Subst.apply_update_ne {σ : Subst} {τ τ' : Srt} {x y : String} {t : Term τ}
    (h : y ≠ x ∨ τ' ≠ τ) : (σ.update τ x t).apply τ' y = σ.apply τ' y := by
  simp only [Subst.update, Subst.apply]
  split
  · next heq => cases h with
    | inl h => exact absurd heq.2 h
    | inr h => exact absurd heq.1 h
  · rfl

theorem Subst.apply_remove_ne {σ : Subst} {τ : Srt} {x y : String}
    (h : y ≠ x) : (σ.remove x).apply τ y = σ.apply τ y := by
  simp [Subst.remove, Subst.apply, h]

theorem Subst.wfIn_update {σ : Subst} {dom : VarCtx} {τ : Srt} {x : String} {t : Term τ} {Δ : Signature}
    (hσ : σ.wfIn dom Δ) (ht : t.wfIn Δ) :
    (σ.update τ x t).wfIn (⟨x, τ⟩ :: dom) Δ :=
  ⟨fun v hv => by
      cases hv with
      | head => simp [Subst.apply_update_same, ht]
      | tail _ hmem =>
        by_cases hname : v.name = x <;> by_cases hty : v.sort = τ
        · cases v; simp only at hname hty; subst hname hty
          simp only [Subst.apply_update_same, ht]
        · simp only [Subst.apply_update_ne (Or.inr hty), hσ.1 v hmem]
        · simp only [Subst.apply_update_ne (Or.inl hname), hσ.1 v hmem]
        · simp only [Subst.apply_update_ne (Or.inl hname), hσ.1 v hmem],
    fun v hv => by
      have hvdom : v ∉ dom := by
        intro hmem
        apply hv
        exact List.mem_cons_of_mem _ hmem
      by_cases hname : v.name = x <;> by_cases hty : v.sort = τ
      · exfalso
        apply hv
        cases v
        simp only at hname hty
        subst hname hty
        exact List.mem_cons_self
      · rw [Subst.apply_update_ne (Or.inr hty)]
        exact hσ.2 v hvdom
      · rw [Subst.apply_update_ne (Or.inl hname)]
        exact hσ.2 v hvdom
      · rw [Subst.apply_update_ne (Or.inl hname)]
        exact hσ.2 v hvdom⟩

theorem Subst.id_wfIn {dom : VarCtx} {Δ : Signature} (hsub : dom ⊆ Δ.vars) (hwf : Δ.wf) :
    Subst.id.wfIn dom Δ :=
  ⟨fun v hv => by
      refine ⟨hsub hv, ?_, ?_⟩
      · intro τ' hconst
        exact Signature.wf_no_const_of_var hwf (hsub hv) hconst
      · intro τ' hv'
        exact Signature.wf_unique_var hwf (hsub hv) hv',
    fun _ _ => rfl⟩

theorem Subst.wfIn_remove {σ : Subst} {dom : VarCtx} {Δ : Signature} {x : String}
    (hσ : σ.wfIn dom Δ) :
    (σ.remove x).wfIn (dom.filter (fun v => v.name != x)) Δ := by
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv' : v ∈ dom ∧ v.name ≠ x := by
      simpa using hv
    rw [Subst.apply_remove_ne hv'.2]
    exact hσ.1 v hv'.1
  · intro v hv
    by_cases hname : v.name = x
    · simp [Subst.remove, Subst.apply, hname]
    · rw [Subst.apply_remove_ne hname]
      apply hσ.2
      intro hvdom
      apply hv
      simp [hvdom, hname]

private theorem Subst.wfIn_bind {σ : Subst} {Δ Δ'' : Signature} {y y' : String} {τ : Srt}
    (hσ : σ.wfIn Δ.vars Δ'') (hvarwf : (Term.var τ y').wfIn Δ'') :
    (σ.bind y τ y').wfIn (Δ.declVar ⟨y, τ⟩).vars Δ'' := by
  have hσ_erase : (σ.remove y).wfIn (Δ.remove y).vars Δ'' := by
    simpa [Signature.remove] using
      (Subst.wfIn_remove (σ := σ) (dom := Δ.vars) (Δ := Δ'') (x := y) hσ)
  simpa [Subst.bind, Signature.declVar, Signature.addVar] using
    (Subst.wfIn_update (σ := σ.remove y) (dom := (Δ.remove y).vars) (x := y) hσ_erase hvarwf)

/-- The binder step of `Formula.subst`: rebinding `y` to a name `y'` fresh for
the target signature maps the source binder scope into the target binder scope. -/
theorem Subst.wfIn_bind_fresh {σ : Subst} {Δ Δ' : Signature} {y y' : String} {τ : Srt}
    (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) (hfresh : y' ∉ Δ'.allNames) :
    (σ.bind y τ y').wfIn (Δ.declVar ⟨y, τ⟩).vars (Δ'.declVar ⟨y', τ⟩) :=
  have hwf_target : (Δ'.declVar ⟨y', τ⟩).wf := Signature.wf_declVar hwfΔ'
  Subst.wfIn_bind
    (Subst.wfIn_mono hσ (Signature.subset_declVar_of_fresh hfresh) hwf_target)
    (Term.var_wfIn_declVar hwf_target)

theorem Term.subst_wfIn {t : Term τ} {σ : Subst} {dom : VarCtx} {Δ Δ' : Signature}
    (ht : t.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ')
    (hwf : Δ'.wf) :
    (t.subst σ).wfIn Δ' := by
  induction t generalizing Δ Δ' σ with
  | var τ x => simp only [Term.subst]; exact hσ.1 ⟨x, τ⟩ (hdom ht.1)
  | const c =>
    simp only [Term.subst, Term.wfIn]
    cases c with
    | uninterpreted name τ =>
      refine ⟨hsymbols.consts _ ht.1, ?_, ?_⟩
      · intro τ' hvar
        exact Signature.wf_no_var_of_const hwf (hsymbols.consts _ ht.1) hvar
      · intro τ' hc'
        exact Signature.wf_unique_const hwf (hsymbols.consts _ ht.1) hc'
    | _ => trivial
  | unop op a iha =>
    simp only [Term.subst, Term.wfIn]
    refine ⟨?_, iha ht.2 hσ hdom hsymbols hwf⟩
    cases op with
    | uninterpreted name _ _ =>
      refine ⟨hsymbols.unary _ ht.1.1, ?_, ?_⟩
      · intro τ' hrel
        exact Signature.wf_no_unaryRel_of_unary hwf (hsymbols.unary _ ht.1.1) hrel
      · intro τ₁' τ₂' hu'
        exact Signature.wf_unique_unary hwf (hsymbols.unary _ ht.1.1) hu'
    | _ => trivial
  | binop op a b iha ihb =>
    simp only [Term.subst, Term.wfIn]
    refine ⟨?_, iha ht.2.1 hσ hdom hsymbols hwf,
      ihb ht.2.2 hσ hdom hsymbols hwf⟩
    cases op with
    | uninterpreted name _ _ _ =>
      refine ⟨hsymbols.binary _ ht.1.1, ?_, ?_⟩
      · intro τ₁' τ₂' hrel
        exact Signature.wf_no_binaryRel_of_binary hwf (hsymbols.binary _ ht.1.1) hrel
      · intro τ₁' τ₂' τ₃' hb'
        exact Signature.wf_unique_binary hwf (hsymbols.binary _ ht.1.1) hb'
    | _ => trivial
  | terop op a b c iha ihb ihc =>
    simp only [Term.subst, Term.wfIn]
    refine ⟨?_, iha ht.2.1 hσ hdom hsymbols hwf,
      ihb ht.2.2.1 hσ hdom hsymbols hwf,
      ihc ht.2.2.2 hσ hdom hsymbols hwf⟩
    cases op with
    | uninterpreted name _ _ _ _ =>
      refine ⟨hsymbols.ternary _ ht.1.1, ?_⟩
      intro τ₁' τ₂' τ₃' τ₄' ht'
      exact Signature.wf_unique_ternary hwf (hsymbols.ternary _ ht.1.1) ht'
    | _ => trivial
  | ite c t e ihc iht ihe =>
    simp only [Term.subst, Term.wfIn]
    exact ⟨ihc ht.1 hσ hdom hsymbols hwf,
           iht ht.2.1 hσ hdom hsymbols hwf,
           ihe ht.2.2 hσ hdom hsymbols hwf⟩

private theorem Pattern.subst_wfIn {p : Pattern} {σ : Subst} {dom : VarCtx}
    {Δ Δ' : Signature}
    (hp : p.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ') (hwf : Δ'.wf) :
    (p.subst σ).wfIn Δ' := by
  cases p with
  | term t =>
    exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | unpred p t =>
    simp only [Pattern.subst, Pattern.wfIn]
    refine ⟨?_, Term.subst_wfIn hp.2 hσ hdom hsymbols hwf⟩
    cases p with
    | uninterpreted name τ =>
      refine ⟨hsymbols.unaryRel _ hp.1.1, ?_, ?_⟩
      · intro τ₁ τ₂ hu
        exact Signature.wf_no_unaryRel_of_unary hwf hu (hsymbols.unaryRel _ hp.1.1)
      · intro τ' hu'
        exact Signature.wf_unique_unaryRel hwf (hsymbols.unaryRel _ hp.1.1) hu'
    | _ => trivial
  | binpred p t₁ t₂ =>
    simp only [Pattern.subst, Pattern.wfIn]
    refine ⟨?_, Term.subst_wfIn hp.2.1 hσ hdom hsymbols hwf,
      Term.subst_wfIn hp.2.2 hσ hdom hsymbols hwf⟩
    cases p with
    | uninterpreted name τ₁ τ₂ =>
      refine ⟨hsymbols.binaryRel _ hp.1.1, ?_, ?_⟩
      · intro τ₁' τ₂' τ₃' hb
        exact Signature.wf_no_binaryRel_of_binary hwf hb (hsymbols.binaryRel _ hp.1.1)
      · intro τ₁' τ₂' hb'
        exact Signature.wf_unique_binaryRel hwf (hsymbols.binaryRel _ hp.1.1) hb'
    | _ => trivial

private theorem Pattern.List.subst_wfIn {ps : List Pattern} {σ : Subst}
    {dom : VarCtx} {Δ Δ' : Signature}
    (hps : Pattern.List.wfIn ps Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ') (hwf : Δ'.wf) :
    Pattern.List.wfIn (ps.map (Pattern.subst σ)) Δ' := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact Pattern.subst_wfIn (hps q hq) hσ hdom hsymbols hwf

def Subst.eval (σ : Subst) (ρ : Env) : Env :=
  { ρ with consts := fun τ x => Term.eval ρ (σ.apply τ x) }

theorem Subst.eval_lookup (σ : Subst) (ρ : Env) (τ : Srt) (x : String) :
    (σ.eval ρ).lookupConst τ x = Term.eval ρ (σ.apply τ x) := by
  simp [Subst.eval, Env.lookupConst]

theorem Term.eval_subst {σ : Subst} {ρ : Env} {t : Term τ} {Δ Δ' : Signature}
    (ht : t.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) :
    Term.eval ρ (t.subst σ) = Term.eval (σ.eval ρ) t := by
  induction t generalizing Δ Δ' with
  | var τ y =>
    simp [Term.subst, Term.eval, Subst.eval_lookup]
  | const c =>
    simp only [Term.subst, Term.eval]
    cases c with
    | uninterpreted name _ =>
      rename_i τ1
      simp [Const.denote, Subst.eval]
      symm
      have hvar : σ.apply τ1 name = .var τ1 name := hσ.2 ⟨name, τ1⟩ (ht.2.1 τ1)
      rw [hvar]
      simp [Term.eval, Env.lookupConst]
    | _ => rfl
  | unop op a iha =>
    simp only [Term.subst, Term.eval]
    rw [iha ht.2 hσ hwfΔ']
    cases op with
    | uninterpreted name _ _ => rfl
    | _ => rfl
  | binop op a b iha ihb =>
    simp only [Term.subst, Term.eval]
    rw [iha ht.2.1 hσ hwfΔ', ihb ht.2.2 hσ hwfΔ']
    cases op with
    | uninterpreted name _ _ _ => rfl
    | _ => rfl
  | terop op a b c iha ihb ihc =>
    simp only [Term.subst, Term.eval]
    rw [iha ht.2.1 hσ hwfΔ', ihb ht.2.2.1 hσ hwfΔ', ihc ht.2.2.2 hσ hwfΔ']
    cases op with
    | uninterpreted name _ _ _ _ => rfl
    | _ => rfl
  | ite c t e ihc iht ihe =>
    simp [Term.subst, Term.eval, ihc ht.1 hσ hwfΔ', iht ht.2.1 hσ hwfΔ', ihe ht.2.2 hσ hwfΔ']

def Formula.subst (σ : Subst) (avoid : List String) : Formula → Formula
  | .true_  => .true_
  | .false_ => .false_
  | .eq τ a b      => .eq τ (a.subst σ) (b.subst σ)
  | .unpred p v    => .unpred p (v.subst σ)
  | .binpred p a b => .binpred p (a.subst σ) (b.subst σ)
  | .not φ         => .not (Formula.subst σ avoid φ)
  | .and φ ψ       => .and (Formula.subst σ avoid φ) (Formula.subst σ avoid ψ)
  | .or φ ψ        => .or (Formula.subst σ avoid φ) (Formula.subst σ avoid ψ)
  | .implies φ ψ   => .implies (Formula.subst σ avoid φ) (Formula.subst σ avoid ψ)
  | .forall_ y τ ps φ =>
    let y' := Fresh.freshName avoid y
    .forall_ y' τ (ps.map (Pattern.subst (σ.bind y τ y')))
      (Formula.subst (σ.bind y τ y') (y' :: avoid) φ)
  | .exists_ y τ φ =>
    let y' := Fresh.freshName avoid y
    .exists_ y' τ (Formula.subst (σ.bind y τ y') (y' :: avoid) φ)

private theorem Subst.eval_bind_agreeOn {σ : Subst} {ρ : Env} {τ : Srt} {y y' : String} {v : τ.denote}
    {Δ Δ' : Signature} (hσ : σ.wfIn Δ.vars Δ') (hsymbols : Δ.SymbolSubset Δ')
    (hwfΔ : Δ.wf) (hy'_fresh : y' ∉ Δ'.allNames) :
    Env.agreeOn (Δ.declVar ⟨y, τ⟩)
      ((σ.bind y τ y').eval (ρ.updateConst τ y' v))
      ((σ.eval ρ).updateConst τ y v) := by
  constructor
  · intro w hw
    have hw' : w = ⟨y, τ⟩ ∨ w ∈ Δ.vars ∧ w.name ≠ y := by
      simpa using hw
    cases hw' with
    | inl hEq =>
      subst hEq
      simp [Subst.eval, Subst.bind, Env.updateConst, Env.lookupConst, Subst.apply,
        Subst.update, Subst.remove, Term.eval]
    | inr hrest =>
      change Term.eval (ρ.updateConst τ y' v) ((σ.bind y τ y').apply w.sort w.name) =
        (((σ.eval ρ).updateConst τ y v).lookupConst w.sort w.name)
      rw [Subst.bind, Subst.apply_update_ne (Or.inl hrest.2), Subst.apply_remove_ne hrest.2,
        Env.lookupConst_updateConst_ne' (Or.inl hrest.2)]
      simpa [Subst.eval, Env.updateConst, Env.lookupConst] using
        (Term.eval_update_fresh (ρ := ρ) (τ' := w.sort) (x := y') (τ := τ)
          (v := v) (Δ := Δ') (hwf := hσ.1 w hrest.1) hy'_fresh)
  · constructor
    · intro c hc
      have hc' : c ∈ Δ.consts ∧ c.name ≠ y := by
        simpa using hc
      have hc_not_var : ⟨c.name, c.sort⟩ ∉ Δ.vars :=
        Signature.wf_no_var_of_const hwfΔ hc'.1
      have hc_not_fresh : c.name ≠ y' := by
        intro hEq
        apply hy'_fresh
        rw [← hEq]
        exact Signature.mem_allNames_of_const (hsymbols.consts c hc'.1)
      change Term.eval (ρ.updateConst τ y' v) ((σ.bind y τ y').apply c.sort c.name) =
        (((σ.eval ρ).updateConst τ y v).lookupConst c.sort c.name)
      rw [Subst.bind, Subst.apply_update_ne (Or.inl hc'.2), Subst.apply_remove_ne hc'.2,
        Env.lookupConst_updateConst_ne' (Or.inl hc'.2), Subst.eval_lookup]
      rw [hσ.2 ⟨c.name, c.sort⟩ hc_not_var]
      simpa [Term.eval, Env.lookupConst] using
        (Env.lookupConst_updateConst_ne' (ρ := ρ) (τ := τ) (τ' := c.sort) (x := y')
          (y := c.name) (v := v) (Or.inl hc_not_fresh))
    · constructor
      · intro u hu
        rfl
      · constructor
        · intro b hb
          rfl
        · constructor
          · intro t ht
            rfl
          · constructor
            · intro u hu
              rfl
            · intro b hb
              rfl

theorem Formula.eval_subst {σ : Subst} {ρ : Env} {φ : Formula} {Δ Δ' : Signature}
    (hφ : φ.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hsymbols : Δ.SymbolSubset Δ')
    (hwfΔ : Δ.wf) (hwfΔ' : Δ'.wf) :
    (φ.subst σ Δ'.allNames).eval ρ ↔ φ.eval (σ.eval ρ) := by
  induction φ generalizing σ Δ Δ' ρ with
  | true_ | false_ => simp [Formula.subst, Formula.eval]
  | eq τ a b =>
    simp [Formula.subst, Formula.eval, Term.eval_subst hφ.1 hσ hwfΔ', Term.eval_subst hφ.2 hσ hwfΔ']
  | unpred p t =>
    simp [Formula.subst, Formula.eval, Term.eval_subst hφ.2 hσ hwfΔ']
    cases p <;> simp [Subst.eval]
  | binpred p a b =>
    simp [Formula.subst, Formula.eval, Term.eval_subst hφ.2.1 hσ hwfΔ',
      Term.eval_subst hφ.2.2 hσ hwfΔ']
    cases p <;> simp [Subst.eval]
  | not φ ih =>
    simp [Formula.subst, Formula.eval, ih hφ hσ hsymbols hwfΔ hwfΔ']
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simp [Formula.subst, Formula.eval, ihφ hφ.1 hσ hsymbols hwfΔ hwfΔ',
      ihψ hφ.2 hσ hsymbols hwfΔ hwfΔ']
  | forall_ y τ ps φ ih =>
    simp only [Formula.subst, Formula.eval]
    let y' := Fresh.freshName Δ'.allNames y
    have hy'_fresh : y' ∉ Δ'.allNames := Fresh.freshName_not_in_avoid Δ'.allNames y
    have hwf_body : φ.wfIn (Δ.declVar ⟨y, τ⟩) := hφ.2
    have hbody (v : τ.denote) := ih (σ := σ.bind y τ y') (Δ := Δ.declVar ⟨y, τ⟩)
      (Δ' := Δ'.declVar ⟨y', τ⟩) (ρ := ρ.updateConst τ y' v)
      hwf_body (Subst.wfIn_bind_fresh hσ hwfΔ' hy'_fresh)
      (Signature.SymbolSubset.declVar_fresh hsymbols hy'_fresh)
      (Signature.wf_declVar hwfΔ) (Signature.wf_declVar hwfΔ')
    have hagree (v : τ.denote) : Env.agreeOn (Δ.declVar ⟨y, τ⟩)
        ((σ.bind y τ y').eval (ρ.updateConst τ y' v))
        ((σ.eval ρ).updateConst τ y v) :=
      Subst.eval_bind_agreeOn (ρ := ρ) (Δ := Δ) (Δ' := Δ') hσ hsymbols hwfΔ hy'_fresh
    constructor <;> intro h v
    · exact (Formula.eval_env_agree hwf_body (hagree v)).mp
        ((hbody v).mp (by simpa [y', Signature.allNames_declVar_of_not_in hy'_fresh] using h v))
    · simpa [y', Signature.allNames_declVar_of_not_in hy'_fresh] using
        (hbody v).mpr ((Formula.eval_env_agree hwf_body (hagree v)).mpr (h v))
  | exists_ y τ φ ih =>
    simp only [Formula.subst, Formula.eval]
    let y' := Fresh.freshName Δ'.allNames y
    have hy'_fresh : y' ∉ Δ'.allNames := Fresh.freshName_not_in_avoid Δ'.allNames y
    have hwf_body : φ.wfIn (Δ.declVar ⟨y, τ⟩) := hφ
    have hbody (v : τ.denote) := ih (σ := σ.bind y τ y') (Δ := Δ.declVar ⟨y, τ⟩)
      (Δ' := Δ'.declVar ⟨y', τ⟩) (ρ := ρ.updateConst τ y' v)
      hwf_body (Subst.wfIn_bind_fresh hσ hwfΔ' hy'_fresh)
      (Signature.SymbolSubset.declVar_fresh hsymbols hy'_fresh)
      (Signature.wf_declVar hwfΔ) (Signature.wf_declVar hwfΔ')
    have hagree (v : τ.denote) : Env.agreeOn (Δ.declVar ⟨y, τ⟩)
        ((σ.bind y τ y').eval (ρ.updateConst τ y' v))
        ((σ.eval ρ).updateConst τ y v) :=
      Subst.eval_bind_agreeOn (ρ := ρ) (Δ := Δ) (Δ' := Δ') hσ hsymbols hwfΔ hy'_fresh
    constructor <;> rintro ⟨v, hv⟩ <;> refine ⟨v, ?_⟩
    · exact (Formula.eval_env_agree hwf_body (hagree v)).mp
        ((hbody v).mp (by simpa [y', Signature.allNames_declVar_of_not_in hy'_fresh] using hv))
    · simpa [y', Signature.allNames_declVar_of_not_in hy'_fresh] using
        (hbody v).mpr ((Formula.eval_env_agree hwf_body (hagree v)).mpr hv)

theorem Formula.subst_wfIn {φ : Formula} {σ : Subst} {Δ Δ' : Signature}
    (hwf : φ.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ')
    (hsymbols : Δ.SymbolSubset Δ')
    (hwfΔ' : Δ'.wf) :
    (φ.subst σ Δ'.allNames).wfIn Δ' := by
  induction φ generalizing σ Δ Δ' with
  | true_ | false_ => trivial
  | eq τ a b =>
    simp [Formula.subst, Formula.wfIn]
    exact ⟨Term.subst_wfIn hwf.1 hσ (by intro x hx; exact hx) hsymbols hwfΔ',
      Term.subst_wfIn hwf.2 hσ (by intro x hx; exact hx) hsymbols hwfΔ'⟩
  | unpred p t =>
    simp [Formula.subst, Formula.wfIn]
    refine ⟨?_, Term.subst_wfIn hwf.2 hσ (by intro x hx; exact hx) hsymbols hwfΔ'⟩
    cases p with
    | uninterpreted name τ =>
      refine ⟨hsymbols.unaryRel _ hwf.1.1, ?_, ?_⟩
      · intro τ₁ τ₂ hu
        exact Signature.wf_no_unaryRel_of_unary hwfΔ' hu (hsymbols.unaryRel _ hwf.1.1)
      · intro τ' hu'
        exact Signature.wf_unique_unaryRel hwfΔ' (hsymbols.unaryRel _ hwf.1.1) hu'
    | _ => trivial
  | binpred p a b =>
    simp [Formula.subst, Formula.wfIn]
    refine ⟨?_, Term.subst_wfIn hwf.2.1 hσ (by intro x hx; exact hx) hsymbols hwfΔ',
      Term.subst_wfIn hwf.2.2 hσ (by intro x hx; exact hx) hsymbols hwfΔ'⟩
    cases p with
    | uninterpreted name τ₁ τ₂ =>
      refine ⟨hsymbols.binaryRel _ hwf.1.1, ?_, ?_⟩
      · intro τ₁' τ₂' τ₃' hb
        exact Signature.wf_no_binaryRel_of_binary hwfΔ' hb (hsymbols.binaryRel _ hwf.1.1)
      · intro τ₁' τ₂' hb'
        exact Signature.wf_unique_binaryRel hwfΔ' (hsymbols.binaryRel _ hwf.1.1) hb'
    | _ => trivial
  | not φ ih =>
    simpa [Formula.subst, Formula.wfIn] using ih hwf hσ hsymbols hwfΔ'
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simpa [Formula.subst, Formula.wfIn] using
      And.intro (ihφ hwf.1 hσ hsymbols hwfΔ')
        (ihψ hwf.2 hσ hsymbols hwfΔ')
  | forall_ y τ ps φ ih =>
    simp only [Formula.subst, Formula.wfIn]
    let y' := Fresh.freshName Δ'.allNames y
    have hy'_fresh : y' ∉ Δ'.allNames := Fresh.freshName_not_in_avoid Δ'.allNames y
    have hwf_target : (Δ'.declVar ⟨y', τ⟩).wf := Signature.wf_declVar hwfΔ'
    have hσ' : (σ.bind y τ y').wfIn (Δ.declVar ⟨y, τ⟩).vars (Δ'.declVar ⟨y', τ⟩) :=
      Subst.wfIn_bind_fresh hσ hwfΔ' hy'_fresh
    have hsymbols' : (Δ.declVar ⟨y, τ⟩).SymbolSubset (Δ'.declVar ⟨y', τ⟩) :=
      Signature.SymbolSubset.declVar_fresh hsymbols hy'_fresh
    exact ⟨by
      simpa [y', Signature.allNames_declVar_of_not_in hy'_fresh] using
        Pattern.List.subst_wfIn hwf.1 hσ' (by intro v hv; exact hv) hsymbols' hwf_target,
      by
        simpa [y', Signature.allNames_declVar_of_not_in hy'_fresh] using
          ih hwf.2 hσ' hsymbols' hwf_target⟩
  | exists_ y τ φ ih =>
    simp only [Formula.subst, Formula.wfIn]
    let y' := Fresh.freshName Δ'.allNames y
    have hy'_fresh : y' ∉ Δ'.allNames := Fresh.freshName_not_in_avoid Δ'.allNames y
    have hwf_target : (Δ'.declVar ⟨y', τ⟩).wf := Signature.wf_declVar hwfΔ'
    have hσ' : (σ.bind y τ y').wfIn (Δ.declVar ⟨y, τ⟩).vars (Δ'.declVar ⟨y', τ⟩) :=
      Subst.wfIn_bind_fresh hσ hwfΔ' hy'_fresh
    have hsymbols' : (Δ.declVar ⟨y, τ⟩).SymbolSubset (Δ'.declVar ⟨y', τ⟩) :=
      Signature.SymbolSubset.declVar_fresh hsymbols hy'_fresh
    exact (by
      simpa [y', Signature.allNames_declVar_of_not_in hy'_fresh] using
        ih hwf hσ' hsymbols' hwf_target)

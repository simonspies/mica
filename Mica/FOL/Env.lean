-- SUMMARY: Environments interpreting the names of a signature, and agreement between them.
import Mica.FOL.Signature

-- ---------------------------------------------------------------------------
-- Environments
-- ---------------------------------------------------------------------------

/-- An interpretation environment for evaluation.

There is intentionally no separate variable environment. SMT-LIB and Z3 see only a
nullary symbol name like `x`; they do not distinguish, at evaluation time, between
`Term.var τ x` and an uninterpreted constant printed as `x`. We therefore interpret both
through the same `consts` map so the Lean semantics matches the SMT semantics. -/
structure Env where
  consts : (τ : Srt) → String → τ.denote
  unary  : (τ₁ τ₂ : Srt) → String → τ₁.denote → τ₂.denote
  binary : (τ₁ τ₂ τ₃ : Srt) → String → τ₁.denote → τ₂.denote → τ₃.denote
  ternary : (τ₁ τ₂ τ₃ τ₄ : Srt) → String →
    τ₁.denote → τ₂.denote → τ₃.denote → τ₄.denote
  unaryRel : (τ : Srt) → String → τ.denote → Prop
  binaryRel : (τ₁ τ₂ : Srt) → String → τ₁.denote → τ₂.denote → Prop

theorem Env.ext {e1 e2 : Env}
    (h1 : e1.consts = e2.consts)
    (h2 : e1.unary = e2.unary) (h3 : e1.binary = e2.binary)
    (h4 : e1.ternary = e2.ternary)
    (h5 : e1.unaryRel = e2.unaryRel) (h6 : e1.binaryRel = e2.binaryRel) : e1 = e2 := by
  cases e1; cases e2; congr

def Env.lookupConst (ρ : Env) (τ : Srt) (x : String) : τ.denote := ρ.consts τ x

def Env.updateConst (ρ : Env) (τ : Srt) (x : String) (v : τ.denote) : Env :=
  { ρ with consts := fun τ' y => if h : τ' = τ ∧ y = x then h.1 ▸ v else ρ.consts τ' y }

def Env.updateUnary (ρ : Env) (τ₁ τ₂ : Srt) (x : String) (f : τ₁.denote → τ₂.denote) : Env :=
  { ρ with unary := fun τ₁' τ₂' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ y = x then h.1 ▸ h.2.1 ▸ f else ρ.unary τ₁' τ₂' y }

def Env.updateBinary (ρ : Env) (τ₁ τ₂ τ₃ : Srt) (x : String)
    (f : τ₁.denote → τ₂.denote → τ₃.denote) : Env :=
  { ρ with binary := fun τ₁' τ₂' τ₃' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ τ₃' = τ₃ ∧ y = x then h.1 ▸ h.2.1 ▸ h.2.2.1 ▸ f
    else ρ.binary τ₁' τ₂' τ₃' y }

def Env.updateTernary (ρ : Env) (τ₁ τ₂ τ₃ τ₄ : Srt) (x : String)
    (f : τ₁.denote → τ₂.denote → τ₃.denote → τ₄.denote) : Env :=
  { ρ with ternary := fun τ₁' τ₂' τ₃' τ₄' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ τ₃' = τ₃ ∧ τ₄' = τ₄ ∧ y = x then
      h.1 ▸ h.2.1 ▸ h.2.2.1 ▸ h.2.2.2.1 ▸ f
    else ρ.ternary τ₁' τ₂' τ₃' τ₄' y }

def Env.updateUnaryRel (ρ : Env) (τ : Srt) (x : String) (f : τ.denote → Prop) : Env :=
  { ρ with unaryRel := fun τ' y =>
    if h : τ' = τ ∧ y = x then h.1 ▸ f else ρ.unaryRel τ' y }

def Env.updateBinaryRel (ρ : Env) (τ₁ τ₂ : Srt) (x : String)
    (f : τ₁.denote → τ₂.denote → Prop) : Env :=
  { ρ with binaryRel := fun τ₁' τ₂' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ y = x then h.1 ▸ h.2.1 ▸ f else ρ.binaryRel τ₁' τ₂' y }

def Env.empty : Env :=
  ⟨fun _ _ => default, fun _ _ _ _ => default, fun _ _ _ _ _ => default,
   fun _ _ _ _ _ _ _ => default, fun _ _ _ => False, fun _ _ _ _ _ => False⟩

instance : Inhabited Env := { default := Env.empty }

@[simp] theorem Env.lookupConst_updateConst_same {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.updateConst τ x v).lookupConst τ x = v := by
  simp [Env.updateConst, Env.lookupConst]

@[simp] theorem Env.lookupConst_updateConst_ne {ρ : Env} {τ : Srt} {x y : String} {v : τ.denote} (h : y ≠ x) :
    (Env.updateConst ρ τ x v).lookupConst τ y = ρ.lookupConst τ y := by
  simp [Env.updateConst, Env.lookupConst, h]

theorem Env.lookupConst_updateConst_ne' {ρ : Env} {τ τ' : Srt} {x y : String} {v : τ.denote}
    (h : y ≠ x ∨ τ' ≠ τ) : (ρ.updateConst τ x v).lookupConst τ' y = ρ.lookupConst τ' y := by
  simp only [Env.updateConst, Env.lookupConst]
  split
  · next heq => cases h with
    | inl h => exact absurd heq.2 h
    | inr h => exact absurd heq.1 h
  · rfl

theorem Env.updateConst_unary {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.updateConst τ x v).unary = ρ.unary := rfl

theorem Env.updateConst_binary {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.updateConst τ x v).binary = ρ.binary := rfl

theorem Env.updateConst_ternary {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.updateConst τ x v).ternary = ρ.ternary := rfl

theorem Env.updateConst_unaryRel {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.updateConst τ x v).unaryRel = ρ.unaryRel := rfl

theorem Env.updateConst_binaryRel {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.updateConst τ x v).binaryRel = ρ.binaryRel := rfl

/-- Extension order on environments: the interpretation of constants and of the
unary/binary/ternary operators is fixed, while the uninterpreted predicate
interpretations may grow. Term evaluation is invariant under it (see
`Term.eval_env_le`); formula evaluation is not. -/
structure Env.le (ρ ρ' : Env) : Prop where
  consts : ρ.consts = ρ'.consts
  unary : ρ.unary = ρ'.unary
  binary : ρ.binary = ρ'.binary
  ternary : ρ.ternary = ρ'.ternary
  unaryRel : ∀ τ name a, ρ.unaryRel τ name a → ρ'.unaryRel τ name a
  binaryRel : ∀ τ₁ τ₂ name a b, ρ.binaryRel τ₁ τ₂ name a b → ρ'.binaryRel τ₁ τ₂ name a b

theorem Env.le.refl (ρ : Env) : Env.le ρ ρ :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem Env.le.updateConst {ρ ρ' : Env} (h : Env.le ρ ρ')
    (τ : Srt) (x : String) (v : τ.denote) :
    Env.le (ρ.updateConst τ x v) (ρ'.updateConst τ x v) := by
  refine ⟨?_, h.unary, h.binary, h.ternary, h.unaryRel, h.binaryRel⟩
  simp only [Env.updateConst, h.consts]

structure Env.agreeOn (Δ : Signature) (ρ ρ' : Env) : Prop where
  intro ::
  vars : ∀ v ∈ Δ.vars, ρ.consts v.sort v.name = ρ'.consts v.sort v.name
  consts : ∀ c ∈ Δ.consts, ρ.consts c.sort c.name = ρ'.consts c.sort c.name
  unary : ∀ u ∈ Δ.unary, ρ.unary u.arg u.ret u.name = ρ'.unary u.arg u.ret u.name
  binary : ∀ b ∈ Δ.binary,
    ρ.binary b.arg1 b.arg2 b.ret b.name = ρ'.binary b.arg1 b.arg2 b.ret b.name
  ternary : ∀ t ∈ Δ.ternary,
    ρ.ternary t.arg1 t.arg2 t.arg3 t.ret t.name = ρ'.ternary t.arg1 t.arg2 t.arg3 t.ret t.name
  unaryRel : ∀ u ∈ Δ.unaryRel, ρ.unaryRel u.arg u.name = ρ'.unaryRel u.arg u.name
  binaryRel : ∀ b ∈ Δ.binaryRel,
    ρ.binaryRel b.arg1 b.arg2 b.name = ρ'.binaryRel b.arg1 b.arg2 b.name

theorem Env.agreeOn_refl : Env.agreeOn Δ ρ ρ :=
  .intro (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Any two environments agree on the empty signature. -/
theorem Env.agreeOn_empty (ρ ρ' : Env) : Env.agreeOn Signature.empty ρ ρ' := by
  refine .intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro x hx <;> simp [Signature.empty] at hx

theorem Env.agreeOn_mono {Δ₁ Δ₂ : Signature} (hsub : Δ₁.Subset Δ₂)
    (h : Env.agreeOn Δ₂ ρ ρ') : Env.agreeOn Δ₁ ρ ρ' :=
  .intro
    (fun x hx => h.vars x (hsub.vars x hx))
    (fun c hc => h.consts c (hsub.consts c hc))
    (fun u hu => h.unary u (hsub.unary u hu))
    (fun b hb => h.binary b (hsub.binary b hb))
    (fun t ht => h.ternary t (hsub.ternary t ht))
    (fun u hu => h.unaryRel u (hsub.unaryRel u hu))
    (fun b hb => h.binaryRel b (hsub.binaryRel b hb))

theorem Env.agreeOn_remove {Δ : Signature} {ρ ρ' : Env} {x : String}
    (h : Env.agreeOn Δ ρ ρ') : Env.agreeOn (Δ.remove x) ρ ρ' :=
  Env.agreeOn_mono (Signature.remove_subset Δ x) h

theorem Env.agreeOn_symm {Δ : Signature} {ρ ρ' : Env} (h : Env.agreeOn Δ ρ ρ') : Env.agreeOn Δ ρ' ρ :=
  .intro
    (fun v hv => (h.vars v hv).symm)
    (fun c hc => (h.consts c hc).symm)
    (fun u hu => (h.unary u hu).symm)
    (fun b hb => (h.binary b hb).symm)
    (fun t ht => (h.ternary t ht).symm)
    (fun u hu => (h.unaryRel u hu).symm)
    (fun b hb => (h.binaryRel b hb).symm)

theorem Env.agreeOn_trans {Δ : Signature}
    (h₁₂ : Env.agreeOn Δ ρ₁ ρ₂) (h₂₃ : Env.agreeOn Δ ρ₂ ρ₃) : Env.agreeOn Δ ρ₁ ρ₃ :=
  .intro
    (fun x hx => (h₁₂.vars x hx).trans (h₂₃.vars x hx))
    (fun c hc => (h₁₂.consts c hc).trans (h₂₃.consts c hc))
    (fun u hu => (h₁₂.unary u hu).trans (h₂₃.unary u hu))
    (fun b hb => (h₁₂.binary b hb).trans (h₂₃.binary b hb))
    (fun t ht => (h₁₂.ternary t ht).trans (h₂₃.ternary t ht))
    (fun u hu => (h₁₂.unaryRel u hu).trans (h₂₃.unaryRel u hu))
    (fun b hb => (h₁₂.binaryRel b hb).trans (h₂₃.binaryRel b hb))

/-- Base-signature agreement is stable under extending each side: if `ρ₁` and
    `ρ₂` agree on `Δ`, and each moves to an environment agreeing on a larger
    signature (`Δ ⊆ Δ₁`, `Δ ⊆ Δ₂`), then the two extended environments still
    agree on `Δ`. -/
theorem Env.agreeOn_of_extensions {Δ Δ₁ Δ₂ : Signature} {ρ₁ ρ₂ ρ₁' ρ₂' : Env}
    (hsub₁ : Δ.Subset Δ₁) (hsub₂ : Δ.Subset Δ₂)
    (hbase : Env.agreeOn Δ ρ₁ ρ₂)
    (h₁ : Env.agreeOn Δ₁ ρ₁ ρ₁') (h₂ : Env.agreeOn Δ₂ ρ₂ ρ₂') :
    Env.agreeOn Δ ρ₁' ρ₂' :=
  Env.agreeOn_trans (Env.agreeOn_symm (Env.agreeOn_mono hsub₁ h₁))
    (Env.agreeOn_trans hbase (Env.agreeOn_mono hsub₂ h₂))

theorem Env.agreeOn_update {ρ ρ' : Env} {Δ : Signature} {τ : Srt} {x : String} {v : τ.denote} :
    Env.agreeOn Δ ρ ρ' →
    Env.agreeOn (Δ.addVar ⟨x, τ⟩) (ρ.updateConst τ x v) (ρ'.updateConst τ x v) :=
  fun hagree =>
  .intro
   (fun w hw => by
    cases hw with
    | head => simp [Env.updateConst]
    | tail _ hw =>
      by_cases hn : w.name = x <;> by_cases ht : w.sort = τ
      · cases w; simp only at hn ht; subst hn ht
        simp [Env.updateConst]
      · simp [Env.updateConst, ht, hagree.vars w hw]
      · simp [Env.updateConst, hn, hagree.vars w hw]
      · simp [Env.updateConst, hn, hagree.vars w hw])
   (fun c hc => by
     by_cases hn : c.name = x <;> by_cases ht : c.sort = τ
     · cases c; simp only at hn ht; subst hn ht
       simp [Env.updateConst]
     · simp [Env.updateConst, ht, hagree.consts c hc]
     · simp [Env.updateConst, hn, hagree.consts c hc]
     · simp [Env.updateConst, hn, hagree.consts c hc])
   (fun u hu => by rw [Env.updateConst_unary]; exact hagree.unary u hu)
   (fun b hb => by rw [Env.updateConst_binary]; exact hagree.binary b hb)
   (fun t ht => by rw [Env.updateConst_ternary]; exact hagree.ternary t ht)
   (fun u hu => by rw [Env.updateConst_unaryRel]; exact hagree.unaryRel u hu)
   (fun b hb => by rw [Env.updateConst_binaryRel]; exact hagree.binaryRel b hb)

theorem Env.agreeOn_declVar {ρ ρ' : Env} {Δ : Signature} {τ : Srt} {x : String} {v : τ.denote} :
    Env.agreeOn Δ ρ ρ' →
    Env.agreeOn (Δ.declVar ⟨x, τ⟩) (ρ.updateConst τ x v) (ρ'.updateConst τ x v) := by
  intro hagree
  simpa [Signature.declVar] using (Env.agreeOn_update (Env.agreeOn_remove hagree))

theorem Env.agreeOn_update_fresh_const {ρ : Env} {c : Decl.Const} {u : c.sort.denote}
    {Δ : Signature} (hfresh : c.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateConst c.sort c.name u) := by
  refine .intro ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro w hw
    have hne : w.name ≠ c.name := by
      intro heq; apply hfresh; rw [← heq]; exact Signature.mem_allNames_of_var hw
    exact (Env.lookupConst_updateConst_ne' (Or.inl hne)).symm
  · intro c' hc'
    have hne : c'.name ≠ c.name := by
      intro heq; apply hfresh; rw [← heq]; exact Signature.mem_allNames_of_const hc'
    exact (Env.lookupConst_updateConst_ne' (Or.inl hne)).symm
  · intro _ _; rw [Env.updateConst_unary]
  · intro _ _; rw [Env.updateConst_binary]
  · intro _ _; rw [Env.updateConst_ternary]
  · intro _ _; rw [Env.updateConst_unaryRel]
  · intro _ _; rw [Env.updateConst_binaryRel]

theorem Env.agreeOn_update_fresh_unary {ρ : Env} {u : Decl.Unary}
    {f : u.arg.denote → u.ret.denote}
    {Δ : Signature} (hfresh : u.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateUnary u.arg u.ret u.name f) :=
  .intro
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun u' hu' => by
       have hne : u'.name ≠ u.name := by
         intro heq; apply hfresh; rw [← heq]; exact Signature.mem_allNames_of_unary hu'
       simp only [Env.updateUnary]
       split
       · next h => exact absurd h.2.2 hne
       · rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)

theorem Env.agreeOn_update_fresh_binary {ρ : Env} {b : Decl.Binary}
    {f : b.arg1.denote → b.arg2.denote → b.ret.denote}
    {Δ : Signature} (hfresh : b.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateBinary b.arg1 b.arg2 b.ret b.name f) :=
  .intro
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun b' hb' => by
       have hne : b'.name ≠ b.name := by
         intro heq; apply hfresh; rw [← heq]; exact Signature.mem_allNames_of_binary hb'
       simp only [Env.updateBinary]
       split
       · next h => exact absurd h.2.2.2 hne
       · rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)

theorem Env.agreeOn_update_fresh_ternary {ρ : Env} {t : Decl.Ternary}
    {f : t.arg1.denote → t.arg2.denote → t.arg3.denote → t.ret.denote}
    {Δ : Signature} (hfresh : t.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateTernary t.arg1 t.arg2 t.arg3 t.ret t.name f) :=
  .intro
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun t' ht' => by
       have hne : t'.name ≠ t.name := by
         intro heq; apply hfresh; rw [← heq]; exact Signature.mem_allNames_of_ternary ht'
       simp only [Env.updateTernary]
       split
       · next h => exact absurd h.2.2.2.2 hne
       · rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)

theorem Env.agreeOn_update_fresh_unaryRel {ρ : Env} {u : Decl.UnaryRel} {f : u.arg.denote → Prop}
    {Δ : Signature} (hfresh : u.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateUnaryRel u.arg u.name f) :=
  .intro
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun u' hu' => by
       have hne : u'.name ≠ u.name := by
         intro heq; apply hfresh; rw [← heq]; exact Signature.mem_allNames_of_unaryRel hu'
       simp only [Env.updateUnaryRel]
       split
       · next h => exact absurd h.2 hne
       · rfl)
    (fun _ _ => rfl)

theorem Env.agreeOn_update_fresh_binaryRel {ρ : Env} {b : Decl.BinaryRel}
    {f : b.arg1.denote → b.arg2.denote → Prop}
    {Δ : Signature} (hfresh : b.name ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (ρ.updateBinaryRel b.arg1 b.arg2 b.name f) :=
  .intro
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun b' hb' => by
       have hne : b'.name ≠ b.name := by
         intro heq; apply hfresh; rw [← heq]; exact Signature.mem_allNames_of_binaryRel hb'
       simp only [Env.updateBinaryRel]
       split
       · next h => exact absurd h.2.2 hne
       · rfl)

/-- Agreement on the environment components used by term evaluation. Relation
interpretations are intentionally ignored. -/
structure Env.agreeOnTerms (Δ : Signature) (ρ₁ ρ₂ : Env) : Prop where
  vars : ∀ v ∈ Δ.vars, ρ₁.consts v.sort v.name = ρ₂.consts v.sort v.name
  consts : ∀ c ∈ Δ.consts, ρ₁.consts c.sort c.name = ρ₂.consts c.sort c.name
  unary : ∀ u ∈ Δ.unary, ρ₁.unary u.arg u.ret u.name = ρ₂.unary u.arg u.ret u.name
  binary : ∀ b ∈ Δ.binary,
    ρ₁.binary b.arg1 b.arg2 b.ret b.name = ρ₂.binary b.arg1 b.arg2 b.ret b.name
  ternary : ∀ t ∈ Δ.ternary,
    ρ₁.ternary t.arg1 t.arg2 t.arg3 t.ret t.name = ρ₂.ternary t.arg1 t.arg2 t.arg3 t.ret t.name

theorem Env.agreeOnTerms_of_agreeOn {Δ : Signature} {ρ₁ ρ₂ : Env}
    (h : Env.agreeOn Δ ρ₁ ρ₂) : Env.agreeOnTerms Δ ρ₁ ρ₂ :=
  ⟨h.vars, h.consts, h.unary, h.binary, h.ternary⟩

theorem Env.agreeOnTerms_declVar {Δ : Signature} {ρ₁ ρ₂ : Env}
    {x : String} {τ : Srt} {v : τ.denote}
    (h : Env.agreeOnTerms Δ ρ₁ ρ₂) :
    Env.agreeOnTerms (Δ.declVar ⟨x, τ⟩)
      (ρ₁.updateConst τ x v) (ρ₂.updateConst τ x v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ∈ ⟨x, τ⟩ :: (Δ.remove x).vars := by
      simpa [Signature.declVar, Signature.addVar] using hw
    cases hw' with
    | head => simp [Env.updateConst]
    | tail _ htail =>
      by_cases hn : w.name = x <;> by_cases ht : w.sort = τ
      · cases w; simp only at hn ht; subst hn ht; simp [Env.updateConst]
      · simp [Env.updateConst, ht, h.vars w (Signature.remove_subset Δ x |>.vars w htail)]
      · simp [Env.updateConst, hn, h.vars w (Signature.remove_subset Δ x |>.vars w htail)]
      · simp [Env.updateConst, hn, h.vars w (Signature.remove_subset Δ x |>.vars w htail)]
  · intro c hc
    have hcΔ : c ∈ Δ.consts :=
      Signature.remove_subset Δ x |>.consts c (by
        simpa [Signature.declVar, Signature.addVar] using hc)
    by_cases hn : c.name = x <;> by_cases ht : c.sort = τ
    · cases c; simp only at hn ht; subst hn ht; simp [Env.updateConst]
    · simp [Env.updateConst, ht, h.consts c hcΔ]
    · simp [Env.updateConst, hn, h.consts c hcΔ]
    · simp [Env.updateConst, hn, h.consts c hcΔ]
  · intro u hu
    rw [Env.updateConst_unary, Env.updateConst_unary]
    exact h.unary u (Signature.remove_subset Δ x |>.unary u (by
      simpa [Signature.declVar, Signature.addVar] using hu))
  · intro b hb
    rw [Env.updateConst_binary, Env.updateConst_binary]
    exact h.binary b (Signature.remove_subset Δ x |>.binary b (by
      simpa [Signature.declVar, Signature.addVar] using hb))
  · intro t ht
    rw [Env.updateConst_ternary, Env.updateConst_ternary]
    exact h.ternary t (Signature.remove_subset Δ x |>.ternary t (by
      simpa [Signature.declVar, Signature.addVar] using ht))

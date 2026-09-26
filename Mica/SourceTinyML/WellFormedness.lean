-- SUMMARY: Well-formedness of specifications in a signature, with its checkers.
import Mica.SourceTinyML.Types
import Mica.SourceTinyML.SpecFn
import Mica.Base.Except

/-!
# Well-formedness

A specification is well formed when it mentions only the symbols of a signature.
Each predicate `wfIn` has a checker `checkWf` and a lemma `checkWf_ok`
that relates the two.
-/

/-! ## Specifications -/

/-- An atom is well-formed in a signature. -/
def Atom.wfIn (Δ : Signature) : Atom T τ → Prop
  | .isint t  => t.wfIn Δ
  | .isbool t => t.wfIn Δ
  | .isinj _ _ t => t.wfIn Δ
  | .own t _  => t.wfIn Δ
  | .arr t _ => t.wfIn Δ
  | .rel name t => (SpecFn.isDefined name t).wfIn Δ ∧ (SpecFn.call name t).wfIn Δ

def Atom.checkWf (p : Atom T τ) (Δ : Signature) : Except String Unit :=
  match p with
  | .isint t  => t.checkWf Δ
  | .isbool t => t.checkWf Δ
  | .isinj _ _ t => t.checkWf Δ
  | .own t _  => t.checkWf Δ
  | .arr t _ => t.checkWf Δ
  | .rel name t => do
      (SpecFn.isDefined name t).checkWf Δ
      (SpecFn.call name t).checkWf Δ

theorem Atom.checkWf_ok {p : Atom T τ} {Δ : Signature} (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | isint t  => exact Term.checkWf_ok h
  | isbool t => exact Term.checkWf_ok h
  | isinj tag arity t => exact Term.checkWf_ok h
  | own t ty => exact Term.checkWf_ok h
  | arr t ty => exact Term.checkWf_ok h
  | rel name t =>
    have ⟨w, hd, hv⟩ := Except.bind_ok h
    exact ⟨Formula.checkWf_ok hd, Term.checkWf_ok hv⟩

theorem Atom.wfIn_mono {p : Atom T τ} {Δ Δ' : Signature}
    (h : p.wfIn Δ) (hmono : Δ.Subset Δ') (hwf : Δ'.wf) : p.wfIn Δ' := by
  cases p with
  | isint t  => exact Term.wfIn_mono t h hmono hwf
  | isbool t => exact Term.wfIn_mono t h hmono hwf
  | isinj tag arity t => exact Term.wfIn_mono t h hmono hwf
  | own t ty => exact Term.wfIn_mono t h hmono hwf
  | arr t ty => exact Term.wfIn_mono t h hmono hwf
  | rel name t =>
    exact ⟨Formula.wfIn_mono _ h.1 hmono hwf, Term.wfIn_mono _ h.2 hmono hwf⟩

/-- An assertion is well-formed in a signature when every formula
    and term it mentions only refers to variables/symbols from `Δ` (extended by its own
    let-bindings). The `retWf` predicate specifies an additional well-formedness
    condition on the return value; by default it is trivially true. -/
def Assertion.wfIn (retWf : α → Signature → Prop) (Δ : Signature) : Assertion T α → Prop
  | .ret a       => retWf a Δ
  | .assert φ k  => φ.wfIn Δ ∧ k.wfIn retWf Δ
  | .let_ v t k  => t.wfIn Δ ∧ k.wfIn retWf (Δ.declVar v)
  | .pred v p k  => p.wfIn Δ ∧ k.wfIn retWf (Δ.declVar v)
  | .ite φ kt ke => φ.wfIn Δ ∧ kt.wfIn retWf Δ ∧ ke.wfIn retWf Δ

def Assertion.checkWf (retCheck : α → Signature → Except String Unit)
    (Δ : Signature) : Assertion T α → Except String Unit
  | .ret a       => retCheck a Δ
  | .assert φ k  => do φ.checkWf Δ; k.checkWf retCheck Δ
  | .let_ v t k  => do t.checkWf Δ; k.checkWf retCheck (Δ.declVar v)
  | .pred v p k  => do p.checkWf Δ; k.checkWf retCheck (Δ.declVar v)
  | .ite φ kt ke => do φ.checkWf Δ; kt.checkWf retCheck Δ; ke.checkWf retCheck Δ

theorem Assertion.checkWf_ok {m : Assertion T α} {retCheck : α → Signature → Except String Unit}
    {retWf : α → Signature → Prop} {Δ : Signature}
    (hret : ∀ a Δ', retCheck a Δ' = .ok () → retWf a Δ')
    (h : m.checkWf retCheck Δ = .ok ()) : m.wfIn retWf Δ := by
  induction m generalizing Δ with
  | ret a => exact hret a Δ h
  | assert φ k ih =>
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    exact ⟨Formula.checkWf_ok h1, ih h2⟩
  | let_ v t k ih =>
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    exact ⟨Term.checkWf_ok h1, ih h2⟩
  | pred v p k ih =>
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    exact ⟨Atom.checkWf_ok h1, ih h2⟩
  | ite φ kt ke iht ihe =>
    have ⟨_, h1, h23⟩ := Except.bind_ok h
    have ⟨_, h2, h3⟩ := Except.bind_ok h23
    exact ⟨Formula.checkWf_ok h1, iht h2, ihe h3⟩

theorem Assertion.wfIn_mono (m : Assertion T α) (retWf : α → Signature → Prop)
    (hret : ∀ a Δ Δ', Δ.Subset Δ' → Δ'.wf → retWf a Δ → retWf a Δ')
    {Δ Δ' : Signature}
    (h : m.wfIn retWf Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : m.wfIn retWf Δ' := by
  induction m generalizing Δ Δ' with
  | ret a => exact hret a Δ Δ' hsub hwf h
  | assert φ k ih => exact ⟨Formula.wfIn_mono φ h.1 hsub hwf, ih h.2 hsub hwf⟩
  | let_ v t k ih =>
    exact ⟨Term.wfIn_mono t h.1 hsub hwf,
      ih h.2 (Signature.Subset.declVar hsub v) (Signature.wf_declVar hwf)⟩
  | pred v p k ih =>
    exact ⟨Atom.wfIn_mono h.1 hsub hwf,
      ih h.2 (Signature.Subset.declVar hsub v) (Signature.wf_declVar hwf)⟩
  | ite φ kt ke iht ihe =>
    exact ⟨Formula.wfIn_mono φ h.1 hsub hwf, iht h.2.1 hsub hwf, ihe h.2.2 hsub hwf⟩

/-- A predicate transformer is well-formed when its outer assertion is well-formed
    and each inner postcondition assertion is also well-formed (in the extended context). -/
def PredTrans.wfIn (Δ : Signature) (pt : PredTrans T) : Prop :=
  Assertion.wfIn
    (fun post Δ' => Assertion.wfIn (fun _ _ => True) (Δ'.declVar ⟨post.name, .value⟩) post.body)
    Δ pt

def PredTrans.checkWf (Δ : Signature) (pt : PredTrans T) : Except String Unit :=
  Assertion.checkWf
    (fun post Δ' => Assertion.checkWf (fun _ _ => .ok ()) (Δ'.declVar ⟨post.name, .value⟩) post.body)
    Δ pt

theorem PredTrans.checkWf_ok {pt : PredTrans T} {Δ : Signature}
    (h : pt.checkWf Δ = .ok ()) : pt.wfIn Δ :=
  Assertion.checkWf_ok
    (fun _ _ hok => Assertion.checkWf_ok (fun _ _ _ => trivial) hok)
    h

theorem PredTrans.wfIn_mono {pt : PredTrans T} {Δ Δ' : Signature}
    (h : pt.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : pt.wfIn Δ' := by
  unfold PredTrans.wfIn at h ⊢
  exact Assertion.wfIn_mono pt _
    (fun post ds ds' hsub' hwf' hpost =>
      Assertion.wfIn_mono post.body _ (fun _ _ _ _ _ h => h) hpost
        (Signature.Subset.declVar hsub' ⟨post.name, .value⟩)
        (Signature.wf_declVar hwf'))
    h hsub hwf

/-- The list of SMT variables corresponding to a spec's arguments. -/
def Spec.argVars (args : List String) : List Var :=
  args.map fun name => ⟨name, .value⟩

/-- A spec is well-formed when its predicate transformer is well-formed in the
    context extended with all argument variables. -/
def Spec.wfIn (spec : Spec T) (Δ : Signature) : Prop :=
  PredTrans.wfIn (Δ.declVars (argVars spec.allArgs)) spec.pred

def Spec.checkWf (spec : Spec T) (Δ : Signature) : Except String Unit :=
  PredTrans.checkWf (Δ.declVars (argVars spec.allArgs)) spec.pred

theorem Spec.checkWf_ok {spec : Spec T} {Δ : Signature}
    (h : spec.checkWf Δ = .ok ()) : spec.wfIn Δ :=
  PredTrans.checkWf_ok h

theorem Spec.wfIn_mono {spec : Spec T} {Δ Δ' : Signature}
    (h : spec.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    spec.wfIn Δ' :=
  PredTrans.wfIn_mono h (Signature.Subset.declVars hsub (argVars spec.allArgs))
    (Signature.wf_declVars hwf)

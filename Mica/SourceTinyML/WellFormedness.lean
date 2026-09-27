-- SUMMARY: Well-formedness of specifications and types in a signature and a type environment, with its checkers.
import Mica.SourceTinyML.Types
import Mica.SourceTinyML.SpecFn
import Mica.Base.Except

/-!
# Well-formedness

A specification is well formed when it mentions only the symbols of a signature.
A type is well formed when, in addition, its named types are declared at their
arity. Each predicate `wfIn` has a checker `checkWf` and a lemma `checkWf_ok`
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

namespace TinyML

/-! ## Well-formed types -/

/-- The specs in a type mention only the symbols of `Δ`, their argument counts
    match their arrows, and the named types of the type are those of `Θ`. -/
inductive Typ.wfIn (Δ : Signature) (Θ : TypeEnv) : Typ → Prop
  | prim (p : PrimitiveType) : Typ.wfIn Δ Θ (.prim p)
  | value : Typ.wfIn Δ Θ .value
  | empty : Typ.wfIn Δ Θ .empty
  | tvar (a : TyVar) : Typ.wfIn Δ Θ (.tvar a)
  | arrowNone {args : List Typ} {ret : Typ} :
      (∀ a ∈ args, Typ.wfIn Δ Θ a) → Typ.wfIn Δ Θ ret → Typ.wfIn Δ Θ (.arrow args ret none)
  | arrow {args : List Typ} {ret : Typ} {s : Spec Typ} :
      (∀ a ∈ args, Typ.wfIn Δ Θ a) → Typ.wfIn Δ Θ ret → s.wfIn Δ →
      s.args.length = args.length → (∀ t ∈ s.types, Typ.wfIn Δ Θ t) →
      Typ.wfIn Δ Θ (.arrow args ret (some s))
  | ref {t : Typ} : Typ.wfIn Δ Θ t → Typ.wfIn Δ Θ (.ref t)
  | array {t : Typ} : Typ.wfIn Δ Θ t → Typ.wfIn Δ Θ (.array t)
  | ownedArray {t : Typ} : Typ.wfIn Δ Θ t → Typ.wfIn Δ Θ (.ownedArray t)
  | vec {t : Typ} : Typ.wfIn Δ Θ t → Typ.wfIn Δ Θ (.vec t)
  | owned {t : Typ} : Typ.wfIn Δ Θ t → Typ.wfIn Δ Θ (.owned t)
  | tuple {ts : List Typ} : (∀ t ∈ ts, Typ.wfIn Δ Θ t) → Typ.wfIn Δ Θ (.tuple ts)
  | sum {ts : List Typ} : (∀ t ∈ ts, Typ.wfIn Δ Θ t) → Typ.wfIn Δ Θ (.sum ts)
  | named {T : TypeName} {args : List Typ} :
      (TypeName.unfold Θ T args).isSome → (∀ a ∈ args, Typ.wfIn Δ Θ a) →
      Typ.wfIn Δ Θ (.named T args)

/-- The payloads of the declarations of `Θ` are well formed. -/
def TypeEnv.wfIn (Δ : Signature) (Θ : TypeEnv) : Prop :=
  ∀ T d, Θ T = some d → ∀ p ∈ d.payloads, Typ.wfIn Δ Θ p

/-- Well-formedness survives more spec symbols and more type declarations. -/
theorem Typ.wfIn_mono {Δ Δ' : Signature} {Θ Θ' : TypeEnv} (hΔ : Δ.Subset Δ') (hwf : Δ'.wf)
    (hΘ : ∀ T d, Θ T = some d → Θ' T = some d) {t : Typ} (h : Typ.wfIn Δ Θ t) :
    Typ.wfIn Δ' Θ' t := by
  induction h with
  | prim p => exact .prim p
  | value => exact .value
  | empty => exact .empty
  | tvar a => exact .tvar a
  | arrowNone _ _ iha ihr => exact .arrowNone iha ihr
  | arrow _ _ hs hlen _ iha ihr iht => exact .arrow iha ihr (Spec.wfIn_mono hs hΔ hwf) hlen iht
  | ref _ ih => exact .ref ih
  | array _ ih => exact .array ih
  | ownedArray _ ih => exact .ownedArray ih
  | vec _ ih => exact .vec ih
  | owned _ ih => exact .owned ih
  | tuple _ ih => exact .tuple ih
  | sum _ ih => exact .sum ih
  | named hunf _ ih => exact .named (by rw [TypeName.unfold_mono hΘ hunf]; exact hunf) ih

/-! ### Checking well-formedness -/

mutual

/-- Decide `Typ.wfIn`. -/
def Typ.checkWf (Δ : Signature) (Θ : TypeEnv) : Typ → Except String Unit
  | .prim _ | .value | .empty | .tvar _ => pure ()
  | .arrow args ret spec => do
    Typ.checkWfList Δ Θ args
    Typ.checkWf Δ Θ ret
    Typ.checkWfSpec? Δ Θ args.length spec
  | .ref t | .array t | .ownedArray t | .vec t | .owned t => Typ.checkWf Δ Θ t
  | .tuple ts | .sum ts => Typ.checkWfList Δ Θ ts
  | .named T args =>
    match TypeName.unfold Θ T args with
    | some _ => Typ.checkWfList Δ Θ args
    | none => .error s!"type {T} is not declared"
termination_by structural t => t

def Typ.checkWfList (Δ : Signature) (Θ : TypeEnv) : List Typ → Except String Unit
  | [] => pure ()
  | t :: ts => do Typ.checkWf Δ Θ t; Typ.checkWfList Δ Θ ts
termination_by structural ts => ts

def Typ.checkWfAtom (Δ : Signature) (Θ : TypeEnv) : {s : Srt} → Atom Typ s → Except String Unit
  | _, .isint _ | _, .isbool _ | _, .isinj .. | _, .rel .. => pure ()
  | _, .own _ t | _, .arr _ t => Typ.checkWf Δ Θ t

def Typ.checkWfPost (Δ : Signature) (Θ : TypeEnv) : Assertion Typ Unit → Except String Unit
  | .ret () => pure ()
  | .assert _ k | .let_ _ _ k => Typ.checkWfPost Δ Θ k
  | .pred _ p k => do Typ.checkWfAtom Δ Θ p; Typ.checkWfPost Δ Θ k
  | .ite _ kt ke => do Typ.checkWfPost Δ Θ kt; Typ.checkWfPost Δ Θ ke
termination_by structural a => a

def Typ.checkWfPredTrans (Δ : Signature) (Θ : TypeEnv) :
    Assertion Typ (Post Typ) → Except String Unit
  | .ret p => Typ.checkWfPost Δ Θ p.body
  | .assert _ k | .let_ _ _ k => Typ.checkWfPredTrans Δ Θ k
  | .pred _ p k => do Typ.checkWfAtom Δ Θ p; Typ.checkWfPredTrans Δ Θ k
  | .ite _ kt ke => do Typ.checkWfPredTrans Δ Θ kt; Typ.checkWfPredTrans Δ Θ ke
termination_by structural a => a

def Typ.checkWfGhost (Δ : Signature) (Θ : TypeEnv) :
    List (String × Typ) → Except String Unit
  | [] => pure ()
  | (_, t) :: rest => do Typ.checkWf Δ Θ t; Typ.checkWfGhost Δ Θ rest
termination_by structural g => g

/-- The specification of an arrow of `n` arguments. -/
def Typ.checkWfSpec (Δ : Signature) (Θ : TypeEnv) (n : Nat) : Spec Typ → Except String Unit
  | s => do
    s.checkWf Δ
    (if s.args.length = n then pure ()
      else .error s!"a specification binds {s.args.length} arguments, its arrow has {n}")
    Typ.checkWfGhost Δ Θ s.ghost
    Typ.checkWfPredTrans Δ Θ s.pred

def Typ.checkWfSpec? (Δ : Signature) (Θ : TypeEnv) (n : Nat) :
    Option (Spec Typ) → Except String Unit
  | none => pure ()
  | some s => Typ.checkWfSpec Δ Θ n s

end

mutual

theorem Typ.checkWf_ok {Δ : Signature} {Θ : TypeEnv} :
    ∀ t : Typ, Typ.checkWf Δ Θ t = .ok () → Typ.wfIn Δ Θ t
  | .prim _, _ => .prim _
  | .value, _ => .value
  | .empty, _ => .empty
  | .tvar _, _ => .tvar _
  | .arrow args ret spec, h => by
    simp only [Typ.checkWf] at h
    have ⟨_, h1, h23⟩ := Except.bind_ok h
    have ⟨_, h2, h3⟩ := Except.bind_ok h23
    have hargs := Typ.checkWfList_ok args h1
    have hret := Typ.checkWf_ok ret h2
    cases spec with
    | none => exact .arrowNone hargs hret
    | some s =>
      obtain ⟨hs, hlen, htypes⟩ := Typ.checkWfSpec?_ok args.length (some s) h3 s rfl
      exact .arrow hargs hret hs hlen htypes
  | .ref t, h => .ref (Typ.checkWf_ok t (by simpa only [Typ.checkWf] using h))
  | .array t, h => .array (Typ.checkWf_ok t (by simpa only [Typ.checkWf] using h))
  | .ownedArray t, h => .ownedArray (Typ.checkWf_ok t (by simpa only [Typ.checkWf] using h))
  | .vec t, h => .vec (Typ.checkWf_ok t (by simpa only [Typ.checkWf] using h))
  | .owned t, h => .owned (Typ.checkWf_ok t (by simpa only [Typ.checkWf] using h))
  | .tuple ts, h => .tuple (Typ.checkWfList_ok ts (by simpa only [Typ.checkWf] using h))
  | .sum ts, h => .sum (Typ.checkWfList_ok ts (by simpa only [Typ.checkWf] using h))
  | .named T args, h => by
    simp only [Typ.checkWf] at h
    split at h
    · rename_i hT
      exact .named (by simp [hT]) (Typ.checkWfList_ok args h)
    · cases h
termination_by structural t => t

theorem Typ.checkWfList_ok {Δ : Signature} {Θ : TypeEnv} :
    ∀ ts : List Typ, Typ.checkWfList Δ Θ ts = .ok () → ∀ t ∈ ts, Typ.wfIn Δ Θ t
  | [], _ => fun _ h => nomatch h
  | t :: ts, h => by
    simp only [Typ.checkWfList] at h
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    intro t' ht'
    rcases List.mem_cons.mp ht' with ht' | ht'
    · rw [ht']
      exact Typ.checkWf_ok t h1
    · exact Typ.checkWfList_ok ts h2 t' ht'
termination_by structural ts => ts

theorem Typ.checkWfAtom_ok {Δ : Signature} {Θ : TypeEnv} :
    ∀ {s : Srt} (a : Atom Typ s), Typ.checkWfAtom Δ Θ a = .ok () →
      ∀ t ∈ a.types, Typ.wfIn Δ Θ t
  | _, .isint _, _ | _, .isbool _, _ | _, .isinj .., _ | _, .rel .., _ =>
    fun _ h => by simp [Atom.types] at h
  | _, .own _ t, h | _, .arr _ t, h => fun t' ht' => by
    simp only [Atom.types, List.mem_singleton] at ht'
    rw [ht']
    exact Typ.checkWf_ok t h
termination_by structural _ a => a

theorem Typ.checkWfPost_ok {Δ : Signature} {Θ : TypeEnv} :
    ∀ a : Assertion Typ Unit, Typ.checkWfPost Δ Θ a = .ok () →
      ∀ t ∈ a.types (fun _ => []), Typ.wfIn Δ Θ t
  | .ret (), _ => fun _ h => by simp [Assertion.types] at h
  | .assert _ k, h | .let_ _ _ k, h => fun t ht =>
    Typ.checkWfPost_ok k h t (by simpa [Assertion.types] using ht)
  | .pred _ p k, h => fun t ht => by
    simp only [Typ.checkWfPost] at h
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    rcases List.mem_append.mp (by simpa [Assertion.types] using ht) with ht | ht
    · exact Typ.checkWfAtom_ok p h1 t ht
    · exact Typ.checkWfPost_ok k h2 t ht
  | .ite _ kt ke, h => fun t ht => by
    simp only [Typ.checkWfPost] at h
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    rcases List.mem_append.mp (by simpa [Assertion.types] using ht) with ht | ht
    · exact Typ.checkWfPost_ok kt h1 t ht
    · exact Typ.checkWfPost_ok ke h2 t ht
termination_by structural a => a

theorem Typ.checkWfPredTrans_ok {Δ : Signature} {Θ : TypeEnv} :
    ∀ a : Assertion Typ (Post Typ), Typ.checkWfPredTrans Δ Θ a = .ok () →
      ∀ t ∈ a.types (fun post => post.body.types fun _ => []), Typ.wfIn Δ Θ t
  | .ret p, h => fun t ht => Typ.checkWfPost_ok p.body h t (by simpa [Assertion.types] using ht)
  | .assert _ k, h | .let_ _ _ k, h => fun t ht =>
    Typ.checkWfPredTrans_ok k h t (by simpa [Assertion.types] using ht)
  | .pred _ p k, h => fun t ht => by
    simp only [Typ.checkWfPredTrans] at h
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    rcases List.mem_append.mp (by simpa [Assertion.types] using ht) with ht | ht
    · exact Typ.checkWfAtom_ok p h1 t ht
    · exact Typ.checkWfPredTrans_ok k h2 t ht
  | .ite _ kt ke, h => fun t ht => by
    simp only [Typ.checkWfPredTrans] at h
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    rcases List.mem_append.mp (by simpa [Assertion.types] using ht) with ht | ht
    · exact Typ.checkWfPredTrans_ok kt h1 t ht
    · exact Typ.checkWfPredTrans_ok ke h2 t ht
termination_by structural a => a

theorem Typ.checkWfGhost_ok {Δ : Signature} {Θ : TypeEnv} :
    ∀ g : List (String × Typ), Typ.checkWfGhost Δ Θ g = .ok () →
      ∀ t ∈ g.map Prod.snd, Typ.wfIn Δ Θ t
  | [], _ => fun _ h => nomatch h
  | (_, t) :: rest, h => by
    simp only [Typ.checkWfGhost] at h
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    intro t' ht'
    rcases List.mem_cons.mp ht' with ht' | ht'
    · rw [ht']
      exact Typ.checkWf_ok t h1
    · exact Typ.checkWfGhost_ok rest h2 t' ht'
termination_by structural g => g

theorem Typ.checkWfSpec_ok {Δ : Signature} {Θ : TypeEnv} (n : Nat) :
    ∀ s : Spec Typ, Typ.checkWfSpec Δ Θ n s = .ok () →
      s.wfIn Δ ∧ s.args.length = n ∧ ∀ t ∈ s.types, Typ.wfIn Δ Θ t
  | s, h => by
    simp only [Typ.checkWfSpec] at h
    have ⟨_, h1, h234⟩ := Except.bind_ok h
    have ⟨_, h2, h34⟩ := Except.bind_ok h234
    have ⟨_, h3, h4⟩ := Except.bind_ok h34
    refine ⟨Spec.checkWf_ok h1, ?_, fun t ht => ?_⟩
    · split at h2
      · assumption
      · cases h2
    · rcases List.mem_append.mp ht with ht | ht
      · exact Typ.checkWfGhost_ok s.ghost h3 t ht
      · exact Typ.checkWfPredTrans_ok s.pred h4 t ht
termination_by structural s => s

theorem Typ.checkWfSpec?_ok {Δ : Signature} {Θ : TypeEnv} (n : Nat) :
    ∀ spec : Option (Spec Typ), Typ.checkWfSpec? Δ Θ n spec = .ok () →
      ∀ s, spec = some s → s.wfIn Δ ∧ s.args.length = n ∧ ∀ t ∈ s.types, Typ.wfIn Δ Θ t
  | none, _ => fun _ h => nomatch h
  | some s, h => fun _ hs => by
    cases hs
    exact Typ.checkWfSpec_ok n s h
termination_by structural spec => spec

end

/-! ### Well-formedness under substitution -/

section Subst

variable {σ : TyVar → Typ}

private theorem Atom.wfIn_substAtom {τ : Srt} (p : Atom Typ τ) (Δ : Signature) :
    (Typ.substAtom σ p).wfIn Δ ↔ p.wfIn Δ := by
  cases p <;> rfl

private theorem Assertion.wfIn_substPost :
    ∀ (m : Assertion Typ Unit) (Δ : Signature),
      (Typ.substPost σ m).wfIn (fun _ _ => True) Δ ↔ m.wfIn (fun _ _ => True) Δ := by
  intro m
  induction m with
  | ret _ => intro Δ; simp [Typ.substPost, Assertion.wfIn]
  | assert φ k ih => intro Δ; simp [Typ.substPost, Assertion.wfIn, ih]
  | let_ v t k ih => intro Δ; simp [Typ.substPost, Assertion.wfIn, ih]
  | pred v p k ih => intro Δ; simp [Typ.substPost, Assertion.wfIn, ih, Atom.wfIn_substAtom]
  | ite φ kt ke iht ihe => intro Δ; simp [Typ.substPost, Assertion.wfIn, iht, ihe]

private theorem PredTrans.wfIn_substPredTrans :
    ∀ (m : Assertion Typ (Post Typ)) (Δ : Signature),
      PredTrans.wfIn Δ (Typ.substPredTrans σ m) ↔ PredTrans.wfIn Δ m := by
  intro m
  unfold PredTrans.wfIn
  induction m with
  | ret p => intro Δ; simp [Typ.substPredTrans, Assertion.wfIn, Assertion.wfIn_substPost]
  | assert φ k ih => intro Δ; simp [Typ.substPredTrans, Assertion.wfIn, ih]
  | let_ v t k ih => intro Δ; simp [Typ.substPredTrans, Assertion.wfIn, ih]
  | pred v p k ih =>
    intro Δ; simp [Typ.substPredTrans, Assertion.wfIn, ih, Atom.wfIn_substAtom]
  | ite φ kt ke iht ihe => intro Δ; simp [Typ.substPredTrans, Assertion.wfIn, iht, ihe]

private theorem Spec.wfIn_substSpec (s : Spec Typ) (Δ : Signature) :
    (Typ.substSpec σ s).wfIn Δ ↔ s.wfIn Δ := by
  simp only [Spec.wfIn, Typ.substSpec, Spec.allArgs, Typ.substGhost_fst]
  exact PredTrans.wfIn_substPredTrans _ _

private theorem Atom.types_substAtom {τ : Srt} (p : Atom Typ τ) :
    (Typ.substAtom σ p).types = p.types.map (Typ.subst σ) := by
  cases p <;> rfl

private theorem Assertion.types_substPost :
    ∀ m : Assertion Typ Unit,
      (Typ.substPost σ m).types (fun _ => []) = (m.types fun _ => []).map (Typ.subst σ) := by
  intro m
  induction m with
  | ret _ => rfl
  | assert φ k ih => simpa [Typ.substPost, Assertion.types] using ih
  | let_ v t k ih => simpa [Typ.substPost, Assertion.types] using ih
  | pred v p k ih => simp [Typ.substPost, Assertion.types, ih, Atom.types_substAtom]
  | ite φ kt ke iht ihe => simp [Typ.substPost, Assertion.types, iht, ihe]

private theorem Assertion.types_substPredTrans :
    ∀ m : Assertion Typ (Post Typ),
      (Typ.substPredTrans σ m).types (fun post => post.body.types fun _ => []) =
        (m.types fun post => post.body.types fun _ => []).map (Typ.subst σ) := by
  intro m
  induction m with
  | ret p => simp [Typ.substPredTrans, Assertion.types, Assertion.types_substPost]
  | assert φ k ih => simpa [Typ.substPredTrans, Assertion.types] using ih
  | let_ v t k ih => simpa [Typ.substPredTrans, Assertion.types] using ih
  | pred v p k ih => simp [Typ.substPredTrans, Assertion.types, ih, Atom.types_substAtom]
  | ite φ kt ke iht ihe => simp [Typ.substPredTrans, Assertion.types, iht, ihe]

private theorem Spec.types_substSpec (s : Spec Typ) :
    (Typ.substSpec σ s).types = s.types.map (Typ.subst σ) := by
  simp [Spec.types, Typ.substSpec, Typ.substGhost_snd, Assertion.types_substPredTrans]

private theorem TypeName.unfold_isSome_map {Θ : TypeEnv} (T : TypeName) (args : List Typ)
    (f : Typ → Typ) :
    (TypeName.unfold Θ T (args.map f)).isSome = (TypeName.unfold Θ T args).isSome := by
  cases T with
  | user n => simp [TypeName.unfold]
  | predef p => simp only [TypeName.unfold, List.length_map]; split <;> rfl

theorem Typ.wfIn_subst {Δ : Signature} {Θ : TypeEnv} (hσ : ∀ a, Typ.wfIn Δ Θ (σ a)) {t : Typ}
    (h : Typ.wfIn Δ Θ t) : Typ.wfIn Δ Θ (Typ.subst σ t) := by
  induction h with
  | prim p => exact .prim p
  | value => exact .value
  | empty => exact .empty
  | tvar a => exact hσ a
  | arrowNone _ _ ihargs ihret =>
    simp only [Typ.subst, Typ.substList_eq, Typ.substSpec?]
    refine .arrowNone (fun a ha => ?_) ihret
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    exact ihargs a' ha'
  | arrow _ _ hs hlen _ ihargs ihret ihtys =>
    simp only [Typ.subst, Typ.substList_eq, Typ.substSpec?]
    refine .arrow (fun a ha => ?_) ihret ((Spec.wfIn_substSpec _ _).mpr hs)
      (by simpa [Typ.substSpec] using hlen) (fun t ht => ?_)
    · obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      exact ihargs a' ha'
    · rw [Spec.types_substSpec] at ht
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
      exact ihtys t' ht'
  | ref _ ih => exact .ref ih
  | array _ ih => exact .array ih
  | ownedArray _ ih => exact .ownedArray ih
  | vec _ ih => exact .vec ih
  | owned _ ih => exact .owned ih
  | tuple _ ih =>
    simp only [Typ.subst, Typ.substList_eq]
    refine .tuple fun t ht => ?_
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact ih t' ht'
  | sum _ ih =>
    simp only [Typ.subst, Typ.substList_eq]
    refine .sum fun t ht => ?_
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact ih t' ht'
  | named hunf _ ih =>
    simp only [Typ.subst, Typ.substList_eq]
    refine .named (by rw [TypeName.unfold_isSome_map]; exact hunf) fun a ha => ?_
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    exact ih a' ha'

end Subst

private theorem Predef.payloads_wfIn {Δ : Signature} {Θ : TypeEnv} (p : Predef) :
    ∀ t ∈ p.decl.payloads, Typ.wfIn Δ Θ t := by
  intro t ht
  cases p with
  | option =>
    simp only [Predef.decl, Predef.ctors, List.map, List.mem_cons, List.not_mem_nil,
      _root_.or_false] at ht
    rcases ht with rfl | rfl
    · exact .prim _
    · exact .tvar _
  | list =>
    simp only [Predef.decl, Predef.ctors, List.map, List.mem_cons, List.not_mem_nil,
      _root_.or_false] at ht
    rcases ht with rfl | rfl
    · exact .prim _
    · refine .tuple fun u hu => ?_
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hu
      rcases hu with rfl | rfl
      · exact .tvar _
      · refine .named (by simp [TypeName.unfold, Predef.arity, Predef.tparams]) fun a ha => ?_
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
        subst ha
        exact .tvar _

/-- Unfolding a well-formed named type gives a well-formed type. -/
theorem Typ.wfIn_unfold {Δ : Signature} {Θ : TypeEnv} (hΘ : TypeEnv.wfIn Δ Θ)
    {T : TypeName} {args : List Typ} {ty : Typ} (hargs : ∀ a ∈ args, Typ.wfIn Δ Θ a)
    (h : TypeName.unfold Θ T args = some ty) : Typ.wfIn Δ Θ ty := by
  have hinst : ∀ d : DataDecl, (∀ p ∈ d.payloads, Typ.wfIn Δ Θ p) →
      Typ.wfIn Δ Θ (d.instantiate args) := by
    intro d hd
    unfold DataDecl.instantiate
    refine .sum fun t ht => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    refine Typ.wfIn_subst (fun v => ?_) (hd p hp)
    split
    · rename_i x ty' hfind
      exact hargs ty' (List.of_mem_zip (List.mem_of_find?_eq_some hfind)).2
    · exact .empty
  cases T with
  | user n =>
    simp only [TypeName.unfold, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    exact hinst d (hΘ _ d hd)
  | predef p =>
    simp only [TypeName.unfold] at h
    split at h
    · cases h
      exact hinst _ (Predef.payloads_wfIn p)
    · cases h

end TinyML

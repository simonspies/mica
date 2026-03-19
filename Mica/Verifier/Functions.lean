import Mica.TinyML.Expr
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.TinyML.WeakestPre
import Mica.Verifier.Monad
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Verifier.Utils
import Mica.Verifier.Expressions
import Mica.Engine.Driver
import Mica.Base.Fresh
import Mathlib.Data.Finmap



/-- Erase multiple keys from a SpecMap. -/
def SpecMap.eraseAll (keys : List String) (S : SpecMap) : SpecMap :=
  keys.foldl (fun acc k => Finmap.erase k acc) S

@[simp] theorem SpecMap.eraseAll_nil (S : SpecMap) : SpecMap.eraseAll [] S = S := rfl

@[simp] theorem SpecMap.eraseAll_cons (k : String) (ks : List String) (S : SpecMap) :
    SpecMap.eraseAll (k :: ks) S = SpecMap.eraseAll ks (Finmap.erase k S) := by
  simp [SpecMap.eraseAll, List.foldl_cons]

private theorem SpecMap.eraseAll_lookup_none_of_none {keys : List String} {S : SpecMap} {y : String}
    (h : S.lookup y = none) : (SpecMap.eraseAll keys S).lookup y = none := by
  induction keys generalizing S with
  | nil => exact h
  | cons k ks ih =>
    rw [eraseAll_cons]; apply ih
    by_cases hky : k = y
    · subst hky; simp [Finmap.lookup_erase]
    · rw [Finmap.lookup_erase_ne (Ne.symm hky)]; exact h

theorem SpecMap.eraseAll_lookup_none {keys : List String} {S : SpecMap} {y : String}
    (hy : y ∈ keys) : (SpecMap.eraseAll keys S).lookup y = none := by
  induction keys generalizing S with
  | nil => simp at hy
  | cons k ks ih =>
    rw [eraseAll_cons]; cases List.mem_cons.mp hy with
    | inl heq => subst heq; exact eraseAll_lookup_none_of_none (by simp [Finmap.lookup_erase])
    | inr hmem => exact ih hmem

theorem SpecMap.eraseAll_lookup_of_notin {keys : List String} {y : String}
    (hy : y ∉ keys) (S : SpecMap) :
    (SpecMap.eraseAll keys S).lookup y = S.lookup y := by
  induction keys generalizing S with
  | nil => rfl
  | cons k ks ih =>
    simp at hy
    rw [eraseAll_cons, ih hy.2, Finmap.lookup_erase_ne hy.1]

theorem SpecMap.wfIn_eraseAll {keys : List String} {S : SpecMap} {decls : List Var}
    (h : S.wfIn decls) : (SpecMap.eraseAll keys S).wfIn decls := by
  induction keys generalizing S with
  | nil => exact h
  | cons k ks ih => exact ih (SpecMap.wfIn_erase h)

/-- Extract argument names from binders, pairing with spec arg info.
    Requires exact length match. -/
private def extractArgNames : List (TinyML.Binder × Option TinyML.Type_) → List (String × TinyML.Type_) →
    Except String (List String)
  | [], [] => .ok []
  | (.named x, _) :: rest, _ :: specRest => do
    let tail ← extractArgNames rest specRest
    .ok (x :: tail)
  | _, _ => .error "checkSpec: argument mismatch"

private theorem extractArgNames_spec {argBinders : List (TinyML.Binder × Option TinyML.Type_)}
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

private theorem findVal_none_of_not_mem
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

private theorem not_mem_of_lookup_zip_reverse_none
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

-- If agreeOnLinked holds and values at each binding are well-typed, then typedSubst holds.
-- Should be moved to Utils.lean later.
private theorem typedSubst_of_agreeOnLinked
    {B : Bindings} {Γ : TinyML.TyCtx} {γ : TinyML.Subst} {ρ : Env}
    (hagree : B.agreeOnLinked ρ γ)
    (htyped_vals : ∀ x x' t, B.lookup x = some x' → Γ x = some t →
      TinyML.ValHasType (ρ.lookup .value x'.name) t) :
    B.typedSubst Γ γ := by
  intro x x' t hmem hΓ
  obtain ⟨_, hval⟩ := hagree x x' hmem
  exact ⟨_, hval, htyped_vals x x' t hmem hΓ⟩

-- foldl extend doesn't change the value at x if x doesn't appear in the list.
-- Should be moved to TinyML/Typing.lean later.
private theorem foldl_extend_stable
    (args : List (String × TinyML.Type_)) (Γ : TinyML.TyCtx) (x : String)
    (hx : ∀ a ∈ args, a.1 ≠ x) :
    (args.foldl (fun ctx a => ctx.extend a.1 a.2) Γ) x = Γ x := by
  induction args generalizing Γ with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons]
    have := ih (Γ.extend a.1 a.2) (fun a' ha' => hx a' (.tail _ ha'))
    rw [this]
    have hne := hx a (.head _)
    simp [TinyML.TyCtx.extend, beq_iff_eq, Ne.symm hne]

-- For lists with "last wins" semantics: if the reversed-zip lookup finds x' at x,
-- and the foldl-Γ lookup finds type t at x, and Forall₂ relates vars to vals
-- with ValsHaveTypes, then the value at x' has type t.
-- All three structures agree on the "last occurrence" of x.
-- Should be moved to Utils.lean later.
private theorem val_typed_of_last_wins
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
                  exact foldl_extend_stable as (Γ₀.extend a.1 a.2) x (by
                    intro ⟨n, t⟩ hmem heq; exact hx_notin t (heq ▸ hmem))
                rw [hΓ_stable] at hΓ
                have hxa' : x = a.1 := by exact beq_iff_eq.mp hxa
                subst hxa'
                simp [TinyML.TyCtx.extend] at hΓ; subst hΓ
                rw [← hlk_head] at htype_head; exact htype_head
              · simp [List.lookup, hxa] at hlookup

-- Should be moved to Utils.lean later.
private theorem agreeOnLinked_zip_reverse
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

def checkSpec (S : SpecMap) (e : TinyML.Expr) (s : Spec) : VerifM Unit := do
  let (fb, argNames, body) ← match e with
    | .fix fb argBinders _ body => do
      match extractArgNames argBinders s.args with
      | .ok names => pure (fb, names, body)
      | .error msg => VerifM.fatal msg
    | _ => VerifM.fatal "checkSpec: expected function"
  let S' := SpecMap.eraseAll argNames (S.insert' fb s)
  Spec.implement s fun argVars => do
    let B : Bindings := (argNames.zip argVars).reverse
    let Γ := (argNames.zip (s.args.map Prod.snd)).foldl (fun ctx (name, ty) => ctx.extend name ty) TinyML.TyCtx.empty
    let (retTy, se) ← compile S' B Γ body
    if retTy.sub s.retTy then pure ()
    else VerifM.fatal s!"checkSpec: return type mismatch"
    pure se

theorem checkSpec_correct (S : SpecMap) (e : TinyML.Expr) (s : Spec)
    (γ : TinyML.Subst)
    (hswf : s.wfIn []) (hSwf : S.wfIn [])
    (hS : S.satisfiedBy γ)
    (st : TransState) (ρ : Env) :
    VerifM.eval (checkSpec S e s) st ρ (fun _ _ _ => True) →
    wp (e.subst γ) (fun v => s.isPrecondFor v) := by
  intro heval
  cases e with
  | fix fb argBinders retTy body =>
    simp only [checkSpec] at heval
    -- Case split on extractArgNames result
    cases hext : extractArgNames argBinders s.args with
    | error msg =>
      simp [hext] at heval
      exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
    | ok argNames =>
      simp [hext] at heval
      have hbody := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ heval)
      dsimp only at hbody
      set bs := argBinders.map Prod.fst
      let γ' := (γ.remove' fb).removeAll' bs
      set fval := TinyML.Val.fix fb argBinders retTy (body.subst γ')
      set S' : SpecMap := SpecMap.eraseAll argNames (S.insert' fb s)
      simp only [TinyML.Expr.subst]
      apply wp.func
      intro vs htyped Φ happly
      set Φ_inv : (TinyML.Val → Prop) → List TinyML.Val → Prop := fun P vs =>
        TinyML.ValsHaveTypes vs (s.args.map Prod.snd) ∧
          PredTrans.apply (fun r => TinyML.ValHasType r s.retTy → P r) s.pred
            (Spec.argsEnv Env.empty s.args vs)
      suffices ∀ vs P, Φ_inv P vs → wp (TinyML.Expr.app (.val fval) (vs.map TinyML.Expr.val)) P from
        this vs Φ ⟨htyped, happly⟩
      exact wp.fix' (body.subst γ') Φ_inv (fun ih_rec vs P ⟨htyped_args, happly_args⟩ => by
        -- Rewrite the double substitution into a single one
        obtain ⟨hlen1, hlen2, hbs_eq⟩ := extractArgNames_spec hext
        have hlen_nv0 : argNames.length = vs.length := by
          have := htyped_args.length_eq; simp at this; omega
        have hlen : bs.length = vs.length := by simp [bs, hbs_eq]; omega
        rw [TinyML.Expr.subst_fix_comp body fb bs γ fval vs hlen]
        set γ_body := γ.update' fb fval |>.updateAll' bs vs
        -- Use implement_correct to get into the body
        apply Spec.implement_correct s _ _ _ vs _ (wp (body.subst γ_body) P) hswf htyped_args hbody happly_args
        intro argVars st' ρ' hargVars_mem hargVars_sort hargVars_lookup hbody_eval
        -- Key facts about fval and the spec map
        have isPrecond : s.isPrecondFor fval := by
          intro vs' htyped' Φ' happly'
          exact ih_rec vs' Φ' ⟨htyped', happly'⟩
        have hS'wf : S'.wfIn [] :=
          SpecMap.wfIn_eraseAll (SpecMap.wfIn_insert' hSwf hswf)
        have hS'_sat : S'.satisfiedBy γ_body := by
          intro y s' hlookup
          -- y is in S' = eraseAll argNames (insert' S fb s)
          -- so y ∉ argNames (erased) and y is in insert' S fb s
          -- Since y ∉ argNames and bs = argNames.map .named, updateAll' doesn't touch y
          have hy_notin : y ∉ argNames := by
            intro hmem
            have := SpecMap.eraseAll_lookup_none hmem (S := S.insert' fb s)
            rw [this] at hlookup; exact absurd hlookup (by simp)
          have hlen_nv : argNames.length = vs.length := by
            have := htyped_args.length_eq; simp at this; omega
          have hγ_body_y : γ_body y = (γ.update' fb fval) y := by
            show ((γ.update' fb fval).updateAll' bs vs) y = _
            simp only [bs, hbs_eq]
            rw [TinyML.Subst.updateAll'_eq _ _ _ _ (by simp; omega)]
            rw [findVal_none_of_not_mem argNames vs y (by omega) hy_notin]
          -- Now case split on whether y = fb name
          have hlookup' : (S.insert' fb s).lookup y = some s' := by
            rwa [← SpecMap.eraseAll_lookup_of_notin hy_notin]
          cases hfb : fb with
          | none =>
            simp [SpecMap.insert', hfb] at hlookup'
            obtain ⟨f, hγf, hprecond⟩ := hS y s' hlookup'
            refine ⟨f, ?_, hprecond⟩
            rw [hγ_body_y]; simp [TinyML.Subst.update', hfb, hγf]
          | named fx =>
            simp only [SpecMap.insert', hfb] at hlookup'
            by_cases hyfx : y = fx
            · subst hyfx
              rw [Finmap.lookup_insert] at hlookup'; simp at hlookup'; subst hlookup'
              refine ⟨fval, ?_, isPrecond⟩
              rw [hγ_body_y]; simp [TinyML.Subst.update', hfb, TinyML.Subst.update_eq]
            · rw [Finmap.lookup_insert_of_ne _ hyfx] at hlookup'
              obtain ⟨f, hγf, hprecond⟩ := hS y s' hlookup'
              refine ⟨f, ?_, hprecond⟩
              rw [hγ_body_y]
              simp [TinyML.Subst.update', hfb, TinyML.Subst.update_eq, beq_false_of_ne hyfx, hγf]
        set Γ := (argNames.zip (s.args.map Prod.snd)).foldl (fun ctx (x : String × TinyML.Type_) => ctx.extend x.1 x.2) TinyML.TyCtx.empty
        set B : Bindings := (argNames.zip argVars).reverse
        have hlen_avs : argNames.length = argVars.length := by
          have := hargVars_lookup.length_eq
          have := htyped_args.length_eq; simp at this; omega
        have hlen_vals : argNames.length = vs.length := by
          have := htyped_args.length_eq; simp at this; omega
        have hagree : Bindings.agreeOnLinked B ρ' γ_body := by
          show Bindings.agreeOnLinked (argNames.zip argVars).reverse ρ'
            ((γ.update' fb fval).updateAll' bs vs)
          simp only [bs, hbs_eq]
          exact agreeOnLinked_zip_reverse argNames argVars vs
            (γ.update' fb fval) ρ' hlen_avs hlen_vals
            hargVars_sort hargVars_lookup
        have hbwf : Bindings.wf B st'.decls := by
          intro ⟨n, v⟩ hp
          apply hargVars_mem v
          have hmem : (n, v) ∈ (argNames.zip argVars) := List.mem_reverse.mp hp
          exact List.of_mem_zip hmem |>.2
        have hts : Bindings.typedSubst B Γ γ_body := by
          apply typedSubst_of_agreeOnLinked hagree
          intro x x' t hmem hΓ
          show TinyML.ValHasType (ρ'.lookup .value x'.name) t
          set args' := argNames.zip (s.args.map Prod.snd)
          have hfst : args'.map Prod.fst = argNames := by
            simp [args']; exact List.map_fst_zip (by simp; omega)
          have hsnd : args'.map Prod.snd = s.args.map Prod.snd := by
            simp [args']; exact List.map_snd_zip (by simp; omega)
          exact val_typed_of_last_wins args' argVars vs ρ' TinyML.TyCtx.empty x x' t
            (by rw [hfst]; exact hlen_avs)
            (by rw [hfst]; exact hlen_vals)
            (by rw [hfst]; exact hmem)
            hΓ hargVars_lookup
            (by rw [hsnd]; exact htyped_args)
        have hcompile := VerifM.eval_bind _ _ _ _ hbody_eval
        apply compile_correct body S' B Γ st' ρ' γ_body _ P
          hcompile hagree hbwf hts hS'_sat hS'wf
        intro result ρ'' st'' retTy' se hΨ hse_wf hse_eval htyped_result
        by_cases hsub : retTy'.sub s.retTy
        · simp [hsub] at hΨ
          have hret := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ hΨ)
          have hret' := VerifM.eval_ret hret
          rw [hse_eval] at hret'
          exact hret' hse_wf (TinyML.ValHasType_sub htyped_result (TinyML.Type_.sub_iff.mp hsub))
        · simp [hsub] at hΨ
          exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ hΨ)).elim)
  | _ =>
    simp only [checkSpec] at heval
    exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim

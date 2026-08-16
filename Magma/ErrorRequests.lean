import Magma.FactorizationEqv

/-!
# Errors as Requests: the Certified Error-Payload Rung

Stratum 3 of the error-payload design (`MACHINE.md` §10; strata 1–2
live in the `kamea-machine` host). The certified machine's six error
arms all cut to the accept absorber — `.ret (.elem 0) σ k` — which is
fail-open, informationless, and invisible in the value. The host's
stratum 1 observes those transitions out-of-band; its stratum 2
rebuilds them as raisable, resumable conditions. This file certifies
the reading both strata rely on, touching nothing: `step` and every
existing theorem (the adequacy tower included) are as they were.

* **The request semantics** `stepE`: identical to `step` except the
  six error arms are *terminal*, yielding a `Request` — kind, culprit,
  store, and the continuation at the error site (the restart payload).
  No new table elements, no new core forms: a request is data about
  the machine, not an extension of it.
* **The factorization theorem** `step_factorizes`: the certified
  machine IS the request semantics composed with the fixed policy
  "resume the carried continuation with the accept absorber"
  (`resume0`). The fail-open default is not primitive — it is one
  policy choice, applied pointwise at each request. The host's
  restarts (`err-resume`) are the same composition at other values
  (`resume`).
* **Erasure** (`loopT_fst`): the traced loop projects to the certified
  loop — the log is observation, not behavior. This is the theorem
  form of stratum 1's bit-identical claim for `loop_run_traced`.
* **Strict mode, certified** (`strict_iff`, `strict_total`,
  `loopE_request`): the strict machine `loopE` stops at the first
  request — the deny-on-any-error policy of the host's `:strict`.
  It accepts a value iff the certified run computes that value with
  an empty error log (deny is sound *and* complete: what strict
  accepts was computed without any error default; what involved a
  default, strict refuses). Every terminating certified run gets a
  verdict, and a denied run's certified value is exactly the
  resume-with-accept continuation of the reported request.
* The seventh fail-open site, driver-level `eval` of non-code, is
  `evalD_non_code`.
-/

set_option autoImplicit false

namespace Dichotomic
namespace ErrorRequests

open FactorizationEqv

/-- One kind per error arm of `step`, plus the driver-level seventh —
    the exact mirror of the host's `ErrKind`. `evalNonCode` is never
    emitted by `stepE`; it is the decode-boundary denial of `evalE`
    (its in-band default is `evalD_non_code`). -/
inductive ErrKind where
  | applyElemNonElem
  | applyNonApplicable
  | derefNonLoc
  | setNonLoc
  | carNonPair
  | cdrNonPair
  | evalNonCode
deriving DecidableEq, Repr

/-- A terminal error request: which arm fired, on what value, with
    the store and the continuation at the error site — the restart
    payload the host's stratum 2 exposes as `err-resume`. -/
structure Request where
  kind    : ErrKind
  culprit : Val
  store   : Store
  kont    : Kont

/-- The request semantics: `step` with the six error arms terminal.
    Every non-error arm is verbatim `step`; the arm order mirrors
    `step` exactly so the overlapping patterns discriminate
    identically. -/
def stepE : State → State ⊕ (Val ⊕ Request)
  | .eval (.atom a) _ σ k => .inl (.ret (.elem a) σ k)
  | .eval (.var n) ρ σ k => .inl (.ret (ρ.getD n (.elem 0)) σ k)
  | .eval (.lam b) ρ σ k => .inl (.ret (.clos b ρ) σ k)
  | .eval (.app f x) ρ σ k => .inl (.eval f ρ σ (.appL x ρ k))
  | .eval (.callcc b) ρ σ k => .inl (.eval b (.cont k :: ρ) σ k)
  | .eval (.ref e) ρ σ k => .inl (.eval e ρ σ (.refK k))
  | .eval (.deref e) ρ σ k => .inl (.eval e ρ σ (.derefK k))
  | .eval (.setref l e) ρ σ k => .inl (.eval l ρ σ (.setL e ρ k))
  | .eval (.cons a b) ρ σ k => .inl (.eval a ρ σ (.consL b ρ k))
  | .eval (.car e) ρ σ k => .inl (.eval e ρ σ (.carK k))
  | .eval (.cdr e) ρ σ k => .inl (.eval e ρ σ (.cdrK k))
  | .eval (.pairp e) ρ σ k => .inl (.eval e ρ σ (.pairK k))
  | .eval (.ite c t e) ρ σ k => .inl (.eval c ρ σ (.iteK t e ρ k))
  | .eval (.eqv a b) ρ σ k => .inl (.eval a ρ σ (.eqvL b ρ k))
  | .ret v _ .halt => .inr (.inl v)
  | .ret v σ (.appL x ρ k) => .inl (.eval x ρ σ (.appR v k))
  | .ret v σ (.appR (.clos b ρ') k) => .inl (.eval b (v :: ρ') σ k)
  | .ret v σ (.appR (.cont k') _) => .inl (.ret v σ k')
  | .ret (.elem b) σ (.appR (.elem a) k) => .inl (.ret (.elem (dotA8 a b)) σ k)
  | .ret v σ (.appR (.elem _) k) => .inr (.inr ⟨.applyElemNonElem, v, σ, k⟩)
  | .ret _ σ (.appR f k) => .inr (.inr ⟨.applyNonApplicable, f, σ, k⟩)
  | .ret v σ (.refK k) => .inl (.ret (.loc σ.length) (σ ++ [v]) k)
  | .ret (.loc n) σ (.derefK k) => .inl (.ret (σ.getD n (.elem 0)) σ k)
  | .ret v σ (.derefK k) => .inr (.inr ⟨.derefNonLoc, v, σ, k⟩)
  | .ret v σ (.setL e ρ k) => .inl (.eval e ρ σ (.setR v k))
  | .ret w σ (.setR (.loc n) k) => .inl (.ret w (σ.set n w) k)
  | .ret _ σ (.setR t k) => .inr (.inr ⟨.setNonLoc, t, σ, k⟩)
  | .ret v σ (.consL b ρ k) => .inl (.eval b ρ σ (.consR v k))
  | .ret w σ (.consR v k) => .inl (.ret (.cell v w) σ k)
  | .ret (.cell u _) σ (.carK k) => .inl (.ret u σ k)
  | .ret v σ (.carK k) => .inr (.inr ⟨.carNonPair, v, σ, k⟩)
  | .ret (.cell _ w) σ (.cdrK k) => .inl (.ret w σ k)
  | .ret v σ (.cdrK k) => .inr (.inr ⟨.cdrNonPair, v, σ, k⟩)
  | .ret (.cell _ _) σ (.pairK k) => .inl (.ret (.elem 0) σ k)
  | .ret _ σ (.pairK k) => .inl (.ret (.elem 1) σ k)
  | .ret (.elem b) σ (.iteK t e ρ k) =>
    .inl (.eval (if b = 1 then e else t) ρ σ k)
  | .ret _ σ (.iteK t _ ρ k) => .inl (.eval t ρ σ k)
  | .ret v σ (.eqvL b ρ k) => .inl (.eval b ρ σ (.eqvR v k))
  | .ret w σ (.eqvR v k) => .inl (.ret (eqvVal v w) σ k)

/-- Resuming a request with a substitute value: continue the carried
    continuation — the restart of the host's stratum 2. -/
def resume (w : Val) (r : Request) : State := .ret w r.store r.kont

/-- The fixed policy the certified machine bakes in: resume with the
    accept absorber. -/
def resume0 (r : Request) : State := resume (.elem 0) r

/-- **The factorization theorem**: the certified machine is the
    request semantics composed with the resume-with-accept policy.
    The fail-open default is one policy choice, not the semantics. -/
theorem step_factorizes (s : State) :
    step s = match stepE s with
      | .inl s' => .inl s'
      | .inr (.inl v) => .inr v
      | .inr (.inr r) => .inl (resume0 r) := by
  cases s with
  | eval p ρ σ k => cases p <;> rfl
  | ret v σ k =>
    cases k with
    | halt => rfl
    | appL x ρ k => rfl
    | appR f k => cases f <;> cases v <;> rfl
    | refK k => rfl
    | derefK k => cases v <;> rfl
    | setL e ρ k => rfl
    | setR t k => cases t <;> rfl
    | consL b ρ k => rfl
    | consR u k => rfl
    | carK k => cases v <;> rfl
    | cdrK k => cases v <;> rfl
    | pairK k => cases v <;> rfl
    | iteK t e ρ k => cases v <;> rfl
    | eqvL b ρ k => rfl
    | eqvR u k => rfl

/-- A logged event: which arm fired, on what value (the Lean mirror of
    the host's `ErrEvent`; the host adds a step index). -/
abbrev ErrEvent := ErrKind × Val

/-- The observation `step` discards: the event this state's step
    fires, if any. -/
def errEvent? (s : State) : Option ErrEvent :=
  match stepE s with
  | .inr (.inr r) => some (r.kind, r.culprit)
  | _ => none

/-- The traced loop: the certified loop carrying the error log beside
    it — the Lean mirror of the host's `loop_run_traced`. -/
def loopT : Nat → State → List ErrEvent → Option (Val × List ErrEvent)
  | 0, _, _ => none
  | fuel + 1, s, acc =>
    match step s with
    | .inl s' => loopT fuel s' (acc ++ (errEvent? s).toList)
    | .inr v => some (v, acc ++ (errEvent? s).toList)

/-- **Erasure**: the trace is observation, not behavior — projecting
    the log away recovers the certified loop exactly (the theorem form
    of stratum 1's bit-identical claim). -/
theorem loopT_fst (n : Nat) (s : State) (acc : List ErrEvent) :
    (loopT n s acc).map Prod.fst = loop n s := by
  induction n generalizing s acc with
  | zero => rfl
  | succ m ih =>
    unfold loopT loop
    cases h : step s with
    | inl s' => simpa using ih s' (acc ++ (errEvent? s).toList)
    | inr v => rfl

/-- The log only grows: whatever a traced run returns extends the
    accumulator it started from. -/
theorem loopT_prefix (n : Nat) (s : State) (acc : List ErrEvent)
    {v : Val} {es : List ErrEvent} (h : loopT n s acc = some (v, es)) :
    ∃ tail, es = acc ++ tail := by
  induction n generalizing s acc with
  | zero => simp [loopT] at h
  | succ m ih =>
    unfold loopT at h
    cases hs : step s with
    | inl s' =>
      rw [hs] at h
      obtain ⟨tail, ht⟩ := ih s' (acc ++ (errEvent? s).toList) h
      exact ⟨(errEvent? s).toList ++ tail, by simp [ht]⟩
    | inr w =>
      rw [hs] at h
      obtain ⟨-, he⟩ := Prod.mk.injEq .. ▸ Option.some.injEq .. ▸ h
      exact ⟨(errEvent? s).toList, he.symm⟩

/-- The strict machine: run the request semantics and stop at the
    first request — the certified deny-on-any-error policy of the
    host's `:strict`. -/
def loopE : Nat → State → Option (Val ⊕ Request)
  | 0, _ => none
  | fuel + 1, s =>
    match stepE s with
    | .inl s' => loopE fuel s'
    | .inr r => some r

/-! Unfolding equations at successor fuel, stated once so the run
theorems can rewrite instead of unfolding. -/

theorem loop_succ (m : Nat) (s : State) :
    loop (m + 1) s = match step s with
      | .inl s' => loop m s'
      | .inr v => some v := rfl

theorem loopT_succ (m : Nat) (s : State) (acc : List ErrEvent) :
    loopT (m + 1) s acc = match step s with
      | .inl s' => loopT m s' (acc ++ (errEvent? s).toList)
      | .inr v => some (v, acc ++ (errEvent? s).toList) := rfl

theorem loopE_succ (m : Nat) (s : State) :
    loopE (m + 1) s = match stepE s with
      | .inl s' => loopE m s'
      | .inr r => some r := rfl

/-- **Strict mode is sound and complete**: the strict machine accepts
    a value iff the certified traced run computes that value with an
    empty error log. What strict accepts was computed without any
    error default; what involved a default, strict refuses. -/
theorem strict_iff (n : Nat) (s : State) (v : Val) :
    loopE n s = some (.inl v) ↔ loopT n s [] = some (v, []) := by
  induction n generalizing s with
  | zero => simp [loopE, loopT]
  | succ m ih =>
    have hfac := step_factorizes s
    rw [loopE_succ, loopT_succ]
    cases hE : stepE s with
    | inl s' =>
      simp only [hE] at hfac
      have hev : errEvent? s = none := by unfold errEvent?; rw [hE]
      simp only [hfac, hev]
      simpa using ih s'
    | inr r =>
      cases r with
      | inl w =>
        simp only [hE] at hfac
        have hev : errEvent? s = none := by unfold errEvent?; rw [hE]
        simp only [hfac, hev]
        simp
      | inr req =>
        simp only [hE] at hfac
        have hev : errEvent? s = some (req.kind, req.culprit) := by
          unfold errEvent?; rw [hE]
        simp only [hfac, hev]
        constructor
        · intro h; simp at h
        · intro h
          exfalso
          have hes : ∃ es, loopT m (resume0 req)
              ([] ++ (some (req.kind, req.culprit)).toList) = some (v, es) ∧
              es = [] := ⟨[], h, rfl⟩
          obtain ⟨es, hrun, hnil⟩ := hes
          obtain ⟨tail, ht⟩ := loopT_prefix m (resume0 req)
            ([] ++ (some (req.kind, req.culprit)).toList) hrun
          rw [hnil] at ht
          simp at ht

/-- Every terminating certified run gets a strict verdict: accepted
    with its value, or denied at a request — there is no third
    outcome. -/
theorem strict_total (n : Nat) (s : State) (v : Val)
    (h : loop n s = some v) :
    loopE n s = some (.inl v) ∨ ∃ r, loopE n s = some (.inr r) := by
  induction n generalizing s with
  | zero => simp [loop] at h
  | succ m ih =>
    have hfac := step_factorizes s
    rw [loop_succ] at h
    rw [loopE_succ]
    cases hE : stepE s with
    | inl s' =>
      simp only [hE] at hfac
      simp only [hfac] at h
      exact ih s' h
    | inr r =>
      cases r with
      | inl w =>
        simp only [hE] at hfac
        simp only [hfac, Option.some.injEq] at h
        simp only [h]
        exact Or.inl trivial
      | inr req => exact Or.inr ⟨req, rfl⟩

/-- **The run-level factorization**: when strict mode denies at a
    request, the certified machine's run is exactly the run continued
    from the resume-with-accept of that request — the fail-open value
    is the denied request plus the baked-in policy. -/
theorem loopE_request (n : Nat) (s : State) (r : Request)
    (h : loopE n s = some (.inr r)) :
    ∃ j, j < n ∧ loop n s = loop j (resume0 r) := by
  induction n generalizing s with
  | zero => simp [loopE] at h
  | succ m ih =>
    have hfac := step_factorizes s
    rw [loopE_succ] at h
    cases hE : stepE s with
    | inl s' =>
      simp only [hE] at hfac h
      obtain ⟨j, hj, hloop⟩ := ih s' h
      refine ⟨j, Nat.lt_succ_of_lt hj, ?_⟩
      rw [loop_succ]
      simp only [hfac]
      exact hloop
    | inr req =>
      simp only [hE] at hfac h
      cases req with
      | inl w => simp at h
      | inr req =>
        rw [Option.some.injEq, Sum.inr.injEq] at h
        subst h
        refine ⟨m, Nat.lt_succ_self m, ?_⟩
        rw [loop_succ]
        simp only [hfac]

/-! ## The six arms, characterized

One lemma per error arm: the exact side condition under which `stepE`
answers a request, with the culprit the host logs. -/

theorem stepE_apply_elem_nonelem (a : Fin 8) (v : Val) (σ : Store)
    (k : Kont) (h : ∀ b, v ≠ .elem b) :
    stepE (.ret v σ (.appR (.elem a) k)) =
      .inr (.inr ⟨.applyElemNonElem, v, σ, k⟩) := by
  cases v with
  | elem b => exact absurd rfl (h b)
  | _ => rfl

theorem stepE_apply_cell (u w v : Val) (σ : Store) (k : Kont) :
    stepE (.ret v σ (.appR (.cell u w) k)) =
      .inr (.inr ⟨.applyNonApplicable, .cell u w, σ, k⟩) := rfl

theorem stepE_apply_loc (n : Nat) (v : Val) (σ : Store) (k : Kont) :
    stepE (.ret v σ (.appR (.loc n) k)) =
      .inr (.inr ⟨.applyNonApplicable, .loc n, σ, k⟩) := rfl

theorem stepE_deref (v : Val) (σ : Store) (k : Kont)
    (h : ∀ n, v ≠ .loc n) :
    stepE (.ret v σ (.derefK k)) = .inr (.inr ⟨.derefNonLoc, v, σ, k⟩) := by
  cases v with
  | loc n => exact absurd rfl (h n)
  | _ => rfl

theorem stepE_setref (w t : Val) (σ : Store) (k : Kont)
    (h : ∀ n, t ≠ .loc n) :
    stepE (.ret w σ (.setR t k)) = .inr (.inr ⟨.setNonLoc, t, σ, k⟩) := by
  cases t with
  | loc n => exact absurd rfl (h n)
  | _ => rfl

theorem stepE_car (v : Val) (σ : Store) (k : Kont)
    (h : ∀ u w, v ≠ .cell u w) :
    stepE (.ret v σ (.carK k)) = .inr (.inr ⟨.carNonPair, v, σ, k⟩) := by
  cases v with
  | cell u w => exact absurd rfl (h u w)
  | _ => rfl

theorem stepE_cdr (v : Val) (σ : Store) (k : Kont)
    (h : ∀ u w, v ≠ .cell u w) :
    stepE (.ret v σ (.cdrK k)) = .inr (.inr ⟨.cdrNonPair, v, σ, k⟩) := by
  cases v with
  | cell u w => exact absurd rfl (h u w)
  | _ => rfl

/-- The seventh fail-open site, driver-level: user `eval` of a value
    that decodes to no program answers the accept absorber in-band —
    the site `kamea-driver::eval_traced` observes as `EvalNonCode`. -/
theorem evalD_non_code (fuel : Nat) (ρ : Env) (σ : Store) (v : Val)
    (h : decodeD v = none) : evalD fuel ρ σ v = some (.elem 0) := by
  unfold evalD; rw [h]

/-! ## Strict eval: the verdict at the decode boundary

Untrusted code enters the system as a quotation handed to `eval`.
That boundary — not a probe through the interpreter, which adequacy
makes provably blind — is where the strict verdict belongs. -/

/-- Strict user-level eval: decode + the strict machine. A non-code
    value is denied as an `evalNonCode` request at the halt
    continuation. Host mirror: `kamea-driver::eval_strict`. -/
def evalE (fuel : Nat) (ρ : Env) (σ : Store) (v : Val) :
    Option (Val ⊕ Request) :=
  match decodeD v with
  | some p => loopE fuel (.eval p ρ σ .halt)
  | none => some (.inr ⟨.evalNonCode, v, σ, .halt⟩)

/-- **Strict eval is conservative**: what it accepts, the certified
    user-level eval computes — with the same value. -/
theorem strict_evalD (fuel : Nat) (ρ : Env) (σ : Store) (v w : Val)
    (h : evalE fuel ρ σ v = some (.inl w)) : evalD fuel ρ σ v = some w := by
  unfold evalE at h
  unfold evalD
  cases hd : decodeD v with
  | none => rw [hd] at h; simp at h
  | some p =>
    rw [hd] at h
    have hT := (strict_iff fuel (.eval p ρ σ .halt) w).mp h
    have hrun := loopT_fst fuel (.eval p ρ σ .halt) []
    rw [hT] at hrun
    exact hrun.symm

/-- The seventh site factorizes too: denying eval-of-non-code and
    resuming with the accept absorber is exactly `evalD`'s in-band
    default. -/
theorem evalE_non_code_factorizes (fuel : Nat) (ρ : Env) (σ : Store)
    (v : Val) (h : decodeD v = none) :
    evalE fuel ρ σ v = some (.inr ⟨.evalNonCode, v, σ, .halt⟩) ∧
    ∀ f, loop (f + 1) (resume0 ⟨.evalNonCode, v, σ, .halt⟩) =
      evalD fuel ρ σ v := by
  refine ⟨by unfold evalE; rw [h], fun f => ?_⟩
  rw [evalD_non_code fuel ρ σ v h]
  rfl

end ErrorRequests
end Dichotomic

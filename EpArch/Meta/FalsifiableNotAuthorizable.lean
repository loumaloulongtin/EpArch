/-
EpArch.Meta.FalsifiableNotAuthorizable — Meta-Status Proof Pack

Packages three meta-level claims about the theory itself:
- (P1) Falsifiable: coherent countercontexts exist
- (P2) Not fully authorizable from observations: underdetermination exists (credit required)
- (P3) Safe on credit: extension-safety prevents collapse

Builds on existing machinery from WorldCtx, WorldWitness, and RevisionSafety — no new axioms.

Note: P2 is an epistemic claim, not a provability claim. "Not fully authorizable from
observational surfaces" means observations underdetermine truth in the intended model;
it does not mean proofs cannot exist or that the theory is inconsistent.
-/

import EpArch.WorldCtx
import EpArch.WorldWitness
import EpArch.Semantics.RevisionSafety
import EpArch.Basic

namespace EpArch.Meta

open EpArch

/-! ## 1. Theory Floor Definition -/

/-- The theory floor package: the W-bundles are inhabitable.

    A WorldCtx satisfies the theory floor if all three core assumption
    bundles have inhabitants. This is NOT a claim about reality; it's
    a specification of the epistemological constraints the theory assumes. -/
def TheoryFloor (C : WorldCtx) : Prop :=
  Nonempty C.W_lies_possible ∧
  Nonempty C.W_bounded_verification ∧
  Nonempty C.W_partial_observability


/-! ## 2. Trivial Context (Counterexample for Falsifiability) -/

/-- A trivial WorldCtx where all bundles fail.

    This context has:
    - World, Agent, Claim, Obs all Unit
    - Truth always True (no false propositions)
    - Utter always True
    - VerifyWithin always True (no verification cost)
    - obs constant

    This makes W_lies_possible, W_bounded_verification, and
    W_partial_observability all fail. -/
def TrivialCtx : WorldCtx where
  World := Unit
  Agent := Unit
  Claim := Unit
  Obs := Unit

  Truth := fun _ _ => True
  Utter := fun _ _ => True
  obs := fun _ => ()
  VerifyWithin := fun _ _ _ => True
  effectiveTime := fun _ => 0

  world_inhabited := ⟨()⟩
  agent_inhabited := ⟨()⟩
  claim_inhabited := ⟨()⟩


/-! ## 3. Pillar 1: Satisfiable Witness + Falsifiability -/

/-- The theory floor is satisfiable: WitnessCtx is a concrete witness.

    This proves non-vacuity in the positive direction: the floor
    package is consistent, not contradictory. -/
theorem theory_floor_satisfiable : TheoryFloor WorldWitness.WitnessCtx :=
  ⟨⟨WorldWitness.holds_W_lies_possible⟩,
   ⟨WorldWitness.holds_W_bounded_verification⟩,
   ⟨WorldWitness.holds_W_partial_observability⟩⟩

/-- W_lies_possible fails in TrivialCtx.

    Proof: W_lies_possible requires ∃ w P, ¬Truth w P.
    But in TrivialCtx, Truth w P = True for all w, P.
    Contradiction. -/
theorem trivial_fails_lies_possible : ¬ Nonempty TrivialCtx.W_lies_possible := by
  intro ⟨h⟩
  have ⟨_, _, h_false⟩ := h.some_false
  -- h_false : ¬ TrivialCtx.Truth w P = ¬ True = False
  exact h_false trivial

/-- In TrivialCtx, no lie is constructible: the kernel discriminator is a no-op.

    TrivialCtx.Truth = fun _ _ => True, so every uttered claim is vacuously true.
    This is the formal statement of "we would not need Lean if lies were impossible":
    in a world where all claims are true, there is nothing to reject. -/
theorem trivial_has_no_lies : ¬∃ w a P, TrivialCtx.Lie w a P :=
  WorldCtx.kernel_redundant_without_lies TrivialCtx (fun _ _ => trivial)

/-- W_bounded_verification fails in TrivialCtx.

    Proof: W_bounded_verification requires ∃ P k, k > 0 ∧ ∀ w, RequiresSteps w P k.
    RequiresSteps w P k = ∀ t, t < k → ¬VerifyWithin w P t.
    But in TrivialCtx, VerifyWithin w P t = True for all w, P, t.
    So for k > 0 and t = 0 < k, we need ¬True, contradiction. -/
theorem trivial_fails_bounded_verification : ¬ Nonempty TrivialCtx.W_bounded_verification := by
  intro ⟨h⟩
  have ⟨P, k, h_pos, h_requires⟩ := h.verification_has_cost
  -- h_requires : ∀ w, TrivialCtx.RequiresSteps w P k
  -- Get any world
  have ⟨w⟩ := TrivialCtx.world_inhabited
  -- h_requires w : ∀ t, t < k → ¬ TrivialCtx.VerifyWithin w P t
  -- Since k > 0, we have 0 < k
  have h_zero_lt : 0 < k := h_pos
  -- So h_requires w 0 h_zero_lt : ¬ TrivialCtx.VerifyWithin w P 0
  have h_neg : ¬ TrivialCtx.VerifyWithin w P 0 := h_requires w 0 h_zero_lt
  -- But TrivialCtx.VerifyWithin w P 0 = True
  exact h_neg trivial

/-- W_partial_observability fails in TrivialCtx.

    Proof: W_partial_observability requires ∃ P, NotDeterminedByObs P.
    NotDeterminedByObs P = ∃ w0 w1, PartialObs w0 w1 ∧ (Truth w0 P ↔ ¬Truth w1 P).
    In TrivialCtx, Truth w P = True for all w, P.
    So we need True ↔ ¬True, which is False. -/
theorem trivial_fails_partial_observability : ¬ Nonempty TrivialCtx.W_partial_observability := by
  intro ⟨h⟩
  have ⟨P, w0, w1, _, h_diff⟩ := h.obs_underdetermines
  -- h_diff : TrivialCtx.Truth w0 P ↔ ¬TrivialCtx.Truth w1 P
  -- = True ↔ ¬True = True ↔ False
  have h_true : TrivialCtx.Truth w0 P := trivial
  have h_neg : ¬TrivialCtx.Truth w1 P := h_diff.mp h_true
  exact h_neg trivial

/-- The theory floor is falsifiable: there exists a coherent context where it fails.

    This is the counterexample direction: we can construct a coherent
    WorldCtx that does NOT satisfy the floor. This means the floor
    is a genuine constraint, not a tautology. -/
theorem theory_floor_falsifiable : ∃ C : @WorldCtx.{0}, ¬ TheoryFloor C :=
  ⟨TrivialCtx, fun ⟨h_lies, _, _⟩ => trivial_fails_lies_possible h_lies⟩


/-! ## 4. Pillar 2: Not Fully Authorizable (Underdetermination) -/

/-- Full authorizability from observations: all claims are determined by obs.

    A context is fully authorizable from observations if, for every claim P,
    observationally equivalent worlds agree on P's truth. -/
def FullyAuthorizableByObs (C : WorldCtx) : Prop :=
  ∀ P : C.Claim, ∀ w0 w1 : C.World, C.PartialObs w0 w1 → (C.Truth w0 P ↔ C.Truth w1 P)

/-- Credit required: not all claims are determined by observations.

    This is the negation of full authorizability: there exists at least
    one claim that observations alone cannot determine. -/
def CreditRequired (C : WorldCtx) : Prop :=
  ∃ P : C.Claim, C.NotDeterminedByObs P

/-- Canonical underdetermined claim extraction from W_partial_observability.

    Given a proof that W_partial_observability holds, extract a canonical
    claim that is not determined by observations. -/
noncomputable def UnderDeterminedClaim (C : WorldCtx) (h : C.W_partial_observability) : C.Claim :=
  Classical.choose h.obs_underdetermines

/-- The extracted claim is indeed underdetermined. -/
theorem underDeterminedClaim_spec (C : WorldCtx) (h : C.W_partial_observability) :
    C.NotDeterminedByObs (UnderDeterminedClaim C h) :=
  Classical.choose_spec h.obs_underdetermines

/-- The theory floor implies credit is required (not fully authorizable from obs).

    Any context satisfying the floor has at least one underdetermined claim,
    so observation alone cannot fully authorize all claims. -/
theorem theory_floor_not_fully_authorizable (C : WorldCtx) :
    TheoryFloor C → CreditRequired C := by
  intro ⟨_, _, h_partial⟩
  have ⟨h⟩ := h_partial
  exact h.obs_underdetermines

/-- The witness context requires credit (specialized form).
    Instance of `theory_floor_not_fully_authorizable`. -/
theorem witness_requires_credit : CreditRequired WorldWitness.WitnessCtx :=
  theory_floor_not_fully_authorizable WorldWitness.WitnessCtx theory_floor_satisfiable

/-- Bridge lemma: credit required implies NOT fully authorizable from observations.

    From `CreditRequired` (∃ underdetermined claim) derive `¬ FullyAuthorizableByObs`.

    Proof: Assume both. CreditRequired gives P with w0, w1 where PartialObs w0 w1
    and (Truth w0 P ↔ ¬Truth w1 P). FullyAuthorizableByObs gives (Truth w0 P ↔ Truth w1 P).
    Composing: Truth w1 P ↔ ¬Truth w1 P, contradiction. -/
theorem credit_required_implies_not_fully_authorizable (C : WorldCtx) :
    CreditRequired C → ¬ FullyAuthorizableByObs C := by
  intro ⟨P, w0, w1, h_obs, h_diff⟩ h_auth
  -- h_auth gives us (Truth w0 P ↔ Truth w1 P)
  have h_same : C.Truth w0 P ↔ C.Truth w1 P := h_auth P w0 w1 h_obs
  -- h_diff gives us (Truth w0 P ↔ ¬Truth w1 P)
  -- Combining: Truth w1 P ↔ ¬Truth w1 P
  have h_contra : C.Truth w1 P ↔ ¬C.Truth w1 P := by
    constructor
    · intro h1
      -- h1 : Truth w1 P
      -- Need: ¬Truth w1 P
      -- From h_same.mpr h1 : Truth w0 P
      -- From h_diff.mp (h_same.mpr h1) : ¬Truth w1 P
      exact h_diff.mp (h_same.mpr h1)
    · intro h1
      -- h1 : ¬Truth w1 P
      -- Need: Truth w1 P
      -- From h_diff.mpr h1 : Truth w0 P (since h_diff: Truth w0 P ↔ ¬Truth w1 P)
      -- h_diff : Truth w0 P ↔ ¬Truth w1 P
      -- So h_diff.mpr h1 gives Truth w0 P
      have h0 : C.Truth w0 P := h_diff.mpr h1
      -- h_same.mp h0 gives Truth w1 P
      exact h_same.mp h0
  -- This is a contradiction: p ↔ ¬p
  cases Classical.em (C.Truth w1 P) with
  | inl h => exact h_contra.mp h h
  | inr h => exact h (h_contra.mpr h)

/-- Direct bridge: theory floor implies NOT fully authorizable from observations.

    Combines `theory_floor_not_fully_authorizable` with the bridge lemma for
    a clean one-step derivation. -/
theorem theory_floor_implies_not_fully_authorizable (C : WorldCtx) :
    TheoryFloor C → ¬ FullyAuthorizableByObs C :=
  fun h => credit_required_implies_not_fully_authorizable C (theory_floor_not_fully_authorizable C h)

/-- The witness context is NOT fully authorizable from observations.
    Instance of `theory_floor_implies_not_fully_authorizable`. -/
theorem witness_not_fully_authorizable : ¬ FullyAuthorizableByObs WorldWitness.WitnessCtx :=
  theory_floor_implies_not_fully_authorizable WorldWitness.WitnessCtx theory_floor_satisfiable


/-! ## 5. Pillar 3: Safe on Credit (Extension Safety) -/

/-- Safe extensions preserve revision-gate results.

    This is the "non-collapse under incompleteness" pillar: even when
    operating on credit (incomplete information), extending the theory
    doesn't break safety properties. -/
def credit_safe_under_extension := RevisionSafety.safe_extension_preserves


/-! ## 6. Headline Theorem: Meta-Status Proof Pack -/

/-- The meta-status proof pack: headline theorem for meta-level claims.

    This packages all three pillars:
    - P1: The floor is satisfiable AND falsifiable (genuine constraint)
    - P2: The floor implies credit required (not fully authorizable from obs)
    - P3: Safe on credit (extension preserves safety)

    This does not guarantee that the real world is this model, uniqueness, or
    psychological claims. -/
theorem meta_status_proof_pack :
    -- P1a: Satisfiable (positive non-vacuity)
    TheoryFloor WorldWitness.WitnessCtx ∧
    -- P1b: Falsifiable (countercontext exists)
    (∃ C : @WorldCtx.{0}, ¬ TheoryFloor C) ∧
    -- P2: Credit required (not fully authorizable from obs)
    CreditRequired WorldWitness.WitnessCtx ∧
    -- P3: Extension safety
    (∀ (C : RevisionSafety.CoreModel) (R : RevisionSafety.RevisionSafeExtension C),
      RevisionSafety.RevisionGate C → RevisionSafety.RevisionGate (RevisionSafety.forget R.ext)) :=
  ⟨theory_floor_satisfiable,
   theory_floor_falsifiable,
   witness_requires_credit,
   credit_safe_under_extension⟩

end EpArch.Meta

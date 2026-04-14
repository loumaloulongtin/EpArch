/-
EpArch.Meta.TheoryCoreClaim — Optional Stretch: First-Class Theory Core Claim

This module implements the optional stretch goal: encoding "the theory itself"
as a first-class claim symbol `theory_core` that is provably underdetermined
by observations.

## Strategy (Conservative Extension)

We do NOT redesign the semantics of Claims globally. Instead:

1. Build an *extension functor* `AddTheoryCore` that adds one new claim symbol
   to a WorldCtx: `Claim' := Sum C.Claim MetaClaim` where `MetaClaim` has one
   constructor: `theory_core`.

2. Freeze core infrastructure (World, Agent, Obs, obs, effectiveTime);
   extend Utter and VerifyWithin for the new symbol.

3. Interpret the new symbol by *aliasing* it to a pre-existing underdetermined
   base claim `P0`: `Truth w (inr theory_core) := Truth w P0`

Then underdetermination transfers:
- If `C.NotDeterminedByObs P0`, then `AddTheoryCore(C,P0).NotDeterminedByObs (inr theory_core)`

## Design Constraints (enforced by construction)

- **Obs frozen:** PartialObs and NotDeterminedByObs are unchanged; obs function is inherited.
- **No circularity:** Truth for theory_core is defined as Truth for P0, not in terms of meta-predicates.
- **No gerrymandering:** The meta token is definitionally an alias of an already-underdetermined claim.
- **No axioms:** This module adds 0 axioms, 0 sorry.

## Claim Budget

**Buys:**
- A literal "self-token" claim symbol you can point to in prose.
- A crisp theorem: `NotDeterminedByObs theory_core` using the same obs surface.

**Does NOT buy:**
- "The real world satisfies theory_core."
- "The theory is uniquely determined / uniquely correct."
- Psychological claims.

-/

import EpArch.WorldCtx
import EpArch.WorldWitness
import EpArch.Meta.FalsifiableNotAuthorizable

namespace EpArch.Meta

open EpArch

/-! ## 1. The Meta Claim Symbol -/

/-- The meta-claim type with a single constructor representing "the theory core."

    This is the token we will show is underdetermined by observations. -/
inductive MetaClaim where
  | theory_core : MetaClaim
  deriving DecidableEq, Inhabited


/-! ## 2. Conservative Extension Functor -/

/-- Add a theory_core claim to an existing WorldCtx by conservative extension.

    Given a base context `C` and a base claim `P0` that is underdetermined in `C`,
    we construct a new context where:
    - Claims are `Sum C.Claim MetaClaim`
    - The new `theory_core` claim has the same truth value as `P0`
    - Everything else (World, Agent, Obs, obs) is inherited unchanged

    This ensures obs is frozen, no circularity, and no gerrymandering. -/
def AddTheoryCore (C : WorldCtx) (P0 : C.Claim) : WorldCtx where
  -- Types: Claims extended, everything else inherited
  World := C.World
  Agent := C.Agent
  Claim := Sum C.Claim MetaClaim
  Obs := C.Obs

  -- Core semantics: obs inherited (frozen)
  obs := C.obs

  -- Truth: base claims use base truth; theory_core aliases P0 (no circularity)
  Truth := fun w claim =>
    match claim with
    | Sum.inl P => C.Truth w P
    | Sum.inr MetaClaim.theory_core => C.Truth w P0

  -- Utterance: base claims use base utterance; theory_core can always be uttered
  Utter := fun a claim =>
    match claim with
    | Sum.inl P => C.Utter a P
    | Sum.inr _ => True

  -- Verification: base claims use base verification; theory_core uses P0's
  VerifyWithin := fun w claim t =>
    match claim with
    | Sum.inl P => C.VerifyWithin w P t
    | Sum.inr _ => C.VerifyWithin w P0 t

  -- Effective time: inherited
  effectiveTime := C.effectiveTime

  -- Inhabitants: inherited (claim uses Sum.inl of base inhabitant)
  world_inhabited := C.world_inhabited
  agent_inhabited := C.agent_inhabited
  claim_inhabited := ⟨Sum.inl (Classical.choice C.claim_inhabited)⟩


/-! ## 3. Transfer Lemma: Underdetermination Lifts -/

/-- PartialObs is preserved under AddTheoryCore (obs is unchanged). -/
theorem addTheoryCore_partialObs_iff (C : WorldCtx) (P0 : C.Claim) (w0 w1 : C.World) :
    (AddTheoryCore C P0).PartialObs w0 w1 ↔ C.PartialObs w0 w1 := by
  simp only [WorldCtx.PartialObs, AddTheoryCore]

/-- Truth of theory_core equals truth of the base claim P0. -/
theorem addTheoryCore_truth_theory_core (C : WorldCtx) (P0 : C.Claim) (w : C.World) :
    (AddTheoryCore C P0).Truth w (Sum.inr MetaClaim.theory_core) = C.Truth w P0 := by
  rfl

/-- Underdetermination transfers: if P0 is underdetermined in C, then theory_core
    is underdetermined in AddTheoryCore C P0.

    This is the key transfer lemma that makes the stretch work without gerrymandering:
    we reuse the same w0, w1, and PartialObs evidence from the base context. -/
theorem lift_notDeterminedByObs_theory_core (C : WorldCtx) (P0 : C.Claim) :
    C.NotDeterminedByObs P0 →
    (AddTheoryCore C P0).NotDeterminedByObs (Sum.inr MetaClaim.theory_core) := by
  intro ⟨w0, w1, h_obs, h_diff⟩
  -- Construct the same witnesses for the extended context
  refine ⟨w0, w1, ?_, ?_⟩
  -- PartialObs is preserved (obs is unchanged)
  · exact (addTheoryCore_partialObs_iff C P0 w0 w1).mpr h_obs
  -- Truth difference transfers (theory_core aliases P0)
  · simp only [AddTheoryCore]
    exact h_diff


/-! ## 4. Universal Schema (No Witness Dependence) -/

/-- Extended context specialized to the extracted underdetermined claim.

    Given any context `C` with `W_partial_observability`, we can:
    1. Extract the canonical underdetermined claim via `UnderDeterminedClaim`
    2. Build the conservative extension with a `theory_core` token

    This removes witness-dependence: the construction works for *any* context
    satisfying the partial observability bundle. -/
noncomputable def AddTheoryCoreFromPartialObs (C : WorldCtx) (h : C.W_partial_observability) : WorldCtx :=
  AddTheoryCore C (UnderDeterminedClaim C h)

/-- The designated theory_core token in the extended context.

    This is the token we prove is underdetermined. -/
def theory_core_token (C : WorldCtx) (h : C.W_partial_observability) :
    (AddTheoryCoreFromPartialObs C h).Claim :=
  Sum.inr MetaClaim.theory_core

/-- **Universal Schema Theorem:**
    For any context with W_partial_observability, the designated theory_core token
    is underdetermined by observations.

    This is the general form that removes witness-dependence. The witness-specific
    theorem `witness_theory_core_not_determined` becomes an instance of this schema.

    **Claim Budget:**
    - Buys: Universal pattern — works for any context satisfying the bundle
    - Does NOT buy: Increased realism — still conservative internalization

    **Constraints:**
    - Obs surface unchanged (`obs := C.obs`)
    - Truth aliases existing claim (no circularity)
    - Pure composition of existing lemmas (no new axioms) -/
noncomputable def theory_core_token_not_determined
    (C : WorldCtx) (h : C.W_partial_observability) :
    (AddTheoryCoreFromPartialObs C h).NotDeterminedByObs (theory_core_token C h) :=
  lift_notDeterminedByObs_theory_core C (UnderDeterminedClaim C h) (underDeterminedClaim_spec C h)


/-! ## 5. Concrete Witness Instantiation -/

/-- The base underdetermined claim in WitnessCtx.

    This extracts a canonical underdetermined claim from the witness context
    using the W_partial_observability bundle. -/
noncomputable def WitnessP0 : WorldWitness.WitnessCtx.Claim :=
  UnderDeterminedClaim WorldWitness.WitnessCtx WorldWitness.holds_W_partial_observability

/-- WitnessP0 is indeed underdetermined in WitnessCtx. -/
noncomputable def witnessP0_not_determined : WorldWitness.WitnessCtx.NotDeterminedByObs WitnessP0 :=
  underDeterminedClaim_spec WorldWitness.WitnessCtx WorldWitness.holds_W_partial_observability

/-- The extended witness context with theory_core claim.

    This is WitnessCtx extended with a theory_core symbol that aliases WitnessP0. -/
noncomputable def WitnessTheoryCoreCtx : WorldCtx :=
  AddTheoryCore WorldWitness.WitnessCtx WitnessP0

/-- The theory_core token in the extended witness context. -/
noncomputable def theory_core : WitnessTheoryCoreCtx.Claim :=
  Sum.inr MetaClaim.theory_core


/-! ## 6. Headline Theorem -/

/-- **Headline Theorem (Optional Stretch):**
    The theory_core claim is not determined by observations.

    This proves that in the extended witness context, the designated token
    `theory_core` is underdetermined by the observational surface.

    **Claim Budget:**
    - Buys: "There exists a designated claim token such that obs does not determine it."
    - Does NOT buy: "The real world satisfies theory_core."

    **Design Constraints Satisfied:**
    - obs is unchanged from WitnessCtx (frozen)
    - Truth of theory_core is defined as Truth of WitnessP0 (no circularity)
    - theory_core is a conservative alias of an already-underdetermined claim
    - No axioms, no sorry -/
theorem witness_theory_core_not_determined :
    WitnessTheoryCoreCtx.NotDeterminedByObs theory_core :=
  lift_notDeterminedByObs_theory_core WorldWitness.WitnessCtx WitnessP0 witnessP0_not_determined

/-- **Corollary:** The witness theorem is an instance of the universal schema.

    This demonstrates that `witness_theory_core_not_determined` is not hand-crafted
    but follows from the general pattern `theory_core_token_not_determined`. -/
theorem witness_theory_core_not_determined' :
    (AddTheoryCoreFromPartialObs WorldWitness.WitnessCtx WorldWitness.holds_W_partial_observability).NotDeterminedByObs
      (theory_core_token WorldWitness.WitnessCtx WorldWitness.holds_W_partial_observability) :=
  theory_core_token_not_determined WorldWitness.WitnessCtx WorldWitness.holds_W_partial_observability

/-- The extended witness context still satisfies the theory floor.

    Adding theory_core doesn't break the floor bundles (they're about the
    original World/Agent/Obs structure, which is unchanged). -/
noncomputable def witnessTheoryCoreCtx_satisfies_floor_bundles :
    Nonempty (WitnessTheoryCoreCtx.W_lies_possible) ∧
    Nonempty (WitnessTheoryCoreCtx.W_bounded_verification) ∧
    Nonempty (WitnessTheoryCoreCtx.W_partial_observability) := by
  constructor
  -- W_lies_possible: need ∃ w P, ¬Truth w P
  · constructor
    constructor
    -- some_false: use the base context's false claim
    · have ⟨w, P, h⟩ := WorldWitness.holds_W_lies_possible.some_false
      exact ⟨w, Sum.inl P, h⟩
    -- unrestricted_utterance: agents can utter anything
    · intro a claim
      match claim with
      | Sum.inl P => exact WorldWitness.holds_W_lies_possible.unrestricted_utterance a P
      | Sum.inr _ => trivial
  constructor
  -- W_bounded_verification: need ∃ P k, k > 0 ∧ ∀ w, RequiresSteps w P k
  · constructor
    constructor
    have ⟨P, k, h_pos, h_req⟩ := WorldWitness.holds_W_bounded_verification.verification_has_cost
    exact ⟨Sum.inl P, k, h_pos, fun w => h_req w⟩
  -- W_partial_observability: need ∃ P, NotDeterminedByObs P
  · constructor
    constructor
    -- Use theory_core itself as the underdetermined claim
    exact ⟨theory_core, witness_theory_core_not_determined⟩

end EpArch.Meta

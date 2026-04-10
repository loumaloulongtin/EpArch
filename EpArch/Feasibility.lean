/-
EpArch/Feasibility.lean — Existence Under Constraints / Non-Vacuity Theorems

This module packages existing witnesses into "system class is nonempty"
statements, providing non-vacuity and existence proofs for
the existence-under-constraints claim.

## Purpose

Natural objections to an epistemic systems framework:
- "Are these constraints even consistent? Maybe they're vacuous."
- "Does a system satisfying these properties actually exist?"

This module answers: Yes. The constraint bundles are satisfiable,
working systems exist, and success forces Bank primitives.

## Headline Theorem

`existence_under_constraints`: There exists a WorkingSystem that is
WellFormed, satisfies all operational properties, AND contains Bank primitives.

This packages non-vacuity + forced primitives into one citable result.

## Claim Budget

**Buys:**
- "The constraint+objective package is consistent (nonempty)"
- "There exists at least one working system meeting the success bundle"
- "Success forces Bank primitives" (via Minimality)

**Does NOT buy:**
- "The real world literally is this model"
- "Uniqueness" (many realizations can exist)
- "Abduction/inference from observed O to existence of S"

-/

import EpArch.WorldWitness
import EpArch.Realizer
import EpArch.Minimality
import EpArch.Convergence

namespace EpArch.Feasibility

/-! ## World Constraint Feasibility -/

/-- World constraint bundles are satisfiable (non-vacuity).

    Uses the WitnessCtx from WorldWitness.lean to show that the
    W_* bundles are jointly satisfiable.

    Note: We use `@WorldCtx.{0}` to fix the universe level to match WitnessCtx. -/
theorem world_bundles_feasible :
    ∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability := by
  refine ⟨EpArch.WorldWitness.WitnessCtx, ?_⟩
  exact EpArch.WorldWitness.all_bundles_satisfiable

/-- Alias for backward compatibility -/
theorem constraints_feasible :
    ∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability :=
  world_bundles_feasible


/-! ## Commitment Feasibility -/

/-- Commitments are jointly satisfiable (named alias for external reference).

    This re-exports `all_commitments_satisfiable` under a consistent name. -/
theorem commitments_feasible :
    -- Commitment 1: Traction/Authorization split
    (∃ a B P, ConcreteModel.c_certainty a P ∧ ¬ConcreteModel.c_knowledge B P) ∧
    (∃ a B P, ConcreteModel.c_knowledge B P ∧ ¬ConcreteModel.c_certainty a P) ∧
    -- Commitment 2: No global ledger supports both
    (∃ G, ¬(ConcreteModel.c_supports_innovation G ∧ ConcreteModel.c_supports_coordination G)) ∧
    -- Commitment 3: S/E/V factorization exists
    (∃ d : ConcreteModel.CDeposit, d.S > 0 ∧ d.E.length > 0 ∧ d.V.length > 0) ∧
    -- Commitment 4: Consensus without redeemability
    (∃ B d, ConcreteModel.c_consensus B d.claim ∧ ¬ConcreteModel.c_redeemable d) ∧
    -- Commitment 5: Export gating
    True ∧
    -- Commitment 6: Repair loop
    (∃ _d c : ConcreteModel.CChallenge, c.field ∈ ["S", "E", "V", "τ"]) ∧
    -- Commitment 7: Header-stripped loses diagnosability
    (∃ d : ConcreteModel.CDeposit, ConcreteModel.c_header_stripped d ∧ d.E.length = 0) ∧
    -- Commitment 8: Fresh/stale differ
    (∃ d1 d2 t, ConcreteModel.c_fresh d1 t ∧ ConcreteModel.c_stale d2 t) :=
  ConcreteModel.all_commitments_satisfiable

/-- Objective bundle is satisfiable: there exists at least one Realizer.

    The Realizer packages the proof that all core commitments
    are simultaneously satisfiable. -/
theorem objectives_feasible : ∃ _ : EpArch.Realizer, True := by
  exact ⟨EpArch.ConcreteRealizer, trivial⟩


/-! ## System-Level Feasibility -/

/-- There exists at least one successful working system.

    This witnesses that the success bundle (WellFormed + SatisfiesAllProperties)
    is non-empty—there's at least one system that achieves it. -/
theorem success_feasible :
    ∃ W : WorkingSystem, WellFormed W ∧ SatisfiesAllProperties W := by
  refine ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem, ?_, ?_⟩
  · exact EpArch.ConcreteInstance.concrete_wellformed
  · exact EpArch.ConcreteInstance.concrete_satisfies_all_properties


/-! ## Minimality Alias -/

/-- Paper-facing name: success forces Bank primitives.

    Any working system that is WellFormed and satisfies all operational
    properties contains Bank primitives.  The proof routes through
    `convergence_structural` via `wellformed_implies_structurally_forced`. -/
theorem goals_force_bank_primitives :
    ∀ W : WorkingSystem, WellFormed W → SatisfiesAllProperties W → containsBankPrimitives W :=
  fun W h_wf h_sat =>
    convergence_structural W (wellformed_implies_structurally_forced W h_wf) h_sat


/-! ## Headline Theorem: Existence Under Constraints -/

/-- Headline theorem: existence-under-constraints (non-vacuity + forced primitives).

    This headline theorem combines three results:
    - There EXISTS a working system (non-vacuity)
    - That system is WellFormed and satisfies all properties (success)
    - That system contains Bank primitives (forced by minimality)

    Together: the success bundle is non-empty, and success forces Bank primitives. -/
theorem existence_under_constraints :
    ∃ W : WorkingSystem,
      WellFormed W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W := by
  refine ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem, ?_⟩
  refine ⟨EpArch.ConcreteInstance.concrete_wellformed,
          EpArch.ConcreteInstance.concrete_satisfies_all_properties, ?_⟩
  exact goals_force_bank_primitives EpArch.ConcreteInstance.ConcreteWorkingSystem
    EpArch.ConcreteInstance.concrete_wellformed
    EpArch.ConcreteInstance.concrete_satisfies_all_properties


/-! ## Joint Feasibility (Legacy) -/

/-- Joint feasibility: world constraints and objectives are both nonempty.

    Kept for backward compatibility. The stronger `existence_under_constraints`
    is the preferred reference. -/
theorem joint_feasible :
    (∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability) ∧
    (∃ _ : EpArch.Realizer, True) := by
  exact ⟨constraints_feasible, objectives_feasible⟩


/-! ## Structural Convergence -/

/-- Paper-facing name (structural version): success forces Bank primitives
    without depending on WellFormed biconditionals. -/
theorem structural_goals_force_bank_primitives :
    ∀ W : WorkingSystem,
      StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W :=
  convergence_structural

/-- Headline theorem (structural version): the concrete model is
    structurally forced, satisfies all properties, and contains Bank
    primitives — without going through WellFormed. -/
theorem existence_under_constraints_structural :
    ∃ W : WorkingSystem,
      StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W := by
  refine ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem, ?_⟩
  refine ⟨EpArch.ConcreteInstance.concrete_structurally_forced,
          EpArch.ConcreteInstance.concrete_satisfies_all_properties, ?_⟩
  exact convergence_structural EpArch.ConcreteInstance.ConcreteWorkingSystem
    EpArch.ConcreteInstance.concrete_structurally_forced
    EpArch.ConcreteInstance.concrete_satisfies_all_properties

/-- Headline theorem (embedding version): full chain from
    `ForcingEmbedding` through `StructurallyForced` to convergence.
    This is the strongest form — the design judgment is localised
    in `concrete_forcing_embedding`, and the derivation is mechanical. -/
theorem existence_under_constraints_embedding :
    ∃ W : WorkingSystem,
      ForcingEmbedding W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W :=
  ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem,
   EpArch.ConcreteInstance.concrete_forcing_embedding,
   EpArch.ConcreteInstance.concrete_satisfies_all_properties,
   EpArch.ConcreteInstance.concrete_structural_convergence⟩


/-! ## World-to-Structural Bridges

These theorems connect the W_* world assumption bundles (WorldCtx.lean) to the
structural impossibility models (Minimality.lean).  Previously the two sides were
proved independently — the structural models had hand-supplied witnesses, and the
world assumptions had witnesses of their own.  These bridges show that any world
satisfying a W_* bundle supplies enough data to construct a matching structural
scenario instance, so the forcing results apply without a separate construction step.

The constructed instances are the minimal form sufficient to trigger the relevant
impossibility theorem — they package the W bundle's witness values, not a full
semantic import of the world's relational structure. -/

/-- Any world satisfying W_bounded_verification constructs a `BoundedVerification`
    instance sufficient to trigger `verification_only_import_incomplete`.

    The W bundle supplies a hard claim P and step count k > 0.  The constructed M
    packages these into the minimal abstract form: `verify_cost := fun _ => k`
    (a constant, not C.RequiresSteps itself) and `budget := 0`.  The world's
    RequiresSteps field is preserved in the existential witness but is not carried
    into M's cost function.

    The constructed M has:
    - M.Claim = C.Claim  (claim type is the world's claim type, not Unit)
    - M.hard_claim = P   (the actual hard claim from the world assumption)
    - M.verify_cost P = k (the extracted step count, as a constant function)
    - ∀ w, C.RequiresSteps w P k  (world witness, returned alongside M)

    verification_only_import_incomplete then fires on M.
    Consequence: the incompleteness is specifically about the claim P the world
    says is hard — not a synthetic Unit witness. -/
theorem w_bounded_forces_incompleteness (C : @EpArch.WorldCtx.{0})
    (W : C.W_bounded_verification) :
    ∃ (P : C.Claim) (k : Nat) (M : BoundedVerification),
      k > 0 ∧
      (∀ w, C.RequiresSteps w P k) ∧
      M.Claim = C.Claim ∧
      ¬∀ c : M.Claim, M.verify_cost c ≤ M.budget := by
  have ⟨P, k, h_pos, h_req⟩ := W.verification_has_cost
  let M : BoundedVerification := ⟨C.Claim, fun _ => k, 0, P, h_pos⟩
  exact ⟨P, k, M, h_pos, h_req, rfl, verification_only_import_incomplete M⟩

/-- Any world satisfying W_lies_possible forces revocation into the architecture.

    The lifecycle is typed over C.Claim and h_absorb references C.Truth directly:
    any false claim is a fixed point of step.  This connects the world's truth
    semantics to the lifecycle's revocation-free structure — they are not two
    separate arguments bolted together.  The SAME P from W is the claim that is
    injectable (lie reach) and indelible (trapped forever).

    h_absorb says: "your step function cannot exit any false claim" —
    the formal statement of a revocation-free lifecycle WITH RESPECT TO
    the world's truth semantics.  Revocation is forced precisely because
    false claims exist and no monotone step can undo their acceptance. -/
theorem w_lies_forces_revocation_need (C : @EpArch.WorldCtx.{0})
    (W : C.W_lies_possible)
    -- Lifecycle over the world's claim type; step fixes every false claim
    (step : C.Claim → C.Claim)
    (h_absorb : ∀ w P, ¬C.Truth w P → step P = P) :
    -- The SAME false claim is injectable by every agent AND permanently trapped
    ∃ w P, ¬C.Truth w P ∧ (∀ a, C.Utter a P) ∧ ∀ n, iter step n P = P := by
  have ⟨w, P, h_false⟩ := W.some_false
  let lc : MonotonicLifecycle := ⟨C.Claim, P, step, h_absorb w P h_false⟩
  exact ⟨w, P, h_false, fun a => W.unrestricted_utterance a P, monotonic_no_exit lc⟩

/-- Any world satisfying W_partial_observability forces redeemability into the architecture.

    W.obs_underdetermines supplies a claim P where observationally equivalent
    worlds disagree on P's truth.  In any closed endorsement system (no external
    constraint-surface contact), P would be endorsed in one world and that
    endorsement could never be falsified — the closure condition holds.
    closed_system_unfalsifiable then fires: no endorsed claim can be
    simultaneously externally falsifiable.

    But P's truth IS falsifiable — the other observationally-equivalent world
    witnesses the opposite truth value.  The closed system cannot represent this:
    external contact (redeemability) is structurally forced.

    The proof: take the underdetermined P and worlds w0, w1 from W.
    Suppose endorsed w0 P.  By closed, Truth w0 P.  By the biconditional,
    ¬Truth w1 P.  But by obs_stable (same obs → same endorsement), endorsed w1 P.
    By closed again, Truth w1 P.  Contradiction.  So no obs-stable closed system
    can endorse the underdetermined claim — redeemability is forced. -/
theorem w_partial_obs_forces_redeemability (C : @EpArch.WorldCtx.{0})
    (W : C.W_partial_observability)
    (endorsed : C.World → C.Claim → Prop)
    (obs_stable : ∀ P w0 w1, C.PartialObs w0 w1 → endorsed w0 P → endorsed w1 P)
    (closed : ∀ w P, endorsed w P → C.Truth w P) :
    ∃ P w0, ¬endorsed w0 P := by
  have ⟨P, w0, w1, h_obs, h_bic⟩ := W.obs_underdetermines
  exact ⟨P, w0, fun h_end =>
    (h_bic.mp (closed w0 P h_end)) (closed w1 P (obs_stable P w0 w1 h_obs h_end))⟩


/-! ## World-Grounded Convergence -/

/-- A working system is world-aware with respect to WorldCtx C if its structural
    forcing implications are grounded in C's world assumptions (for those that
    have W_* bundle counterparts) and by structural analysis (for the rest).

    Three of the six StructurallyForced implications are justified by W_* bundles:
    - trust_forcing        ← W_bounded_verification (verification_only_import_incomplete)
    - revocation_forcing   ← W_lies_possible        (monotonic_no_exit)
    - redeemability_forcing ← W_partial_observability (closed_system_unfalsifiable)

    Three are justified by structural impossibility arguments alone and have no
    W_* bundle counterpart (AgentDisagreement, DiscriminatingImport,
    PrivateOnlyStorage) — included here as unconditional hypotheses. -/
def WorldAwareSystem (C : @EpArch.WorldCtx.{0}) (W : WorkingSystem) : Prop :=
  (C.W_bounded_verification  → handles_bounded_audit W    → HasTrustBridges W)  ∧
  (C.W_lies_possible         → handles_adversarial W      → HasRevocation W)    ∧
  (C.W_partial_observability → handles_truth_pressure W   → HasRedeemability W) ∧
  (handles_distributed_agents W → HasBubbles W) ∧
  (handles_export W             → HasHeaders W)  ∧
  (handles_coordination W       → HasBank W)

/-- Headline theorem: a working system operating in any world satisfying all
    three EpArch world assumptions, that is world-aware and satisfies all
    operational properties, necessarily contains Bank primitives.

    The W_* bundles are the direct antecedent of convergence.  The proof
    constructs StructurallyForced W from WorldAwareSystem by threading Wv, Wl,
    Wo through the three world-conditional implications, then applies
    convergence_structural.  All three W_* bundles are non-trivially consumed:
    removing any one leaves the corresponding forcing implication unprovable. -/
theorem world_assumptions_force_bank_primitives (C : @EpArch.WorldCtx.{0})
    (Wl : C.W_lies_possible)
    (Wv : C.W_bounded_verification)
    (Wo : C.W_partial_observability)
    (W : WorkingSystem)
    (h_wa : WorldAwareSystem C W)
    (h_sat : SatisfiesAllProperties W) :
    containsBankPrimitives W := by
  apply convergence_structural W _ h_sat
  exact { scope_forcing        := h_wa.2.2.2.1
          trust_forcing        := h_wa.1 Wv
          header_forcing       := h_wa.2.2.2.2.1
          revocation_forcing   := h_wa.2.1 Wl
          bank_forcing         := h_wa.2.2.2.2.2
          redeemability_forcing := h_wa.2.2.1 Wo }

/-- Any StructurallyForced system satisfies WorldAwareSystem for any WorldCtx.

    Proof by weakening: StructurallyForced asserts all six capability→feature
    implications *unconditionally*, while WorldAwareSystem only requires three of
    them *conditionally* (behind W_* hypothesis guards).  Ignoring the W_* guard
    via `fun _ =>` discharges each conditional, reducing WorldAwareSystem to a
    strict weakening of StructurallyForced. -/
theorem structurally_forced_is_world_aware (C : @EpArch.WorldCtx.{0}) (W : WorkingSystem)
    (h_sf : StructurallyForced W) : WorldAwareSystem C W :=
  ⟨fun _ => h_sf.trust_forcing,
   fun _ => h_sf.revocation_forcing,
   fun _ => h_sf.redeemability_forcing,
   h_sf.scope_forcing,
   h_sf.header_forcing,
   h_sf.bank_forcing⟩

/-- Zero-hypothesis corollary: the concrete working system contains Bank primitives
    with no free assumptions.

    Proof path:
    (1) WitnessCtx (WorldWitness.lean) witnesses all three W_* bundles.
    (2) concrete_structurally_forced gives StructurallyForced ConcreteWorkingSystem.
    (3) structurally_forced_is_world_aware converts that to WorldAwareSystem WitnessCtx.
    (4) concrete_satisfies_all_properties gives SatisfiesAllProperties.
    (5) world_assumptions_force_bank_primitives closes the proof.

    The three world assumptions that appear as hypotheses in
    world_assumptions_force_bank_primitives are discharged here by the WitnessCtx
    model, leaving a fully closed theorem. -/
theorem kernel_world_forces_bank_primitives :
    containsBankPrimitives EpArch.ConcreteInstance.ConcreteWorkingSystem :=
  world_assumptions_force_bank_primitives
    EpArch.WorldWitness.WitnessCtx
    EpArch.WorldWitness.holds_W_lies_possible
    EpArch.WorldWitness.holds_W_bounded_verification
    EpArch.WorldWitness.holds_W_partial_observability
    EpArch.ConcreteInstance.ConcreteWorkingSystem
    (structurally_forced_is_world_aware _ _
      EpArch.ConcreteInstance.concrete_structurally_forced)
    EpArch.ConcreteInstance.concrete_satisfies_all_properties

end EpArch.Feasibility

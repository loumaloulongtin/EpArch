# Theorem Registry

A lookup index, not a proof narrative. Each family entry records the
high-level claim, the primary files, the entry theorem, and a short list of
load-bearing supporting theorems. For the main proof route see
[PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md); for the trusted base see
[AXIOMS.md](AXIOMS.md).

---

## How to use this file

- Find the family that matches the claim you want to inspect.
- Open the **entry theorem** in the listed primary file. That theorem is
  the canonical statement of the claim.
- Supporting theorems are deliberately limited (2–5 per family). They are
  the pieces a reviewer most often wants to follow next; they are not an
  exhaustive enumeration. Open the primary files for the full list.

Pathology dissolutions (Gettier, Fake Barn, Lottery, Moorean, preface,
closure, luminosity) live here — in family F5, not in cases/.

---

## F1. Lifecycle, withdrawal gates, repair

**Claim.** Deposit status types (Candidate / Deposited / Quarantined / Revoked)
gate which actions the LTS permits; withdrawal requires `Deposited`; repair
requires prior challenge and re-enters validation.

**Primary files.**
[Theorems/Withdrawal.lean](../../EpArch/Theorems/Withdrawal.lean),
[Theorems/Corners.lean](../../EpArch/Theorems/Corners.lean),
[Semantics/StepSemantics.lean](../../EpArch/Semantics/StepSemantics.lean).

**Entry theorem.** `withdrawal_gates` (`Theorems/Withdrawal.lean`) — withdrawal preconditions.

**Supporting.** `withdrawal_requires_deposited`, `candidate_blocks_withdrawal`,
`repair_enforces_revalidation`, `repair_requires_prior_challenge`,
`repair_resets_to_candidate`.

---

## F2. Competition gate (revision ⇔ self-correction)

**Claim.** Self-correction is exactly the capability to revise; a domain that
prohibits revision admits no demonstrating-self-correction trace.

**Primary files.**
[Semantics/StepSemantics.lean](../../EpArch/Semantics/StepSemantics.lean),
[Theorems/Corners.lean](../../EpArch/Theorems/Corners.lean).

**Entry theorem.** `no_revision_no_correction` — `prohibitsRevision s ⇒ ¬ ∃ t, demonstratesSelfCorrection t`.

**Supporting.** `self_correction_requires_revision`,
`self_correcting_domain_permits_revision`,
`frozen_canon_no_revocation`, `frozen_canon_no_revocation_trace`.

---

## F3. Export / strip asymmetry and diagnosability

**Claim.** Header-stripping is information-destroying; stripped deposits
have zero observable fields and cannot target field-specific repair.

**Primary files.**
[Theorems/Strip.lean](../../EpArch/Theorems/Strip.lean),
[Theorems/Diagnosability.lean](../../EpArch/Theorems/Diagnosability.lean).

**Entry theorem.** `strip_reduces_diagnosability` — strip lowers diagnosability monotonically.

**Supporting.** `no_strip_left_inverse`, `import_cannot_reconstruct`,
`different_headers_same_strip`, `stripped_no_field_repair`,
`epistemic_diagnosability_full` / `epistemic_diagnosability_stripped`.

---

## F4. Temporal validity (τ)

**Claim.** Tick-monotonicity is a structural Step gate; τ-expiry is agent
policy, not a `Step.withdraw` precondition.

**Primary files.**
[Semantics/StepSemantics.lean](../../EpArch/Semantics/StepSemantics.lean).

**Entry theorem.** `tick_preserves_valid_status` — `Step.tick` preserves
status validity. The structural monotonicity (`s.clock ≤ t'`) is enforced by
the `Step.tick` constructor's `h_mono` argument; it is a typed precondition,
not a separate theorem.

**Supporting.** None at LTS level. Corner-7-style theorems were retired with
the removal of `isCurrentDeposit` from the withdraw gate.

---

## F5. Pathology dissolutions and case bindings

**Claim.** Classical epistemological puzzles (Gettier, Fake Barn, Lottery,
Moorean, preface, closure, luminosity, …) are diagnosed by the architecture
as type errors or specific S/E/V failures, not as substantive paradoxes.

**Primary files.**
[Theorems/Cases/](../../EpArch/Theorems/Cases) (Gettier, FakeBarn, Standard,
VacuousStandard, TypeErrors),
[Theorems/Dissolutions.lean](../../EpArch/Theorems/Dissolutions.lean),
[Theorems/Pathologies.lean](../../EpArch/Theorems/Pathologies.lean),
[Theorems/Modal.lean](../../EpArch/Theorems/Modal.lean).

**Entry theorems by case.**
- `gettier_is_V_failure` (`Theorems/Cases/Gettier.lean`)
- `fake_barn_is_E_failure` (`Theorems/Cases/FakeBarn.lean`)
- `standard_failure_targets_S`, `canonical_standard_case_is_standard` (`Theorems/Cases/Standard.lean`)
- `vacuous_standard_is_S_failure` (`Theorems/Cases/VacuousStandard.lean`)
- `LotteryIsTypeError` (`Theorems/Cases/TypeErrors.lean`); `lottery_paradox_dissolved_architecturally` (`Theorems/Corners.lean`); `confabulation_is_type_error` (`Theorems/Cases/TypeErrors.lean`)
- `moorean_export_contradiction`, `preface_dissolution`, `closure_type_separation`, `luminosity_type_separation`, `higher_order_relocation`, `apriori_domain_parameterization` (`Theorems/Dissolutions.lean`)
- `testimony_is_export`, `disagreement_is_routing`, `injustice_is_import_corruption`, `local_redeemability_survives` (`Theorems/Pathologies.lean`)

Linking-axiom discharges (every former opaque "philosophical link" is now a
proved theorem) live alongside the case bindings in
`Theorems/Dissolutions.lean`, `Theorems/Pathologies.lean`, and
[Theorems/NotationBridge.lean](../../EpArch/Theorems/NotationBridge.lean).

---

## F6. Modal properties (Safety/Sensitivity ↔ V/E)

**Claim.** Modal epistemic notions (safety, sensitivity) reduce to
V-independence and E-coverage on the deposit's header.

**Primary files.**
[Theorems/Modal.lean](../../EpArch/Theorems/Modal.lean).

**Entry theorem.** `safety_ctx_V_link` — `SafetyCtx C sc ⇒ V_indepCtx C sc` (over `SafetyCaseCtx`).

**Supporting.** `sensitivity_ctx_E_link`, `gettier_ctx_exhibits_provenance_gap`.

---

## F7. Structural forcing chain (per-dimension and bundled)

**Claim.** Each of the eight EpArch pressures (`Pressure` cases: scope, trust,
headers, revocation, bank, redeemability, authorization, storage) forces its
corresponding Bank primitive; the bundled form forces the full primitive
package without a `WorldCtx`.

**Primary files.**
[Minimality.lean](../../EpArch/Minimality.lean),
[Convergence.lean](../../EpArch/Convergence.lean),
[Scenarios.lean](../../EpArch/Scenarios.lean),
[GroundedEvidence.lean](../../EpArch/GroundedEvidence.lean),
[WorldBridges.lean](../../EpArch/WorldBridges.lean).

**Entry theorem.** `bundled_structure_forces_bank_primitives`
(`WorldBridges.lean`) — `SystemOperationalBundle W → WorldBridgeBundle W → SatisfiesAllProperties W → containsBankPrimitives W`.

**Supporting (per-dimension forcing).**
`disagreement_forces_bubbles`, `private_coordination_forces_bank`,
`monotonic_lifecycle_forces_revocation`,
`discriminating_import_forces_headers`,
`bounded_verification_forces_trust_bridges`,
`closed_endorsement_forces_redeemability`,
`uniform_access_forces_acl`,
`bounded_capacity_forces_storage_management`. Plus the route-closing
`grounded_world_and_structure_force_bank_primitives` in `WorldBridges.lean`.

**Behavioral / depth companions.**
`working_systems_equivalent`
([Theorems/BehavioralEquivalence.lean](../../EpArch/Theorems/BehavioralEquivalence.lean));
`no_budget_is_sufficient`, `endorser_cannot_self_verify`
([Concrete/VerificationDepth.lean](../../EpArch/Concrete/VerificationDepth.lean)).

---

## F8. Bounded recall, analogical bridge, residual risk

**Claim.** Bounded-budget impossibility extends from import-time
verification to recall (withdrawal) and to novel-input scratch verification;
budgeted bridges carry irreducible residual risk; mitigation surface is
relatively minimal.

**Primary files.**
[Minimality.lean](../../EpArch/Minimality.lean) (§9–§11),
[ResidualRiskMitigation.lean](../../EpArch/ResidualRiskMitigation.lean).

**Entry theorems.**
- `recall_only_withdrawal_incomplete` — recall direction (`Minimality.lean §9`).
- `scratch_verification_insufficient_for_novel_inputs` — analogical direction (`§10`).
- `risk_not_eliminable_by_budgeted_bridge` — residual risk (`§11`).
- `removing_any_mechanism_leaves_obligation_uncovered` — relative minimality
  (`ResidualRiskMitigation.lean`).

**Supporting.**
`bounded_recall_forces_recency_filter`, `analogical_recall_forced`,
`recall_is_bounded_verification_instance`,
`analogical_is_bounded_verification_instance`,
`eparch_surface_groundedly_covers_residual_risk_modes`,
`all_modes_grounded_and_groundedly_covered`,
`every_mechanism_mitigates_some_mode`.

---

## F9. Adversarial model and W ⇒ mechanism obligations

**Claim.** Attack vocabulary is type-level (`AdversarialBase`); concrete
attacks are blocked at gates; `W_*` world bundles convert former mechanism
axioms into conditional obligation theorems.

**Primary files.**
[Adversarial/Base.lean](../../EpArch/Adversarial/Base.lean),
[Adversarial/Concrete.lean](../../EpArch/Adversarial/Concrete.lean),
[Adversarial/Obligations.lean](../../EpArch/Adversarial/Obligations.lean),
[WorldCtx.lean](../../EpArch/WorldCtx.lean).

**Entry theorems.**
- `concrete_attack_succeeds`, `ddos_V_channel_collapse_blocks_withdrawal`
  (`Adversarial/Concrete.lean`) — gates fire on concrete instances.
- `lie_possible_of_W`, `bounded_audit_fails`, `cost_asymmetry_of_W`,
  `partial_obs_no_omniscience` (`WorldCtx.lean`) — world-bundle obligations.

**Supporting.** `τ_compressed_deposit_blocked`,
`V_spoof_deposit_blocked`, `overwhelmed_channel_collapses_V`,
`spoofed_V_blocks_path_of_W`, `ddos_causes_verification_collapse_of_W`,
`trust_bridge_maintains_path_of_W`, `cheap_validator_maintains_path_of_W`.

---

## F10. Health goals and design imposition

**Claim.** Health goals (corrigibility, sound deposits, safe withdrawal,
reliable export, self-correction, autonomy under PRP) plus agent-imperfection
constraints force specific mechanisms; absence of a forced mechanism
contradicts the goal.

**Primary files.**
[Health.lean](../../EpArch/Health.lean),
[Agent/Imposition.lean](../../EpArch/Agent/Imposition.lean),
[Agent/Constraints.lean](../../EpArch/Agent/Constraints.lean),
[Mechanisms.lean](../../EpArch/Mechanisms.lean).

**Entry theorem.** `no_escalation_forces_bridge` (`Health.lean`) —
`AutonomyUnderPRPGoal + mustHandle + scratch failure + ¬canEscalate ⇒ budgeted analogical bridge is forced`.

**Supporting.**
`corrigible_needs_revision`, `sound_deposits_needs_verification`,
`autonomy_forces_bridge_or_escalation`,
`residual_risk_forced_when_no_scratch_no_escalation`,
`safe_withdrawal_needs_reversibility`,
`sound_deposits_need_cheap_validator`,
`reliable_export_needs_gate`,
`no_global_closure_of_PRP`, `needs_revision_of_PRP`.

---

## F11. Scope / irrelevance

**Claim.** Out-of-scope fundamentals (physics, consciousness, psychology,
embodiment, traction implementation, optimal rationality) are irrelevant by
design — no architectural theorem depends on them.

**Primary files.**
[Semantics/ScopeIrrelevance.lean](../../EpArch/Semantics/ScopeIrrelevance.lean).

**Entry theorem.** `extra_state_revision_gate_transport` — `RevisionGate`
transports across any extra-state extension via `transport_core`.

**Supporting.** `extra_state_compatible`,
`consciousness_irrelevant_revision_gate`,
`psychology_irrelevant_revision_gate`,
`qualia_irrelevant_revision_gate`,
`structurally_forced_phantom_extension`,
`consciousness_invariant_under_forcing`,
`psychology_invariant_under_forcing`,
`qualia_invariant_under_forcing`.

---

## F12. Revision safety, transport, and modular reconfiguration

**Claim.** Compatible extensions preserve revision-gate, all five health
goals, and the LTS-universal operational theorems; sub-bundles inherit safety
both downward and upward (lattice-stability).

**Primary files.**
[Semantics/RevisionSafety.lean](../../EpArch/Semantics/RevisionSafety.lean),
[Meta/TheoremTransport.lean](../../EpArch/Meta/TheoremTransport.lean),
[Meta/Tier4Transport.lean](../../EpArch/Meta/Tier4Transport.lean),
[Meta/Reconfiguration.lean](../../EpArch/Meta/Reconfiguration.lean).

**Entry theorems.**
- `transport_core` (`Semantics/RevisionSafety.lean`) — `Compatible E C → RevisionGate C → RevisionGate (forget E)`.
- `health_goal_transport_pack` (`Meta/TheoremTransport.lean`) — five-goal Tier 3 pack.
- `tier4_full_pack` / `tier4_full_pack_surj` (`Meta/Tier4Transport.lean`) — eight-conjunct Tier 4 pack.
- `modularity_pack` (`Meta/TheoremTransport.lean`) — full bidirectional lattice-stability.

**Supporting.** `safe_extension_preserves`,
`safety_preserved_under_contract_refinement`,
`graceful_degradation`, `sub_revision_safety`,
`quarantine_requires_challenge_structured`, `no_self_healing_bank`.

---

## F13. Multi-agent corroboration

**Claim.** Single-source authorization is exploitable; corroboration is
forced by the no-single-point-of-failure goal; common-mode failure breaks
naive k-of-n; independence is the structural escape.

**Primary files.**
[Agent/Corroboration.lean](../../EpArch/Agent/Corroboration.lean).

**Entry theorem.** `corroboration_package` — T1 (vulnerability) ∧ T3 (common-mode) bundled.

**Supporting.** `single_source_can_accept_false`,
`no_spof_requires_multi_source`,
`common_mode_breaks_naive_corroboration`,
`common_mode_requires_diversity`,
`k_of_n_suffices_under_independence`.

---

## F14. Entrenchment

**Claim.** Entrenchment (Certainty + structural refusal to revise) breaks
safe withdrawal: an inactive deposit cannot satisfy `isDeposited` and no
`Step.withdraw` fires.

**Primary files.**
[Theorems/Corners.lean](../../EpArch/Theorems/Corners.lean).

**Entry theorem.** `entrenchment_breaks_safe_withdrawal`.

**Supporting.** `entrenched_cannot_withdraw`.

---

## F15. Observational completeness

**Claim.** Headers and deposits are extensional in their named fields — no
hidden degrees of freedom; field-equal deposits are predicate-indistinguishable.

**Primary files.**
[Header.lean](../../EpArch/Header.lean).

**Entry theorem.** `observational_completeness_full` — all nine primitive
fields determine the deposit.

**Supporting.** `header_ext`, `deposit_ext`, `observational_completeness`.

---

## F16. Feasibility and existence under constraints

**Claim.** The constraint+objective package is consistent; success forces
the Bank primitives; concrete witnesses inhabit the existence theorems.

**Primary files.**
[Feasibility.lean](../../EpArch/Feasibility.lean),
[Convergence.lean](../../EpArch/Convergence.lean),
[Concrete/](../../EpArch/Concrete),
[WorldWitness.lean](../../EpArch/WorldWitness.lean).

**Entry theorem.** `existence_under_constraints_structural`
(`Feasibility.lean`) — `∃ W, StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W`.

**Supporting.** `convergence_structural`,
`existence_under_constraints_embedding`,
`world_bundles_feasible`, `commitments_feasible`, `realizer_exists`,
`all_bundles_satisfiable`, `concrete_satisfies_all_properties`.

For the canonical statement of what witness theorems do and do not buy,
see [WITNESS-SCOPE.md](WITNESS-SCOPE.md).

---

## F17. Meta-status: falsifiable, not fully authorizable

**Claim.** The theory floor is satisfiable, falsifiable (a counter-context
exists), and not fully authorizable from observation alone — credit is
required.

**Primary files.**
[Meta/FalsifiableNotAuthorizable.lean](../../EpArch/Meta/FalsifiableNotAuthorizable.lean).

**Entry theorem.** `meta_status_proof_pack` — P1 ∧ P2 ∧ P3 packaged.

**Supporting.** `theory_floor_satisfiable`, `theory_floor_falsifiable`,
`theory_floor_not_fully_authorizable`,
`witness_not_fully_authorizable`,
`credit_safe_under_extension`, `trivial_has_no_lies`.

**Vocabulary.** Allowed: "not fully authorizable from obs",
"underdetermined", "credit required". Avoid: "never provable true",
"unprovable".

---

## F18. Modularity meta-theorem and configurable certification

**Claim.** Every subset of the eight constraints yields a partial
well-formedness biconditional; `EpArchConfig` selects one of 32 theorem
clusters and the certification engine returns a machine-checked
`CertifiedProjection` for each enabled cluster.

**Primary files.**
[Meta/Modular.lean](../../EpArch/Meta/Modular.lean),
[Minimality.lean](../../EpArch/Minimality.lean),
[Meta/Config.lean](../../EpArch/Meta/Config.lean),
[Meta/ClusterRegistry.lean](../../EpArch/Meta/ClusterRegistry.lean).

**Entry theorems.**
- `modular` (`Meta/Modular.lean`) — `∀ S W, PartialWellFormed W S → projection_valid S W`.
- `clusterEnabled_sound` (`Meta/Config.lean`) — `clusterEnabled cfg c = true → clusterValid c`.

**Supporting.** `partial_no_constraints`, `pwf_subset_mono`,
`safe_relaxation`, `pwf_add_bubbles` … `pwf_add_storage_management`,
the `cluster_forcing_*`, `cluster_goal_*`, `cluster_world_*`, and
`cluster_lattice_*` named witnesses in `Meta/Config.lean`.

For the modularity scope statement (what modular reconfiguration buys and
what it does not), see
[../architecture/MODULARITY.md](../architecture/MODULARITY.md).

---

## Where the main proof route lives

The headline forcing route runs through five core-route files:
`Scenarios.lean → GroundedEvidence.lean → Minimality.lean → Convergence.lean → WorldBridges.lean`,
closing on `bundled_structure_forces_bank_primitives` (F7) and
`existence_under_constraints_structural` (F16). The route, its entry
certificate, and the dependency narrative live in
[PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md), not here.

---

## Optional / stretch families

- **Theory-core token (conservative extension).** `witness_theory_core_not_determined`
  in [Meta/TheoryCoreClaim.lean](../../EpArch/Meta/TheoryCoreClaim.lean);
  scope and what the token does and does not buy live in
  [WITNESS-SCOPE.md](WITNESS-SCOPE.md).
- **Lean-kernel self-application.** `lean_kernel_existence`,
  `lean_kernel_forces_bank_primitives`, `lean_kernel_no_tradeoff` in
  [Meta/LeanKernel/World.lean](../../EpArch/Meta/LeanKernel/World.lean);
  S-failure taxonomy in
  [Meta/LeanKernel/SFailure.lean](../../EpArch/Meta/LeanKernel/SFailure.lean);
  full S/E/V repair lifecycle in
  [Meta/LeanKernel/RepairLoop.lean](../../EpArch/Meta/LeanKernel/RepairLoop.lean).
  The one named axiom (`lean_kernel_verification_path`) lives in
  [Meta/LeanKernel/VerificationPath.lean](../../EpArch/Meta/LeanKernel/VerificationPath.lean)
  and is not in the `Main.lean` import surface — see
  [AXIOMS.md](AXIOMS.md) and [optional/LEAN-KERNEL.md](../optional/LEAN-KERNEL.md).

---

## Go next

- [PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md) — the forcing route through F7 and F16.
- [START-HERE.md](../START-HERE.md) — recommended reading order across these families.

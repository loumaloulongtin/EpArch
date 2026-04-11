# Paper Section ↔ Lean Artifact Mapping

**Purpose:** Extraction guide from Lean → paper. Each section lists Lean artifacts and tier for paper-facing claims.

**Tier key:** A = proved, B = conditional on W-bundle (`W_* → Conclusion`), C = design requirement (intentionally postulated), D = not paper-facing.

**Usage:** Hand this document to a third party; they should know what is "paper-facing" without guessing.

---

## Core Vocabulary (Paper-Facing)

These are the canonical types and predicates exported via `EpArch/PaperFacing.lean`.
All paper claims should reference these definitions.

### World Layer (EpArch/WorldCtx.lean)

| Artifact | Type | Tier | Description |
|----------|------|------|-------------|
| `WorldCtx` | `structure` | C | Semantic signature for world layer |
| `WorldCtx.Claim` | `Type` | C | Canonical claim/proposition type |
| `WorldCtx.Truth` | `World → Claim → Prop` | C | World-relative truth predicate |
| `WorldCtx.Lie` | `World → Agent → Claim → Prop` | A | Agent utters falsehood (derived from Truth) |
| `WorldCtx.NotDeterminedByObs` | `Claim → Prop` | A | Truth underdetermined by observation |
| `WorldCtx.RequiresSteps` | `World → Claim → Nat → Prop` | C | Bounded verification cost |

### World Assumption Bundles

| Bundle | Tier | Contents | Enables |
|--------|------|----------|---------|
| `W_lies_possible` | C | some_false, unrestricted_utterance | `lie_possible_of_W` |
| `W_bounded_verification` | C | verification_has_cost | Bounded audit theorems |
| `W_partial_observability` | C | obs_underdetermines | Epistemic limits |
| `W_asymmetric_costs` | C | export_cost < defense_cost | `cost_asymmetry_of_W` |

---

## Section Overview

| § | Title | Primary File(s) | Tier | Coverage | Key Artifacts |
|---|-------|-----------------|------|----------|---------------|
| 1 | Introduction | Commitments.lean | A | ✅ Full | 8 commitments (all proved) |
| 2 | Core Split | Basic.lean, Theorems.lean | A | ✅ Full | `traction_broader_than_authorization` |
| 3 | JTB Underspecified | Theorems.lean | A | ✅ Diagnoses | `gettier_is_V_failure` |
| 4 | The Ladder | Basic.lean | C | ✅ Full | `LadderStage` (5-stage), `Entrenched` |
| 5 | Bubbles | Basic.lean, StepSemantics.lean | A | ✅ Full | `export_requires_header` |
| 6 | The Bank | Bank.lean, StepSemantics.lean | A | ✅ Full | `withdrawal_requires_three_gates` |
| 7 | Validation (S,E,V) | Header.lean, StepSemantics.lean | A | ✅ Full | `has_SEV_factorization` |
| 8 | Redeemability | Commitments.lean | A | ✅ Full | `redeemability_requires_more_than_consensus` |
| 9 | Operating Modes | Basic.lean | C | ✅ Type | `OperatingMode` enum |
| 10 | Export | StepSemantics.lean, Theorems.lean | A | ✅ Full | `no_strip_left_inverse` |
| 11 | Availability/Consultation | Bank.lean | D | ⚠️ Partial | Bank structure only |
| 12 | Failure Modes | Theorems.lean | A | ✅ Diagnoses | `no_revision_no_correction` |
| 13 | Access/Orphaning | — | D | 📝 Downstream | Kernel-external by design |
| 14 | Bubble Hygiene | StepSemantics.lean, Theorems.lean | A | ✅ Full | `tick_can_cause_staleness` |
| 15 | Explanatory Recipe | Diagnosability.lean, Theorems.lean | A | ✅ Full | `strip_reduces_diagnosability` |
| 16 | Corroboration | Agent/Corroboration.lean | A | ✅ Full | `corroboration_package` |
| 17 | Institutional | — | D | 📝 Paper-only | Not formalized |
| 18 | Domain Self-Correction | StepSemantics.lean | A | ✅ Theorem | `self_correcting_domain_permits_revision` |
| 19 | Conclusion | — | D | 📝 Paper-only | Not formalized |

**Legend:** ✅ Full | ⚠️ Partial/opaque | 📝 Kernel-external
**Tiers:** A=Proved | B=Conditional | C=Spec | D=Kernel-external (by design or paper-only)

---

## Detailed Mappings

### §1 Introduction — Forcing Commitments

**Paper Claim:** Eight commitments force the architecture.

**Tier:** A (Proved) — All 8 commitments are proved standalone theorems.

**Lean Artifacts:**

| Commitment | Theorem/Def | File:Line | Tier |
|------------|-------------|-----------|------|
| C1: Traction/Authorization split | `innovation_allows_traction_without_authorization` + `caveated_authorization_does_not_force_certainty` | Commitments.lean:129,159 | A |
| C2: No global ledger | `WorldCtx.no_ledger_tradeoff` | WorldCtx.lean | A |
| C3: S/E/V factorization | ~~`SEVFactorization`~~ (theorem; trivially provable) + `has_strong_SEV_factorization` (real localization constraint) | Commitments.lean / StepSemantics.lean | A/C |
| C4: Redeemability external | `redeemable` (def) + `path_route_exists` / `contact_was_made` / `verdict_discriminates` (opaque) | Commitments.lean:229 | C |
| C5: Export gating | `ExportGating` | Commitments.lean:321 | A |
| C6: Repair loop | `RepairLoopExists` | Commitments.lean:355 | A |
| C7: Header asymmetry | `header_stripping_produces_pathology` | Commitments.lean:998 | A |
| C8: Temporal validity | `TemporalValidity` | Commitments.lean:848 | A |

---

### §2 Core Split — Traction vs Authorization

**Paper Claim:** Traction is broader than authorization; many things have traction without being authorized.

**Tier:** A (Derived) — The core theorem is proved.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `Traction` | `structure` | Basic.lean | C |
| `Authorization` | `structure` | Basic.lean | C |
| `traction_broader_than_authorization` | `theorem` | Theorems.lean:2647 | A |
| `authorization_implies_traction` | `theorem` | Theorems.lean:2666 | A |

**Math:** $\text{Authorization}(x) \Rightarrow \text{Traction}(x)$ but $\neg(\text{Traction}(x) \Rightarrow \text{Authorization}(x))$

---

### §3 JTB Underspecified — Gettier

**Paper Claim:** Gettier cases are V-field failures; architecture routes them to specific diagnoses.

**Tier:** A (Derived) — Case-binding theorems are proved.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `GettierCase` | `structure` | Theorems.lean:335 | C |
| `gettier_is_V_failure` | `theorem` | Theorems.lean:395 | A |
| `canonical_gettier_is_gettier` | `theorem` | Theorems.lean:414 | A |
| `FakeBarnCase` | `structure` | Theorems.lean:468 | C |
| `fake_barn_is_E_failure` | `theorem` | Theorems.lean:513 | A |

---

### §4 The Ladder — Epistemic Stages

**Paper Claim:** Epistemic traction follows a five-stage ladder: Denial → Doubt → Ignorance → Belief → Certainty. Cost-sensitivity discriminates sub-Ignorance stages (Denial, Doubt) from post-Ignorance stages (Belief, Certainty). Entrenchment (Certainty + structural refusal to revise) is a pathological state that breaks safe withdrawal.

**Tier:** C (Spec/Interface) — Full five-stage enum with Entrenchment predicate.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `LadderStage` | `inductive` | Basic.lean:121 | C |
| `LadderStage.Denial` | `constructor` | Basic.lean:122 | C |
| `LadderStage.Doubt` | `constructor` | Basic.lean:123 | C |
| `LadderStage.Ignorance` | `constructor` | Basic.lean:124 | C |
| `LadderStage.Belief` | `constructor` | Basic.lean:125 | C |
| `LadderStage.Certainty` | `constructor` | Basic.lean:126 | C |
| `Entrenched` | `def` | Basic.lean:189 | C |
| `EntrenchedAgent` | `structure` | Theorems.lean:2756 | C |
| `deposit_no_longer_active` | `def` | Theorems.lean:2765 | C |
| `entrenchment_breaks_safe_withdrawal` | `theorem` | Theorems.lean:2784 | A |
| `entrenched_cannot_withdraw` | `theorem` | Theorems.lean:2806 | A |

> **Kernel note:** EpArch formalizes the ladder as a typed interface and boundary surface (`LadderStage`, `Entrenched`). Rich internal ladder dynamics — belief update rules, graded modulation, epistemic path-dependence — are intentionally outside the kernel to preserve agent agnosticism. Agents that do not operate on the full five-stage model remain first-class coordination participants.

---

### §5 Bubbles — Scoped Authorization

**Paper Claim:** Authorization is scoped to bubbles; cross-bubble transfer requires explicit export.

**Tier:** A (Derived) — Export requirements are proved from LTS semantics.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `Bubble` | `inductive` | Basic.lean | C |
| `Step.export_with_bridge` | `constructor` | StepSemantics.lean | C |
| `Step.export_revalidate` | `constructor` | StepSemantics.lean | C |
| `export_requires_header` | `theorem` | StepSemantics.lean:1476 | A |

---

### §6 The Bank — External Authorization

**Paper Claim:** The Bank provides the substrate for deposits, withdrawals, and lifecycle management.

**Tier:** A (Derived) — Gate requirements are proved.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `Validate_B`, `Accept_B`, `Challenge_B`, `Repair_B`, `Revoke_B`, `Restore_B`, `Export_B_C`, `Import_C` | `def` | Bank.lean | C |
| `canWithdrawAt` | `def` | StepSemantics.lean | A |
| `withdrawal_requires_three_gates` | `theorem` | StepSemantics.lean:1465 | A |
| `canWithdrawAt_iff_gates` | `theorem` | Theorems.lean:164 | A |

---

### §7 Validation (S, E, V)

**Paper Claim:** Validation factors into Source (S), Entailment (E), and Verification (V).

**Tier:** A (Derived) — Factorization enables legibility/identification theorems.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `Header` | `structure` | Header.lean | C |
| `Field` | `inductive` | Basic.lean:200 (`.S`, `.E`, `.V`, `.τ`, `.content`, `.provenance`) | C |
| `has_SEV_factorization` | `def` | StepSemantics.lean:934 | A |
| `factorization_enables_legibility` | `theorem` | StepSemantics.lean:970 | A |
| `factorization_enables_field_identification` | `theorem` | StepSemantics.lean:945 | A |
| `header_ext` | `theorem` | Header.lean:149 | A |
| `deposit_ext` | `theorem` | Header.lean:166 | A |
| `observational_completeness` | `theorem` | Header.lean:182 | A |
| `observational_completeness_full` | `theorem` | Header.lean:199 | A |

---

### §8 Redeemability — External Accountability

**Paper Claim:** Redeemability is external; consensus is not sufficient for knowledge.

**Tier:** A/C — C4a (redeemability external) is a design commitment (opaque evidence interface); C4b (consensus insufficient) is proved.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `redeemable` | `def` | Commitments.lean:229 | C |
| `path_route_exists` / `contact_was_made` / `verdict_discriminates` | `opaque` | Commitments.lean | C |
| `redeemability_requires_more_than_consensus` | `theorem` | Commitments.lean:981 | A |

---

### §9 Operating Modes — System States

**Paper Claim:** Systems have distinct operating modes (normal, degraded, recovery).

**Tier:** C (Spec/Interface) — Type only.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `OperatingMode` | `inductive` | Basic.lean:260 | C |
| `OperatingMode.normal` | `constructor` | Basic.lean | C |
| `OperatingMode.degraded` | `constructor` | Basic.lean | C |
| `OperatingMode.recovery` | `constructor` | Basic.lean | C |

---

### §10 Export — Strip Asymmetry

**Paper Claim:** Export strips headers; stripping is irreversible.

**Tier:** A (Derived) — Strip non-injectivity is proved.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `strip` | `def` | Header.lean/Theorems.lean | A |
| `no_strip_left_inverse` | `theorem` | Theorems.lean:1962 | A |
| `import_cannot_reconstruct` | `theorem` | Theorems.lean:1988 | A |
| `different_headers_same_strip` | `theorem` | Theorems.lean:1931 | A |
| `stripV_not_injective` | `theorem` | Theorems.lean:1277 | A |

**Math:** $\nexists f.\, f \circ \text{strip} = \text{id}$

---

### §11 Availability vs Consultation — Access Patterns

**Paper Claim:** Availability (can access) differs from consultation (do access); access semantics matter.

**Tier:** D (Future) — Partial formalization only.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `Bank` | `structure` | Bank.lean:59 | C |
| `knowledge_B` | `def` | Bank.lean | A |
| `deposited` | `def` | Bank.lean | A |
| `hasDeposit` | `def` | Bank.lean | A |

**Status:** The Availability/Consultation distinction is conceptual in the paper but not fully formalized. Only Bank structure exists.

---

### §12 Failure Modes — Competition Gate

**Paper Claim:** Self-correction requires revision capability.

**Tier:** A (Derived) — Necessity theorems are proved from LTS semantics.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `no_revision_no_correction` | `theorem` | StepSemantics.lean:807 | A |
| `self_correction_requires_revision` | `theorem` | StepSemantics.lean:844 | A |
| `self_correcting_domain_permits_revision` | `theorem` | StepSemantics.lean:878 | A |
| `prohibits_revision` | `def` | StepSemantics.lean:595 | A |
| `demonstratesSelfCorrection` | `def` | StepSemantics.lean | A |

**Math:** $\text{prohibitsRevision}(s) \Rightarrow \neg\exists t.\, \text{SelfCorrects}(t)$

---

### §14 Bubble Hygiene — Temporal Validity

**Paper Claim:** Deposits have temporal validity (τ); staleness blocks operations.

**Tier:** A (Derived) — Staleness blocking is proved.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `τ_valid` | `def` | StepSemantics.lean:152 | A |
| `Stale` | `def` | Theorems.lean:2360 | A |
| `stale_blocks_withdrawal` | `theorem` | Theorems.lean:2379 | A |
| `tick_can_cause_staleness` | `theorem` | Theorems.lean:2398 | A |
| `withdrawal_requires_fresh` | `theorem` | Theorems.lean:2367 | A |

---

### §15 Explanatory Recipe — Diagnosability

**Paper Claim:** Header stripping reduces diagnosability; fewer fields → coarser repair.

**Tier:** A (Derived) — Diagnosability monotonicity is proved.

**Lean Artifacts (v8 Diagnosability module):**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `AllFields` | `def` | Diagnosability.lean | A |
| `StrippedFields` | `def` | Diagnosability.lean | A |
| `ObservableFields` | `def` | Diagnosability.lean | A |
| `diagnosability` | `def` | Diagnosability.lean | A |
| `diagnosability_full` | `theorem` | Diagnosability.lean | A |
| `diagnosability_stripped` | `theorem` | Diagnosability.lean | A |
| `strip_reduces_diagnosability` | `theorem` | Diagnosability.lean | A |
| `stripped_no_field_repair` | `theorem` | Diagnosability.lean | A |
| `repair_requires_observability` | `theorem` | Diagnosability.lean | A |

**Bridge to v7:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `FieldCount_Full` | `def` | Theorems.lean | A |
| `FieldCount_Stripped` | `def` | Theorems.lean | A |
| `strip_reduces_field_count` | `theorem` | Theorems.lean:2100 | A |
| `fewer_fields_coarser_repair` | `theorem` | Theorems.lean:2113 | A |

---

### §16 Multi-Agent Corroboration

**Paper Claim:** No-Single-Point-of-Failure goals require multi-source attestation; corroboration fails under common-mode (bubble infection).

**Tier:** A (Derived) — Necessity and failure theorems are proved.

**Lean Artifacts (Agent/Corroboration.lean):**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `SingleSourceAttack` | `structure` | Corroboration.lean | C |
| `CommonModeAttack` | `structure` | Corroboration.lean | C |
| `SingleSourceAcceptance` | `def` | Corroboration.lean | C |
| `HasKWitnesses` | `def` | Corroboration.lean | C |
| `KOfNIndependentAcceptance` | `def` | Corroboration.lean | C |
| `IndependenceBounded` | `def` | Corroboration.lean | C |
| `HonestImpliesTrue` | `def` | Corroboration.lean | C |
| `single_source_can_accept_false` | `theorem` | Corroboration.lean | A |
| `no_spof_requires_multi_source` | `theorem` | Corroboration.lean | A |
| `common_mode_breaks_naive_corroboration` | `theorem` | Corroboration.lean | A |
| `two_of_two_fails_under_common_mode` | `theorem` | Corroboration.lean | A |
| `common_mode_requires_diversity` | `theorem` | Corroboration.lean | A |
| `k_of_n_suffices_under_independence` | `theorem` | Corroboration.lean | A |
| `corroboration_package` | `theorem` | Corroboration.lean | A |

**Theorem Summary:**

| Theorem | Role | Statement |
|---------|------|-----------|
| T1: `no_spof_requires_multi_source` | Necessity | NoSPoF goal → ¬SingleSourceAcceptance |
| T2: `k_of_n_suffices_under_independence` | Sufficiency | k > t → k-of-n works |
| T3: `common_mode_breaks_naive_corroboration` | Failure | CommonMode → witnesses fail together |
| T4: `common_mode_requires_diversity` | Diversity | CommonMode → ¬IndependenceBounded |

---

## Lottery Paradox (Cross-Section)

**Paper Claim:** Lottery paradox dissolved by Candidate/Deposited distinction.

**Tier:** A (Derived) — Dissolution is proved from type distinction.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `LotterySituation` | `structure` | Theorems.lean:539 | C |
| `LotteryIsTypeError` | `theorem` | Theorems.lean:581 | A |
| `ConfabulationCase` | `structure` | Theorems.lean:607 | C |
| `confabulation_is_type_error` | `theorem` | Theorems.lean:626 | A |
| `credence_does_not_auto_close` | `theorem` | Theorems.lean:2562 | A |
| `status_distinction_blocks_lottery` | `theorem` | Theorems.lean:2591 | A |
| `lottery_paradox_dissolved_architecturally` | `theorem` | Theorems.lean:2692 | A |
| `candidate_blocks_withdrawal` | `theorem` | Theorems.lean:2527 | A |

---

## Tier B: Obligation Theorems (Conditional)

**Paper Claim:** Under world assumptions W, mechanisms M are forced.

**Tier:** B (Conditional) — All theorems have shape `W_* → Mechanism`.

### Attack & Collapse Theorems

| Theorem | W-Bundle | Conclusion | File:Line |
|---------|----------|------------|-----------|
| `spoofed_V_blocks_path_of_W` | `W_spoofedV` | V-spoofing blocks verification | AdversarialObligations.lean:94 |
| `ddos_causes_verification_collapse_of_W` | `W_ddos` | DDoS → collapse | AdversarialObligations.lean:153 |
| `collapse_causes_centralization_of_W` | `W_collapse_centralization` | Collapse → centralization | AdversarialObligations.lean:182 |
| `lies_scale_of_W` | `W_lies_scale` | Lies scale with agent count | AdversarialObligations.lean:213 |
| `rolex_ddos_structural_equivalence_of_W` | `W_rolex_ddos` | Same exploit at different scales | AdversarialObligations.lean:252 |
| `ddos_to_centralization_of_W` | Composed | DDoS → centralization (composed) | AdversarialObligations.lean:269 |

### Countermeasure Theorems

| Theorem | W-Bundle | Countermeasure | File:Line |
|---------|----------|----------------|-----------|
| `cheap_validator_blocks_V_attack_of_W` | `W_cheap_validator` | CheapValidator blocks V-attack | AdversarialObligations.lean:334 |
| `trust_bridge_blocks_V_attack_of_W` | `W_trust_bridge` | TrustBridge blocks V-attack | AdversarialObligations.lean:365 |
| `reversibility_neutralizes_τ_of_W` | `W_reversibility` | Reversibility neutralizes τ | AdversarialObligations.lean:404 |
| `E_inclusion_closes_expertise_gap_of_W` | `W_E_inclusion` | E-inclusion closes expertise gap | AdversarialObligations.lean:444 |
| `cheap_constraint_blocks_V_spoof_of_W` | `W_cheap_constraint` | CheapConstraint blocks V-spoof | AdversarialObligations.lean:476 |

---

## Health Goals — Necessity Theorems (Tier A)

**Paper Claim:** Health goals force capability requirements; mechanisms are necessary.

**Tier:** A (Derived) — Health goals are definitional; necessity theorems are proved.

### Health Goal Definitions (EpArch/Health.lean)

| Goal | Definition | File:Line |
|------|------------|-----------|
| `SafeWithdrawalGoal` | Withdrawals succeed when all gates pass | Health.lean:55 |
| `ReliableExportGoal` | Exports preserve validity across bubbles | Health.lean:63 |
| `CorrigibleLedgerGoal` | Existence + soundness conjunction: revision capability required | Health.lean:76 |
| `SoundDepositsGoal` | Deposits can be verified | Health.lean:86 |
| `SelfCorrectionGoal` | System can self-correct errors | Health.lean:95 |
| `SelfCorrectingSystem` | Active self-correction: `SelfCorrectionGoal ∧ ∃ B, selfCorrects B` | Health.lean:104 |

### Capability Predicates

| Capability | Definition | File:Line |
|------------|------------|-----------|
| `HasSubmitCapability` | Can submit new deposits | Health.lean:114 |
| `HasRevisionCapability` | Can revise existing deposits | Health.lean:119 |
| `HasVerificationCapability` | Can verify deposits | Health.lean:123 |
| `HasSelfCorrectionCapability` | Has revision + detection | Health.lean:128 |

### Necessity Theorems (PROVED)

| Theorem | Premise | Conclusion | File:Line |
|---------|---------|------------|-----------|
| `corrigible_needs_revision` | `CorrigibleLedgerGoal` (single premise) | `HasRevisionCapability` | Health.lean:144 |
| `self_correction_needs_revision` | `SelfCorrectingSystem` (single premise) | `HasRevisionCapability` | Health.lean:153 |
| `sound_deposits_needs_verification` | `SoundDepositsGoal` | `HasVerificationCapability` | Health.lean:162 |

---

## Revision Safety — Extension Guarantees

**Paper Claim:** Extensions and strengthening cannot break existing results; incompleteness is safe.

**Tier:** A (Derived) — All three guarantees are fully proved.

**Paper Citations:** §7.0 (A.R1–A.R3), §9.6 (A.R1–A.R3)

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `premise_strengthening` | `theorem` | RevisionSafety.lean | A |
| `transport_core` | `theorem` | RevisionSafety.lean | A |
| `safe_extension_preserves` | `theorem` | RevisionSafety.lean | A |
| `CoreSig` | `structure` | RevisionSafety.lean | C |
| `CoreOps` | `structure` | RevisionSafety.lean | C |
| `Compatible` | `structure` | RevisionSafety.lean | C |
| `RevisionSafeExtension` | `structure` | RevisionSafety.lean | C |
| `PaperFacing` | `def` | RevisionSafety.lean | A |
| `forget` | `def` | RevisionSafety.lean | A |
| `goodExtension_compatible` | `theorem` | RevisionSafety.lean | A |
| `badExtension_incompatible_witness` | `theorem` | RevisionSafety.lean | A |

---

## Concrete Model — Non-Vacuity

**Paper Claim:** The axioms are satisfiable; success forces Bank primitives.

**Tier:** A (Derived) — Satisfiability is witnessed constructively; minimality is proved.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `concreteBubble` | `def` | ConcreteLedgerModel.lean:978 | A |
| `concreteAgent` | `def` | ConcreteLedgerModel.lean:981 | A |
| `concrete_trace` | `def` | ConcreteLedgerModel.lean:1137 | A |
| `all_commitments_satisfiable` | `theorem` | ConcreteLedgerModel.lean:559 | A |
| `concrete_satisfies_all_properties` | `theorem` | ConcreteLedgerModel.lean:~900 | A |
| `concrete_has_*` | `theorem` family | ConcreteLedgerModel.lean:841-866 | A |
| `concrete_forcing_embedding` | `def` | ConcreteLedgerModel.lean | A |
| `concrete_structurally_forced` | `theorem` | ConcreteLedgerModel.lean | A |
| `concrete_structural_convergence` | `theorem` | ConcreteLedgerModel.lean | A |
| `existence_under_constraints_structural` | `theorem` | Feasibility.lean | A |
| `bundled_structure_forces_bank_primitives` | `theorem` | Feasibility.lean | A |
| `joint_feasible` | `theorem` | Feasibility.lean | A |
| `ConcreteSuccessfulSystem` | `def` | Realizer.lean | A |
| `ConcreteRealizer` | `def` | Realizer.lean | A |

**Headline Theorem:** `existence_under_constraints_structural` packages:
1. **Non-vacuity** — a working system exists
2. **Success** — it is structurally forced and satisfies all properties
3. **Forced primitives** — Bank primitives are necessary (via `convergence_structural`)

**Status:** Zero axioms in ConcreteLedgerModel.lean, Realizer.lean, Feasibility.lean (fully constructive).

---

## Paper Appendix — Existence Under Constraints

**Paper Claim:** The formalization proves existence of a successful system AND that success forces Bank primitives.

**Tier:** A (Derived) — The headline theorem is fully proved.

**Lean Artifacts:**

| Artifact | Type | File:Line | Tier |
|----------|------|-----------|------|
| `structural_goals_force_bank_primitives` | `theorem` | Feasibility.lean | A |
| `existence_under_constraints_structural` | `theorem` | Feasibility.lean | A |
| `existence_under_constraints_embedding` | `theorem` | Feasibility.lean | A |
| `bundled_structure_forces_bank_primitives` | `theorem` | Feasibility.lean | A |
| `kernel_world_forces_bank_primitives` | `theorem` | Feasibility.lean | A |
| `SuccessfulSystem` | `structure` | Realizer.lean | C |
| `ConcreteSuccessfulSystem` | `def` | Realizer.lean | A |
| `convergence_structural` | `theorem` | Convergence.lean | A |

**Math Form (structural path):**

$$\exists W : \text{WorkingSystem}.\, \text{StructurallyForced}(W) \land \text{SatisfiesAllProperties}(W) \land \text{containsBankPrimitives}(W)$$

**Math Form (embedding path):**

$$\exists W : \text{WorkingSystem}.\, \text{ForcingEmbedding}(W) \land \text{SatisfiesAllProperties}(W) \land \text{containsBankPrimitives}(W)$$

**Supporting Theorem (Minimality — structural path):**

$$\forall W.\, \text{StructurallyForced}(W) \to \text{SatisfiesAllProperties}(W) \to \text{containsBankPrimitives}(W)$$

**Structural chain:** `ForcingEmbedding` → `embedding_to_structurally_forced` → `convergence_structural` → `containsBankPrimitives`

---

## Paper Appendix — Meta-Status (Falsifiable / Not Fully Authorizable)

**Paper Claim:** The theory floor is falsifiable, not fully authorizable from observations, and safe to use on credit.

**Tier:** A (Derived) — All theorems fully proved.

**Lean Artifacts:**

| Artifact | Type | File | Paper Claim |
|----------|------|------|-------------|
| `meta_status_proof_pack` | `theorem` | Meta/FalsifiableNotAuthorizable.lean | Headline: P1 ∧ P2 ∧ P3 |
| `theory_floor_satisfiable` | `theorem` | Meta/FalsifiableNotAuthorizable.lean | Floor is consistent |
| `theory_floor_falsifiable` | `theorem` | Meta/FalsifiableNotAuthorizable.lean | Countercontext exists |
| `witness_not_fully_authorizable` | `theorem` | Meta/FalsifiableNotAuthorizable.lean | Credit required |
| `credit_safe_under_extension` | `theorem` | Meta/FalsifiableNotAuthorizable.lean | Non-collapse |
| `witness_theory_core_not_determined` | `theorem` | Meta/TheoryCoreClaim.lean | theory_core underdetermined |
| `theory_core_token_not_determined` | `def` | Meta/TheoryCoreClaim.lean | Universal schema |

---

## Kernel-External Items (Tier D)

These are not missing features. The distinction matters: items here are excluded by deliberate architectural choice, not by planning shortfall.

### Out of scope for the kernel by design

Excluded to preserve agent agnosticism and heterogeneous applicability:

| Paper Concept | Section | Reason |
|---------------|---------|--------|
| Full Ladder dynamics (belief update rules, graded modulation) | §4 | Requires agent-internal belief model — baking it in would break agent agnosticism |
| Rich access/consultation semantics | §11 | Agent-specific; the kernel formalizes the typed interface surface only |

### Paper-only / narrative-only

These sections carry philosophical argument or motivation not intended as kernel theorems:

| Paper Concept | Section | Notes |
|---------------|---------|-------|
| Institutional contexts | §17 | Narrative framing; no kernel theorem target |
| Domain-level sociological self-correction | §18 | Broader sociological claim in the paper; `self_correcting_domain_permits_revision` captures the formal core |
| Conclusion | §19 | Narrative synthesis only |

### Possible downstream extensions

Implementable as agent-specific overlays or application layers, but not part of the kernel:

| Paper Concept | Section | Notes |
|---------------|---------|-------|
| Orphaned deposit recovery | §13 | State-tracking complexity belongs to application layers |
| Domain-level correlated adversaries (graded independence) | — | Binary case is formalized; graded refinement is a downstream overlay |

---

## Why Mechanisms Are Mandatory — Agent Layer

**File:** `EpArch/Agent.lean`

**Paper Claim:** The architecture's mechanisms aren't optional—they're forced by agent constraints.

**Tier:** A (Derived) — Necessity theorems are proved from agent constraints + health goals.

### The Pattern

```
AgentConstraints + SystemHealth goal → NeedsMechanism
```

Agent constraints (bounded verification, fallibility, PRP) combined with system health goals (safe withdrawal, sound deposits, reliable export) **force** specific mechanisms to exist.

### Lean Artifacts

| Theorem | Premise (AgentConstraints) | Goal (SystemHealth) | Mechanism Forced | Tier |
|---------|---------------------------|---------------------|------------------|------|
| `safe_withdrawal_needs_reversibility` | τ-bounded agents | SafeWithdrawal | Reversibility | A |
| `sound_deposits_need_cheap_validator` | Limited audit + PRP | SoundDeposits | CheapValidator | A |
| `reliable_export_needs_gate` | Fallible observation | ReliableExport | ExportGate | A |

### PRP Theorems (Permanent Redeemability Pressure)

**Tier:** A (Derived)

PRP captures "agents are permanently challenged by redeemability for as long as they exist."

| Theorem | Statement | File:Line | Tier |
|---------|-----------|-----------|------|
| `no_global_closure_of_PRP` | PRP prevents finite verification closure | Agent/Constraints.lean:122 | A |
| `needs_revision_of_PRP` | PRP implies mandatory revision hooks | Agent/Constraints.lean:144 | A |
| `needs_scoping_of_PRP` | PRP forces bounded audit surfaces | Agent/Constraints.lean:156 | A |

### Containment Invariants

**Tier:** A (Derived) — Proved from LTS step semantics.

Agent faults (lies, omissions, misreports) cannot crash the system:

| Theorem | Invariant | Proof Method | Tier |
|---------|-----------|--------------|------|
| `truth_invariant_preserved` | Agent actions cannot flip truth | Trace induction | A |
| `gate_invariant_preserved` | Agent actions cannot disable gate | Trace induction | A |
| `agent_containment` | Combined containment | Composition | A |

**Key insight:** These are **proved** from the Agent LTS step semantics, not asserted as axioms. The containment follows from how agent actions are defined, not from world assumptions.

### Why This Matters for the Paper

The paper's central claim is that the architecture is **forced**, not chosen. The Agent layer demonstrates this by:

1. Stating agent constraints (what agents are like)
2. Stating system health goals (what we want)
3. Proving mechanisms are necessary (what must exist)

This closes the argument: given realistic agents and desired properties, you **cannot avoid** having reversibility, cheap validators, and export gates.

---

## Quick Reference: Key Theorem Locations

| Paper Claim | Lean Theorem | Location | Tier |
|-------------|--------------|----------|------|
| Existence under constraints | `existence_under_constraints_structural` | Feasibility.lean | A |
| Bank primitives forced (structural) | `bundled_structure_forces_bank_primitives` | Feasibility.lean | A |
| Self-correction requires revision | `no_revision_no_correction` | StepSemantics.lean:807 | A |
| Strip has no left inverse | `no_strip_left_inverse` | Theorems.lean:1962 | A |
| Lottery dissolved | `lottery_paradox_dissolved_architecturally` | Theorems.lean:2692 | A |
| Stale blocks withdrawal | `stale_blocks_withdrawal` | Theorems.lean:2379 | A |
| Gettier is V-failure | `gettier_is_V_failure` | Theorems.lean:395 | A |
| Diagnosability monotonic | `strip_reduces_diagnosability` | Diagnosability.lean | A |
| Model is satisfiable | `all_commitments_satisfiable` | ConcreteLedgerModel.lean:559 | A |
| Entrenchment breaks withdrawal | `entrenchment_breaks_safe_withdrawal` | Theorems.lean:2784 | A |
| Deposit observational completeness | `observational_completeness_full` | Header.lean:199 | A |
| Deposit extensionality | `deposit_ext` | Header.lean:166 | A |

---

## Certification Engine — Configurable Cluster Surface (Buckets 27–28)

**Paper Role:** Proves that the theorem corpus is modular in a strong, machine-checkable sense: any sub-combination of constraints, health goals, and world bundles can be selected, and the engine delivers a `CertifiedProjection` carrying genuine proof witnesses for every enabled cluster.

### Bucket 27 — Modularity Meta-Theorem (`Meta/Modular.lean`)

| Artifact | Type | File | Tier |
|----------|------|------|------|
| `ConstraintSubset` | `structure` | Minimality.lean | A |
| `PartialWellFormed W S` | `def` | Minimality.lean | A |
| `allConstraints` / `noConstraints` | `def` | Minimality.lean | A |
| `modular` | `theorem` | Meta/Modular.lean | A |

**Key result:** `modular : ∀ S W, PartialWellFormed W S → projection_valid S W` — dropping constraint X = setting `S.X := false`; the X-conjunct becomes vacuously true.

### Bucket 28 — Certification Engine (`Meta/ClusterRegistry.lean` + `Meta/Config.lean`)

**Registry / routing** (`Meta/ClusterRegistry.lean`):

| Artifact | Type | Purpose |
|----------|------|---------|
| `ClusterTag` | `inductive` | 29 cluster tags (Tiers 2–4 + world + meta-modular + lattice) |
| `EnabledConstraintCluster` … `EnabledLatticeCluster` | `inductive` (×6) | Per-family sub-inductives with `toClusterTag` |
| `allConstraintClusters` … `allLatticeClusters` | `def` (×6) | Per-family canonical lists |
| `allClusters` | `def` | All 29 tags derived from the 6 lists |
| `clusterEnabled` | `def` | `EpArchConfig → ClusterTag → Bool`; meta-modular and lattice always enabled |
| `clusterDescription` | `def` | Human-readable one-line description per tag |

**Witness carriers / certification** (`Meta/Config.lean`):

| Artifact | Type | Purpose |
|----------|------|---------|
| `MetaModularWitness` | `inductive` | Indexed proof carrier for 1 constraint-modularity cluster |
| `LatticeWitness` | `inductive` | Indexed proof carrier for 3 lattice-stability clusters |
| `metaModularWitness` / `latticeWitness` | `def` | Proof-delivering functions for each family |
| `CertifiedProjection` | `structure` | Full proof bundle: enabled clusters + all witness families + filtered enabled lists |
| `certify` | `def` | `EpArchConfig → CertifiedProjection cfg` |
| `mem_enabledMetaModularWitnesses_of_enabled` | `theorem` | Completeness: enabled cluster → witness in filtered list |
| `mem_enabledLatticeWitnesses_of_enabled` | `theorem` | Completeness: enabled cluster → witness in filtered list |
| `cluster_meta_modular` … `cluster_lattice_pack` | `theorem` (×4) | Named proof witnesses for all 4 new clusters (Phase F) |

---

### Bucket 29 — Lean Kernel Instantiation (`Meta/LeanKernelModel.lean`)

Self-referential: Lean's own type-checking kernel instantiated as both a `WorldCtx` (sorry / heartbeat / proof irrelevance) and a `WorkingSystem` (all six Bank primitives grounded in kernel features). Not tied to a specific paper section; serves as a proof-of-concept instantiation and meta-theorem companion.

| Artifact | Type | File | Tier |
|----------|------|------|------|
| `LeanKernelCtx` | `def` | Meta/LeanKernelModel.lean | A |
| `LeanWorkingSystem` | `def` | Meta/LeanKernelModel.lean | A |
| `holds_W_lies_possible` / `holds_W_bounded_verification` / `holds_W_partial_observability` | `theorem` (×3) | Meta/LeanKernelModel.lean | A |
| `lean_kernel_satisfies_bundles` / `lean_kernel_theory_floor` / `lean_kernel_no_tradeoff` / `lean_is_eparch_world` | `theorem` (×4) | Meta/LeanKernelModel.lean | A |
| `lean_has_bubbles` … `lean_has_redeemability` | `theorem` (×6) | Meta/LeanKernelModel.lean | A |
| `lean_implements_bank_primitives` / `lean_partial_wellformed` / `lean_satisfies_all_properties` / `lean_structurally_forced` / `lean_structural_convergence` | `theorem` (×5) | Meta/LeanKernelModel.lean | A |
| `lean_namespace_requires_scope_separation` / `lean_no_flat_namespace_resolver` / `lean_has_bubbles_grounded` | `theorem` (×3) | Meta/LeanKernelModel.lean | A |
| `lean_kernel_forces_bank_primitives` / `lean_kernel_existence` | `theorem` (×2) | Meta/LeanKernelModel.lean | A |

**Key result:** `lean_kernel_existence` — joint two-layer existential: `(∃ C : WorldCtx, …) ∧ (∃ W : WorkingSystem, PartialWellFormed W allConstraints ∧ StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W)`. Self-referential: type-checked by the kernel it models.

---

## Export Path

All paper-facing artifacts are exported via:

```
EpArch/PaperFacing.lean → MainPaper.lean
```

**Rule:** If a theorem is not exported through `PaperFacing.lean`, it is not paper-facing.

**Verification:** Run `lake build MainPaper` to ensure all paper-facing exports compile.

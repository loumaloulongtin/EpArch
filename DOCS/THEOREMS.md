# Theorem Inventory

This document catalogs **712** proved theorems in the formalization, organized by argumentative role. The count covers all named `theorem` declarations in the EpArch namespace (case-sensitive keyword match, excluding example lines inside doc comments).

**What the architecture claims:** Decentralized epistemic authorization requires specific structural mechanisms — a lifecycle with type-separated stages, header-preserving export, a revision loop, temporal validity, and a Bank substrate. These aren't design preferences; they are forced by the combination of agent constraints and system health goals.

**What this document is:** A bucketed theorem index (Buckets 1–29), grouped by the architectural claim each cluster supports. Each bucket names the Lean file, the key theorems, and the claim each cluster establishes. This file covers the full proof burden distribution across the repo. For deeper exposition of any area, the standalone DOCS files are the right place. For the modularity story — what survives disabling a constraint, health goal, or world bundle, and by what formal mechanism — see [MODULARITY.md](MODULARITY.md).

**Tier labels:** **A** = proved unconditionally, **B** = conditional on a W-bundle premise, **C** = design commitment (context-bundled structural assumption).

**All theorems are fully proved** — zero `sorry`, zero `axiom` declarations. See [AXIOMS.md](AXIOMS.md) for the current assumption boundary.

## Notation Dictionary

| Lean | Math | Description |
|------|------|-------------|
| `Trace.hasRevision t` | $\exists a \in t.\, a \in \{\text{Challenge}, \text{Revoke}\}$ | Trace contains revision action |
| `demonstratesSelfCorrection t i` | $\text{status}_s(i) = \text{Deposited} \land \text{status}_{s'}(i) = \text{Revoked}$ | Deposit transitions to revoked |
| `prohibits_revision s` | $\forall t : \text{Trace}(s, -).\ t.\text{hasRevision} = \text{false}$ | All traces from s contain no revision action |
| `diagnosability(h)` | $|\text{ObservableFields}(h)|$ | Cardinality of observable fields |
| `canTargetRepair f h` | $f \in \text{ObservableFields}(h)$ | Field is observable for repair |
| `τ_valid clock τ` | $\tau \leq \text{clock}$ | Timestamp within validity window |
| `strip d` | $\pi_{\text{content}}(d)$ | Project deposit to content only |

---

## Bucket 1: Lifecycle & Type-Separation

**Role:** Establishes that different deposit statuses create different operational affordances.

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `candidate_blocks_withdrawal` | Theorems/Corners.lean | Candidate status blocks withdrawal | Lottery dissolution |
| `withdrawal_requires_deposited` | Theorems/Corners.lean | Must be Deposited to withdraw | Bank gates |
| `submit_produces_candidate` | Theorems/Corners.lean | Submit creates Candidate status | Lifecycle |
| `traction_broader_than_authorization` | Theorems/Corners.lean | Traction âŠƒ Authorization | Core split |
| `authorization_implies_traction` | Theorems/Corners.lean | Authorization → Traction | One direction |

### Math Form

$$\text{Candidate}(d) \Rightarrow \neg\text{canWithdraw}(d)$$

$$\text{canWithdraw}(d) \Rightarrow \text{Deposited}(d) \land \text{ACL}(a,d) \land \tau\text{-valid}(d)$$

---

## Bucket 2: Competition Gate Cluster (Revision ⇔ Self-Correction)

**Role:** The central forcing constraint — self-correction requires revision capability.

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `no_revision_no_correction` | StepSemantics.lean | No revision → no self-correction | Competition gate |
| `self_correction_requires_revision` | StepSemantics.lean | Self-correction → revision occurred | Forward direction |
| `self_correcting_domain_permits_revision` | StepSemantics.lean | Self-correcting domain → permits revision | Domain level |
| `repair_requires_prior_challenge` | Theorems/Withdrawal.lean | Repair presupposes challenge | Repair loop |
| `repair_enforces_revalidation` | Theorems/Withdrawal.lean | Repair requires fresh validation | No silent fix |
| `frozen_canon_no_revocation` | Theorems/Corners.lean | Single restricted step: ¬Revoked before → ¬Revoked after | Corner 6: Frozen canon |
| `frozen_canon_no_revocation_trace` | Theorems/Corners.lean | allRestrictedTrace t → ¬Revoked at start → ¬Revoked after full trace (trace induction over all steps) | Corner 6: Frozen canon (full trace) |

### Math Form

$$\text{prohibitsRevision}(s) \Rightarrow \neg\exists t.\, \text{demonstratesSelfCorrection}(t)$$

$$\text{SelfCorrecting}(D) \Rightarrow \text{permitsRevision}(D)$$

---

## Bucket 3: Export/Strip Asymmetry

**Role:** Header stripping is information-destroying; import cannot reconstruct.

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `no_strip_left_inverse` | Theorems/Strip.lean | ¬∃ f. f âˆ˜ strip = id | Irreversibility |
| `strip_not_injective_if` | Theorems/Strip.lean | (d₁ ≠ d₂) ∧ (strip d₁ = strip d₂) → ¬∀ x y, strip x = strip y → x = y (negated injectivity, not just existential re-wrap) | Non-injectivity |
| `import_cannot_reconstruct` | Theorems/Strip.lean | Import doesn't restore header | No reconstruction |
| `different_headers_same_strip` | Theorems/Strip.lean | h₁ ≠ h₂ → strip(h₁) = strip(h₂) | Non-injectivity |
| `different_headers_different_deposits` | Theorems/Strip.lean | Different headers → different deposits | Provenance identity |
| `strip_loses_header_info` | Theorems/Strip.lean | Strip removes V field | Information loss |
| `content_eq_not_implies_deposit_eq` | Theorems/Strip.lean | Same content ≠ same deposit | Provenance matters |
| `provenance_matters` | Theorems/Strip.lean | Different provenance → different deposits | Identity |

### stripV Properties

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `stripV_irreversible` | Theorems/Strip.lean | ∃ p1 ≠ p2 in Provenance → ¬∃ f. f âˆ˜ stripV = id (requires non-trivial Provenance type) | V-strip irreversibility |
| `stripV_idempotent` | Theorems/Strip.lean | stripV(stripV(x)) = stripV(x) | Idempotency |
| `stripV_preserves_claim` | Theorems/Strip.lean | stripV preserves the claim | Content preserved |

### Export Visibility (Corner 9)

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `export_creates_visibility` | Theorems/Corners.lean | Export step → deposit visible in target bubble | Export semantics |
| `export_creates_B2_deposit` | Theorems/Corners.lean | Export step → concrete deposit record in target ledger (single premise) | Deposit creation |
| `export_ignores_target_acl` | Theorems/Corners.lean | Export fires without ACL check on target | ACL gap at boundary |

### Math Form

$$\neg \exists f : \text{Stripped} \to \text{Full}.\, f \circ \text{strip} = \text{id}$$

$$h_1 \neq h_2 \land \text{claim}(h_1) = \text{claim}(h_2) \Rightarrow \text{strip}(h_1) = \text{strip}(h_2)$$

---

## Bucket 4: Diagnosability (Observability Monotonicity)

**Role:** Header stripping reduces diagnosability; fewer observable fields → coarser repair.

### Core Theorems (Diagnosability.lean)

| Theorem | Statement | Claim |
|---------|-----------|-------------|
| `diagnosability_full` | Full deposits: diagnosability = 6 | Full observability |
| `diagnosability_stripped` | Stripped deposits: diagnosability = 0 | Zero observability |
| `strip_reduces_diagnosability` | strip → diagnosability decreases | Monotonicity |
| `stripped_no_field_repair` | Stripped can't target any field | Coarse repair |
| `full_can_repair_any` | Full can target any field | Surgical repair |
| `repair_requires_observability` | Repair granularity = observable fields | Equivalence |

### Bridge Theorems (Theorems/Headers.lean)

| Theorem | Statement | Claim |
|---------|-----------|-------------|
| `strip_reduces_field_count` | FieldCount stripped < full | Field count |
| `fewer_fields_coarser_repair` | Fewer fields → coarser repair | Repair quality |
| `sev_refines_stripped` | SEV partitions refine stripped | Refinement |
| `stripped_not_implies_sev` | Stripped âŠ„ SEV distinction | Asymmetry |

### Math Form

$$\text{diagnosability}(\text{full}) = 6 > 0 = \text{diagnosability}(\text{stripped})$$

$$f \notin \text{ObservableFields}(d) \Rightarrow \neg\text{canTargetRepair}(f, d)$$

### Field-Localization Bridge (StepSemantics.lean)

| Theorem | Statement | Claim |
|---------|-----------|-------------|
| `factorization_enables_field_identification` | Broken field is contained in the 6-field enum {S,E,V,τ,red,acl} | Field enum completeness |
| `factorization_enables_legibility` | Deposited deposit with a broken field → Legible | Legibility |
| `strong_sev_localizes_to_core_fields` | Strong SEV factorization → broken field âˆˆ {S,E,V} | Strong SEV → core-field localization |
| `all_challenges_field_specific` | All challenges target one of 6 canonical fields | Field specificity |
| `headers_enable_field_diagnosis` | depositHasHeader → challenge is field-specific | Header enables diagnosis |
| `header_enables_efficient_resolution` | depositHasHeader → efficient resolution via field targeting | Header efficiency |
| `headers_improve_localization` | depositHasHeader → localization_score = 1 | Optimal localization |

### Diagnosability Metric Theorems (Theorems/Headers.lean)

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `field_checkable_iff_header` | Theorems/Headers.lean | field_checkable s d_idx f ↔ depositHasHeader s d_idx (Field param is universally free) | Checkability ≡ header presence |
| `harder_without_headers` | Theorems/Headers.lean | ¬depositHasHeader → ¬field_checkable (structural; any field) | Stripped strictly harder |
| `header_stripped_harder` | Theorems/Headers.lean | header_stripped → systematically_harder | Header effect (dispute level) |
| `header_improves_diagnosability` | Theorems/Headers.lean | depositHasHeader → field_checkable (positive direction, dual to harder_without_headers) | Header → field checkable |
| `header_localization_link` | Theorems/Headers.lean | depositHasHeader → challenge_is_field_specific ∧ field_checkable | Header → localization |
| `diagnose_finds_broken` | Theorems/Withdrawal.lean | Sound diagnosis oracle finds broken field | Diagnostic completeness |

### Diagnosability Coupling Theorems (Theorems/Strip.lean)

Bridge theorems coupling the Diagnosability.lean and Theorems/Strip.lean metric systems:

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `fieldcount_full_eq_diagnosability` | Theorems/Strip.lean | FieldCount_Full = diagnosability true | Bridge: field-count ↔ score |
| `stripped_diagnosability_is_zero` | Theorems/Strip.lean | diagnosability false = 0 | Bridge: stripped score = 0 |
| `v8_implies_v7_strip_reduces` | Theorems/Strip.lean | v8 hard → v7 field-count reduction | Bridge: v8 ⇒ v7 |
| `stripped_repair_must_be_coarse` | Theorems/Strip.lean | ∀ f, ¬canTargetRepair false f | Bridge: coarse repair (alias stripped_no_field_repair) |
| `full_repair_can_be_surgical` | Theorems/Strip.lean | ∀ f, canTargetRepair true f | Bridge: surgical repair (alias full_can_repair_any) |

---

## Bucket 5: τ (Temporal Validity)

**Role:** Time creates pressure for maintenance; staleness blocks operations.

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `stale_blocks_withdrawal` | Theorems/Corners.lean | Stale deposits can't withdraw | Hygiene |
| `tick_can_cause_staleness` | Theorems/Corners.lean | Clock tick → may become stale | Time pressure |
| `withdrawal_requires_fresh` | Theorems/Corners.lean | Withdrawal needs τ-valid | Freshness gate |
| `τ_valid_mono` | StepSemantics.lean | τ validity is monotonic in clock | Temporal ordering |
| `current_from_clock` | Theorems/Withdrawal.lean | current(clock, τ) iff τ ≤ clock | Temporal predicate |
| `current_stable` | Theorems/Withdrawal.lean | every deposit is current w.r.t. its own timestamp (no external hypothesis required) | Deposit-intrinsic currency |

### Math Form

$$\text{Stale}(d, \text{clock}) \Rightarrow \neg\text{canWithdraw}(d)$$

$$\tau\text{-valid}(\text{clock}, \tau) \land \text{clock}' > \text{clock} \Rightarrow \text{may}(\neg\tau\text{-valid}(\text{clock}', \tau))$$

---

## Bucket 6: Case Bindings (Illustrative)

**Role:** Map epistemological puzzles to architectural diagnoses. These are *illustrative*, not claimed as philosophical theorems.

### Gettier Cases

| Theorem | File | Diagnosis |
|---------|------|-----------|
| `gettier_is_V_failure` | Theorems/Cases.lean | Gettier = V-field failure (unconditional; `tracks_false_certified` structural field) |
| `gettier_ground_disconnected` | Theorems/Cases.lean | Truth-maker and provenance are structurally distinct grounds (`ground_distinct` field) |
| `canonical_gettier_is_gettier` | Theorems/Cases.lean | Canonical Gettier satisfies `IsGettierCase` |
| `canonical_gettier_conditions` | Theorems/Cases.lean | Canonical Gettier satisfies all GettierCase conditions |

### Fake Barn Cases

| Theorem | File | Diagnosis |
|---------|------|----------|
| `fake_barn_is_E_failure` | Theorems/Cases.lean | Fake Barn = E-field failure (unconditional; `e_certified` structural field) |
| `fake_barn_profile_yields_E_failure` | Theorems/Cases.lean | Alias demonstrating the structural certification pattern |
| `canonical_fake_barn_is_fake_barn` | Theorems/Cases.lean | Canonical fake barn satisfies FakeBarnCase |

### Standard Case (S-Field Failure)

Two subtypes: relational (threshold mismatch per consuming agent) and absolute/void (E + V together
certify that S is vacuous regardless of consumer). Both repair by targeting Field.S.

| Theorem | File | Diagnosis |
|---------|------|------------|
| `standard_case_is_S_failure` | Theorems/Cases.lean | IsStandardCase → case_S_inadequate (Prop-level; not Bool.not_false) |
| `canonical_standard_case_is_standard` | Theorems/Cases.lean | Peanut-allergy canonical case satisfies IsStandardCase |
| `standard_failure_targets_S` | Theorems/Cases.lean | IsStandardCase → S_fails = true (executable mirror) |
| `standard_failure_is_relational` | Theorems/Cases.lean | Same deposit standard: allergic agent fails, lenient agent passes |
| `same_deposit_standard_split_yields_relational_S_failure` | Theorems/Cases.lean | Generic: same deposit_standard + opposite threshold outcomes → RelationalClearanceSplit |
| `canonical_allergy_is_relational_split` | Theorems/Cases.lean | Canonical allergy pair is a RelationalClearanceSplit |
| `s_failure_v_is_sound` | Theorems/Cases.lean | In an S-failure, V-provenance is genuinely tracking (V is positively certified) |
| `s_failure_e_is_sound` | Theorems/Cases.lean | In an S-failure, E-coverage has no relevant gap (E is positively certified) |
| `s_failure_v_mode_and_e_threat` | Theorems/Cases.lean | Data-backed form: `mode = .direct_inspection` and `threat âˆˆ modeled_threats` (concrete witnesses) |
| `relational_S_requires_matching_VE_data` | Theorems/Cases.lean | Relational S-failure: symmetric V/E data across both consumers; only threshold differs |

### Vacuous Standard Case (S Voided by E + V Interaction)

| Theorem | File | Diagnosis |
|---------|------|------------|
| `vacuous_standard_is_S_failure` | Theorems/Cases.lean | VacuousStandardCase → S_is_vacuous (both conditions certified as structural fields) |
| `testimony_only_plus_unreliable_source_yields_void_S` | Theorems/Cases.lean | Generic: testimony-only S over documented-unreliable source → void S |
| `canonical_liar_cook_is_void` | Theorems/Cases.lean | Known-liar cook case → S_is_vacuous (instance of generic theorem) |
| `absolute_vs_relational_S_failure` | Theorems/Cases.lean | Both failure subtypes in one theorem: relational (allergy) ∧ absolute (liar cook) |

### Lottery Paradox

| Theorem | Diagnosis |
|---------|-----------|
| `LotteryIsTypeError` | Lottery = type error (Traction ≠ Authorization) |
| `lottery_no_deposit_blocks_withdraw` | Without an authorized deposit, `Step.withdraw` is uninhabited (operationally blocked, not just mislabelled) |
| `confabulation_is_type_error` | Confabulation = type error (LLM instantiation of LotteryIsTypeError) |
| `credence_does_not_auto_close` | High credence ≠ authorization |
| `status_distinction_blocks_lottery` | Candidate/Deposited distinction blocks paradox |
| `lottery_paradox_dissolved_architecturally` | Full dissolution theorem |

### Other Puzzles

| Theorem | Puzzle | File | Diagnosis |
|---------|--------|------|----------|
| `closure_type_separation` | Closure | Theorems/Dissolutions.lean | Type separation |
| `luminosity_type_separation` | Luminosity | Theorems/Dissolutions.lean | Type separation |
| `local_redeemability_survives` | Skepticism | Theorems/Pathologies.lean | Local redeemability survives |
| `context_is_policy` | Contextualism | Theorems/Pathologies.lean | Policy variation |
| `testimony_is_export` | Testimony | Theorems/Pathologies.lean | Export structure |
| `disagreement_is_routing` | Disagreement | Theorems/Pathologies.lean | Routing |
| `higher_order_relocation` | Higher-order knowledge | Theorems/Dissolutions.lean | Relocation to S/E/V fields |
| `apriori_domain_parameterization` | A priori knowledge | Theorems/Dissolutions.lean | Domain parameterization |
| `moorean_is_export_contradiction` | Moorean paradox | Theorems/Dissolutions.lean | Export contradiction (pair to `moorean_export_contradiction`) |
| `preface_dissolution` | Preface paradox | Theorems/Dissolutions.lean | `meta_deposit_about_collection p` directly from `p.standards_differ`; no `individual_deposits` premise — type-separation holds regardless of whether the claims list is empty |
| `forgotten_evidence_persistence` | Forgotten evidence | Theorems/Pathologies.lean | Persistence via header |
| `group_bubble_separation` | Group knowledge | Theorems/Pathologies.lean | Bubble separation |
| `deposit_exportability` / `certainty_not_exportable` | Value of knowledge | Theorems/Pathologies.lean | Exportability distinction |
| `injustice_is_import_corruption` | Epistemic injustice | Theorems/Pathologies.lean | Import corruption |
| `artifact_bubble_membership` | Extended cognition | Theorems/Pathologies.lean | Bubble membership |

---

## Bucket 7: Invariant Preservation

**Role:** System maintains well-formedness across transitions.

| Theorem | File | Statement |
|---------|------|-----------|
| `step_preserves_valid_status` | StepSemantics.lean | Steps preserve valid statuses |
| `trace_preserves_valid_status` | StepSemantics.lean | Traces preserve valid statuses |
| `step_preserves_separation` | StepSemantics.lean | Steps preserve type separation |
| `step_preserves_auditability` | StepSemantics.lean | Steps preserve auditability |
| `step_no_revision_preserves_deposited` | StepSemantics.lean | Revision-free step preserves `isDeposited` for all deposits |
| `trace_no_revision_preserves_deposited` | StepSemantics.lean | Revision-free trace preserves `isDeposited` (induction over steps) |
| `deposits_survive_revision_free_trace` | Theorems/Pathologies.lean | LTS corollary: deposits survive any revision-free trace |
| `step_preserves_ladder_map` | StepSemantics.lean | `ladder_map` is invariant under every Step (all constructors use `{ s with … }`) |
| `closure_ladder_invariant` | StepSemantics.lean | Contextual alias of `step_preserves_ladder_map` for the closure puzzle |
| `trace_preserves_ladder_map` | StepSemantics.lean | `ladder_map` is invariant under any Trace (induction over steps) |
| `no_bank_trace_generates_ladder_content` | StepSemantics.lean | Point-wise: no Trace changes `ladder_map f P` for any (agent, claim) pair |
| `trace_cannot_elevate_ladder` | StepSemantics.lean | A trace starting with Ignorance for (f, P) ends with Ignorance |
| `bank_trace_cannot_discharge_closure` | StepSemantics.lean | A trace that starts with Certainty for (f, P) cannot remove it |

---

## Bucket 8: Modal Properties (Safety/Sensitivity ↔ S/E/V)

**Role:** Connect modal epistemology to architectural fields.

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `safety_V_link` | StepSemantics.lean | Unsafe → ¬V_independent | Safety = V |
| `sensitivity_E_link` | StepSemantics.lean | Insensitive → ¬E_covers | Sensitivity = E |
| `safety_iff_V_independence` | StepSemantics.lean | Safe ↔ V_independent | Biconditional |
| `sensitivity_iff_E_coverage` | StepSemantics.lean | Sensitive ↔ E_covers | Biconditional |
| `headers_provide_modal_properties` | StepSemantics.lean | header_preserved → Safe ∧ Sensitive | Headers matter |
| `stripped_headers_lose_modal_properties` | StepSemantics.lean | ¬header_preserved → Unsafe ∧ Insensitive | Stripping hurts |
| `safety_sensitivity_coincide` | StepSemantics.lean | Safe ↔ Sensitive | Coincidence |
| `modal_robustness_is_header_preservation` | StepSemantics.lean | (Safe ∧ Sensitive) ↔ header_preserved | Unified |

### Math Form

$$\text{Safe}(d) \Leftrightarrow \text{V-independent}(d) \Leftrightarrow \text{header-preserved}(d)$$

$$\text{Sensitive}(d) \Leftrightarrow \text{E-covers}(d) \Leftrightarrow \text{header-preserved}(d)$$

### Modal Case Theorems (Theorems/Modal.lean)

WorldCtx-parameterized forms: `SafetyCaseCtx` and `SensitivityCaseCtx` carry universally-quantified
obs-bounded predicates; their theorems do genuine modus-tollens reasoning over worlds.
The former Bool-flag `SafetyCase`/`SensitivityCase` structures and their one-step alias theorems
have been retired in favour of these structural forms.

| Theorem | File | Statement |
|---------|------|-----------|
| `safety_ctx_V_link` | Theorems/Modal.lean | ¬SafetyCtx → ¬V_indepCtx (instantiates `v_independent` at `sc.world` via `obs_aligned`) |
| `sensitivity_ctx_E_link` | Theorems/Modal.lean | ¬SensitivityCtx → ¬E_counterfactualCtx (instantiates `e_covers` at `sc.world` via `cf_obs_aligned`) |
| `gettier_profile_yields_V_failure` | Theorems/Modal.lean | GettierCaseCtx profile → provenance-gap witness (WorldCtx level) |
| `gettier_ctx_exhibits_provenance_gap` | Theorems/Modal.lean | IsGettierCtx → ∃ w’ s.t. Truth w’ P ∧ obs w’ = obs world ∧ w’ ≠ world |

---

## Bucket 9: Grounded Minimality (StepSemantics.lean)

**Role:** Each architectural feature is necessary for specific capabilities.

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `grounded_coordination_requires_bank` | StepSemantics.lean | Coordination → Bank | Bank necessity |
| `grounded_export_requires_headers` | StepSemantics.lean | Export → Headers | Header necessity |
| `grounded_bounded_audit_requires_bridges` | StepSemantics.lean | Bounded audit → Bridges | Bridge necessity |
| `grounded_no_bridge_forces_revalidation` | StepSemantics.lean | No bridge → revalidate | Export cost |
| `grounded_revocation_requires_quarantine` | StepSemantics.lean | Revocation → Quarantine | Quarantine necessity |
| `grounded_distributed_agents_require_bubbles` | StepSemantics.lean | Distributed → Bubbles | Bubble necessity |
| `grounded_truth_pressure_requires_redeemability` | StepSemantics.lean | Truth pressure → Redeemability | Redeemability necessity |

---

## Bucket 9b: Abstract Structural Forcing Layer (Minimality.lean + Convergence.lean)

**Role:** Provide structurally-grounded proofs that each constraint forces its feature. The six structural impossibility models in Minimality.lean independently justify each `handles_X → HasY` implication. The §1b–§6b alternative-dismissal theorems cover the completeness side: each evaluated alternative either reproduces the same impossibility or satisfies the forced-primitive definition.

**Strongest result:** Six per-dimension `*_forces_*` theorems (Convergence.lean) each take a single `Represents*` witness and directly force the `Has*` feature — no `handles_X W`, no biconditionals, no `WellFormed`. These are orthogonal: each fires independently of the other five. Bundled into `SystemOperationalBundle` / `WorldBridgeBundle`, they feed the headline `bundled_structure_forces_bank_primitives` theorem in Feasibility.lean.

### Structural Impossibility Models (Minimality.lean)

Six abstract scenario structures, each proving that a degenerate configuration is impossible.

| Theorem | Structure | Impossibility proved |
|---------|-----------|----------------------|
| `flat_scope_impossible` | `AgentDisagreement` | No flat acceptance function can faithfully represent two disagreeing agents |
| `verification_only_import_incomplete` | `BoundedVerification` | Some claims exceed any fixed budget; verification-only import cannot cover them |
| `uniform_import_nondiscriminating` / `no_sound_complete_uniform_import` | `DiscriminatingImport` | A uniform import function cannot be both sound and complete |
| `monotonic_no_exit` | `MonotonicLifecycle` | An absorbing accepted state cannot be escaped at any step count |
| `private_storage_no_sharing` | `PrivateOnlyStorage` | Isolated agent storage makes shared deposit access impossible |
| `closed_system_unfalsifiable` | `ClosedEndorsement` | A closed endorsement system has no externally falsifiable endorsed claim |

### Alternative Architecture Dismissals (Minimality.lean §1b–§6b)

For each of the six forcing dimensions, alternative mechanisms are instantiated and shown to either reduce to the original impossibility or satisfy the forced-primitive definition. None escape the forcing argument.

| §  | Alternatives covered | Key theorems |
|----|----------------------|---------------|
| §1b | Capability-token systems, federated namespaces, parameterized gates | `capability_flat_impossible`, `federated_flat_impossible`, `parameterized_gate_flat_impossible` — each gives an `AgentDisagreement`; `flat_scope_impossible` fires unchanged |
| §2b | Staged verification, delegated verification markets | `staged_verification_incomplete` (cumulative-cost `BoundedVerification`); `delegated_is_trust_bridge` + `trust_required_iff_not_locally_verifiable` + `delegation_necessary_iff_locally_inadequate` — delegation satisfies the trust-bridge definition |
| §3b | Content-addressed routing, global contextual routing state | `content_addressed_has_header` — sound+complete content-addressed import satisfies `IsHeader` directly; `global_routing_cannot_discriminate` — global state is effectively uniform |
| §4b | Quarantine, hold/shadow, rollback | `quarantine_violates_absorbing`, `hold_violates_absorbing`, `rollback_violates_absorbing` — each is a non-absorbing exit from accepted, i.e., revocation under another name |
| §5b | Replicated logs, attestation networks, CRDT-based shared state | `replicated_log_is_shared`, `attestation_network_is_shared`, `crdt_is_shared` — each satisfies the sharing condition; isolation does not hold; each qualifies as a shared ledger under the definition |
| §6b | Anomaly signaling, partial contestation, soft falsifiability | `anomaly_signal_insufficient`; `partial_contestation_closed_on_endorsed`; `soft_falsifiability_closed`; `*_closed_when_universal` under coverage assumption |

### `IsHeader` Definition (Minimality.lean)

`IsHeader M f` — a routing function `f : M.Claim → Bool` is a header for `DiscriminatingImport` scenario `M` iff it discriminates good from bad claims (`f M.good ≠ f M.bad`).

| Theorem | Statement | Role |
|---------|-----------|------|
| `sound_complete_import_is_header` | Sound+complete import → `IsHeader` | Any sound+complete import satisfies the header definition |
| `routing_requires_header` | ∃ sound+complete f → ∃ header | Any working routing function carries a header |
| `content_addressed_has_header` | Sound+complete content-addressed policy → `IsHeader` | Sound+complete content-addressed routing satisfies `IsHeader` |

### Forcing Stratification (Minimality.lean §6c)

The six forcing dimensions differ in strength; §6c establishes this with explicit counterexamples.

| Tier | Dimensions | Key theorem | What it says |
|------|------------|-------------|---------------|
| Hard | Scope, revocation, bank, partial contestation | `redeemability_hard_forced`, `partial_contestation_hard_forced` | Impossibility fires from structural fields alone, no coverage assumption |
| Soft | Anomaly signaling, soft falsifiability | `anomaly_not_hard_forced`, `soft_falsifiability_not_hard_forced` | Consistent instances exist with endorsed+falsifiable claims; coverage assumption (`∀ c, endorsed c → signals c`) cannot be discharged from structure alone |

`anomaly_not_hard_forced` and `soft_falsifiability_not_hard_forced` exhibit explicit counterexamples (vacuous `emits_anomaly`/`flagged`) confirming soft closure is genuinely weaker than hard forcing.

### Pressure Dimension Index (Minimality.lean)

The `Pressure` inductive type is the canonical dimension index for the EpArch forcing layer. All six forcing dimensions are cases of a single type; every forcing-layer predicate is now a function `Pressure → Prop` rather than six separate fields.

```lean
inductive Pressure where
  | scope | trust | headers | revocation | bank | redeemability
  deriving DecidableEq, Repr
```

| Dispatch function | Type | What it routes |
|-------------------|------|----------------|
| `handles_pressure W` | `Pressure → Prop` | Maps each dimension to its operational handle predicate (`handles_distributed_agents`, `handles_bounded_audit`, …) |
| `forced_feature W` | `Pressure → Prop` | Maps each dimension to its forced structural feature (`HasBubbles`, `HasTrustBridges`, …) |
| `bridge_scenario W` | `Pressure → Prop` | Maps each dimension to its bridge predicate (`BridgeBubbles`, `BridgeTrust`, …) |

Using `Pressure` as the index means every `cases P` in a proof is machine-exhaustiveness-checked by Lean's kernel. A proposed seventh dimension must be added as a new `Pressure` constructor — at which point the compiler flags every `cases P` site until the new forcing chain is supplied. This is architectural enforcement, not documentation convention. See `DOCS/MODULARITY.md § "What exhaustiveness means here"` for the scope boundary this claim carries.

Key definitions that are now universally quantified over `Pressure`:
- `SatisfiesAllProperties W := ∀ P : Pressure, handles_pressure W P`
- `containsBankPrimitives W := ∀ P : Pressure, forced_feature W P`
- `StructurallyForced W` — single field `forcing : ∀ P, handles_pressure W P → forced_feature W P`
- `ForcingEmbedding W` — single field `embed : ∀ P, handles_pressure W P → forced_feature W P ∨ bridge_scenario W P`
- `all_bridges_impossible W P : ¬bridge_scenario W P` — exhaustive impossibility theorem (proves by `cases P`)

### Forcing Package (Convergence.lean)

| Structure/Theorem | Description |
|-------------------|-------------|
| `StructurallyForced W` | Single field `forcing : ∀ P : Pressure, handles_pressure W P → forced_feature W P`; replaces the old six named fields |
| `ForcingEmbedding W` | Single field `embed : ∀ P : Pressure, handles_pressure W P → forced_feature W P ∨ bridge_scenario W P`; replaces old six named fields |
| `embedding_to_structurally_forced` | `ForcingEmbedding W → StructurallyForced W` (one line: `.embed` + `all_bridges_impossible`; no Classical reasoning) |
| `convergence_structural` | `StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W` — preferred convergence path; one line via `∀ P` |
| `structural_impossibility` | `StructurallyForced W → (∃ P, ¬forced_feature W P) → ¬SatisfiesAllProperties W` — existential form |

### Per-Dimension Structural Forcing Theorems (Convergence.lean)

Six independent theorems — one per EpArch dimension — each taking a single `Represents*` witness and a structural hypothesis, and directly forcing the corresponding `Has*` feature. **No `handles_X W` required. No biconditionals. Orthogonal: zero cross-dependencies.** This is the strongest form of the per-dimension claim: any system that concretely faces exactly one EpArch operational pressure is mathematically forced to have the corresponding Bank primitive.

| Theorem | Witness required | Feature forced |
|---------|-----------------|----------------|
| `disagreement_forces_bubbles` | `RepresentsDisagreement W` + flat-acceptance witnesses | `HasBubbles W` |
| `private_coordination_forces_bank` | `RepresentsPrivateCoordination W` + shared-deposit witnesses | `HasBank W` |
| `monotonic_lifecycle_forces_revocation` | `RepresentsMonotonicLifecycle W` + escape witnesses | `HasRevocation W` |
| `discriminating_import_forces_headers` | `RepresentsDiscriminatingImport W` + sound/complete import witnesses | `HasHeaders W` |
| `bounded_verification_forces_trust_bridges` | `RepresentsBoundedVerification W` + verification witnesses | `HasTrustBridges W` |
| `closed_endorsement_forces_redeemability` | `RepresentsClosedEndorsement W` + endorsement witnesses | `HasRedeemability W` |

Proof pattern for each: `by_cases h : HasFeature W; exact h; exact (impossible_without_feature ... h ...).elim` — classical case split with the abstract impossibility model closing the negative branch.

### Witness Bundle Structures (Convergence.lean)

Two named record types group the per-dimension witnesses symmetrically. Split rationale: `SystemOperationalBundle` is purely architectural (no world-semantic content, no `WorldCtx`); `WorldBridgeBundle` covers world-adjacent dimensions that are W-specific.

| Structure | Dimensions bundled | Content |
|-----------|-------------------|---------|
| `SystemOperationalBundle W` | Scope, headers, bank | `Rd : RepresentsDisagreement W` + flat-acceptance fields; `Ri : RepresentsDiscriminatingImport W` + import fields; `Rp : RepresentsPrivateCoordination W` + shared-deposit fields |
| `WorldBridgeBundle W` | Revocation, trust bridges, redeemability | `Rm : RepresentsMonotonicLifecycle W` + escape fields; `Rb : RepresentsBoundedVerification W` + trust fields; `Re : RepresentsClosedEndorsement W` + endorsement + falsifiability fields |

### Headline Convergence Theorems (Feasibility.lean)

| Theorem | Signature | Role |
|---------|-----------|------|
| `grounded_world_and_structure_force_bank_primitives` | `(W : WorkingSystem) → (Rd Rb Ri Rm Rp Re : Represents* W) → bridge hypotheses → SatisfiesAllProperties W → containsBankPrimitives W` | All-six forcing with fully explicit `Represents*` witnesses; no `WorldCtx`, no W_* bundles; holds for any world |
| `bundled_structure_forces_bank_primitives` | `(W : WorkingSystem) → SystemOperationalBundle W → WorldBridgeBundle W → SatisfiesAllProperties W → containsBankPrimitives W` | Headline 4-argument form; unpacks both bundles into `grounded_world_and_structure_force_bank_primitives` |

**Key architectural boundary:** `W_*` bundles (`WorldCtx.lean`) are `Prop`-valued; `Represents*` structures carry `Type`-valued fields (`State : Type`, `Claim : Type`). No `Type` can be extracted from a `Prop` — the universe boundary is genuine. The `W_*` bundles are natural *motivation* for the witnesses but are not formal preconditions; callers supply `Represents*` witnesses directly.

### Bridge Predicates and Impossibility (Convergence.lean)

| Predicate | `bridge_*_impossible` | What is ruled out |
|-----------|-----------------------|--------------------|
| `BridgeBubbles W` | `bridge_bubbles_impossible` | Flat scope faithful to two disagreeing agents |
| `BridgeTrust W` | `bridge_trust_impossible` | All claims fitting within budget |
| `BridgeHeaders W` | `bridge_headers_impossible` | Sound-and-complete uniform import |
| `BridgeRevocation W` | `bridge_revocation_impossible` | Escaping the absorbing accepted state |
| `BridgeBank W` | `bridge_bank_impossible` | Isolated agents sharing a deposit |
| `BridgeRedeemability W` | `bridge_redeemability_impossible` | Endorsed claim externally falsifiable in closed system |

### Convergence and Impossibility (Convergence.lean)

| Theorem | Statement | Role |
|---------|-----------|------|
| `convergence_structural` | `StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W` | Preferred convergence path; no `WellFormed` dependency |
| `structural_impossibility` | `StructurallyForced W → missing any feature → ¬SatisfiesAllProperties W` | Contrapositive: missing a feature blocks all-property satisfaction |

### Scenario Predicates (Convergence.lean)

`Represents*` structures supply concrete claim/agent/lifecycle data so the abstract impossibility models fire on real systems, not hypothetical ones. Six scenario types match the six forcing dimensions. Each carries a right-branch embedding theorem: a system with the scenario predicate and lacking the corresponding feature is in the impossible abstract scenario.

The six per-dimension `*_forces_*` theorems are built directly on these predicates and are the canonical "use these" entry points for the forcing argument. They supersede the earlier `handles_X W` / biconditional path as the primary forcing mechanism: no `PartialWellFormed`, no `handles_X W`, no biconditionals needed.

### Grounded Compliance API (Minimality.lean)

Product-facing constructor layer. `GroundedBehavior` bundles one `GroundedX` witness per dimension; `withGroundedBehavior` stamps all six `Option GroundedXStrict` evidence fields onto any base `WorkingSystem`. The two theorems below close the loop: behavioral flags are `true` by `Option.isSome`, and biconditionals hold because spec flags are `true` by construction.

| Definition / Theorem | File | Statement | Role |
|---------------------|------|-----------|------|
| `GroundedBehavior` | Minimality.lean | 6-field record (`bubbles`, `trust_bridges`, `headers`, `revocation`, `bank`, `redeemability`), one `GroundedX` per dimension | Evidence bundle for behavioral flags |
| `WorkingSystem.withGroundedBehavior` | Minimality.lean | Sets all six `Option GroundedXStrict` fields from a `GroundedBehavior`; leaves spec/other fields from base | Proof-carrying `WorkingSystem` constructor |
| `grounded_behavior_satisfies_all` | Minimality.lean | `∀ B W, SatisfiesAllProperties (withGroundedBehavior B W)` | Behavioral flags → all six `handles_*` predicates |
| `grounded_partial_wellformed` | Minimality.lean | `∀ B G, PartialWellFormed (withGroundedBehavior B {spec := G.toSystemSpec, …}) allConstraints` | Behavioral + spec evidence → full biconditional closure |

**Usage pattern:** supply `GroundedBehavior` + `GroundedSystemSpec` → get `PartialWellFormed W allConstraints` + `SatisfiesAllProperties W` in one call. See `lean_partial_wellformed` / `lean_satisfies_all_properties` in `Meta/LeanKernel/World.lean` for the self-referential instantiation.

---

## Bucket 9c: Observation-Boundary Equivalence (BehavioralEquivalence.lean)

**Role:** Proves that any two `GroundedBehavior` certificates produce identical observations on all inputs. `Behavior B i` is determined solely by the input constructor — not by the structural content of `B`. The step-bridge section operationally grounds this: for withdraw, challenge, and tick inputs, a concrete `Step` is constructed from `B`'s evidence (`bank`, `trust_bridges`, `revocation`) and structurally consumed via `cases h`, so the equality is derived *through* an actual firing. Export falls back to definitional equality because `header_preserved` is opaque and cannot be reflected into a concrete `depositHasHeader` for the unit-type instantiation.

### Definitions

- `Input` — abstract input events (withdraw, export, challenge, time-advance)
- `Observation` — observable outcomes
- `Behavior B i` — observation produced by `B : GroundedBehavior` on input `i`; determined by input shape, not by witness content; no fallback branch
- `BehaviorallyEquivalent B1 B2` — identical observations on all inputs
- `input_to_action` — maps `Input` to the matching concrete `StepSemantics.Action`
- `observe_step_action` — extracts an `Observation` from a concrete action
- `ReadyState i` — a `CState` + proof that `Step` fires for `input_to_action i`
- `withdraw_ready_state B a b d` — constructs `ReadyState` from `B.bank`/`B.trust_bridges`
- `challenge_ready_state B c f` — constructs `ReadyState` from `B.revocation`

### Theorems

| Theorem | Statement | Role |
|---------|-----------|------|
| `behavioral_equiv_refl/symm/trans` | Equivalence relation properties | Structural foundation |
| `satisfies_all_fixes_flags` | `SatisfiesAllProperties W` → all six flags are `true` | Bridges property satisfaction to flag values |
| `behavior_step_consistent` | `Behavior B i = observe_step_action (input_to_action i)` for all `B`, `i` | Definitional bridge; both sides action-indexed |
| `behavior_from_step` | Given `Step s (input_to_action i) s'`, derive `observe_step_action ... = Behavior B i` by `cases i <;> cases h` | Step-consuming bridge; eliminates the Step constructor |
| `grounded_export_step` | Export Step fires given `depositHasHeader` + `hasTrustBridge` | Conditional; `header_preserved` opaque prevents unconditional form |
| `working_systems_equivalent` | Any two `GroundedBehavior` witnesses are behaviorally equivalent; unconditional — no `SatisfiesAllProperties` premise | Main theorem |
| `grounded_behaviors_equivalent` | Same equivalence proved by `cases i <;> rfl`; no Step witnesses | Reveals depth ceiling: equality is input-indexed, not state-indexed |

---

## Bucket 9d: Kernel Verification Depth (VerificationDepth.lean)

**Role:** Provides a *constructive* kernel-level witness that `W_bounded_verification` is not an empirical world assumption but follows from the structural properties of the verification relation itself. `DepthClaim n` is a depth-indexed proposition family with exactly n constructors; a budget-d verifier traverses only d constructors and therefore cannot decide `DepthClaim (d+1)`, which is genuinely true. This justifies the bounded-audit forcing argument for trust bridges by construction rather than supposition.

### Definitions

| Definition | Description |
|------------|-------------|
| `DepthClaim : Nat → Prop` | Inductive family: `DepthClaim n` has exactly n constructors (`base`, n × `step`); represents a proposition whose verification cost is structurally n |
| `bounded_verify : Nat → Nat → Bool` | Budget-d decision procedure; `bounded_verify d n = true ↔ n ≤ d` |
| `DepthWorldCtx : WorldCtx` | Concrete `WorldCtx` where `Claim := Nat`, `Truth _ n := DepthClaim n`, `VerifyWithin _ n t ↔ n ≤ t`; `W_bounded_verification` holds by construction |

### Theorems

| Theorem | Statement | Role |
|---------|-----------|------|
| `depth_claim_provable` | `∀ n, DepthClaim n` | Every claim in the family is true; ensures incompleteness is genuine, not vacuous |
| `bounded_verify_sound` | `n ≤ d → bounded_verify d n = true` | Budget-d verifier correctly accepts depth-≤-d claims |
| `bounded_verify_incomplete` | `bounded_verify d (d+1) = false` | Budget-d verifier rejects the true depth-(d+1) claim |
| `no_budget_is_sufficient` | `∀ d, ∃ n, DepthClaim n ∧ bounded_verify d n = false` | No finite budget covers the full family |
| `endorser_cannot_self_verify` | `bounded_verify n (n+1) = false` | An endorsement of depth-n has depth n+1; budget-n verifiers cannot check their own endorsements (kernel shadow of trust-bridge / redeemability forcing) |
| `DepthWorldCtx_requires_steps` | `(∀ w, DepthWorldCtx.RequiresSteps w n k) ↔ k ≤ n` | Step-cost characterization of `DepthWorldCtx` |
| `depth_world_satisfies_bounded_verification` | `Nonempty DepthWorldCtx.W_bounded_verification` | `W_bounded_verification` holds in `DepthWorldCtx` — no empirical assumption needed |
| `depth_world_exceeds_any_budget` | `∀ d w, DepthWorldCtx.RequiresSteps w (d+1) (d+1)` | For any budget d, a harder claim exists in the kernel world |

**Architectural note:** `DepthWorldCtx` shows that `W_bounded_verification` is satisfiable (and hence the forcing argument is non-vacuous) via a `WorldCtx` whose verification cost is structurally intrinsic. This is the `Type`-side constructive companion to the `Prop`-side `WorldWitness.lean` non-vacuity proof for `W_bounded_verification`.

---

## Bucket 10: Adversarial Model (Adversarial/Base.lean)

**Role:** Formalize attack patterns and boundary conditions.

### Attack Structures

| Definition | Description |
|------------|-------------|
| `FullStackAttack` | Coordinated multi-primitive attack |
| `PseudoDeposit` | Deposit with spoofed V |
| `DDoSAttack` | Bandwidth exhaustion |
| `DDoSVector` | Four attack vectors |
| `AttackLevel` | 5-level hierarchy (Lie → DDoS) |
| `Lie` | Primitive false deposit |
| `ProxySubstitution` | Similarity exploitation |

### Core Theorems in Adversarial/Base.lean (Proved)

| Theorem | File | Statement |
|---------|------|----------|
| `sophistication_monotonic` | Adversarial/Base.lean | Attack levels form monotonic hierarchy |
| `sincerity_norms_irrelevant` | Adversarial/Base.lean | Lies don't require violating sincerity norms |
| `lies_structurally_possible` | Adversarial/Base.lean | Lies are structurally possible given `is_lie` |
| `adversarial_proxy_signature` | Adversarial/Base.lean | Adversarial proxy = truthful but mislicensed |

---

## Bucket 11: Repair Loop Semantics

**Role:** Challenge-repair-revalidation cycle.

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `repair_enforces_revalidation` | Theorems/Withdrawal.lean | Repair → revalidate | No silent fix |
| `submit_enforces_revalidation` | Theorems/Withdrawal.lean | Submit → validate | Validation on entry |
| `repair_requires_prior_challenge` | Theorems/Withdrawal.lean | Repair requires quarantine | Challenge first |
| `challenge_has_field_localization` | StepSemantics.lean | Challenge targets field | Field-specific |
| `repair_requires_quarantine` | StepSemantics.lean | Repair needs quarantine | State gate |
| `repair_targets_field` | StepSemantics.lean | Repair addresses field | Surgical |
| `repair_produces_candidate` | StepSemantics.lean | Repair → Candidate | Back to start |
| `repair_resets_to_candidate` | StepSemantics.lean | Full cycle reset | Lifecycle |

---

## Bucket 12: Withdrawal Gates (Three-Gate Model)

**Role:** Withdrawal requires Status + ACL + τ.

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `withdrawal_requires_three_gates` | StepSemantics.lean | Status ∧ ACL ∧ τ | Three gates |
| `withdrawal_gates` | Theorems/Withdrawal.lean | Withdrawal preconditions | Gate theorem |
| `canWithdrawAt_iff_gates` | Theorems/Withdrawal.lean | CanWithdraw ↔ gates | Equivalence |
| `withdrawal_requires_canWithdrawAt` | Theorems/Withdrawal.lean | Step requires predicate | Enforcement |
| `canWithdrawAt_enables_step` | Theorems/Withdrawal.lean | Predicate enables step | Sufficiency |

---

## Bucket 13: Obligation Theorems (World ⇒ Mechanism)

**Role:** Convert implicit mechanism axioms into explicit conditional theorems.

**Files:** `World.lean`, `Adversarial/Obligations.lean`

### Core Theorems (World.lean)

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `lie_possible_of_W` | WorldCtx.lean | W_lies_possible → ∃ w a P, Lie w a P | Adversarial: lies exist |
| `all_agents_can_lie_of_W` | WorldCtx.lean | W_lies_possible → ∀ a, can_lie a | Adversarial: universal capability |
| `bounded_audit_fails` | WorldCtx.lean | RequiresSteps w P k → t < k → ¬VerifyWithin | Bounded audit |
| `cost_asymmetry_of_W` | WorldCtx.lean | W_asymmetric_costs → export < defense | Adversarial: cost asymmetry |
| `partial_obs_no_omniscience` | WorldCtx.lean | W_partial_observability → ∃ P, NotDeterminedByObs P | No omniscience: obs underdetermines truth |

### Adversarial Obligation Theorems (Adversarial/Obligations.lean)

#### Batch A: Mechanism Axioms

| Theorem | File | Statement | Original Axiom |
|---------|------|-----------|----------------|
| `spoofed_V_blocks_path_of_W` | Adversarial/Obligations.lean | W_spoofedV → spoofed V → ¬path | `spoofed_V_blocks_path` |
| `ddos_causes_verification_collapse_of_W` | Adversarial/Obligations.lean | W_ddos → overwhelmed → collapsed | `ddos_causes_verification_collapse` |
| `collapse_causes_centralization_of_W` | Adversarial/Obligations.lean | W_collapse → collapsed → centralized | `collapse_causes_centralization` |
| `lies_scale_of_W` | Adversarial/Obligations.lean | W_lies_scale → export < defense | `lies_scale` |
| `rolex_ddos_structural_equivalence_of_W` | Adversarial/Obligations.lean | W_rolex_ddos → same_structure | `rolex_ddos_structural_equivalence` |
| `ddos_to_centralization_of_W` | Adversarial/Obligations.lean | W_ddos_full → overwhelmed → centralized | (composed chain) |

#### Batch B: Boundary Condition Countermeasures

| Theorem | File | Statement | Original Axiom |
|---------|------|-----------|----------------|
| `cheap_validator_blocks_V_attack_of_W` | Adversarial/Obligations.lean | W_cheap_validator → cheap validator → ¬V_attack | `cheap_validator_blocks_V_attack` |
| `trust_bridge_blocks_V_attack_of_W` | Adversarial/Obligations.lean | W_trust_bridge → trust bridge → ¬V_attack | `trust_bridge_blocks_V_attack` |
| `reversibility_neutralizes_τ_of_W` | Adversarial/Obligations.lean | W_reversibility → reversible → ¬τ_attack | `reversibility_neutralizes_τ` |
| `E_inclusion_closes_expertise_gap_of_W` | Adversarial/Obligations.lean | W_E_inclusion → E includes threat → ¬gap_exploited | `E_inclusion_closes_expertise_gap` |
| `cheap_constraint_blocks_V_spoof_of_W` | Adversarial/Obligations.lean | W_cheap_constraint → cheap test → ¬V_attack | `cheap_constraint_blocks_V_spoof` |

**World Assumption Bundles:** 16 `W_*` bundles (`W_lies_possible` through `W_cheap_constraint`) each gate exactly one obligation theorem above; full definitions in WorldCtx.lean and Adversarial/Obligations.lean.

### Math Form

$$\text{W-lies-possible} \Rightarrow \exists w\, a\, P.\, \text{Lie}(w, a, P)$$

$$\text{RequiresSteps}(w, P, k) \land t < k \Rightarrow \neg\text{VerifyWithin}(w, P, t)$$

$$\text{W-ddos-full} \land \text{overwhelmed}(s) \Rightarrow \text{centralized}(t)$$

---

## Adversarial Attack Surfaces

Each architectural constraint creates both a capability and an exploitable surface. Five canonical surfaces follow directly from the bucket structure: **Lifecycle** (ladder overload, premature closure — `DDoSVector.LadderOverload`, `τ_compressed`), **Revision** (challenge flooding, denial triggering — `DDoSVector.DenialTriggering`), **Export/Strip Asymmetry** (V-spoofing, proxy substitution, provenance laundering — `stripV_loses_provenance`, `ProxySubstitution`, `no_strip_left_inverse`), **Diagnosability** (E-field poisoning, diagnostic denial — `DDoSVector.EFieldPoisoning`, `stripped_no_field_repair`), and **Temporal Validity** (τ compression, staleness induction — `FullStackAttack.τ_compressed`, `tick_can_cause_staleness`). Coordinated full-stack attacks are formalized as `FullStackAttack` in Adversarial/Base.lean; the four `DDoSVector` constructors cover the exhaustive attack vector taxonomy.


---

## Bucket 14: Health → Necessity Theorems

**Role:** Connect health goals to mechanism requirements (invariants).

**File:** `Health.lean`, `Agent/Imposition.lean`

### Capability Predicates (Agent/Imposition.lean)

| Predicate | Description | What It Captures |
|-----------|-------------|------------------|
| `ReversibleWithdrawal` | System can undo withdrawals | Reversibility capability |
| `CheapValidatorAvailable` | System has low-cost verification | Validator capability |
| `ExportGateEnforced` | System blocks erroneous exports | Gate capability |

### Health Goal Definitions (Health.lean)

Health goals are definitional predicates over `CoreModel`/`CoreOps`:

| Definition | Signature | Description |
|------------|-----------|-------------|
| `SafeWithdrawalGoal` | `CoreModel → Prop` | Authorized submissions only |
| `ReliableExportGoal` | `CoreModel → Prop` | No contamination propagation |
| `CorrigibleLedgerGoal` | `CoreModel → Prop` | Existence + soundness conjunction: `(∃ B, hasRevision B) ∧ (revise → truth)` |
| `SoundDepositsGoal` | `CoreModel → Prop` | Verifiable within effectiveTime |
| `SelfCorrectionGoal` | `CoreModel → Prop` | `selfCorrects B → hasRevision B` (conditional goal) |
| `SelfCorrectingSystem` | `CoreModel → Prop` | `SelfCorrectionGoal M ∧ ∃ B, selfCorrects B` (active self-correction) |

### Necessity Theorems (Proved, Health.lean)

| Theorem | Premise | Conclusion |
|---------|---------|------------|
| `corrigible_needs_revision` | `CorrigibleLedgerGoal` (single premise) | `HasRevisionCapability` |
| `self_correction_needs_revision` | `SelfCorrectingSystem` (single premise) | `HasRevisionCapability` |
| `sound_deposits_needs_verification` | `SoundDepositsGoal` + `∃truth` | `HasVerificationCapability` |

### Math Form

$$\text{CorrigibleLedgerGoal}(M) \Rightarrow \text{HasRevisionCapability}(M)$$

$$\text{SelfCorrectingSystem}(M) \Rightarrow \text{HasRevisionCapability}(M)$$

---

## Bucket 15: Scope/Irrelevance Theorems

**Role:** Turn "out of scope" prose into machine-checkable scope boundaries.

**File:** `ScopeIrrelevance.lean`

These theorems prove that out-of-scope fundamentals (physics, consciousness, psychology, embodiment) are irrelevant by design — no architectural theorem depends on them.

### S1: Substrate Independence

| Structure/Theorem | Description |
|-------------------|-------------|
| `Model` | Abstract interface (World, Agent, PropLike, Obs, Truth, Utter, obs) |
| `ModelHom` | Structure-preserving map between models |
| `substrate_preserves_existence` | Homomorphisms preserve truth |

### S2: Minimal Agency

| Structure/Theorem | Description |
|-------------------|-------------|
| `MinimalAgent` | Agent with only id and opaque state |
| `agent_identity_suffices` | Theorems using only id work for any implementation |

### S3: Extra-State Erasure

| Theorem | Description | Fundamental Addressed |
|---------|-------------|-----------------------|
| `extra_state_erasure` | P a ↔ P (a, x).1 | General erasure |
| `psychology_irrelevant` | System properties ignore psychology | Psychology |
| `consciousness_irrelevant` | Functional properties ignore qualia | Consciousness |
| `embodiment_irrelevant` | Abstract properties ignore embodiment | Embodiment |

### S4: Traction-Implementation Irrelevance

| Theorem | Description | Fundamental Addressed |
|---------|-------------|-----------------------|
| `traction_modulation_confined` | If two traction functions agree on P, their `ladder_stage` output is identical — `agentTraction` has exactly one observable surface | Traction mechanism (confinement) |
| `traction_implementation_irrelevant` | Any system property over `LadderStage` is invariant under traction-function substitution | Psychology/cognition/policy (implementation) |

### Fundamentals Coverage

| Fundamental | Status | Mechanism |
|-------------|--------|-----------|
| Physics/Substrate | Irrelevant | `ModelHom` preserves |
| Consciousness | Irrelevant | Extra state erased |
| Psychology | Irrelevant | System-level only |
| Embodiment | Irrelevant | Via `Obs` abstraction |
| Traction implementation | Confined + Irrelevant | `traction_modulation_confined` + `traction_implementation_irrelevant` |
| Optimal Rationality | Not assumed | No Bayes dependency |
| Free Will | Not assumed | No moral judgment |
| Metaphysics of Truth | Abstract | Truth is predicate |

---

## Bucket 16: Discharged Linking Axioms

**Role:** Convert philosophical "linking axioms" from axioms to definitional theorems.

**Files:** `Theorems/Dissolutions.lean`, `Theorems/Pathologies.lean`

Each linking axiom is discharged by making an opaque predicate concrete — replacing an assumed philosophical connection with explicit typed fields and well-formedness constraints.

### Batch 1: Discharged Axioms — Explicit Fields

| Original Axiom | Now Theorem | Mechanism |
|----------------|-------------|-----------|
| `testimony_is_export` | âœ… theorem | `via_trust : Bool` field forces disjunction |
| `forgotten_evidence_persistence` | âœ… theorem | Deposit structure separates agent access from deposit |
| `disagreement_is_routing` | âœ… theorem | `MismatchType` enum exhausts cases |
| `group_bubble_separation` | âœ… theorem | Tautological (`≠` = `bubbles_differ`) |
| `deposit_exportability` | âœ… theorem | `KnowledgeState` distinguishes deposit/certainty |
| `certainty_not_exportable` | âœ… theorem | Pattern matching on `KnowledgeState` |
| `local_redeemability_survives` | âœ… theorem | `severs_constraint_contact s → local_redeemability_holds s B` via required `global_implies_local` structural field; not a definitional identity |
| `context_is_policy` | âœ… theorem | Fields make policy variation explicit; uses `high_stakes_implies_policy` structural invariant |
| `no_semantic_shift` | âœ… theorem | `is_semantic_shift` is vacuously false (`PropLike ≠ PropLike` is `False`) |
| `injustice_is_import_corruption` | âœ… theorem | Fields encode deflation/downgrade |
| `artifact_bubble_membership` | âœ… theorem | Tautological (inclusion = membership) |

### Batch 2: Discharged Axioms — Concrete Definitions

| Original Axiom | Now Theorem | Mechanism |
|----------------|-------------|-----------|
| `DiagnoseField` | âœ… def + theorem | `DiagnosableDeposit` with `broken_fields` list |
| `safety_V_link` | âœ… theorem | `Unsafe d → ¬V_independent d`; uses `V_spoofable_iff_not_independent`; Safety and V-independence are the same `Deposit`-level predicate |
| `sensitivity_E_link` | âœ… theorem | `Insensitive d → ¬E_covers_counterfactual d`; analogous to `safety_V_link`; discharged via `E_has_gap_iff_not_covers` |
| `closure_type_separation` | âœ… theorem | `closure_puzzle` with boolean fields + explicit hypotheses |
| `luminosity_type_separation` | âœ… theorem | `luminosity_puzzle` where the `either_available` structural invariant directly supplies the disjunction; no caller hypothesis needed (contrast `closure_type_separation` which takes explicit `h_ladder`) |
| `higher_order_relocation` | âœ… theorem | `higher_order_case` + `WellFormedHigherOrder` constraint |
| `apriori_domain_parameterization` | âœ… theorem | `apriori_case` + `WellFormedApriori` constraint |
| `moorean_export_contradiction` | âœ… theorem | `moorean_case` + `ExportRequiresDeposit` constraint |
| `notation_invariance_of_redeemability` | âœ… theorem | Proof-redeemability is invariant under coherent bijective relabeling of propositions |
| `notation_invariance_of_empirical_redeemability` | âœ… theorem | Empirical redeemability likewise notation-invariant |
| `math_practice_is_bubble_distinct` | âœ… theorem | Mathematical practice is a bubble: notation varies, structural position (constraint surface) does not |
| `bridge_monolithic_opaque` | âœ… theorem | `¬depositHasHeader → ¬field_checkable` via `harder_without_headers`; header absence makes challenge fields guesses, not diagnoses |
| `bridge_stripped_ungrounded` | âœ… theorem | Follows from depositHasHeader definition |

---

## Bucket 17: Revision Safety

**Role:** Guarantee that extending/strengthening the model doesn't break existing results.

**File:** `RevisionSafety.lean`

Three levels of safety are formalized: premise strengthening (adding premises preserves implications), compatible extensions (commuting laws preserve revision-gate properties), and LTS refinement safety (refinements preserve invariants).

### Premise Strengthening Theorems (Tier A)

| Theorem | Statement | Description |
|---------|-----------|-------------|
| `premise_strengthening` | (A → C) → (A ∧ B → C) | Adding constraints preserves implications |
| `premise_strengthening_dep` | (∀x, A x → C) → (∀x, A x ∧ B x → C) | Dependent version |
| `premise_chain` | (A → B → C) → (A ∧ B → C) | Chain composition |

### Compatible Extension Framework (Tier A)

`CoreModel` bundles the core type signature and operations. `Compatible` extensions are `ExtModel`s whose extra fields commute with `CoreModel` projections — ensuring the transport theorems below hold.

### Transport Theorems (Tier A)

| Theorem | Statement | Description |
|---------|-----------|-------------|
| `transport_core` | Compatible E C → RevisionGate C → RevisionGate (forget E) | Core transport |
| `safe_extension_preserves` | RevisionSafeExtension C → RevisionGate C → RevisionGate (forget R.ext) | Safe extension |
| `safety_preserved_under_contract_refinement` | Refinement → IsInvariant C Safety → IsInvariant R (Safety âˆ˜ φ) | LTS refinement |

### Acceptance Tests (Diagnostic)

| Theorem | Description |
|---------|-------------|
| `goodExtension_compatible` | Extra-state extension satisfies Compatible (Iff.refl) |
| `badExtension_incompatible_witness` | Semantic-breaking extension FAILS Compatible |
| `badExtension_incompatible_if_id` | Corollary for identity projection |

### Math Form

$$\text{Compatible}(E, C) \land \text{RevisionGate}(C) \Rightarrow \text{RevisionGate}(\text{forget}(E))$$

$$\text{Compatible} := \forall B.\, E.\text{selfCorrects}(B) \Leftrightarrow C.\text{selfCorrects}(\pi_B(B))$$

---

## Bucket 18: Agent Constraints & PRP

**Role:** Mechanize "the system is designed for imperfect agents" via structural constraints.

**File:** `Agent.lean`

**Permanent Redeemability Pressure (PRP):** agents face an infinite stream of challenges exceeding their verification budget — terminal epistemic closure is unreachable. The theorems in `Agent/Imposition.lean` derive that `AgentConstraints + HealthGoal + ¬Mechanism → False`.

### PRP Consequence Theorems (Tier A — Fully Proved)

| Theorem | Statement | Claim |
|---------|-----------|-------------|
| `no_global_closure_of_PRP` | ¬∃ t_final, ∀ t ≥ t_final, ∀ c, cost ≤ budget | No terminal epistemic closure |
| `needs_revision_of_PRP` | ∀ t, ∃ t' > t, challenge exceeds budget | Revision hooks mandatory |
| `needs_scoping_of_PRP` | ∃ t c, challenge exceeds budget | Scoped audit surfaces forced |
| `needs_revalidation_of_PRP` | ¬StableDepositSet under PRP | Stable deposit sets impossible |
| `prp_incompatible_with_global_redeemability` | ¬GlobalRedeemability under PRP | Global redeemability impossible |

### Math Form (PRP Theorems)

$$\text{PRP} \Rightarrow \neg\exists t_{\text{final}}.\, \forall t \geq t_{\text{final}}.\, \forall c.\, \text{cost}(c) \leq \text{budget}(a, t)$$

---

## Bucket 25: Theorem Transport — Health Goal Layer (Tier 3 Closure)

**Role:** Machine-certifies that every health-goal predicate is transport-safe under compatible model extensions. Forms the lattice-stability guarantee for the health goal layer.

**File:** `Meta/TheoremTransport.lean`

### Transport Theorems (∀-predicates — plain `Compatible`)

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `transport_safe_withdrawal` | Meta/TheoremTransport.lean | `Compatible E C → SafeWithdrawalGoal C → SafeWithdrawalGoal (forget E)` | Withdrawal gates preserved |
| `transport_reliable_export` | Meta/TheoremTransport.lean | `Compatible E C → ReliableExportGoal C → ReliableExportGoal (forget E)` | Export gates preserved |
| `transport_sound_deposits` | Meta/TheoremTransport.lean | `Compatible E C → SoundDepositsGoal C → SoundDepositsGoal (forget E)` | Deposit soundness preserved |
| `transport_self_correction` | Meta/TheoremTransport.lean | `Compatible E C → SelfCorrectionGoal C → SelfCorrectionGoal (forget E)` | Competition gate preserved |
| `transport_corrigible_universal` | Meta/TheoremTransport.lean | `Compatible E C → CorrigibleLedgerGoal C → ∀ B, hasRevision B → revise-soundness` | Universal part of corrigibility |
| `transport_corrigible_ledger` | Meta/TheoremTransport.lean | `SurjectiveCompatible E C → CorrigibleLedgerGoal C → CorrigibleLedgerGoal (forget E)` | Full corrigibility (needs surjectivity) |

### Vacuous Operation Theorems

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `vacuous_selfCorrects_revision_gate` | Meta/TheoremTransport.lean | `VacuousSelfCorrects M → RevisionGate M` | Disabled self-correction → RevisionGate vacuous |
| `vacuous_revision_corrigible_universal` | Meta/TheoremTransport.lean | `VacuousRevise M → universal corrigibility` | Disabled revise → revision part trivial |
| `vacuous_submit_safe_withdrawal` | Meta/TheoremTransport.lean | `VacuousSubmit M → SafeWithdrawalGoal M` | Disabled submit → safe withdrawal vacuous |
| `vacuous_truth_sound_deposits` | Meta/TheoremTransport.lean | `VacuousTruth M → SoundDepositsGoal M` | Disabled truth → sound deposits vacuous |
| `vacuous_truth_reliable_export` | Meta/TheoremTransport.lean | `VacuousTruth M → ReliableExportGoal M` | Disabled truth → reliable export vacuous |

### Headline Pack

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `health_goal_transport_pack` | Meta/TheoremTransport.lean | All five ∀-transports packaged | Full Tier 3 certification |

### Supporting Definitions

| Definition | File | Purpose |
|------------|------|---------|
| `OperationMask` | Meta/TheoremTransport.lean | 8-bool operation dependency record |
| `mask_selfCorrection` | Meta/TheoremTransport.lean | Mask for RevisionGate |
| `mask_safeWithdrawal` | Meta/TheoremTransport.lean | Mask for SafeWithdrawalGoal |
| `mask_reliableExport` | Meta/TheoremTransport.lean | Mask for ReliableExportGoal |
| `mask_soundDeposits` | Meta/TheoremTransport.lean | Mask for SoundDepositsGoal |
| `mask_corrigibleLedger` | Meta/TheoremTransport.lean | Mask for CorrigibleLedgerGoal |
| `SurjectiveCompatible` | Meta/TheoremTransport.lean | Compatible + πBubble/πDeposit surjective |
| `VacuousSelfCorrects`/`VacuousHasRevision`/`VacuousRevise`/`VacuousSubmit`/`VacuousTruth` | Meta/TheoremTransport.lean | Disabled-operation predicates |

---

## Bucket 26: Theorem Transport — Main Library Layer (Tier 4 Closure)

**Role:** Machine-certifies that all four theorem clusters in the main library are transport-safe. Closes the Tier 4 gap in DOCS/MODULARITY.md: not just the competition gate but all operational LTS theorems and all five health goals are machine-certified as transport-safe.

**File:** `Meta/Tier4Transport.lean`

### Cluster A: Standalone Commitments Family

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `commitments_pack` | Commitments.lean | SEVFactorization ∧ header_stripping_harder ∧ TemporalValidity | Unconditional commitment bundle (C3/C7b/C8) |

C1, C2, C4b, C5, C6b are proved as named theorems in `Commitments.lean`
(see `innovation_allows_traction_without_authorization`, `WorldCtx.no_ledger_tradeoff`,
`redeemability_requires_more_than_consensus`, `ExportGating`, `NoSelfCorrectionWithoutRevision`).

### Cluster B: Structural Unconditional

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `structural_theorems_unconditional` | Meta/Tier4Transport.lean | SEVFactorization ∧ TemporalValidity ∧ monolithic_not_injective ∧ header_stripping_harder | Cluster B certification |

### Cluster B Extended: LTS-Universal Operational Theorems

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `lts_theorems_step_universal` | Meta/Tier4Transport.lean | withdrawal_gates ∧ repair_enforces_revalidation ∧ repair_requires_prior_challenge ∧ submit_enforces_revalidation | Packages four LTS facts as universally valid for all SystemState/Step |

### Cluster C: Concrete Bank Bridge

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `concrete_bank_vacuous_gate` | Meta/Tier4Transport.lean | `ConcreteBankModel` with `selfCorrects := False` satisfies RevisionGate | Base case |
| `concrete_bank_transport` | Meta/Tier4Transport.lean | `Compatible E ConcreteBankModel → RevisionGate base → RevisionGate (forget E)` | Extension safety |
| `concrete_bank_vacuous_transport` | Meta/Tier4Transport.lean | Combines base + transport for the vacuous case | Convenience theorem |

### Cluster C Extended: All Five Health Goals Transport

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `concrete_bank_all_goals_transport` | Meta/Tier4Transport.lean | SafeWithdrawalGoal ∧ ReliableExportGoal ∧ SoundDepositsGoal ∧ SelfCorrectionGoal ∧ CorrigibleLedgerGoal (universal ∀-part) all transport through Compatible ConcreteBankModel extensions | Full health-goal transport certification (plain Compatible) |

### Cluster C Extended: Full CorrigibleLedgerGoal Transport (SurjectiveCompatible)

The \u2203-component of `CorrigibleLedgerGoal` (`\u2203 B, hasRevision B`) needs a preimage
pullback that `Compatible` alone cannot provide. `SurjectiveCompatible` adds
`bubbleSurj` (every C-bubble has a preimage in E), enabling full transport.

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `concrete_bank_all_goals_transport_surj` | Meta/Tier4Transport.lean | SafeWithdrawalGoal ∧ ReliableExportGoal ∧ SoundDepositsGoal ∧ SelfCorrectionGoal ∧ **full** CorrigibleLedgerGoal (∃+∀) transport through SurjectiveCompatible extensions | Full corrigibility: no residual ∃-witness caveat |

### Full Pack

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `tier4_full_pack` | Meta/Tier4Transport.lean | SEV ∧ LTS-withdrawal ∧ SafeWithdrawal ∧ ReliableExport ∧ SoundDeposits ∧ SelfCorrection ∧ universal-corrigibility | Headline Tier 4 pack (plain Compatible; ∀-corrigibility only) |
| `tier4_full_pack_surj` | Meta/Tier4Transport.lean | Same 8 conjuncts with **full** CorrigibleLedgerGoal (∃+∀) in place of universal-corrigibility | Maximal Tier 4 pack (SurjectiveCompatible; no residual caveat) |

### Supporting Definitions

| Definition | File | Purpose |
|------------|------|---------|
| `ConcreteBankModel` | Meta/Tier4Transport.lean | CoreModel instance from concrete EpArch bank types |

### Math Form

$$\forall E \supseteq C_{\text{bank}},\; G(C_{\text{bank}}) \Rightarrow G(\text{forget}(E)) \text{ for } G \in \{\text{SafeWithdrawal, ReliableExport, SoundDeposits, SelfCorrection, Corrigible}_\forall\}$$

$$\text{Step}_{\text{withdraw}} \Rightarrow \text{ACL} \land \tau\text{-valid} \land \text{Deposited} \quad (\text{for every } SystemState)$$

### Design-Imposition Theorems (Tier A — Proved)

Pattern: `AgentConstraints + HealthGoal + ¬Mechanism → False`
File: `Agent/Imposition.lean`

| Theorem | Statement | Mechanism Required |
|---------|-----------|-------------------|
| `safe_withdrawal_needs_reversibility` | Time-bounded agents need reversibility | Reversibility |
| `sound_deposits_need_cheap_validator` | PRP + bounded audit need cheap validators | CheapValidator |
| `reliable_export_needs_gate` | Fallible observation needs export gates | ExportGate |

### Budget Forcing (Corner 8)

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `finite_budget_forces_triage` | Theorems/Corners.lean | ledger.length > budget → ∃ d_idx not revalidated | Corner 8: Budget overflow forces triage |

### Fault Containment Theorems (Tier A)

**File:** `Agent/Resilience.lean`

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `lie_containment_principle` | Agent/Resilience.lean | Lies create untrusted deposits, don't flip truth | Epistemic sandbox |
| `no_gate_bypass` | Agent/Resilience.lean | Gate enforcement is architectural, not agent-dependent | Gate invariance |

### AgentLTS Simulation Theorems (Tier A)

**File:** `Agent/Resilience.lean`

`AgentLTS` is a proof-oriented abstraction of `StepSemantics` that packages containment invariants as an LTS with a simulation relation. Theorems here prove that StepSemantics preserves these invariants via the simulation.

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `truth_invariant_preserved` | Agent/Resilience.lean | Single step preserves truth invariant | Containment: truth is stable |
| `truth_preserved_along_trace` | Agent/Resilience.lean | Full trace preserves truth invariant | Containment: trace-level truth |
| `gate_invariant_preserved` | Agent/Resilience.lean | Single step preserves gate invariant | Containment: gate is stable |
| `gate_preserved_along_trace` | Agent/Resilience.lean | Full trace preserves gate invariant | Containment: trace-level gate |
| `agent_containment` | Agent/Resilience.lean | Agent actions are contained within the epistemic sandbox | Fault containment |
| `invariants_transfer_via_simulation` | Agent/Resilience.lean | If `AgentLTS` preserves invariant I, then `StepSemantics` preserves I | Simulation correctness |
| `stepsemantics_preserves_containment_invariants` | Agent/Resilience.lean | StepSemantics directly preserves truth + gate invariants | Headline containment closure |

---

## Bucket 19: Feasibility / Existence Under Constraints (Tier A)

**Role:** Establishes that the constraint+objective package is consistent AND that success forces Bank primitives.

### Headline Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `structural_goals_force_bank_primitives` | Feasibility.lean | ∀ W. StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W | Minimality: forced primitives (structural path) |
| `existence_under_constraints_structural` | Feasibility.lean | ∃ W. StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W | Existence via structural path |
| `existence_under_constraints_embedding` | Feasibility.lean | ∃ W. ForcingEmbedding W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W | Existence via embedding path (strongest form) |
| `bundled_structure_forces_bank_primitives` | Feasibility.lean | `SystemOperationalBundle W → WorldBridgeBundle W → SatisfiesAllProperties W → containsBankPrimitives W` | Headline 4-argument form; no `WorldCtx` |
| `world_bundles_feasible` | Feasibility.lean | World bundles satisfiable | World non-vacuity |
| `commitments_feasible` | Feasibility.lean | 8 commitments satisfiable | Model non-vacuity |
| `joint_feasible` | Feasibility.lean | Constraints + objectives jointly satisfiable | Non-vacuity |
| `all_bundles_satisfiable` | WorldWitness.lean | W_* bundles jointly satisfiable | World witness |
| `all_commitments_satisfiable` | ConcreteLedgerModel.lean | 8 commitments have witnesses | Commitment witness |
| `concrete_satisfies_all_properties` | ConcreteLedgerModel.lean | ConcreteWorkingSystem satisfies all properties | Witness for success |

### Supporting Structures

| Structure | File | Purpose |
|-----------|------|---------|
| `Realizer` | Realizer.lean | Type packaging commitment proofs |
| `SuccessfulSystem` | Realizer.lean | Type packaging successful system (W + sf + sat) |
| `ConcreteRealizer` | Realizer.lean | Realizer witness instance |
| `ConcreteSuccessfulSystem` | Realizer.lean | SuccessfulSystem witness instance |
| `WitnessCtx` | WorldWitness.lean | Concrete WorldCtx instance |

---

## Bucket 20: Meta-Status Proof Pack (Tier A)

**Role:** Establishes the theory's epistemic status: falsifiable, not fully authorizable, safe on credit.

### Headline Theorem

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `meta_status_proof_pack` | Meta/FalsifiableNotAuthorizable.lean | P1 ∧ P2 ∧ P3 packaged | Meta-status |

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `theory_floor_satisfiable` | Meta/FalsifiableNotAuthorizable.lean | TheoryFloor WitnessCtx | Floor is consistent |
| `theory_floor_falsifiable` | Meta/FalsifiableNotAuthorizable.lean | ∃ C, ¬ TheoryFloor C | Countercontext exists |
| `theory_floor_not_fully_authorizable` | Meta/FalsifiableNotAuthorizable.lean | TheoryFloor C → CreditRequired C | Credit required |
| `witness_requires_credit` | Meta/FalsifiableNotAuthorizable.lean | CreditRequired WitnessCtx | Witness needs credit |
| `credit_required_implies_not_fully_authorizable` | Meta/FalsifiableNotAuthorizable.lean | CreditRequired C → ¬FullyAuthorizableByObs C | Bridge lemma |
| `theory_floor_implies_not_fully_authorizable` | Meta/FalsifiableNotAuthorizable.lean | TheoryFloor C → ¬FullyAuthorizableByObs C | Clean P2 |
| `witness_not_fully_authorizable` | Meta/FalsifiableNotAuthorizable.lean | ¬FullyAuthorizableByObs WitnessCtx | Instantiated P2 |
| `credit_safe_under_extension` | Meta/FalsifiableNotAuthorizable.lean | Extensions preserve revision-gate | Non-collapse |
| `trivial_has_no_lies` | Meta/FalsifiableNotAuthorizable.lean | `¬∃ w a P, TrivialCtx.Lie w a P` — if all propositions are true everywhere, no lie is constructible; uses `kernel_redundant_without_lies` | Contrapositive of `W_lies_possible`; EpArch mechanisms are non-trivial in any world that departs from TrivialCtx |

### Optional Stretch: Theory Core Claim (Witness-Specific)

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `lift_notDeterminedByObs_theory_core` | Meta/TheoryCoreClaim.lean | Underdetermination transfers | Transfer lemma |
| `witness_theory_core_not_determined` | Meta/TheoryCoreClaim.lean | `NotDeterminedByObs theory_core` | Headline stretch |
| `witnessTheoryCoreCtx_satisfies_floor_bundles` | Meta/TheoryCoreClaim.lean | Floor preserved | Extension preserves floor |

| Definition | File | Purpose |
|------------|------|---------|
| `MetaClaim` | Meta/TheoryCoreClaim.lean | Single constructor `theory_core` |
| `AddTheoryCore` | Meta/TheoryCoreClaim.lean | Conservative extension functor |
| `WitnessTheoryCoreCtx` | Meta/TheoryCoreClaim.lean | WitnessCtx + theory_core |
| `theory_core` | Meta/TheoryCoreClaim.lean | The designated underdetermined token |

### Universal Schema (No Witness Dependence)

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `theory_core_token_not_determined` | Meta/TheoryCoreClaim.lean | Universal: any C with bundle | Schema theorem |
| `witness_theory_core_not_determined'` | Meta/TheoryCoreClaim.lean | Witness as instance of schema | Instance corollary |

| Definition | File | Purpose |
|------------|------|---------|
| `AddTheoryCoreFromPartialObs` | Meta/TheoryCoreClaim.lean | Extension specialized to extracted claim |
| `theory_core_token` | Meta/TheoryCoreClaim.lean | The designated token (parametric) |

### Supporting Definitions

| Definition | File | Purpose |
|------------|------|---------|
| `TheoryFloor` | Meta/FalsifiableNotAuthorizable.lean | W-bundles inhabitable |
| `TrivialCtx` | Meta/FalsifiableNotAuthorizable.lean | Countercontext where floor fails |
| `CreditRequired` | Meta/FalsifiableNotAuthorizable.lean | ∃ P, NotDeterminedByObs P |
| `FullyAuthorizableByObs` | Meta/FalsifiableNotAuthorizable.lean | ∀ P, determines_truth P |

### Vocabulary Guard

**DO NOT say:** "never provable true", "unprovable"  
**Allowed:** "not fully authorizable from obs", "underdetermined", "credit required"

---

## Bucket 21: Multi-Agent Corroboration

**Role:** Formal machinery for when multi-agent corroboration is required (conditional minimality) and when it fails (common-mode / bubble infection).

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `single_source_can_accept_false` | Agent/Corroboration.lean | Single-source attack → can accept false | T1: Vulnerability |
| `no_spof_requires_multi_source` | Agent/Corroboration.lean | NoSPoF goal + attack → contradiction | T1: Necessity |
| `common_mode_breaks_naive_corroboration` | Agent/Corroboration.lean | Common-mode → k-of-n fails for k ≤ compromised | T3: Bubble infection |
| `two_of_two_fails_under_common_mode` | Agent/Corroboration.lean | 2-of-2 fails under common-mode | T3: Minimal case |
| `common_mode_requires_diversity` | Agent/Corroboration.lean | ∀ k ≤ compromised, naive k-of-n fails | T4: Diversity required |
| `k_of_n_suffices_under_independence` | Agent/Corroboration.lean | Independence bound + k > t → resilient | T2: Sufficiency |
| `corroboration_package` | Agent/Corroboration.lean | T1 ∧ T3 bundled | Headline package |

### Supporting Definitions

| Definition | File | Purpose |
|------------|------|---------|
| `SingleSourceAttack` | Agent/Corroboration.lean | Weak adversary: can corrupt one source |
| `CommonModeAttack` | Agent/Corroboration.lean | Strong adversary: correlated compromise |
| `SingleSourceAcceptance` | Agent/Corroboration.lean | Accept on one attestation |
| `HasKWitnesses` | Agent/Corroboration.lean | k witnesses from pool attest |
| `KOfNIndependentAcceptance` | Agent/Corroboration.lean | k pairwise-independent witnesses |
| `IndependenceBounded` | Agent/Corroboration.lean | At most t compromised among independent |
| `HonestImpliesTrue` | Agent/Corroboration.lean | Honest attestation → truth |

---

## Bucket 22: Entrenchment (Pathological Ladder State)

**Role:** Entrenchment (Certainty + structural refusal to revise) breaks safe withdrawal — the deposit becomes inactive but the agent cannot acknowledge this.

**References:** A.S7, B1.10, B1.11

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `entrenchment_breaks_safe_withdrawal` | Theorems/Corners.lean | Entrenched + inactive deposit → ¬isDeposited | A.S7: Entrenchment blocks withdrawal |
| `entrenched_cannot_withdraw` | Theorems/Corners.lean | Entrenched + inactive → no Step.withdraw fires | B1.10/B1.11: Full withdrawal failure |

### Supporting Definitions

| Definition | File | Description |
|------------|------|-------------|
| `Entrenched` | Basic.lean:189 | `certainty_L a P ∧ ignores_bank_signal a P` — Certainty + closed review channel |
| `EntrenchedAgent` | Theorems/Corners.lean | Structure bundling agent, claim, and entrenchment proof |
| `deposit_no_longer_active` | Theorems/Corners.lean | Deposit is Quarantined or Revoked |

### Math Form

$$\text{Entrenched}(a, P) \land \text{deposit-no-longer-active}(s, d) \Rightarrow \neg\text{isDeposited}(s, d)$$

---

## Bucket 23: Observational Completeness (Header/Deposit Extensionality)

**Role:** Proves deposit identity is exhausted by named fields — no hidden degrees of freedom. Forces adversaries onto constraint enumeration rather than field discovery.

**References:** A.OC1, A.OC2, B16b.1–B16b.4

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `header_ext` | Header.lean:149 | Headers agreeing on 6 fields are equal | B16b.1: Header extensionality |
| `deposit_ext` | Header.lean:166 | Deposits agreeing on 4 fields are equal | A.OC2: Deposit extensionality |
| `observational_completeness` | Header.lean:182 | Field-equal deposits are predicate-indistinguishable | B16b.3: Closure theorem |
| `observational_completeness_full` | Header.lean:199 | All 9 primitive fields → predicate-indistinguishable | A.OC1: Full field version |

### Math Form

$$d_1.P = d_2.P \;\land\; d_1.h = d_2.h \;\land\; d_1.\text{bubble} = d_2.\text{bubble} \;\land\; d_1.\text{status} = d_2.\text{status} \implies d_1 = d_2$$

$$\forall\, \text{Pred},\ d_1 = d_2 \implies \text{Pred}(d_1) \implies \text{Pred}(d_2)$$

---

## Bucket 24: Lattice-Stability / Graceful Scale-Down

**Role:** Proves EpArch is bidirectionally modular at the `RevisionGate` / competition-gate layer: the `RevisionGate` predicate is preserved in both directions under bundle perturbation. Removing the self-correction health goal leaves a valid sub-architecture where `RevisionGate` holds vacuously; compatible extensions at any level preserve `RevisionGate` through the existing transport machinery.

**File:** `Modularity.lean`

**The headline claim:** EpArch is a floor, not a cage. Any sub-bundle is a valid EpArch instantiation; any compatible extension of a sub-bundle is safe.

### Downward: Graceful Degradation

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `graceful_degradation` | Modularity.lean | `NoSelfCorrection M → RevisionGate M` | Vacuous gate: drop self-correction goal → RevisionGate holds |

### OdometerModel — Concrete Minimal Sub-bundle

A non-revisable system satisfying only `SoundDepositsGoal` (readings must be verifiable). Demonstrates that EpArch applies to systems far simpler than its full constraint envelope.

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `odometer_no_self_correction` | Modularity.lean | `NoSelfCorrection OdometerModel` | Odometer has no self-correction |
| `odometer_revision_gate` | Modularity.lean | `RevisionGate OdometerModel` | Odometer satisfies the revision gate (vacuously) |
| `odometer_sound_deposits` | Modularity.lean | `SoundDepositsGoal OdometerModel` | Readings are verifiable within effectiveTime |
| `odometer_not_corrigible` | Modularity.lean | `¬CorrigibleLedgerGoal OdometerModel` | Correctly fails the revision goal it does not claim |

### Sub-level RevisionSafety (Downward + Upward)

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `sub_revision_safety` | Modularity.lean | `Compatible E S.model → RevisionGate S.model → RevisionGate (forget E)` | RevisionSafety holds at every sub-bundle level |
| `odometer_extension_safe` | Modularity.lean | `Compatible E OdometerModel → RevisionGate (forget E)` | Any compatible extension of the odometer satisfies the revision gate |

### Headline: ModularityPack

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `modularity_pack` | Modularity.lean | `GracefulDegradation ∧ SubRevisionSafety ∧ FullRevisionSafety` | Full bidirectional lattice-stability |

### Math Form

$$\text{NoSelfCorrection}(M) \Rightarrow \text{RevisionGate}(M)$$

$$\text{Compatible}(E, S) \land \text{RevisionGate}(S) \Rightarrow \text{RevisionGate}(\text{forget}(E))$$

$$\text{ModularityPack} := \text{GracefulDegradation} \land \text{SubRevisionSafety} \land \text{safe\_extension\_preserves}$$

### Supporting Definitions

| Definition | File | Purpose |
|------------|------|---------|
| `RevisionGate` | RevisionSafety.lean | `∀ B, selfCorrects B → hasRevision B` — competition gate predicate |
| `NoSelfCorrection` | Modularity.lean | Sub-bundle predicate: no bubble self-corrects |
| `SubBundle` | Modularity.lean | CoreModel + active SubGoal predicate + satisfaction witness |
| `OdometerModel` | Modularity.lean | Concrete sub-bundle: one bubble, append-only, SoundDepositsGoal only |

---

## Bucket 27: Modularity Meta-Theorem — ∀ S âŠ† Constraints, projection_valid S

**Role:** Machine-certifies that EpArch is fully modular: there exists a single
universally-quantified theorem over all subsets of the six constraints, and a
`PartialWellFormed` type that lets users opt into exactly k ≤ 6 constraints.

**Files:** `Minimality.lean` (definitions: `ConstraintSubset`, `PartialWellFormed`, `allConstraints`, `noConstraints`) + `Meta/Modular.lean` (theorems: `partial_no_constraints`, `modular`)

### Definitions

| Definition | File | Purpose |
|------------|------|---------|
| `ConstraintSubset` | Minimality.lean | 6-Bool vector selecting which constraints are active |
| `PartialWellFormed W S` | Minimality.lean | Subset-parameterized biconditional fragment; `allConstraints` is the strongest subset |
| `allConstraints` | Minimality.lean | `âŸ¨true,true,true,true,true,trueâŸ©` — strongest subset (all six biconditionals) |
| `noConstraints` | Minimality.lean | `âŸ¨false,false,false,false,false,falseâŸ©` — nothing required |

### Theorems

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `partial_no_constraints` | Meta/Modular.lean | `PartialWellFormed W noConstraints` holds for every W | Base case: empty subset |
| `modular` | Meta/Modular.lean | `∀ S W, PartialWellFormed W S → projection_valid S W` | **The meta-theorem** |

### Math Form

$$\text{PartialWellFormed}(W, S) :\equiv \bigwedge_{X \in S} (\text{handles}_X(W) \leftrightarrow \text{HasFeature}_X(W))$$

$$\texttt{modular}: \forall S \subseteq \text{Constraints},\; \forall W,\; \text{PartialWellFormed}(W, S) \Rightarrow \bigwedge_{X \in S} (\text{handles}_X(W) \Rightarrow \text{HasFeature}_X(W))$$

### Design Note

Dropping constraint X = setting `S.X := false`. The X-conjunct in `modular`'s conclusion
becomes `false = true → ...`, which is vacuously true. The forcing theorems for all
other selected constraints remain live implications backed by the required biconditionals.

---

## Bucket 28: Configurable Certification Engine — `EpArchConfig → ClusterTag → certified proof`

**Role:** Closes the claim that all 29 theorem clusters are individually certified:
25 clusters (constraint, goal, Tier 4, world) are user-selectable via `EpArchConfig`;
the remaining 4 (1 constraint-modularity meta-theorem cluster + 3 lattice-stability
clusters) are always enabled because they depend on no config gate. Given any
`EpArchConfig`, the engine computes exactly which clusters apply and provides
machine-checked justification for each enabled cluster. This includes 8 world-bundle
obligation clusters wiring `EpArchConfig.worlds` to proved obligation theorems in
`WorldCtx.lean` and `Adversarial/Obligations.lean`, 1 constraint-modularity cluster from
`Meta/Modular.lean`, and 3 lattice-stability clusters from `Modularity.lean`.

**Note on `.partial_observability`:** Now fully wired. `WorldCtx.partial_obs_no_omniscience`
formalizes the epistemic-gap argument: under partial observability there exists a proposition
that no agent can determine from observations alone — independent of the PRP cost-budget
argument. Together, PRP (cost) and partial observability (underdetermination) give two
orthogonal reasons terminal epistemic closure is unreachable.

**Files:** `Meta/ClusterRegistry.lean` (29-cluster tag registry, routing, per-family canonical lists) and `Meta/Config.lean` (witness carriers, `certify`, completeness theorems, named proof witnesses)

**Design:** `clusterEnabled cfg c : Bool` is the computable routing function. `showConfig cfg`
is `#eval`-able and returns human-readable cluster descriptions. `certify cfg` returns a
`CertifiedProjection` that names every enabled cluster and carries genuine `ConstraintProof`
records for each Tier 2 forcing cluster.  Named proof witnesses (`cluster_forcing_*`,
`cluster_goal_*`, `cluster_tier4_*`, `cluster_world_*`) state and prove the exact proposition
for each cluster.

**Three-layer architecture:**
1. **Routing layer** — `clusterEnabled`, `enabled`, `complete`, `sound` (all clusters, routing only, `clusterValid := True`)
2. **Constraint proof layer** — `constraintProof`/`constraintWitnesses` (Tier 2 forcing clusters: real `ConstraintProof` with genuine proposition + proof; possible because `WorkingSystem` is monomorphic)
3. **Proof-content layer** — `cluster_*` universe-polymorphic theorems (all 29 clusters; goal/Tier4/world/meta-modular/lattice clusters reference universe-polymorphic types and live in `Meta/Config.lean`)

### Definitions / Configuration Language

| Definition | File | Purpose |
|------------|------|---------|
| `ConstraintTag` | Meta/Config.lean | 6 constraint tags (distributed_agents … truth_pressure) |
| `GoalTag` | Meta/Config.lean | 5 health-goal tags (safeWithdrawal … selfCorrection) |
| `WorldTag` | Meta/Config.lean | 8 world-bundle tags (lies_possible … ddos) |
| `EpArchConfig` | Meta/Config.lean | User-supplied config: lists of active constraints/goals/worlds |
| `ClusterTag` | Meta/ClusterRegistry.lean | 29 cluster tags spanning Tiers 2–4, world obligations, constraint-modularity, and lattice-stability |
| `EnabledConstraintCluster` | Meta/ClusterRegistry.lean | Sub-inductive: 6 Tier 2 forcing cluster tags |
| `EnabledGoalCluster` | Meta/ClusterRegistry.lean | Sub-inductive: 6 Tier 3 health-goal transport cluster tags |
| `EnabledTier4Cluster` | Meta/ClusterRegistry.lean | Sub-inductive: 5 Tier 4 library cluster tags |
| `EnabledWorldCluster` | Meta/ClusterRegistry.lean | Sub-inductive: 8 world-bundle cluster tags |
| `EnabledMetaModularCluster` | Meta/ClusterRegistry.lean | Sub-inductive: 1 constraint-modularity meta-theorem cluster tag |
| `EnabledLatticeCluster` | Meta/ClusterRegistry.lean | Sub-inductive: 3 lattice-stability cluster tags |
| `EnabledConstraintCluster.toClusterTag` | Meta/ClusterRegistry.lean | Embed constraint sub-tag into `ClusterTag` |
| `EnabledGoalCluster.toClusterTag` | Meta/ClusterRegistry.lean | Embed goal sub-tag into `ClusterTag` |
| `EnabledTier4Cluster.toClusterTag` | Meta/ClusterRegistry.lean | Embed Tier 4 sub-tag into `ClusterTag` |
| `EnabledWorldCluster.toClusterTag` | Meta/ClusterRegistry.lean | Embed world sub-tag into `ClusterTag` |
| `EnabledMetaModularCluster.toClusterTag` | Meta/ClusterRegistry.lean | Embed meta-modular sub-tag into `ClusterTag` |
| `EnabledLatticeCluster.toClusterTag` | Meta/ClusterRegistry.lean | Embed lattice sub-tag into `ClusterTag` |
| `allConstraintClusters` | Meta/ClusterRegistry.lean | Canonical list of 6 Tier 2 cluster tags |
| `allGoalClusters` | Meta/ClusterRegistry.lean | Canonical list of 6 Tier 3 cluster tags |
| `allTier4Clusters` | Meta/ClusterRegistry.lean | Canonical list of 5 Tier 4 cluster tags |
| `allWorldClusters` | Meta/ClusterRegistry.lean | Canonical list of 8 world-bundle cluster tags |
| `allMetaModularClusters` | Meta/ClusterRegistry.lean | Canonical list of 1 constraint-modularity cluster tag |
| `allLatticeClusters` | Meta/ClusterRegistry.lean | Canonical list of 3 lattice-stability cluster tags |
| `allClusters` | Meta/ClusterRegistry.lean | Canonical ordered list of all 29 ClusterTags (derived from 6 per-family lists) |
| `clusterEnabled` | Meta/ClusterRegistry.lean | `EpArchConfig → ClusterTag → Bool` (computable routing); meta-modular and lattice always enabled |
| `clusterDescription` | Meta/ClusterRegistry.lean | `ClusterTag → String` — one-line human-readable description |
| `explainConfig` | Meta/Config.lean | `EpArchConfig → List ClusterTag` — enabled clusters |
| `clusterValid` | Meta/Config.lean | `ClusterTag → Prop` — always `True` (every cluster is proved) |
| `showConfig` | Meta/Config.lean | `EpArchConfig → List String` — `#eval`-able routing report |
| `ConstraintProof` | Meta/Config.lean | Proof-carrying record: `statement : Prop`, `proof : statement` (Tier 2 only) |
| `constraintProof` | Meta/Config.lean | `EnabledConstraintCluster → ConstraintProof` — real proposition + proof for each forcing cluster |
| `MetaModularWitness` | Meta/Config.lean | Indexed proof carrier for constraint-modularity cluster (1 constructor: `.modular`) |
| `metaModularWitness` | Meta/Config.lean | `(c : EnabledMetaModularCluster) → MetaModularWitness c` — delivers the proof |
| `LatticeWitness` | Meta/Config.lean | Indexed proof carrier for lattice-stability clusters (3 constructors: `.graceful`, `.subSafety`, `.pack`) |
| `latticeWitness` | Meta/Config.lean | `(c : EnabledLatticeCluster) → LatticeWitness c` — delivers the proof |
| `CertifiedProjection` | Meta/Config.lean | Proof-carrying record: enabled clusters + soundness + `constraintWitnesses` + `metaModularWitnesses` + `latticeWitnesses` + filtered enabled lists for all families |
| `certify` | Meta/Config.lean | `EpArchConfig → CertifiedProjection cfg` |
| `fullConfig` | Meta/Config.lean | Sample: all 6 constraints, 5 goals, 8 worlds |
| `minimalConfig` | Meta/Config.lean | Sample: 1 constraint, 1 goal, no worlds |
| `goalsOnlyConfig` | Meta/Config.lean | Sample: no constraints, all 5 goals |

### Theorems

#### Soundness Theorem

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `clusterEnabled_sound` | Meta/Config.lean | `clusterEnabled cfg c = true → clusterValid c` | All enabled clusters are machine-proved |

#### Correspondence / Completeness Theorems

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `mem_enabledConstraintWitnesses_of_enabled` | Meta/Config.lean | `clusterEnabled cfg c.toClusterTag = true → âŸ¨c, constraintProof câŸ© âˆˆ (certify cfg).enabledConstraintWitnesses` | Completeness of Tier 2 witness list |
| `mem_enabledGoalWitnesses_of_enabled` | Meta/Config.lean | `clusterEnabled cfg c.toClusterTag = true → âŸ¨c, goalWitness câŸ© âˆˆ ...` | Completeness of Tier 3 witness list |
| `mem_enabledTier4Witnesses_of_enabled` | Meta/Config.lean | `clusterEnabled cfg c.toClusterTag = true → âŸ¨c, tier4Witness câŸ© âˆˆ ...` | Completeness of Tier 4 witness list |
| `mem_enabledWorldWitnesses_of_enabled` | Meta/Config.lean | `clusterEnabled cfg c.toClusterTag = true → âŸ¨c, worldWitness câŸ© âˆˆ ...` | Completeness of world witness list |
| `mem_enabledMetaModularWitnesses_of_enabled` | Meta/Config.lean | `clusterEnabled cfg c.toClusterTag = true → âŸ¨c, metaModularWitness câŸ© âˆˆ (certify cfg).enabledMetaModularWitnesses` | **Phase F** — completeness of meta-modular witness list |
| `mem_enabledLatticeWitnesses_of_enabled` | Meta/Config.lean | `clusterEnabled cfg c.toClusterTag = true → âŸ¨c, latticeWitness câŸ© âˆˆ (certify cfg).enabledLatticeWitnesses` | **Phase F** — completeness of lattice witness list |

#### Tier 2 Named Proof Witnesses (Forcing)

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `cluster_forcing_distributed_agents` | Meta/Config.lean | `StructurallyForced W → handles_distributed_agents W → HasBubbles W` | Witness for `.forcing_distributed_agents` |
| `cluster_forcing_bounded_audit` | Meta/Config.lean | `StructurallyForced W → handles_bounded_audit W → HasTrustBridges W` | Witness for `.forcing_bounded_audit` |
| `cluster_forcing_export` | Meta/Config.lean | `StructurallyForced W → handles_export W → HasHeaders W` | Witness for `.forcing_export` |
| `cluster_forcing_adversarial` | Meta/Config.lean | `StructurallyForced W → handles_adversarial W → HasRevocation W` | Witness for `.forcing_adversarial` |
| `cluster_forcing_coordination` | Meta/Config.lean | `StructurallyForced W → handles_coordination W → HasBank W` | Witness for `.forcing_coordination` |
| `cluster_forcing_truth` | Meta/Config.lean | `StructurallyForced W → handles_truth_pressure W → HasRedeemability W` | Witness for `.forcing_truth` |

#### Tier 3 Named Proof Witnesses (Health-Goal Transport)

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `cluster_goal_safeWithdrawal` | Meta/Config.lean | `Compatible E C → SafeWithdrawalGoal C → SafeWithdrawalGoal (forget E)` | Witness for `.goal_safeWithdrawal` |
| `cluster_goal_reliableExport` | Meta/Config.lean | `Compatible E C → ReliableExportGoal C → ReliableExportGoal (forget E)` | Witness for `.goal_reliableExport` |
| `cluster_goal_soundDeposits` | Meta/Config.lean | `Compatible E C → SoundDepositsGoal C → SoundDepositsGoal (forget E)` | Witness for `.goal_soundDeposits` |
| `cluster_goal_selfCorrection` | Meta/Config.lean | `Compatible E C → SelfCorrectionGoal C → SelfCorrectionGoal (forget E)` | Witness for `.goal_selfCorrection` |
| `cluster_goal_corrigible_universal` | Meta/Config.lean | `Compatible E C → CorrigibleLedgerGoal C → ∀-corrigibility for (forget E)` | Witness for `.goal_corrigible_universal` |
| `cluster_goal_corrigible_full` | Meta/Config.lean | `SurjectiveCompatible E C → CorrigibleLedgerGoal C → CorrigibleLedgerGoal (forget E)` | Witness for `.goal_corrigible_full` |

#### Tier 4-C Named Proof Witnesses (Bank Goal Transport)

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `cluster_tier4_bank_goals_compat` | Meta/Config.lean | All 5 ∀-goals + universal corrigibility via Compatible | Witness for `.tier4_bank_goals_compat` |
| `cluster_tier4_bank_goals_surj` | Meta/Config.lean | All 5 goals + full CorrigibleLedgerGoal via SurjectiveCompatible | Witness for `.tier4_bank_goals_surj` |

#### World-Bundle Named Proof Witnesses (Obligation Theorems)

All 8 `WorldTag` values are wired to proved obligation theorems.
`.partial_observability` was the last to be wired (commit `44dc17d`),
formalizing the epistemic-gap argument via `WorldCtx.partial_obs_no_omniscience`.

| Theorem | File | Statement | World Bundle | Underlying Theorem |
|---------|------|-----------|--------------|--------------------|
| `cluster_world_lies_possible` | Meta/Config.lean | `C.W_lies_possible → ∃ w a P, C.Lie w a P` | `.lies_possible` | `WorldCtx.lie_possible_of_W` |
| `cluster_world_bounded_audit` | Meta/Config.lean | `C.RequiresSteps w P k → t < k → ¬C.VerifyWithin w P t` | `.bounded_verification` | `WorldCtx.bounded_audit_fails` |
| `cluster_world_asymmetric_costs` | Meta/Config.lean | `C.W_asymmetric_costs → W.export_cost < W.defense_cost` | `.asymmetric_costs` | `WorldCtx.cost_asymmetry_of_W` |
| `cluster_world_partial_observability` | Meta/Config.lean | `C.W_partial_observability → ∃ P, C.NotDeterminedByObs P` | `.partial_observability` | `WorldCtx.partial_obs_no_omniscience` |
| `cluster_world_spoofed_v` | Meta/Config.lean | `W_spoofedV → is_V_spoofed v → ¬has_path p` | `.spoofedV` | `AdversarialObligations.spoofed_V_blocks_path_of_W` |
| `cluster_world_lies_scale` | Meta/Config.lean | `W_lies_scale → W.costs.export_cost < W.costs.defense_cost` | `.lies_scale` | `AdversarialObligations.lies_scale_of_W` |
| `cluster_world_rolex_ddos` | Meta/Config.lean | `W_rolex_ddos → same_structure W.rolex_structure W.ddos_structure` | `.rolex_ddos` | `AdversarialObligations.rolex_ddos_structural_equivalence_of_W` |
| `cluster_world_ddos` | Meta/Config.lean | `W_ddos → some_vector_overwhelmed s → is_collapsed c` | `.ddos` | `AdversarialObligations.ddos_causes_verification_collapse_of_W` |

#### Constraint-Modularity Meta-Theorem Witnesses (Phase F)

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `cluster_meta_modular` | Meta/Config.lean | `∀ S W, PartialWellFormed W S → projection_valid S W` | Witness for `.meta_modular` |

#### Lattice-Stability Witnesses (Phase F)

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `cluster_lattice_graceful` | Meta/Config.lean | `∀ M, NoSelfCorrection M → RevisionGate M` | Witness for `.lattice_graceful` |
| `cluster_lattice_sub_safety` | Meta/Config.lean | `Compatible E S.model → RevisionGate S.model → RevisionGate (forget E)` | Witness for `.lattice_sub_safety` |
| `cluster_lattice_pack` | Meta/Config.lean | Full bidirectional lattice-stability conjunction (graceful + sub-safety + full revision safety) | Witness for `.lattice_pack` |

---

## Bucket 29: Lean Kernel Instantiation (Meta/LeanKernel/)

**Role:** Self-referential demonstration that Lean's own type-checking kernel is a valid, fully-grounded EpArch instantiation. Two layers are proved: (1) `LeanKernelCtx : WorldCtx` satisfies three W_* world-assumption bundles with kernel-specific interpretations (`sorry` ↔ lies, heartbeat ↔ bounded verification, proof irrelevance ↔ partial observability); (2) `LeanWorkingSystem : WorkingSystem` satisfies all six architectural features, `PartialWellFormed allConstraints`, and `containsBankPrimitives` — both by direct construction and by the structural convergence path. Self-referential note: this file is type-checked by the same kernel it models.

**Files:** `Meta/LeanKernel/World.lean` (world + architecture layers, OleanStaleness), `Meta/LeanKernel/SFailure.lean` (S-field failure taxonomy)

### World Layer (LeanKernelCtx — WorldCtx Instantiation)

| Theorem | Statement | Kernel Interpretation |
|---------|-----------|----------------------|
| `holds_W_lies_possible` | `LeanKernelCtx.W_lies_possible` | `sorry` is an unconditional utterance gate; `False` is a true-but-unprovable claim in the clean environment |
| `holds_W_bounded_verification` | `LeanKernelCtx.W_bounded_verification` | Every elaboration step consumes ≥ 1 heartbeat; a budget-0 verifier cannot decide any claim |
| `holds_W_partial_observability` | `LeanKernelCtx.W_partial_observability` | Proof irrelevance: `obs w = ()` for all `w`; clean and sorry-tainted worlds are observation-equivalent yet truth-distinct |
| `lean_kernel_satisfies_bundles` | All three bundles jointly inhabited | Joint `Nonempty` witness for the three W_* types |
| `lean_kernel_theory_floor` | `EpArch.Meta.TheoryFloor LeanKernelCtx` | Kernel is a concrete `TheoryFloor` witness alongside `WitnessCtx` |
| `lean_kernel_no_tradeoff` | `∀ L, obs_based L → ¬(supports_innovation L ∧ supports_coordination L)` | Kernel faces the same innovation/coordination tradeoff; Bank architecture is the structural response |
| `lean_is_eparch_world` | `∃ C : WorldCtx, Nonempty C.W_lies_possible ∧ … ∧ Nonempty C.W_partial_observability` | Existential: a valid EpArch WorldCtx exists — instantiated as `LeanKernelCtx` |

### Architecture Layer (LeanWorkingSystem — Has* Predicates)

`LeanWorkingSystem` is built from `withGroundedBehavior LeanGroundedBehavior {spec := LeanGroundedSystemSpec.toSystemSpec, …}`. All six `Option GroundedXStrict` fields are `some`; all six `HasX` predicates follow from `grounded_spec_contains_all`.

| Theorem | Statement | Evidence Source |
|---------|-----------|----------------|
| `lean_has_bubbles` | `HasBubbles LeanWorkingSystem` | `LeanGroundedBubbles` (Nat vs Int namespace disagreement) |
| `lean_has_trust_bridges` | `HasTrustBridges LeanWorkingSystem` | `LeanGroundedTrustBridges` (`import Init` trust bridge) |
| `lean_has_headers` | `HasHeaders LeanWorkingSystem` | `LeanGroundedHeaders` (`Nat.succ` type signature preserved) |
| `lean_has_revocation` | `HasRevocation LeanWorkingSystem` | `LeanGroundedRevocation` (sorry-tainted term → quarantine) |
| `lean_has_bank` | `HasBank LeanWorkingSystem` | `LeanGroundedBank` (InitDef produced and consumed) |
| `lean_has_redeemability` | `HasRedeemability LeanWorkingSystem` | `LeanGroundedRedeemability` (`#print axioms` audit path) |

### Architecture Layer — Properties and Forcing

| Theorem | Statement | Route |
|---------|-----------|-------|
| `lean_implements_bank_primitives` | `containsBankPrimitives LeanWorkingSystem` | Direct: `∀ P, HasX` by inspection of `GroundedXStrict` fields |
| `lean_partial_wellformed` | `PartialWellFormed LeanWorkingSystem allConstraints` | Via `grounded_partial_wellformed LeanGroundedBehavior LeanGroundedSystemSpec` |
| `lean_satisfies_all_properties` | `SatisfiesAllProperties LeanWorkingSystem` | Via `grounded_behavior_satisfies_all LeanGroundedBehavior _` |
| `lean_structurally_forced` | `StructurallyForced LeanWorkingSystem` | Via `embedding_to_structurally_forced lean_forcing_embedding` |
| `lean_structural_convergence` | `containsBankPrimitives LeanWorkingSystem` | Indirect: `convergence_structural` via `StructurallyForced`; independently verified |
| `lean_kernel_forces_bank_primitives` | `containsBankPrimitives LeanWorkingSystem` | Citability alias; uses the direct route (`lean_implements_bank_primitives`) |

### Namespace Forcing

`leanNamespaceDisagreement` is the concrete `AgentDisagreement` built from Lean's `open Nat` vs `open Int` semantics. `flat_scope_impossible` fires on it, grounding the bubble-necessity argument in kernel structure.

| Theorem | Statement | Role |
|---------|-----------|------|
| `lean_namespace_requires_scope_separation` | `¬∃ f, (∀ n, f n ↔ openNatAccepts n) ∧ (∀ n, f n ↔ openIntAccepts n)` | `flat_scope_impossible` instantiated on kernel name-resolution |
| `lean_no_flat_namespace_resolver` | `openNatAccepts` and `openIntAccepts` → `False` | Bridge impossibility: a flat resolver faithful to both namespaces is contradictory |
| `lean_has_bubbles_grounded` | `spec_has_bubbles LeanKernelSystemSpecGrounded` | `HasBubbles` derived from `LeanGroundedBubbles` evidence directly |

### Two-Layer Joint Witness

| Theorem | Statement | Role |
|---------|-----------|------|
| `lean_kernel_existence` | `(∃ C : WorldCtx, …three bundles…) ∧ (∃ W : WorkingSystem, PartialWellFormed W allConstraints ∧ StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W)` | Headline two-layer existential; type-checked by the kernel it witnesses |

### Math Form

$$\text{LeanKernelCtx.W\_lies\_possible} \;\Leftrightarrow\; \texttt{sorry} \text{ closes any goal}$$

$$\text{LeanKernelCtx.W\_bounded\_verification} \;\Leftrightarrow\; \text{heartbeat budget exhaustion}$$

$$\text{LeanKernelCtx.W\_partial\_observability} \;\Leftrightarrow\; \text{proof irrelevance}$$

$$\text{containsBankPrimitives}(\text{LeanWorkingSystem}) \quad \text{(directly and via } \text{convergence\_structural}\text{)}$$

### .olean Cache as Deposit Lifecycle (OleanStaleness)

`OleanRecord` maps a compiled object-file artifact to a `CDeposit` by setting τ = `compiled_at` (the source epoch at build time).

| Name | Statement | Interpretation |
|------|-----------|---------------|
| `olean_stale_when_source_changed` | `0 < r.compiled_at → source_changed epoch r → compute_status (olean_as_deposit r path) epoch = .Stale` | A changed source makes the `.olean` deposit stale; τ = compiled_at falls below the current epoch |
| `stale_olean_blocks_withdrawal` | `0 < r.compiled_at → source_changed epoch r → ¬ c_can_withdraw … (olean_as_deposit r path) epoch` | Stale `.olean` cannot be withdrawn; `c_can_withdraw` requires `compute_status = .Deposited` |

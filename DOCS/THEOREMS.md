# Theorem Inventory

This document catalogs **435** proved theorems in the formalization, organized by argumentative role. The count covers all named theorems, lemmas, and equivalent definitions in the EpArch namespace; internal list-manipulation helpers are excluded.

**What the architecture claims:** Decentralized epistemic authorization requires specific structural mechanisms — a lifecycle with type-separated stages, header-preserving export, a revision loop, temporal validity, and a Bank substrate. These aren't design preferences; they are forced by the combination of agent constraints and system health goals.

**What this document is:** A bucketed theorem index (Buckets 1–23), grouped by the claim each cluster supports. Each bucket names the Lean file, the key theorems, and the paper claim they underwrite. This is broader than Appendix A of the paper, which covers only paper-cited theorems with full math notation; this file covers the full proof burden distribution across the repo. For deeper exposition of any area, the standalone DOCS files are the right place.

**Tier labels:** **A** = proved unconditionally, **B** = conditional on a W-bundle premise, **C** = design axiom.

**All theorems are fully proved** — zero `sorry`, zero new axioms beyond the 35 listed in [AXIOMS.md](AXIOMS.md).

## Notation Dictionary

| Lean | Math | Description |
|------|------|-------------|
| `Trace.hasRevision t` | $\exists a \in t.\, a \in \{\text{Challenge}, \text{Revoke}\}$ | Trace contains revision action |
| `demonstratesSelfCorrection t i` | $\text{status}_s(i) = \text{Deposited} \land \text{status}_{s'}(i) = \text{Revoked}$ | Deposit transitions to revoked |
| `prohibits_revision s` | $\forall i.\, \neg\text{Quarantined}(s, i)$ | No deposit is challengeable |
| `diagnosability(h)` | $|\text{ObservableFields}(h)|$ | Cardinality of observable fields |
| `canTargetRepair f h` | $f \in \text{ObservableFields}(h)$ | Field is observable for repair |
| `τ_valid clock τ` | $\tau \leq \text{clock}$ | Timestamp within validity window |
| `strip d` | $\pi_{\text{content}}(d)$ | Project deposit to content only |

---

## Bucket 1: Lifecycle & Type-Separation

**Paper Role:** Establishes that different deposit statuses create different operational affordances.

### Core Theorems

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `candidate_blocks_withdrawal` | Theorems.lean | Candidate status blocks withdrawal | §5: Lottery dissolution |
| `withdrawal_requires_deposited` | Theorems.lean | Must be Deposited to withdraw | §6: Bank gates |
| `submit_produces_candidate` | Theorems.lean | Submit creates Candidate status | §6: Lifecycle |
| `traction_broader_than_authorization` | Theorems.lean | Traction ⊃ Authorization | §2: Core split |
| `authorization_implies_traction` | Theorems.lean | Authorization → Traction | §2: One direction |

### Math Form

$$\text{Candidate}(d) \Rightarrow \neg\text{canWithdraw}(d)$$

$$\text{canWithdraw}(d) \Rightarrow \text{Deposited}(d) \land \text{ACL}(a,d) \land \tau\text{-valid}(d)$$

---

## Bucket 2: Competition Gate Cluster (Revision ⇔ Self-Correction)

**Paper Role:** The central forcing constraint — self-correction requires revision capability.

### Core Theorems

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `no_revision_no_correction` | StepSemantics.lean | No revision → no self-correction | §12: Competition gate |
| `self_correction_requires_revision` | StepSemantics.lean | Self-correction → revision occurred | §12: Forward direction |
| `self_correcting_domain_permits_revision` | StepSemantics.lean | Self-correcting domain → permits revision | §12: Domain level |
| `repair_requires_prior_challenge` | Theorems.lean | Repair presupposes challenge | §14: Repair loop |
| `repair_enforces_revalidation` | Theorems.lean | Repair requires fresh validation | §14: No silent fix |
| `frozen_canon_no_revocation` | Theorems.lean | Single restricted step: ¬Revoked before → ¬Revoked after | Corner 6: Frozen canon |
| `frozen_canon_no_revocation_trace` | Theorems.lean | allRestrictedTrace t → ¬Revoked at start → ¬Revoked after full trace (trace induction over all steps) | Corner 6: Frozen canon (full trace) |

### Math Form

$$\text{prohibitsRevision}(s) \Rightarrow \neg\exists t.\, \text{demonstratesSelfCorrection}(t)$$

$$\text{SelfCorrecting}(D) \Rightarrow \text{permitsRevision}(D)$$

---

## Bucket 3: Export/Strip Asymmetry

**Paper Role:** Header stripping is information-destroying; import cannot reconstruct.

### Core Theorems

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `no_strip_left_inverse` | Theorems.lean | ¬∃ f. f ∘ strip = id | §10: Irreversibility |
| `strip_not_injective_if` | Theorems.lean | (d₁ ≠ d₂) ∧ (strip d₁ = strip d₂) → ¬∀ x y, strip x = strip y → x = y (negated injectivity, not just existential re-wrap) | §10: Non-injectivity |
| `import_cannot_reconstruct` | Theorems.lean | Import doesn't restore header | §10: No reconstruction |
| `different_headers_same_strip` | Theorems.lean | h₁ ≠ h₂ → strip(h₁) = strip(h₂) | §10: Non-injectivity |
| `different_headers_different_deposits` | Theorems.lean | Different headers → different deposits | §10: Provenance identity |
| `strip_loses_header_info` | Theorems.lean | Strip removes V field | §10: Information loss |
| `content_eq_not_implies_deposit_eq` | Theorems.lean | Same content ≠ same deposit | §10: Provenance matters |
| `provenance_matters` | Theorems.lean | Different provenance → different deposits | §10: Identity |

### stripV Properties

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `stripV_irreversible` | Theorems.lean | ∃ p1 ≠ p2 in Provenance → ¬∃ f. f ∘ stripV = id (requires non-trivial Provenance type) | §10: V-strip irreversibility |
| `stripV_idempotent` | Theorems.lean | stripV(stripV(x)) = stripV(x) | §10: Idempotency |
| `stripV_preserves_claim` | Theorems.lean | stripV preserves the claim | §10: Content preserved |

### Export Visibility (Corner 9)

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `export_creates_visibility` | Theorems.lean | Export step → deposit visible in target bubble | §10: Export semantics |
| `export_creates_B2_deposit` | Theorems.lean | Export step → concrete deposit record in target ledger (single premise) | §10: Deposit creation |
| `export_ignores_target_acl` | Theorems.lean | Export fires without ACL check on target | §10: ACL gap at boundary |

### Math Form

$$\nexists f : \text{Stripped} \to \text{Full}.\, f \circ \text{strip} = \text{id}$$

$$h_1 \neq h_2 \land \text{claim}(h_1) = \text{claim}(h_2) \Rightarrow \text{strip}(h_1) = \text{strip}(h_2)$$

---

## Bucket 4: Diagnosability (Observability Monotonicity)

**Paper Role:** Header stripping reduces diagnosability; fewer observable fields → coarser repair.

### v8 Diagnosability Module (Diagnosability.lean)

| Theorem | Statement | Paper Claim |
|---------|-----------|-------------|
| `diagnosability_full` | Full deposits: diagnosability = 6 | §15: Full observability |
| `diagnosability_stripped` | Stripped deposits: diagnosability = 0 | §15: Zero observability |
| `strip_reduces_diagnosability` | strip → diagnosability decreases | §7: Monotonicity |
| `stripped_no_field_repair` | Stripped can't target any field | §15: Coarse repair |
| `full_can_repair_any` | Full can target any field | §15: Surgical repair |
| `repair_requires_observability` | Repair granularity = observable fields | §15: Equivalence |

### v7 Bridge Theorems (Theorems.lean)

| Theorem | Statement | Paper Claim |
|---------|-----------|-------------|
| `strip_reduces_field_count` | FieldCount stripped < full | §7: Field count |
| `fewer_fields_coarser_repair` | Fewer fields → coarser repair | §15: Repair quality |
| `sev_refines_stripped` | SEV partitions refine stripped | §7: Refinement |
| `stripped_not_implies_sev` | Stripped ⊄ SEV distinction | §7: Asymmetry |

### Math Form

$$\text{diagnosability}(\text{full}) = 6 > 0 = \text{diagnosability}(\text{stripped})$$

$$f \notin \text{ObservableFields}(d) \Rightarrow \neg\text{canTargetRepair}(f, d)$$

### v7 Field-Localization Bridge (StepSemantics.lean)

| Theorem | Statement | Paper Claim |
|---------|-----------|-------------|
| `factorization_enables_field_identification` | Any broken Field ∈ {S,E,V,τ,red,acl} (Field enum exhaustion; has_SEV_factorization = True for all deposits; SEV premise vacuous) | §7: Field enum completeness |
| `factorization_enables_legibility` | Deposited + ∃ broken field → Legible (Field enum exhaustion; SEV premise vacuous) | §7: Legibility |
| `strong_sev_localizes_to_core_fields` | StepSemantics.lean | has_strong_SEV_factorization(∀ f, broken→f∈[S,E,V]) → ∃ broken field ∈ [S,E,V] (SEV premise essential; conclusion strictly stronger than 6-field) | §7: Strong SEV → core-field localization |
| `all_challenges_field_specific` | All challenges target one of 6 canonical fields | §7/§14: Field specificity |
| `headers_enable_field_diagnosis` | depositHasHeader → challenge is field-specific | §7: Header enables diagnosis |
| `header_enables_efficient_resolution` | depositHasHeader → efficient resolution via field targeting | §14: Header efficiency |
| `headers_improve_localization` | depositHasHeader → localization_score = 1 | §14: Optimal localization |

### Diagnosability Metric Theorems (Theorems.lean)

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `harder_without_headers` | Theorems.lean | diagLE(diagScore false, diagScore true) | §7: Stripped strictly harder |
| `header_stripped_harder` | Theorems.lean | header_stripped → systematically_harder | §7: Header effect (dispute level) |
| `header_improves_diagnosability` | Theorems.lean | header_preserved → ¬systematically_harder self | §7: Preserved → non-pathological |
| `header_localization_link` | Theorems.lean | dispute ∧ header_preserved → localizes | §7/§15: Header → localization |
| `diagnose_finds_broken` | Theorems.lean | Sound diagnosis oracle finds broken field | §15: Diagnostic completeness |

### v8 ↔ v7 Coupling Theorems (Theorems.lean)

Bridge theorems connecting Diagnosability.lean (v8) and Theorems.lean (v7) metrics:

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `fieldcount_full_eq_diagnosability` | Theorems.lean | FieldCount_Full = diagnosability true | Bridge: field-count ↔ score |
| `stripped_diagnosability_is_zero` | Theorems.lean | diagnosability false = 0 | Bridge: stripped score = 0 |
| `v8_implies_v7_strip_reduces` | Theorems.lean | v8 hard → v7 field-count reduction | Bridge: v8 ⇒ v7 |
| `stripped_repair_must_be_coarse` | Theorems.lean | ∀ f, ¬canTargetRepair false f | Bridge: coarse repair (alias stripped_no_field_repair) |
| `full_repair_can_be_surgical` | Theorems.lean | ∀ f, canTargetRepair true f | Bridge: surgical repair (alias full_can_repair_any) |

---

## Bucket 5: τ (Temporal Validity)

**Paper Role:** Time creates pressure for maintenance; staleness blocks operations.

### Core Theorems

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `stale_blocks_withdrawal` | Theorems.lean | Stale deposits can't withdraw | §14: Hygiene |
| `tick_can_cause_staleness` | Theorems.lean | Clock tick → may become stale | §14: Time pressure |
| `withdrawal_requires_fresh` | Theorems.lean | Withdrawal needs τ-valid | §14: Freshness gate |
| `τ_valid_mono` | StepSemantics.lean | τ validity is monotonic in clock | §14: Temporal ordering |
| `current_from_clock` | Theorems.lean | current(clock, τ) iff τ ≤ clock | §14: Temporal predicate |
| `current_stable` | Theorems.lean | current is preserved under non-tick steps | §14: Stability |

### Math Form

$$\text{Stale}(d, \text{clock}) \Rightarrow \neg\text{canWithdraw}(d)$$

$$\tau\text{-valid}(\text{clock}, \tau) \land \text{clock}' > \text{clock} \Rightarrow \text{may}(\neg\tau\text{-valid}(\text{clock}', \tau))$$

---

## Bucket 6: Case Bindings (Illustrative)

**Paper Role:** Map epistemological puzzles to architectural diagnoses. These are *illustrative*, not claimed as philosophical theorems.

### Gettier Cases

| Theorem | File | Diagnosis |
|---------|------|-----------|
| `gettier_is_V_failure` | Theorems.lean | Gettier = V-field failure |
| `GettierRoutesToVFailure` | Theorems.lean | Routes to V diagnosis |
| `canonical_gettier_is_gettier` | Theorems.lean | Structure match |
| `canonical_gettier_conditions` | Theorems.lean | Canonical Gettier satisfies all GettierCase conditions |

### Fake Barn Cases

| Theorem | Diagnosis |
|---------|-----------|
| `fake_barn_is_E_failure` | Fake Barn = E-field failure |
| `FakeBarnRoutesToEFailure` | Routes to E diagnosis |
| `canonical_fake_barn_is_fake_barn` | Canonical fake barn satisfies FakeBarnCase |
| `canonical_fake_barn_has_E_failure` | Canonical fake barn → E-field failure |

### Lottery Paradox

| Theorem | Diagnosis |
|---------|-----------|
| `LotteryIsTypeError` | Lottery = type error (Traction ≠ Authorization) |
| `confabulation_is_type_error` | Confabulation = type error (LLM instantiation of LotteryIsTypeError) |
| `credence_does_not_auto_close` | High credence ≠ authorization |
| `status_distinction_blocks_lottery` | Candidate/Deposited distinction blocks paradox |
| `lottery_paradox_dissolved_architecturally` | Full dissolution theorem |

### Other Puzzles

| Theorem | Puzzle | Diagnosis |
|---------|--------|-----------|
| `closure_dissolution` | Closure | Type separation |
| `luminosity_dissolution` | Luminosity | Type separation |
| `skepticism_dissolution` | Skepticism | Local redeemability |
| `contextualism_dissolution` | Contextualism | Policy variation |
| `testimony_dissolution` | Testimony | Export structure |
| `peer_disagreement_dissolution` | Disagreement | Routing |
| `higher_order_knowledge_dissolution` | Higher-order knowledge | Epistemic regress dissolved |
| `apriori_dissolution` | A priori knowledge | Domain parameterization |
| `moorean_is_export_contradiction` | Moorean paradox | Export contradiction (pair to `moorean_export_contradiction`) |
| `preface_dissolution` | Preface paradox | individual_deposits p → meta_deposit_about_collection p (standards differ by construction; non-tautological — preface_case requires standards_differ field) |
| `forgotten_evidence_dissolution` | Forgotten evidence | Persistence via header |
| `group_knowledge_dissolution` | Group knowledge | Bubble separation |
| `value_of_knowledge_dissolution` | Value of knowledge | Exportability distinction |
| `epistemic_injustice_dissolution` | Epistemic injustice | Import corruption |
| `extended_cognition_dissolution` | Extended cognition | Bubble membership |

---

## Bucket 7: Invariant Preservation

**Paper Role:** System maintains well-formedness across transitions.

| Theorem | File | Statement |
|---------|------|-----------|
| `step_preserves_valid_status` | StepSemantics.lean | Steps preserve valid statuses |
| `trace_preserves_valid_status` | StepSemantics.lean | Traces preserve valid statuses |
| `step_preserves_separation` | StepSemantics.lean | Steps preserve type separation |
| `step_preserves_auditability` | StepSemantics.lean | Steps preserve auditability |
| `step_no_revision_preserves_deposited` | StepSemantics.lean | Revision-free step preserves `isDeposited` for all deposits |
| `trace_no_revision_preserves_deposited` | StepSemantics.lean | Revision-free trace preserves `isDeposited` (induction over steps) |
| `deposits_survive_revision_free_trace` | Theorems.lean | LTS corollary: deposits survive any revision-free trace |

---

## Bucket 8: Modal Properties (Safety/Sensitivity ↔ S/E/V)

**Paper Role:** Connect modal epistemology to architectural fields.

### Core Theorems

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `safety_V_link` | StepSemantics.lean | Unsafe → ¬V_independent | §7: Safety = V |
| `sensitivity_E_link` | StepSemantics.lean | Insensitive → ¬E_covers | §7: Sensitivity = E |
| `safety_iff_V_independence` | StepSemantics.lean | Safe ↔ V_independent | §7: Biconditional |
| `sensitivity_iff_E_coverage` | StepSemantics.lean | Sensitive ↔ E_covers | §7: Biconditional |
| `headers_provide_modal_properties` | StepSemantics.lean | header_preserved → Safe ∧ Sensitive | §7: Headers matter |
| `stripped_headers_lose_modal_properties` | StepSemantics.lean | ¬header_preserved → Unsafe ∧ Insensitive | §7: Stripping hurts |
| `safety_sensitivity_coincide` | StepSemantics.lean | Safe ↔ Sensitive | §7: Coincidence |
| `modal_robustness_is_header_preservation` | StepSemantics.lean | (Safe ∧ Sensitive) ↔ header_preserved | §7: Unified |

### Math Form

$$\text{Safe}(d) \Leftrightarrow \text{V\_independent}(d) \Leftrightarrow \text{header\_preserved}(d)$$

$$\text{Sensitive}(d) \Leftrightarrow \text{E\_covers}(d) \Leftrightarrow \text{header\_preserved}(d)$$

### Modal Case Theorems (Theorems.lean)

Applications of the safety/sensitivity framework to specific epistemological cases:

| Theorem | File | Statement |
|---------|------|-----------|
| `safety_V_link_case` | Theorems.lean | SafetyCase → V-violation |
| `safety_is_V_condition` | Theorems.lean | Safety collapses to V-independence for SafetyCase |
| `sensitivity_E_link_case` | Theorems.lean | SensitivityCase → E-gap |
| `sensitivity_is_E_condition` | Theorems.lean | Sensitivity collapses to E-coverage for SensitivityCase |

---

## Bucket 9: Grounded Minimality (StepSemantics.lean)

**Paper Role:** Each architectural feature is necessary for specific capabilities.

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `grounded_coordination_requires_bank` | StepSemantics.lean | Coordination → Bank | §6: Bank necessity |
| `grounded_export_requires_headers` | StepSemantics.lean | Export → Headers | §10: Header necessity |
| `grounded_bounded_audit_requires_bridges` | StepSemantics.lean | Bounded audit → Bridges | §10: Bridge necessity |
| `grounded_no_bridge_forces_revalidation` | StepSemantics.lean | No bridge → revalidate | §10: Export cost |
| `grounded_revocation_requires_quarantine` | StepSemantics.lean | Revocation → Quarantine | §14: Quarantine necessity |
| `grounded_distributed_agents_require_bubbles` | StepSemantics.lean | Distributed → Bubbles | §5: Bubble necessity |
| `grounded_truth_pressure_requires_redeemability` | StepSemantics.lean | Truth pressure → Redeemability | §8: Redeemability necessity |

---

## Bucket 10: Adversarial Model (AdversarialBase.lean)

**Paper Role:** Formalize attack patterns and boundary conditions.

### Attack Structures

| Definition | Description | Paper Source |
|------------|-------------|--------------|
| `FullStackAttack` | Coordinated multi-primitive attack | Appendix E |
| `PseudoDeposit` | Deposit with spoofed V | Appendix E |
| `DDoSAttack` | Bandwidth exhaustion | Appendix C |
| `DDoSVector` | Four attack vectors | Appendix C.2 |
| `AttackLevel` | 5-level hierarchy (Lie → DDoS) | §15.10 |
| `Lie` | Primitive false deposit | §15.10 |
| `ProxySubstitution` | Similarity exploitation | §15.11 |

### Core Theorems in AdversarialBase.lean (Proved)

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `sophistication_monotonic` | AdversarialBase.lean | Attack levels form monotonic hierarchy | §15.10 |
| `sincerity_norms_irrelevant` | AdversarialBase.lean | Lies don't require violating sincerity norms | §15.10 |
| `lies_structurally_possible` | AdversarialBase.lean | Lies are structurally possible given `is_lie` | §15.10 |
| `adversarial_proxy_signature` | AdversarialBase.lean | Adversarial proxy = truthful but mislicensed | §15.11 |

---

## Bucket 11: Repair Loop Semantics

**Paper Role:** Challenge-repair-revalidation cycle.

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `repair_enforces_revalidation` | Theorems.lean | Repair → revalidate | §14: No silent fix |
| `submit_enforces_revalidation` | Theorems.lean | Submit → validate | §6: Validation on entry |
| `repair_requires_prior_challenge` | Theorems.lean | Repair requires quarantine | §14: Challenge first |
| `challenge_has_field_localization` | StepSemantics.lean | Challenge targets field | §14: Field-specific |
| `repair_requires_quarantine` | StepSemantics.lean | Repair needs quarantine | §14: State gate |
| `repair_targets_field` | StepSemantics.lean | Repair addresses field | §14: Surgical |
| `repair_produces_candidate` | StepSemantics.lean | Repair → Candidate | §14: Back to start |
| `repair_resets_to_candidate` | StepSemantics.lean | Full cycle reset | §14: Lifecycle |

---

## Bucket 12: Withdrawal Gates (Three-Gate Model)

**Paper Role:** Withdrawal requires Status + ACL + τ.

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `withdrawal_requires_three_gates` | StepSemantics.lean | Status ∧ ACL ∧ τ | §6: Three gates |
| `withdrawal_gates` | Theorems.lean | Withdrawal preconditions | §6: Gate theorem |
| `canWithdrawAt_iff_gates` | Theorems.lean | CanWithdraw ↔ gates | §6: Equivalence |
| `withdrawal_requires_canWithdrawAt` | Theorems.lean | Step requires predicate | §6: Enforcement |
| `canWithdrawAt_enables_step` | Theorems.lean | Predicate enables step | §6: Sufficiency |

---

## Bucket 13: Obligation Theorems (World ⇒ Mechanism)

**Paper Role:** Convert implicit mechanism axioms into explicit conditional theorems.

**Files:** `World.lean`, `AdversarialObligations.lean`

### Philosophy

World assumptions parameterize theorems rather than being asserted as true.
This transforms "take it or leave it" axioms into "if you accept X, then Y follows."

### Core Theorems (World.lean)

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `lie_possible_of_W` | World.lean | W_lies_possible → ∃ w a P, Lie w a P | Adversarial: lies exist |
| `all_agents_can_lie_of_W` | World.lean | W_lies_possible → ∀ a, can_lie a | Adversarial: universal capability |
| `bounded_audit_fails` | World.lean | RequiresSteps w P k → t < k → ¬VerifyWithin | §14: Bounded audit |
| `cost_asymmetry_of_W` | World.lean | W_asymmetric_costs → export < defense | Adversarial: cost asymmetry |

### Adversarial Obligation Theorems (AdversarialObligations.lean)

#### Batch A: Mechanism Axioms

| Theorem | File | Statement | Original Axiom |
|---------|------|-----------|----------------|
| `spoofed_V_blocks_path_of_W` | AdversarialObligations.lean | W_spoofedV → spoofed V → ¬path | `spoofed_V_blocks_path` |
| `ddos_causes_verification_collapse_of_W` | AdversarialObligations.lean | W_ddos → overwhelmed → collapsed | `ddos_causes_verification_collapse` |
| `collapse_causes_centralization_of_W` | AdversarialObligations.lean | W_collapse → collapsed → centralized | `collapse_causes_centralization` |
| `lies_scale_of_W` | AdversarialObligations.lean | W_lies_scale → export < defense | `lies_scale` |
| `rolex_ddos_structural_equivalence_of_W` | AdversarialObligations.lean | W_rolex_ddos → same_structure | `rolex_ddos_structural_equivalence` |
| `ddos_to_centralization_of_W` | AdversarialObligations.lean | W_ddos_full → overwhelmed → centralized | (composed chain) |

#### Batch B: Boundary Condition Countermeasures

| Theorem | File | Statement | Original Axiom |
|---------|------|-----------|----------------|
| `cheap_validator_blocks_V_attack_of_W` | AdversarialObligations.lean | W_cheap_validator → cheap validator → ¬V_attack | `cheap_validator_blocks_V_attack` |
| `trust_bridge_blocks_V_attack_of_W` | AdversarialObligations.lean | W_trust_bridge → trust bridge → ¬V_attack | `trust_bridge_blocks_V_attack` |
| `reversibility_neutralizes_τ_of_W` | AdversarialObligations.lean | W_reversibility → reversible → ¬τ_attack | `reversibility_neutralizes_τ` |
| `E_inclusion_closes_expertise_gap_of_W` | AdversarialObligations.lean | W_E_inclusion → E includes threat → ¬gap_exploited | `E_inclusion_closes_expertise_gap` |
| `cheap_constraint_blocks_V_spoof_of_W` | AdversarialObligations.lean | W_cheap_constraint → cheap test → ¬V_attack | `cheap_constraint_blocks_V_spoof` |

### World Assumption Bundles

| Bundle | Contents | Enables |
|--------|----------|---------|
| `W_lies_possible` | some_false, unrestricted_utterance | lie_possible_of_W |
| `W_bounded_verification` | verification_has_cost | bounded_audit_fails |
| `W_partial_observability` | obs_underdetermines | (future: epistemic limits) |
| `W_asymmetric_costs` | export_cost, defense_cost, asymmetry | cost_asymmetry_of_W |
| `W_spoofedV` | broken_chain_no_path | spoofed_V_blocks_path_of_W |
| `W_ddos` | overwhelm_causes_collapse | ddos_causes_verification_collapse_of_W |
| `W_collapse_centralization` | exhaustion_triggers_delegation | collapse_causes_centralization_of_W |
| `W_lies_scale` | costs, asymmetry_holds | lies_scale_of_W |
| `W_rolex_ddos` | rolex_structure, ddos_structure, both_* | rolex_ddos_structural_equivalence_of_W |
| `W_ddos_full` | extends W_ddos, W_collapse_centralization | ddos_to_centralization_of_W |
| `W_cheap_validator` | cheap_validator_enables_check | cheap_validator_blocks_V_attack_of_W |
| `W_trust_bridge` | trust_bridge_enables_check | trust_bridge_blocks_V_attack_of_W |
| `W_reversibility` | reversibility_neutralizes | reversibility_neutralizes_τ_of_W |
| `W_E_inclusion` | E_modeling_closes_gap | E_inclusion_closes_expertise_gap_of_W |
| `W_cheap_constraint` | cheap_test_exposes_spoof | cheap_constraint_blocks_V_spoof_of_W |

### Math Form

$$\text{W\_lies\_possible} \Rightarrow \exists w\, a\, P.\, \text{Lie}(w, a, P)$$

$$\text{RequiresSteps}(w, P, k) \land t < k \Rightarrow \neg\text{VerifyWithin}(w, P, t)$$

$$\text{W\_ddos\_full} \land \text{overwhelmed}(s) \Rightarrow \text{centralized}(t)$$

---

## Adversarial Attack Surfaces

Each architectural constraint creates both a capability and an exploitable surface. The following tables catalog attack scenarios formalized through Lean structures in the adversarial modules.

### Lifecycle (Candidate/Deposited Gap)
| Attack | Mechanism | Formalized In |
|--------|-----------|---------------|
| Ladder Overload | Flood Candidate stage faster than validation | `DDoSVector.LadderOverload` |
| Premature Closure Pressure | Force Candidate→Deposited before validation | `τ_compressed` in `FullStackAttack` |
| Traction Hijacking | Generate traction without earning authorization | `TractionAuthorizationSplit`; `lies_scale_of_W` |

### Revision / Self-Correction
| Attack | Mechanism | Formalized In |
|--------|-----------|---------------|
| Challenge Flooding | Overwhelm revision capacity with frivolous challenges | DDoS on repair loop |
| Denial Triggering | Induce "nothing is trustworthy" state | `DDoSVector.DenialTriggering` |
| Revision Weaponization | Abuse challenge mechanism for harassment | `repair_requires_prior_challenge` (quarantine gate) |

### Export / Strip Asymmetry
| Attack | Mechanism | Formalized In |
|--------|-----------|---------------|
| V-spoofing | Stripped deposits lose provenance | `stripV_loses_provenance`, `stripV_not_injective` |
| Proxy substitution | Stripping enables "similar enough" swaps | `ProxySubstitution`; `lies_scale_of_W` |
| Provenance laundering | Strip → re-wrap with false headers | `no_strip_left_inverse` |
| Authority inflation | Stripped claim re-attributed to higher authority | `stripV_loses_provenance` |

### Diagnosability
| Attack | Mechanism | Formalized In |
|--------|-----------|---------------|
| E-field poisoning | Flood environment with noise → degrade E-field reliability | `DDoSVector.EFieldPoisoning` |
| Diagnostic denial | Force stripping → only coarse repair possible | `stripped_no_field_repair` |
| Repair loop exhaustion | Trigger unlocalizable repairs → infinite retry | `stripped_no_field_repair` |

### Temporal Validity (τ)
| Attack | Mechanism | Formalized In |
|--------|-----------|---------------|
| τ compression | Force artificially short validity windows | `τ_compressed` in `FullStackAttack` |
| Staleness induction | Delay victim's refresh → deposits expire | `tick_can_cause_staleness` |
| Temporal denial | Flood refresh queue → critical deposits can't renew | maintenance pressure semantics |
| Clock manipulation | Accelerate expiry via shared/observable clock | `stale_blocks_withdrawal` |

### Coordinated Full-Stack
| Attack Class | Lean Reference | Severity |
|--------------|----------------|----------|
| Resource Exhaustion | `DDoSVector.LadderOverload`, `DDoSVector.VChannelExhaustion` | High |
| Provenance Spoofing | `stripV_loses_provenance`, `ProxySubstitution` | Medium |
| Diagnostic Degradation | `DDoSVector.EFieldPoisoning` | Medium |
| Temporal Pressure | `FullStackAttack.τ_compressed` | Medium |
| Environmental Poisoning | `fake_barn_is_E_failure` | High |
| Coordinated Full-Stack | `FullStackAttack` structure | Critical |

The `FullStackAttack` structure (`AdversarialBase.lean`) captures coordinated attacks combining: `τ_compressed` (force rapid re-verification), `V_spoofed` (fake provenance), `cues_amplified` (cheap signals substituted for expensive checks), `consultation_blocked` (block access to real validators), `expertise_exploited` (exploit expertise gap).

---

## Bucket 14: Health → Necessity Theorems

**Paper Role:** Connect health goals to mechanism requirements (invariants).

**File:** `Health.lean`, `Agent/Imposition.lean`

### Philosophy

If you want health property X, you NEED mechanism Y. These are conditional necessity claims.

### Capability Predicates (Agent/Imposition.lean)

| Predicate | Description | What It Captures |
|-----------|-------------|------------------|
| `ReversibleWithdrawal` | System can undo withdrawals | Reversibility capability |
| `CheapValidatorAvailable` | System has low-cost verification | Validator capability |
| `ExportGateEnforced` | System blocks erroneous exports | Gate capability |

### Health Goal Definitions (Health.lean)

Health goals are now definitional predicates over `CoreModel`/`CoreOps` (0 axioms):

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

**Paper Role:** Turn "out of scope" prose into machine-checkable scope boundaries.

**File:** `ScopeIrrelevance.lean`

### Philosophy

Reduce reviewer attack surface by proving that certain "fundamentals" (physics, consciousness, psychology, embodiment) are *irrelevant-by-design* — theorems don't depend on them.

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

### Fundamentals Coverage

| Fundamental | Status | Mechanism |
|-------------|--------|-----------|
| Physics/Substrate | Irrelevant | `ModelHom` preserves |
| Consciousness | Irrelevant | Extra state erased |
| Psychology | Irrelevant | System-level only |
| Embodiment | Irrelevant | Via `Obs` abstraction |
| Optimal Rationality | Not assumed | No Bayes dependency |
| Free Will | Not assumed | No moral judgment |
| Metaphysics of Truth | Abstract | Truth is predicate |

---

## Bucket 16: Discharged Linking Axioms

**Paper Role:** Convert philosophical "linking axioms" from axioms to definitional theorems.

**File:** `Theorems.lean`

### Philosophy

The original formalization had 20 "linking axioms" that connected philosophical concepts
(testimony, disagreement, contextualism, etc.) to the model structure. Phase 4 discharges
these by making the opaque predicates concrete.

### Batch 1: Discharged Axioms (10) — Explicit Fields

| Original Axiom | Now Theorem | Mechanism |
|----------------|-------------|-----------|
| `testimony_is_export` | ✅ theorem | `via_trust : Bool` field forces disjunction |
| `forgotten_evidence_persistence` | ✅ theorem | Deposit structure separates agent access from deposit |
| `disagreement_is_routing` | ✅ theorem | `MismatchType` enum exhausts cases |
| `group_bubble_separation` | ✅ theorem | Tautological (`≠` = `bubbles_differ`) |
| `deposit_exportability` | ✅ theorem | `KnowledgeState` distinguishes deposit/certainty |
| `certainty_not_exportable_link` | ✅ theorem | Pattern matching on `KnowledgeState` |
| `local_redeemability_survives` | ✅ theorem | Definitional identity: `local_redeemability_holds = severs_constraint_contact` |
| `context_is_policy` | ✅ theorem | Fields make policy variation explicit; uses `high_stakes_implies_policy` structural invariant |
| `no_semantic_shift` | ✅ theorem | `is_semantic_shift` is vacuously false (`PropLike ≠ PropLike` is `False`) |
| `injustice_is_import_corruption` | ✅ theorem | Fields encode deflation/downgrade |
| `artifact_bubble_membership` | ✅ theorem | Tautological (inclusion = membership) |

### Batch 2: Discharged Axioms (10) — Concrete Definitions

| Original Axiom | Now Theorem | Mechanism |
|----------------|-------------|-----------|
| `DiagnoseField` | ✅ def + theorem | `DiagnosableDeposit` with `broken_fields` list |
| `safety_V_link` | ✅ theorem | `SafetyCase` with `v_ok` field; Safety ≡ V_independence |
| `sensitivity_E_link` | ✅ theorem | `SensitivityCase` with `e_ok` field; Sensitivity ≡ E_covers |
| `closure_type_separation` | ✅ theorem | `closure_puzzle` with boolean fields + explicit hypotheses |
| `luminosity_type_separation` | ✅ theorem | `luminosity_puzzle` with boolean fields + disjunction hypothesis |
| `higher_order_relocation` | ✅ theorem | `higher_order_case` + `WellFormedHigherOrder` constraint |
| `apriori_domain_parameterization` | ✅ theorem | `apriori_case` + `WellFormedApriori` constraint |
| `moorean_export_contradiction` | ✅ theorem | `moorean_case` + `ExportRequiresDeposit` constraint |
| `notation_invariance_of_redeemability` | ✅ theorem | Proof-redeemability is invariant under coherent bijective relabeling of propositions |
| `notation_invariance_of_empirical_redeemability` | ✅ theorem | Empirical redeemability likewise notation-invariant |
| `math_practice_is_bubble_distinct` | ✅ theorem | Mathematical practice is a bubble: notation varies, structural position (constraint surface) does not |
| `bridge_monolithic_opaque` | ✅ theorem | Vacuously true (has_SEV_factorization = True by construction) |
| `bridge_stripped_ungrounded` | ✅ theorem | Follows from depositHasHeader definition |

### Discharge Pattern

**Key insight:** Axioms encoding philosophical claims become theorems when:
1. Opaque predicates become concrete definitions with explicit fields
2. Well-formedness constraints encode the intended relationships
3. Theorems follow from structure + constraints

**Result:** All 20 linking axioms in Theorems.lean are now proved theorems.

### Notation Invariance (Added)

Three theorems establishing that the constraint surface is notation-independent:

| Theorem | Statement |
|---------|-----------|
| `notation_invariance_of_redeemability` | `redeemability_is_proof_consistency a ↔ redeemability_is_proof_consistency (relabel_case r a)` |
| `notation_invariance_of_empirical_redeemability` | `redeemability_is_physical_experiment a ↔ redeemability_is_physical_experiment (relabel_case r a)` |
| `math_practice_is_bubble_distinct` | Two relabelings produce distinct surface proposals (P varies) while redeemability is bitwise identical |

**Self-referential significance:** These proofs are themselves discharged by Lean's kernel — the constraint surface they claim is notation-invariant. Mathematical *practice* (notation, proof standards, community acceptance) is a bubble in the EpArch sense; the underlying structural positions are not.

---

## Bucket 17: Revision Safety

**Paper Role:** Guarantee that extending/strengthening the model doesn't break existing results.

**File:** `RevisionSafety.lean`

### Philosophy

Answers the question: "If I adopt this architecture and it's later incomplete, do I get stuck?"

**Answer:** No. The formalization provides three levels of revision safety:
1. **Premise Strengthening** — Adding assumptions preserves implications
2. **Compatible Extensions** — Extensions satisfying commuting laws preserve paper-facing properties
3. **Refinement Safety** — LTS refinements preserve safety invariants

### Premise Strengthening Theorems (Tier A)

| Theorem | Statement | Description |
|---------|-----------|-------------|
| `premise_strengthening` | (A → C) → (A ∧ B → C) | Adding constraints preserves implications |
| `premise_strengthening_dep` | (∀x, A x → C) → (∀x, A x ∧ B x → C) | Dependent version |
| `premise_chain` | (A → B → C) → (A ∧ B → C) | Chain composition |

### Compatible Extension Framework (Tier A)

| Structure | Description |
|-----------|-------------|
| `CoreSig` | Core type signature (Agent, Claim, Bubble, Time, Deposit, Header) |
| `CoreOps` | Core operations (truth, obs, verifyWithin, hasRevision, selfCorrects) |
| `CoreModel` | Bundle of CoreSig + CoreOps + Nonempty Bubble |
| `ExtSig` | Extended signature (adds AgentExtra, WorldExtra) |
| `ExtOps` | Extended operations (adds getAgentExtra, getWorldExtra) |
| `ExtModel` | Bundle of ExtSig + ExtOps |
| `Compatible` | Commuting laws between ExtModel and CoreModel |

### Compatible Structure (Contract Mode)

```lean
structure Compatible (E : ExtModel) (C : CoreModel) where
  -- Projections
  πBubble : E.sig.Bubble → C.sig.Bubble
  πDeposit : E.sig.Deposit → C.sig.Deposit
  πTime : E.sig.Time → C.sig.Time
  πAgent : E.sig.Agent → C.sig.Agent
  -- World primitive commuting laws
  truth_comm : ∀ B d, E.ops.truth B d ↔ C.ops.truth (πBubble B) (πDeposit d)
  obs_comm : ∀ d, E.ops.obs d ↔ C.ops.obs (πDeposit d)
  verifyWithin_comm : ∀ B d t, E.ops.verifyWithin B d t ↔ C.ops.verifyWithin (πBubble B) (πDeposit d) (πTime t)
  effectiveTime_comm : ∀ B, πTime (E.ops.effectiveTime B) = C.ops.effectiveTime (πBubble B)
  -- Bank primitive commuting laws
  submit_comm : ∀ a B d, E.ops.submit a B d ↔ C.ops.submit (πAgent a) (πBubble B) (πDeposit d)
  revise_comm : ∀ B d d', E.ops.revise B d d' ↔ C.ops.revise (πBubble B) (πDeposit d) (πDeposit d')
  -- Capability predicate commuting laws
  hasRevision_comm : ∀ B, E.ops.hasRevision B ↔ C.ops.hasRevision (πBubble B)
  selfCorrects_comm : ∀ B, E.ops.selfCorrects B ↔ C.ops.selfCorrects (πBubble B)
```

### Transport Theorems (Tier A)

| Theorem | Statement | Description |
|---------|-----------|-------------|
| `transport_core` | Compatible E C → PaperFacing C → PaperFacing (forget E) | Core transport |
| `safe_extension_preserves` | RevisionSafeExtension C → PaperFacing C → PaperFacing (forget R.ext) | Safe extension |
| `safety_preserved_under_contract_refinement` | Refinement → IsInvariant C Safety → IsInvariant R (Safety ∘ φ) | LTS refinement |

### Acceptance Tests (Diagnostic)

| Theorem | Description |
|---------|-------------|
| `goodExtension_compatible` | Extra-state extension satisfies Compatible (Iff.refl) |
| `badExtension_incompatible_witness` | Semantic-breaking extension FAILS Compatible |
| `badExtension_incompatible_if_id` | Corollary for identity projection |

### Key Diagnostic

The `badExtension_incompatible_witness` theorem proves that an extension which changes `selfCorrects` to always return `True` **cannot** satisfy `Compatible` with any model that has a non-self-correcting bubble.

This is the core contract: semantic-breaking extensions are blocked by the type system.

### Math Form

$$\text{Compatible}(E, C) \land \text{PaperFacing}(C) \Rightarrow \text{PaperFacing}(\text{forget}(E))$$

$$\text{Compatible} := \forall B.\, E.\text{selfCorrects}(B) \Leftrightarrow C.\text{selfCorrects}(\pi_B(B))$$

---

## Bucket 18: Agent Constraints & PRP

**Paper Role:** Mechanize "the system is designed for imperfect agents" via structural constraints.

**File:** `Agent.lean`

### Philosophy

The Agent layer captures why mechanisms are mandatory under realistic agent constraints.
Key insight: **Permanent Redeemability Pressure (PRP)** — agents are continuously challenged
and cannot achieve terminal epistemic closure.

### Agent Constraint Structure

| Structure | Description |
|-----------|-------------|
| `AgentConstraints` | Bundle of agent limitations (bounded verification, fallible observation, strategic utterance, PRP) |
| `PRP` | Permanent Redeemability Pressure (challenge stream, costs, budgets, infinite challenge arrival) |
| `Challenge` | Time-indexed challenge with content |
| `Budget` | Agent verification capacity function |
| `Mechanisms` | Architectural mechanism availability predicates |
| `HealthGoals` | System health objectives |
| `FaultEvent` | Agent failure modes (Lie, Omit, Misobserve, Forget, MisreportEvidence) |

### PRP Structure (Core)

```lean
structure PRP (Agent Claim : Type u) where
  challengeStream : TimeIdx → Option (Challenge Claim)
  challengeCost : VerifyCost Claim
  agentBudget : Agent → Budget
  challengesInfinite : ∀ t, ∃ t' > t, (challengeStream t').isSome
  pressureExists : ∀ a t, ∃ t' > t, ∃ c, 
    challengeStream t' = some c ∧ challengeCost c.content > agentBudget a t'
```

### PRP Consequence Theorems (Tier A — Fully Proved)

| Theorem | Statement | Paper Claim |
|---------|-----------|-------------|
| `no_global_closure_of_PRP` | ¬∃ t_final, ∀ t ≥ t_final, ∀ c, cost ≤ budget | No terminal epistemic closure |
| `needs_revision_of_PRP` | ∀ t, ∃ t' > t, challenge exceeds budget | Revision hooks mandatory |
| `needs_scoping_of_PRP` | ∃ t c, challenge exceeds budget | Scoped audit surfaces forced |
| `needs_revalidation_of_PRP` | ¬StableDepositSet under PRP | Stable deposit sets impossible |
| `prp_incompatible_with_global_redeemability` | ¬GlobalRedeemability under PRP | Global redeemability impossible |

### Math Form (PRP Theorems)

$$\text{PRP} \Rightarrow \neg\exists t_{\text{final}}.\, \forall t \geq t_{\text{final}}.\, \forall c.\, \text{cost}(c) \leq \text{budget}(a, t)$$

**Interpretation:** Under PRP, agents cannot reach a time after which all challenges are affordable.
This is the formalization of "embedded agency" — no God's-eye-view, no terminal verification.

### Design-Imposition Theorems (Tier A — Proved)

Pattern: `AgentConstraints + HealthGoal + ¬Mechanism → False`
File: `Agent/Imposition.lean`

| Theorem | Statement | Mechanism Required |
|---------|-----------|-------------------|
| `safe_withdrawal_needs_reversibility` | Time-bounded agents need reversibility | Reversibility |
| `sound_deposits_need_cheap_validator` | PRP + bounded audit need cheap validators | CheapValidator |
| `reliable_export_needs_gate` | Fallible observation needs export gates | ExportGate |

**Note:** These are proved theorems (Tier A), not axioms. They derive that certain
combinations are impossible from the agent-constraint and health-goal definitions.
The containment invariants (`truth_invariant_preserved`, `gate_invariant_preserved`)
are also proved by trace induction.

### Budget Forcing (Corner 8)

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `finite_budget_forces_triage` | Theorems.lean | ledger.length > budget → ∃ d_idx not revalidated | Corner 8: Budget overflow forces triage |

### Fault Containment Theorems (Tier A)

| Theorem | Statement | Paper Claim |
|---------|-----------|-------------|
| `lie_containment_principle` | Lies create untrusted deposits, don't flip truth | Epistemic sandbox |
| `no_gate_bypass` | Gate enforcement is architectural, not agent-dependent | Gate invariance |

### Claim Budget

**This module CAN claim:**
- ✅ PRP implies no terminal epistemic closure (proved)
- ✅ PRP forces ongoing revision/scoping (proved)
- ✅ Agent constraints necessitate mechanisms (structural disjunction)
- ✅ Faults are contained architecturally (trivial cases proved)

**This module CANNOT claim:**
- ❌ Specific agent psychology or decision-making
- ❌ Quantitative budget/cost relationships (only qualitative)
- ❌ Full proof of mechanism necessity (requires Health/LTS linkage)

---

## Bucket 19: Feasibility / Existence Under Constraints (Tier A)

**Paper Role:** Establishes that the constraint+objective package is consistent AND that success forces Bank primitives.

### Headline Theorem

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `existence_under_constraints` | Feasibility.lean | ∃ W. WellFormed W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W | Appendix: Existence + forced primitives |

### Core Theorems

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `goals_force_bank_primitives` | Feasibility.lean | ∀ W. WellFormed W → SatisfiesAllProperties W → containsBankPrimitives W | Minimality: forced primitives |
| `success_feasible` | Feasibility.lean | ∃ W. WellFormed W ∧ SatisfiesAllProperties W | Success bundle non-empty |
| `world_bundles_feasible` | Feasibility.lean | World bundles satisfiable | Appendix: World non-vacuity |
| `commitments_feasible` | Feasibility.lean | 8 commitments satisfiable | Appendix: Model non-vacuity |
| `joint_feasible` | Feasibility.lean | Constraints + objectives jointly satisfiable | Non-vacuity |
| `all_bundles_satisfiable` | WorldWitness.lean | W_* bundles jointly satisfiable | Appendix: World witness |
| `all_commitments_satisfiable` | ConcreteLedgerModel.lean | 8 commitments have witnesses | Appendix: Commitment witness |
| `concrete_satisfies_all_properties` | ConcreteLedgerModel.lean | ConcreteWorkingSystem satisfies all properties | Witness for success |

### Supporting Structures

| Structure | File | Purpose |
|-----------|------|---------|
| `Realizer` | Realizer.lean | Type packaging commitment proofs |
| `SuccessfulSystem` | Realizer.lean | Type packaging successful system (W + wf + sat) |
| `ConcreteRealizer` | Realizer.lean | Realizer witness instance |
| `ConcreteSuccessfulSystem` | Realizer.lean | SuccessfulSystem witness instance |
| `WitnessCtx` | WorldWitness.lean | Concrete WorldCtx instance |

### Claim Budget

**This bucket CAN claim:**
- ✅ The 8 paper commitments are jointly satisfiable
- ✅ World constraint bundles have at least one witness
- ✅ A working system meeting the success bundle exists
- ✅ Success forces Bank primitives (minimality)
- ✅ The architecture is not vacuous

**This bucket CANNOT claim:**
- ❌ The real world literally is this model
- ❌ Uniqueness of realization
- ❌ Abduction from observations to existence

---

## Bucket 20: Meta-Status Proof Pack (Tier A)

**Paper Role:** Establishes the theory's epistemic status: falsifiable, not fully authorizable, safe on credit.

### Headline Theorem

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `meta_status_proof_pack` | Meta/FalsifiableNotAuthorizable.lean | P1 ∧ P2 ∧ P3 packaged | Appendix: Meta-status |

### Core Theorems

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `theory_floor_satisfiable` | Meta/FalsifiableNotAuthorizable.lean | TheoryFloor WitnessCtx | Floor is consistent |
| `theory_floor_falsifiable` | Meta/FalsifiableNotAuthorizable.lean | ∃ C, ¬ TheoryFloor C | Countercontext exists |
| `theory_floor_not_fully_authorizable` | Meta/FalsifiableNotAuthorizable.lean | TheoryFloor C → CreditRequired C | Credit required |
| `witness_requires_credit` | Meta/FalsifiableNotAuthorizable.lean | CreditRequired WitnessCtx | Witness needs credit |
| `credit_required_implies_not_fully_authorizable` | Meta/FalsifiableNotAuthorizable.lean | CreditRequired C → ¬FullyAuthorizableByObs C | Bridge lemma |
| `theory_floor_implies_not_fully_authorizable` | Meta/FalsifiableNotAuthorizable.lean | TheoryFloor C → ¬FullyAuthorizableByObs C | Clean P2 |
| `witness_not_fully_authorizable` | Meta/FalsifiableNotAuthorizable.lean | ¬FullyAuthorizableByObs WitnessCtx | Instantiated P2 |
| `credit_safe_under_extension` | Meta/FalsifiableNotAuthorizable.lean | Extensions preserve paper-facing | Non-collapse |

### Optional Stretch: Theory Core Claim (Witness-Specific)

| Theorem | File | Statement | Paper Claim |
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

| Theorem | File | Statement | Paper Claim |
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

### Claim Budget

**This bucket CAN claim:**
- ✅ Floor package is consistent (witness exists)
- ✅ Floor package is falsifiable (countercontext exists)
- ✅ Full authorization from obs is impossible
- ✅ Extension doesn't collapse paper-facing claims
- ✅ (Stretch) A designated `theory_core` token is underdetermined
- ✅ (Universal) Schema works for any context with W_partial_observability

**This bucket CANNOT claim:**
- ❌ The real world is the witness
- ❌ The theory is "unprovable" (wrong vocabulary)
- ❌ People must accept it

---

## Bucket 21: Multi-Agent Corroboration (Appendix)

**Paper Role:** Formal machinery for when multi-agent corroboration is required (conditional minimality) and when it fails (common-mode / bubble infection).

### Core Theorems

| Theorem | File | Statement | Paper Claim |
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

### Claim Budget

**This bucket CAN claim:**
- ✅ Formal reason "why 2-3 independent attestations beats one" (under explicit interface)
- ✅ Formal reason "why corroboration can fail" (common-mode / bubble infection)
- ✅ Conditional minimality: if NoSPoF goal, corroboration is forced
- ✅ Independence is a parameter (explicit knob), not hidden assumption

**This bucket CANNOT claim:**
- ❌ "Humans do this in practice" (no sociology)
- ❌ "The real world satisfies the independence interface" (no realism)
- ❌ "Corroboration guarantees truth" (only reduces risk under constraints)

---

## Bucket 22: Entrenchment (Pathological Ladder State)

**Paper Role:** Entrenchment (Certainty + structural refusal to revise) breaks safe withdrawal — the deposit becomes inactive but the agent cannot acknowledge this.

**Paper References:** A.S7, B1.10, B1.11

### Core Theorems

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `entrenchment_breaks_safe_withdrawal` | Theorems.lean:2784 | Entrenched + inactive deposit → ¬isDeposited | A.S7: Entrenchment blocks withdrawal |
| `entrenched_cannot_withdraw` | Theorems.lean:2806 | Entrenched + inactive → no Step.withdraw fires | B1.10/B1.11: Full withdrawal failure |

### Supporting Definitions

| Definition | File | Description |
|------------|------|-------------|
| `Entrenched` | Basic.lean:142 | `certainty_L a P ∧ ∀ (_signal : Prop), True` — Certainty + refuses revision |
| `EntrenchedAgent` | Theorems.lean:2756 | Structure bundling agent, claim, and entrenchment proof |
| `deposit_no_longer_active` | Theorems.lean:2765 | Deposit is Quarantined or Revoked |

### Math Form

$$\text{Entrenched}(a, P) \land \text{deposit\_no\_longer\_active}(s, d) \Rightarrow \neg\text{isDeposited}(s, d)$$

### Claim Budget

**This bucket CAN claim:**
- ✅ "An entrenched agent cannot safely withdraw when the Bank has quarantined or revoked the deposit"
- ✅ "Entrenchment is a pathological *defect* of Certainty, not a synonym for it"

**This bucket CANNOT claim:**
- ❌ "All agents at Certainty are entrenched" (Entrenchment is an additional predicate)
- ❌ "Real-world stubbornness is exactly this" (model-relative)

---

## Bucket 23: Observational Completeness (Header/Deposit Extensionality)

**Paper Role:** Proves deposit identity is exhausted by named fields — no hidden degrees of freedom. Forces adversaries onto constraint enumeration rather than field discovery.

**Paper References:** A.OC1, A.OC2, B16b.1–B16b.4

### Core Theorems

| Theorem | File | Statement | Paper Claim |
|---------|------|-----------|-------------|
| `header_ext` | Header.lean:149 | Headers agreeing on 6 fields are equal | B16b.1: Header extensionality |
| `deposit_ext` | Header.lean:166 | Deposits agreeing on 4 fields are equal | A.OC2: Deposit extensionality |
| `observational_completeness` | Header.lean:182 | Field-equal deposits are predicate-indistinguishable | B16b.3: Closure theorem |
| `observational_completeness_full` | Header.lean:199 | All 9 primitive fields → predicate-indistinguishable | A.OC1: Full field version |

### Math Form

$$d_1.P = d_2.P \;\land\; d_1.h = d_2.h \;\land\; d_1.\text{bubble} = d_2.\text{bubble} \;\land\; d_1.\text{status} = d_2.\text{status} \implies d_1 = d_2$$

$$\forall\, \text{Pred},\ d_1 = d_2 \implies \text{Pred}(d_1) \implies \text{Pred}(d_2)$$

### Claim Budget

**This bucket CAN claim:**
- ✅ "Deposits agreeing on all named fields are identical" (proved extensionality)
- ✅ "The named fields exhaust deposit identity — no hidden degrees of freedom"
- ✅ "Any proposed extension either refines an existing field (compatible, protected by A.R1–A.R3) or is operationally inert"

**This bucket CANNOT claim:**
- ❌ "No other field decomposition could work" (observational completeness is closure *within* our choice)
- ❌ "The constraint enumeration is provably complete" (that requires external adequacy argument)

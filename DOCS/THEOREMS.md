# Theorem Inventory

This document catalogs the proved theorems in the formalization, organized by argumentative role.

**What the architecture claims:** Decentralized epistemic authorization requires specific structural mechanisms — a lifecycle with type-separated stages, header-preserving export, a revision loop, temporal validity, and a Bank substrate. These aren't design preferences; they are forced by the combination of agent constraints and system health goals.

**What this document is:** A bucketed theorem index (Buckets 1–30), grouped by the architectural claim each cluster supports. Each bucket names the Lean file, the key theorems, and the claim each cluster establishes. This file covers the full proof burden distribution across the repo. For deeper exposition of any area, the standalone DOCS files are the right place. For the modularity story — what survives disabling a constraint, health goal, or world bundle, and by what formal mechanism — see [MODULARITY.md](MODULARITY.md).

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
| `authorization_implies_traction` | Theorems/Corners.lean | Authorization → Traction (one direction) | Core split |
| `innovation_allows_traction_without_authorization` | Commitments.lean | Traction without authorization (other direction) | Core split |

### Math Form

$$\text{Candidate}(d) \Rightarrow \neg\text{canWithdraw}(d)$$

$$\text{canWithdraw}(d) \Rightarrow \text{Deposited}(d) \land \text{ACL}(a,d) \land \tau\text{-valid}(d)$$

---

## Bucket 2: Competition Gate Cluster (Revision ⇔ Self-Correction)

**Role:** The central forcing constraint — self-correction requires revision capability.

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `no_revision_no_correction` | Semantics/StepSemantics.lean | No revision → no self-correction | Competition gate |
| `self_correction_requires_revision` | Semantics/StepSemantics.lean | Self-correction → revision occurred | Forward direction |
| `self_correcting_domain_permits_revision` | Semantics/StepSemantics.lean | Self-correcting domain → permits revision | Domain level |
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

### Math Form

$$\neg \exists f : \text{Stripped} \to \text{Full}.\, f \circ \text{strip} = \text{id}$$

$$h_1 \neq h_2 \land \text{claim}(h_1) = \text{claim}(h_2) \Rightarrow \text{strip}(h_1) = \text{strip}(h_2)$$

---

## Bucket 4: Diagnosability (Observability Monotonicity)

**Role:** Header stripping reduces diagnosability; fewer observable fields → coarser repair.

### Core Theorems (Theorems/Diagnosability.lean)

| Theorem | Statement | Claim |
|---------|-----------|-------------|
| `diagnosability_full` | Full deposits: diagnosability = 6 | Full observability |
| `diagnosability_stripped` | Stripped deposits: diagnosability = 0 | Zero observability |
| `strip_reduces_diagnosability` | strip → diagnosability decreases | Monotonicity |
| `stripped_no_field_repair` | Stripped can't target any field | Coarse repair |
| `full_can_repair_any` | Full can target any field | Surgical repair |
| `epistemic_diagnosability_full` | Epistemic diagnosability (S/E/V) = 3 for full deposits | Grounds score-3 constant |
| `epistemic_diagnosability_stripped` | Epistemic diagnosability = 0 for stripped deposits | Grounds score-0 floor |

### Bridge Theorems (Commitments.lean)

| Theorem | Statement | Claim |
|---------|-----------|-------------|
| `epistemic_and_full_agree_on_stripped` | `epistemic_diagnosability false = diagnosability false` | Both models agree: stripped = 0 |

### Math Form

$$\text{diagnosability}(\text{full}) = 6 > 0 = \text{diagnosability}(\text{stripped})$$

$$f \notin \text{ObservableFields}(d) \Rightarrow \neg\text{canTargetRepair}(f, d)$$


---

## Bucket 5: τ (Temporal Validity)

**Role:** Time creates pressure for maintenance; staleness blocks operations.

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `stale_blocks_withdrawal` | Theorems/Corners.lean | Stale deposits can't withdraw | Hygiene |
| `tick_can_cause_staleness` | Theorems/Corners.lean | Clock tick → may become stale | Time pressure |
| `withdrawal_requires_fresh` | Theorems/Corners.lean | Withdrawal needs τ-valid | Freshness gate |
| `τ_valid_mono` | Semantics/StepSemantics.lean | τ validity is monotonic in clock | Temporal ordering |
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
| `gettier_is_V_failure` | Theorems/Cases/Gettier.lean | Gettier = V-field failure (unconditional; `tracks_false_certified` structural field) |
| `gettier_ground_disconnected` | Theorems/Cases/Gettier.lean | Truth-maker and provenance are structurally distinct grounds (`ground_distinct` field) |
| `canonical_gettier_is_gettier` | Theorems/Cases/Gettier.lean | Canonical Gettier satisfies `IsGettierCase` |
| `canonical_gettier_conditions` | Theorems/Cases/Gettier.lean | Canonical Gettier satisfies all GettierCase conditions |

### Fake Barn Cases

| Theorem | File | Diagnosis |
|---------|------|----------|
| `fake_barn_is_E_failure` | Theorems/Cases/FakeBarn.lean | Fake Barn = E-field failure (unconditional; `e_certified` structural field) |
| `fake_barn_profile_yields_E_failure` | Theorems/Cases/FakeBarn.lean | Alias demonstrating the structural certification pattern |
| `canonical_fake_barn_is_fake_barn` | Theorems/Cases/FakeBarn.lean | Canonical fake barn satisfies FakeBarnCase |

### Standard Case (S-Field Failure)

Two subtypes: relational (threshold mismatch per consuming agent) and absolute/void (E + V together
certify that S is vacuous regardless of consumer). Both repair by targeting Field.S.

| Theorem | File | Diagnosis |
|---------|------|------------|
| `standard_case_is_S_failure` | Theorems/Cases/Standard.lean | IsStandardCase → case_S_inadequate (Prop-level; not Bool.not_false) |
| `canonical_standard_case_is_standard` | Theorems/Cases/Standard.lean | Peanut-allergy canonical case satisfies IsStandardCase |
| `standard_failure_targets_S` | Theorems/Cases/Standard.lean | IsStandardCase → S_fails = true (executable mirror) |
| `standard_failure_is_relational` | Theorems/Cases/Standard.lean | Same deposit standard: allergic agent fails, lenient agent passes |
| `same_deposit_standard_split_yields_relational_S_failure` | Theorems/Cases/Standard.lean | Generic: same deposit_standard + opposite threshold outcomes → RelationalClearanceSplit |
| `canonical_allergy_is_relational_split` | Theorems/Cases/Standard.lean | Canonical allergy pair is a RelationalClearanceSplit |
| `s_failure_v_is_sound` | Theorems/Cases/Standard.lean | In an S-failure, V-provenance is genuinely tracking (V is positively certified) |
| `s_failure_e_is_sound` | Theorems/Cases/Standard.lean | In an S-failure, E-coverage has no relevant gap (E is positively certified) |
| `s_failure_v_mode_and_e_threat` | Theorems/Cases/Standard.lean | Data-backed form: `mode = .direct_inspection` and `threat ∈ modeled_threats` (concrete witnesses) |
| `relational_S_requires_matching_VE_data` | Theorems/Cases/Standard.lean | Relational S-failure: symmetric V/E data across both consumers; only threshold differs |

### Vacuous Standard Case (S Voided by E + V Interaction)

| Theorem | File | Diagnosis |
|---------|------|------------|
| `vacuous_standard_is_S_failure` | Theorems/Cases/VacuousStandard.lean | VacuousStandardCase → S_is_vacuous (both conditions certified as structural fields) |
| `testimony_only_plus_unreliable_source_yields_void_S` | Theorems/Cases/VacuousStandard.lean | Generic: testimony-only S over documented-unreliable source → void S |
| `canonical_liar_cook_is_void` | Theorems/Cases/VacuousStandard.lean | Known-liar cook case → S_is_vacuous (instance of generic theorem) |
| `absolute_vs_relational_S_failure` | Theorems/Cases/VacuousStandard.lean | Both failure subtypes in one theorem: relational (allergy) ∧ absolute (liar cook) |

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
| `step_preserves_valid_status` | Semantics/StepSemantics.lean | Steps preserve valid statuses |
| `trace_preserves_valid_status` | Semantics/StepSemantics.lean | Traces preserve valid statuses |
| `step_preserves_separation` | Semantics/StepSemantics.lean | Steps preserve type separation |
| `step_preserves_auditability` | Semantics/StepSemantics.lean | Steps preserve auditability |
| `step_no_revision_preserves_deposited` | Semantics/StepSemantics.lean | Revision-free step preserves `isDeposited` for all deposits |
| `trace_no_revision_preserves_deposited` | Semantics/StepSemantics.lean | Revision-free trace preserves `isDeposited` (induction over steps) |
| `deposits_survive_revision_free_trace` | Theorems/Pathologies.lean | LTS corollary: deposits survive any revision-free trace |
| `step_preserves_ladder_map` | Semantics/StepSemantics.lean | `ladder_map` is invariant under every Step (all constructors use `{ s with … }`) |
| `closure_ladder_invariant` | Semantics/StepSemantics.lean | Contextual alias of `step_preserves_ladder_map` for the closure puzzle |
| `trace_preserves_ladder_map` | Semantics/StepSemantics.lean | `ladder_map` is invariant under any Trace (induction over steps) |
| `no_bank_trace_generates_ladder_content` | Semantics/StepSemantics.lean | Point-wise: no Trace changes `ladder_map f P` for any (agent, claim) pair |
| `trace_cannot_elevate_ladder` | Semantics/StepSemantics.lean | A trace starting with Ignorance for (f, P) ends with Ignorance |
| `bank_trace_cannot_discharge_closure` | Semantics/StepSemantics.lean | A trace that starts with Certainty for (f, P) cannot remove it |

---

## Bucket 8: Modal Properties (Safety/Sensitivity ↔ S/E/V)

**Role:** Connect modal epistemology to architectural fields.

> **Note:** `Semantics/ModalLinks.lean` was removed. The modal vocabulary (Safe, Sensitive, V_independent, E_covers) and its connection to `header_preserved` was entirely definitional — all eight theorems reduced to `Iff.rfl` or `exact h`. The case-level theorems below (in `Theorems/`) remain.

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

## Bucket 9: Grounded Minimality (Semantics/LinkingAxioms.lean)

**Role:** Each architectural feature is necessary for specific capabilities.

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `grounded_coordination_requires_bank` | Semantics/LinkingAxioms.lean | Coordination → Bank | Bank necessity |
| `grounded_export_requires_headers` | Semantics/LinkingAxioms.lean | Export → Headers | Header necessity |
| `grounded_bounded_audit_requires_bridges` | Semantics/LinkingAxioms.lean | Bounded audit → Bridges | Bridge necessity |
| `grounded_no_bridge_forces_revalidation` | Semantics/LinkingAxioms.lean | No bridge → revalidate | Export cost |
| `grounded_revocation_requires_quarantine` | Semantics/LinkingAxioms.lean | Revocation → Quarantine | Quarantine necessity |
| `grounded_distributed_agents_require_bubbles` | Semantics/LinkingAxioms.lean | Distributed → Bubbles | Bubble necessity |
| `grounded_truth_pressure_requires_redeemability` | Semantics/LinkingAxioms.lean | Truth pressure → Redeemability | Redeemability necessity |

---

## Bucket 9b: Abstract Structural Forcing Layer (Minimality.lean + Convergence.lean)

**Role:** Provide structurally-grounded proofs that each constraint forces its feature. The seven structural impossibility models in Minimality.lean independently justify each `handles_X → HasY` implication. The §1b–§7b alternative-dismissal theorems cover the completeness side: each evaluated alternative either reproduces the same impossibility or satisfies the forced-primitive definition.

**Strongest result:** Seven per-dimension `*_forces_*` theorems (Convergence.lean) each take a single `Represents*` witness and directly force the `Has*` feature — no `handles_X W`, no biconditionals, no `WellFormed`. These are orthogonal: each fires independently of the other six. Bundled into `SystemOperationalBundle` / `WorldBridgeBundle`, they feed the headline `bundled_structure_forces_bank_primitives` theorem in Feasibility.lean.

### Structural Impossibility Models (Minimality.lean)

Seven abstract scenario structures, each proving that a degenerate configuration is impossible.

| Theorem | Structure | Impossibility proved |
|---------|-----------|----------------------|
| `flat_scope_impossible` | `AgentDisagreement` | No flat acceptance function can faithfully represent two disagreeing agents |
| `verification_only_import_incomplete` | `BoundedVerification` | Some claims exceed any fixed budget; verification-only import cannot cover them |
| `uniform_import_nondiscriminating` / `no_sound_complete_uniform_import` | `DiscriminatingImport` | A uniform import function cannot be both sound and complete |
| `monotonic_no_exit` | `MonotonicLifecycle` | An absorbing accepted state cannot be escaped at any step count |
| `private_storage_no_sharing` | `PrivateOnlyStorage` | Isolated agent storage makes shared deposit access impossible |
| `closed_system_unfalsifiable` | `ClosedEndorsement` | A closed endorsement system has no externally falsifiable endorsed claim |
| `flat_authorization_impossible` | `TwoTierAccess` | A flat authorization predicate cannot faithfully represent both submission and commit tiers |

### Pressure Dimension Index (Minimality.lean)

The `Pressure` inductive type is the canonical dimension index for the EpArch forcing layer. All seven forcing dimensions are cases of a single type; every forcing-layer predicate is now a function `Pressure → Prop` rather than seven separate fields.

```lean
inductive Pressure where
  | scope | trust | headers | revocation | bank | redeemability | authorization
  deriving DecidableEq, Repr
```


Using `Pressure` as the index means every `cases P` in a proof is machine-exhaustiveness-checked by Lean's kernel. A proposed eighth dimension must be added as a new `Pressure` constructor — at which point the compiler flags every `cases P` site until the new forcing chain is supplied. This is architectural enforcement, not documentation convention. See `DOCS/MODULARITY.md § "What exhaustiveness means here"` for the scope boundary this claim carries.

Key definitions that are now universally quantified over `Pressure`:
- `SatisfiesAllProperties W := ∀ P : Pressure, handles_pressure W P`
- `containsBankPrimitives W := ∀ P : Pressure, forced_feature W P`
- `StructurallyForced W` — single field `forcing : ∀ P, handles_pressure W P → forced_feature W P`
- `ForcingEmbedding W` — single field `embed : ∀ P, handles_pressure W P → forced_feature W P ∨ bridge_scenario W P`
- `all_bridges_impossible W P : ¬bridge_scenario W P` — exhaustive impossibility theorem (proves by `cases P`)

### Per-Dimension Structural Forcing Theorems (Convergence.lean)

Seven independent theorems — one per EpArch dimension — each taking a single `Represents*` witness and a structural hypothesis, and directly forcing the corresponding `Has*` feature. **No `handles_X W` required. No biconditionals. Orthogonal: zero cross-dependencies.** This is the strongest form of the per-dimension claim: any system that concretely faces exactly one EpArch operational pressure is mathematically forced to have the corresponding Bank primitive.

| Theorem | Witness required | Feature forced |
|---------|-----------------|----------------|
| `disagreement_forces_bubbles` | `RepresentsDisagreement W` + flat-acceptance witnesses | `HasBubbles W` |
| `private_coordination_forces_bank` | `RepresentsPrivateCoordination W` + shared-deposit witnesses | `HasBank W` |
| `monotonic_lifecycle_forces_revocation` | `RepresentsMonotonicLifecycle W` + escape witnesses | `HasRevocation W` |
| `discriminating_import_forces_headers` | `RepresentsDiscriminatingImport W` + sound/complete import witnesses | `HasHeaders W` |
| `bounded_verification_forces_trust_bridges` | `RepresentsBoundedVerification W` + verification witnesses | `HasTrustBridges W` |
| `closed_endorsement_forces_redeemability` | `RepresentsClosedEndorsement W` + endorsement witnesses | `HasRedeemability W` |
| `uniform_access_forces_granular_acl` | `RepresentsUniformAccess W` + two-tier witnesses | `HasGranularACL W` |

Proof pattern for each: `by_cases h : HasFeature W; exact h; exact (impossible_without_feature ... h ...).elim` — classical case split with the abstract impossibility model closing the negative branch.


### Headline Convergence Theorems (Feasibility.lean)

| Theorem | Signature | Role |
|---------|-----------|------|
| `grounded_world_and_structure_force_bank_primitives` | `(W : WorkingSystem) → (Rd Rb Ri Rm Rp Re Ra : Represents* W) → bridge hypotheses → SatisfiesAllProperties W → containsBankPrimitives W` | All-seven forcing with fully explicit `Represents*` witnesses; no `WorldCtx`, no W_* bundles; holds for any world |
| `bundled_structure_forces_bank_primitives` | `(W : WorkingSystem) → SystemOperationalBundle W → WorldBridgeBundle W → SatisfiesAllProperties W → containsBankPrimitives W` | Headline 4-argument form; unpacks both bundles into `grounded_world_and_structure_force_bank_primitives` |

**Key architectural boundary:** `W_*` bundles (`WorldCtx.lean`) are `Prop`-valued; `Represents*` structures carry `Type`-valued fields (`State : Type`, `Claim : Type`). No `Type` can be extracted from a `Prop` — the universe boundary is genuine. The `W_*` bundles are natural *motivation* for the witnesses but are not formal preconditions; callers supply `Represents*` witnesses directly.

---

## Bucket 9c: Observation-Boundary Equivalence (Theorems/BehavioralEquivalence.lean)

**Role:** Proves that any two `GroundedBehavior` certificates produce identical observations on all inputs. `Behavior B i` is determined solely by the input constructor — not by the structural content of `B`. The step-bridge section operationally grounds this: for withdraw, challenge, and tick inputs, a concrete `Step` is constructed at Unit types and structurally consumed via `cases h`, so the equality is derived *through* an actual firing. Export falls back to definitional equality because `header_preserved` is opaque and cannot be reflected into a concrete `depositHasHeader` for the unit-type instantiation.

**Certificate semantics:** `GroundedBehavior` is intentionally domain-agnostic — its fields carry abstract type parameters (`Entry`, `Claim`, etc.) that a domain fills in with its own types. `B` is a type-level certificate confirming the caller's features typecheck against EpArch's mechanism signatures; it does not construct the `CState` and does not guarantee design quality. The `let _ :=` lines in the ready-state builders confirm certificate field presence only. A domain instantiator (EV charging, finance, Lean kernel) that wants mechanically grounded evidence replaces those lines with substantive obligations over their own types. The kernel enforces the observation boundary contract; domain correctness is the instantiator's responsibility.

**Extension model:** Any domain that provides a `GroundedBehavior` instantiation immediately inherits `working_systems_equivalent` — any two implementations holding the certificate agree at the observation boundary, regardless of internal design. See `Meta/LeanKernel/World.lean` (`LeanGroundedBehavior`) for the reference instantiation.

### Theorems

| Theorem | Statement | Role |
|---------|-----------|------|
| `behavioral_equiv_refl/symm/trans` | Equivalence relation properties | Structural foundation |
| `satisfies_all_fixes_flags` | `SatisfiesAllProperties W` → all seven flags are `true` | Bridges property satisfaction to flag values |
| `behavior_step_consistent` | `Behavior B i = observe_step_action (input_to_action i)` for all `B`, `i` | Definitional bridge; both sides action-indexed |
| `behavior_from_step` | Given `Step s (input_to_action i) s'`, derive `observe_step_action ... = Behavior B i` by `cases i <;> cases h` | Step-consuming bridge; eliminates the Step constructor |
| `grounded_export_step` | Export Step fires given `depositHasHeader` + `hasTrustBridge` | Conditional; `header_preserved` opaque prevents unconditional form |
| `working_systems_equivalent` | Any two `GroundedBehavior` witnesses are behaviorally equivalent; unconditional — no `SatisfiesAllProperties` premise | Main theorem |
| `grounded_behaviors_equivalent` | Same equivalence proved by `cases i <;> rfl`; no Step witnesses | Reveals depth ceiling: equality is input-indexed, not state-indexed |

---

## Bucket 9d: Kernel Verification Depth (Concrete/VerificationDepth.lean)

**Role:** Provides a *constructive* kernel-level witness that `W_bounded_verification` is not an empirical world assumption but follows from the structural properties of the verification relation itself. `DepthClaim n` is a depth-indexed proposition family with exactly n constructors; a budget-d verifier traverses only d constructors and therefore cannot decide `DepthClaim (d+1)`, which is genuinely true. This justifies the bounded-audit forcing argument for trust bridges by construction rather than supposition.

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

### Core Theorems in Adversarial/Base.lean (Proved)

| Theorem | File | Statement |
|---------|------|----------|
| `is_lie_iff` | Adversarial/Base.lean | `is_lie l ↔ l.fabricated_V ∧ l.severed_redeemability` — biconditional by `Iff.rfl` |

---

## Bucket 10a: Concrete Attack Mitigation (Adversarial/Concrete.lean)

**Role:** Connect the abstract attack vocabulary to concrete type instances (`CDeposit`, `CAuditChannel`,
`CExportRequest` from `Concrete/Types.lean`). Four-step demonstration that gate conditions are
un-bypassable at the concrete model level.

### Step 3: Attack-Named Wrappers and DDoS Chain

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------|
| `τ_compressed_deposit_blocked` | Adversarial/Concrete.lean | τ-compression attack blocked at status gate | τCompress → τ gate |
| `V_spoof_deposit_blocked` | Adversarial/Concrete.lean | V-spoofing attack blocked at status gate | VSpoof → V gate |
| `pseudo_deposit_blocked_at_candidate_stage` | Adversarial/Concrete.lean | Pseudo-deposit stalls at `.Candidate` | PseudoDeposit → V gate |
| `overwhelmed_channel_collapses_V` | Adversarial/Concrete.lean | `c_channel_overwhelmed ∧ sources.length > capacity → c_process_V = []` | Channel capacity math |
| `ddos_V_channel_collapse_blocks_withdrawal` | Adversarial/Concrete.lean | DDoS chain: channel overload → V = [] → ¬c_can_withdraw | DDoS → V gate (5-step) |
| `concrete_attack_succeeds` | Adversarial/Concrete.lean | `attack_succeeds concrete_full_stack_attack` holds | Attack vocab non-vacuity |
| `full_stack_attack_concrete_blocked` | Adversarial/Concrete.lean | Matching `CDeposit` blocked by τ gate at current_time 100 | End-to-end |

**Scope boundary:** these theorems prove gate conditions are un-bypassable *when invoked*. Whether an agent must invoke `c_can_withdraw` before constructing a `CExportRequest` is an agent-layer protocol obligation, not enforced by `EpArch.Adversarial.Concrete`. EpArch proves the gates are sound; agents prove the gates are invoked in the right order.

---

## Bucket 11: Repair Loop Semantics

**Role:** Challenge-repair-revalidation cycle.

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `repair_enforces_revalidation` | Theorems/Withdrawal.lean | Repair → revalidate | No silent fix |
| `submit_enforces_revalidation` | Theorems/Withdrawal.lean | Submit → validate | Validation on entry |
| `repair_requires_prior_challenge` | Theorems/Withdrawal.lean | Repair requires quarantine | Challenge first |
| `challenge_has_field_localization` | Semantics/StepSemantics.lean | Challenge targets field | Field-specific |
| `repair_requires_quarantine` | Semantics/StepSemantics.lean | Repair needs quarantine | State gate |
| `repair_targets_field` | Semantics/StepSemantics.lean | Repair addresses field | Surgical |
| `repair_produces_candidate` | Semantics/StepSemantics.lean | Repair → Candidate | Back to start |
| `repair_resets_to_candidate` | Semantics/StepSemantics.lean | Full cycle reset | Lifecycle |

---

## Bucket 12: Withdrawal Gates (Three-Gate Model)

**Role:** Withdrawal requires Status + ACL + τ.

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `withdrawal_requires_three_gates` | Semantics/StepSemantics.lean | Status ∧ ACL ∧ τ | Three gates |
| `withdrawal_gates` | Theorems/Withdrawal.lean | Withdrawal preconditions | Gate theorem |
| `canWithdrawAt_iff_gates` | Theorems/Withdrawal.lean | CanWithdraw ↔ gates | Equivalence |
| `withdrawal_requires_canWithdrawAt` | Theorems/Withdrawal.lean | Step requires predicate | Enforcement |
| `canWithdrawAt_enables_step` | Theorems/Withdrawal.lean | Predicate enables step | Sufficiency |

---

## Bucket 13: Obligation Theorems (World ⇒ Mechanism)

**Role:** Convert implicit mechanism axioms into explicit conditional theorems.

**Files:** `WorldCtx.lean`, `Adversarial/Obligations.lean`

### Core Theorems (WorldCtx.lean)

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
| `cheap_validator_maintains_path_of_W` | Adversarial/Obligations.lean | W_cheap_validator → cheap validator reachable → not revoked → PathExists d | `cheap_validator_blocks_V_attack` |
| `trust_bridge_maintains_path_of_W` | Adversarial/Obligations.lean | W_trust_bridge → trust bridge → τ > 0 → not revoked → PathExists d | `trust_bridge_blocks_V_attack` |
| `reversibility_maintains_path_after_τ_compress_of_W` | Adversarial/Obligations.lean | W_reversibility → reversible → not revoked → PathExists d survives τ compress | `reversibility_neutralizes_τ` |
| `E_inclusion_prevents_collapse_of_W` | Adversarial/Obligations.lean | W_E_inclusion → E includes threat → ¬verification_collapsed a | `E_inclusion_closes_expertise_gap` |
| `cheap_constraint_maintains_path_of_W` | Adversarial/Obligations.lean | W_cheap_constraint → constraint cheaply testable → not revoked → PathExists d | `cheap_constraint_blocks_V_spoof` |

**World Assumption Bundles:** 16 `W_*` bundles (`W_lies_possible` through `W_cheap_constraint`) each gate exactly one obligation theorem above; full definitions in WorldCtx.lean and Adversarial/Obligations.lean.

### Math Form

$$\text{W-lies-possible} \Rightarrow \exists w\, a\, P.\, \text{Lie}(w, a, P)$$

$$\text{RequiresSteps}(w, P, k) \land t < k \Rightarrow \neg\text{VerifyWithin}(w, P, t)$$

$$\text{W-ddos-full} \land (\text{ladder\_overloaded}(a) \lor \text{V\_channel\_exhausted}(a) \lor \text{E\_field\_poisoned}(a) \lor \text{denial\_triggered}(a)) \Rightarrow \text{trust\_centralized}(a)$$

---

## Adversarial Attack Surfaces

Each architectural constraint creates both a capability and an exploitable surface. Five canonical surfaces follow directly from the bucket structure: **Lifecycle** (ladder overload, premature closure — `DDoSVector.LadderOverload`, `τ_compressed`), **Revision** (challenge flooding, denial triggering — `DDoSVector.DenialTriggering`), **Export/Strip Asymmetry** (V-spoofing, proxy substitution, provenance laundering — `stripV_loses_provenance`, `ProxySubstitution`, `no_strip_left_inverse`), **Diagnosability** (E-field poisoning, diagnostic denial — `DDoSVector.EFieldPoisoning`, `stripped_no_field_repair`), and **Temporal Validity** (τ compression, staleness induction — `FullStackAttack.τ_compressed`, `tick_can_cause_staleness`). Coordinated full-stack attacks are formalized as `FullStackAttack` in Adversarial/Base.lean; the four `DDoSVector` constructors cover the exhaustive attack vector taxonomy.


---

## Bucket 14: Health → Necessity Theorems

**Role:** Connect health goals to mechanism requirements (invariants).

**File:** `Health.lean`, `Agent/Imposition.lean`

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

**File:** `Semantics/ScopeIrrelevance.lean`

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

**Files:** `Theorems/Dissolutions.lean`, `Theorems/Pathologies.lean`, `Theorems/NotationBridge.lean`

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

### Batch 3: Notation Bridge Extensions

**File:** `Theorems/NotationBridge.lean`

| Theorem | Mechanism |
|---------|-----------|
| `notation_opacity_prevents_authorization` | ¬(σ′ pointwise equals σ) from divergence witness — single mismatch defeats identification |
| `bridge_export_enables_authorization` | `notation_bridge_case` instantiates `notation_invariance_of_redeemability`; Layer 1 at the export-packet bijection |
| `accidental_correctness_is_not_authorization` | ¬(σ′ = σ as functions) from route mismatch; surface correctness does not repair the authorization gap |

---

## Bucket 17: Revision Safety

**Role:** Guarantee that extending/strengthening the model doesn't break existing results.

**File:** `Semantics/RevisionSafety.lean`

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

### Math Form

$$\text{Compatible}(E, C) \land \text{RevisionGate}(C) \Rightarrow \text{RevisionGate}(\text{forget}(E))$$

$$\text{Compatible} := \forall B.\, E.\text{selfCorrects}(B) \Leftrightarrow C.\text{selfCorrects}(\pi_B(B))$$

---

## Bucket 18: Agent Constraints & PRP

**Role:** Mechanize "the system is designed for imperfect agents" via structural constraints.

**Files:** `Agent/Constraints.lean`, `Agent/Imposition.lean`, `Agent/Resilience.lean`, `Agent/Corroboration.lean`

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
| `deposit_promotion_requires_bank_authority` | Agent/Resilience.lean | Only `Step.promote` (with `hasBankAuthority`) can advance a claim to Deposited | Bank authority gate |

---

## Bucket 19: Feasibility / Existence Under Constraints (Tier A)

**Role:** Establishes that the constraint+objective package is consistent AND that success forces Bank primitives.

### Headline Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `convergence_structural` | Convergence.lean | ∀ W. StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W | Minimality: forced primitives (structural path) |
| `existence_under_constraints_structural` | Feasibility.lean | ∃ W. StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W | Existence via structural path |
| `existence_under_constraints_embedding` | Feasibility.lean | ∃ W. ForcingEmbedding W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W | Existence via embedding path (strongest form) |
| `bundled_structure_forces_bank_primitives` | WorldBridges.lean | `SystemOperationalBundle W → WorldBridgeBundle W → SatisfiesAllProperties W → containsBankPrimitives W` | Headline 4-argument form; no `WorldCtx` |
| `world_bundles_feasible` | Feasibility.lean | World bundles satisfiable | World non-vacuity |
| `commitments_feasible` | Feasibility.lean | 8 commitments satisfiable | Model non-vacuity |
| `joint_feasible` | Feasibility.lean | Constraints + objectives jointly satisfiable | Non-vacuity |
| `all_bundles_satisfiable` | WorldWitness.lean | W_* bundles jointly satisfiable | World witness |
| `all_commitments_satisfiable` | Concrete/Commitments.lean | 8 commitments have witnesses | Commitment witness |
| `concrete_satisfies_all_properties` | Concrete/WorkingSystem.lean | ConcreteWorkingSystem satisfies all properties | Witness for success |

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


---

## Bucket 22: Entrenchment (Pathological Ladder State)

**Role:** Entrenchment (Certainty + structural refusal to revise) breaks safe withdrawal — the deposit becomes inactive but the agent cannot acknowledge this.

**References:** A.S7, B1.10, B1.11

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `entrenchment_breaks_safe_withdrawal` | Theorems/Corners.lean | Entrenched + inactive deposit → ¬isDeposited | A.S7: Entrenchment blocks withdrawal |
| `entrenched_cannot_withdraw` | Theorems/Corners.lean | Entrenched + inactive → no Step.withdraw fires | B1.10/B1.11: Full withdrawal failure |

### Math Form

$$\text{Entrenched}(a, P) \land \text{deposit-no-longer-active}(s, d) \Rightarrow \neg\text{isDeposited}(s, d)$$

---

## Bucket 23: Observational Completeness (Header/Deposit Extensionality)

**Role:** Proves deposit identity is exhausted by named fields — no hidden degrees of freedom. Forces adversaries onto constraint enumeration rather than field discovery.

**References:** A.OC1, A.OC2, B16b.1–B16b.4

### Core Theorems

| Theorem | File | Statement | Claim |
|---------|------|-----------|-------------|
| `header_ext` | Header.lean:129 | Headers agreeing on 6 fields are equal | B16b.1: Header extensionality |
| `deposit_ext` | Header.lean:146 | Deposits agreeing on 4 fields are equal | A.OC2: Deposit extensionality |
| `observational_completeness` | Header.lean:162 | Field-equal deposits are predicate-indistinguishable | B16b.3: Closure theorem |
| `observational_completeness_full` | Header.lean:179 | All 9 primitive fields → predicate-indistinguishable | A.OC1: Full field version |

### Math Form

$$d_1.P = d_2.P \;\land\; d_1.h = d_2.h \;\land\; d_1.\text{bubble} = d_2.\text{bubble} \;\land\; d_1.\text{status} = d_2.\text{status} \implies d_1 = d_2$$

$$\forall\, \text{Pred},\ d_1 = d_2 \implies \text{Pred}(d_1) \implies \text{Pred}(d_2)$$

---

## Bucket 24: Lattice-Stability / Graceful Scale-Down

**Role:** Proves EpArch is bidirectionally modular at the `RevisionGate` / competition-gate layer: the `RevisionGate` predicate is preserved in both directions under bundle perturbation. Removing the self-correction health goal leaves a valid sub-architecture where `RevisionGate` holds vacuously; compatible extensions at any level preserve `RevisionGate` through the existing transport machinery.

**Files:** `Meta/TheoremTransport.lean` (abstract theorems + `SubBundle`, `NoSelfCorrection`, `modularity_pack`) · `Meta/LeanKernel/OdometerModel.lean` (concrete sub-bundle witness)

**The headline claim:** EpArch is a floor, not a cage. Any sub-bundle is a valid EpArch instantiation; any compatible extension of a sub-bundle is safe.

### Downward: Graceful Degradation

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `graceful_degradation` | Meta/TheoremTransport.lean | `NoSelfCorrection M → RevisionGate M` | Vacuous gate: drop self-correction goal → RevisionGate holds |

### OdometerModel — Concrete Minimal Sub-bundle

A non-revisable system satisfying only `SoundDepositsGoal` (readings must be verifiable). Demonstrates that EpArch applies to systems far simpler than its full constraint envelope.

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `odometer_no_self_correction` | Meta/LeanKernel/OdometerModel.lean | `NoSelfCorrection OdometerModel` | Odometer has no self-correction |
| `odometer_revision_gate` | Meta/LeanKernel/OdometerModel.lean | `RevisionGate OdometerModel` | Odometer satisfies the revision gate (vacuously) |
| `odometer_sound_deposits` | Meta/LeanKernel/OdometerModel.lean | `SoundDepositsGoal OdometerModel` | Readings are verifiable within effectiveTime |
| `odometer_not_corrigible` | Meta/LeanKernel/OdometerModel.lean | `¬CorrigibleLedgerGoal OdometerModel` | Correctly fails the revision goal it does not claim |

### Sub-level RevisionSafety (Downward + Upward)

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `sub_revision_safety` | Meta/TheoremTransport.lean | `Compatible E S.model → RevisionGate S.model → RevisionGate (forget E)` | RevisionSafety holds at every sub-bundle level |
| `odometer_extension_safe` | Meta/LeanKernel/OdometerModel.lean | `Compatible E OdometerModel → RevisionGate (forget E)` | Any compatible extension of the odometer satisfies the revision gate |

### Headline: ModularityPack

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `modularity_pack` | Meta/TheoremTransport.lean | `GracefulDegradation ∧ SubRevisionSafety ∧ FullRevisionSafety` | Full bidirectional lattice-stability |

### Math Form

$$\text{NoSelfCorrection}(M) \Rightarrow \text{RevisionGate}(M)$$

$$\text{Compatible}(E, S) \land \text{RevisionGate}(S) \Rightarrow \text{RevisionGate}(\text{forget}(E))$$

$$\text{ModularityPack} := \text{GracefulDegradation} \land \text{SubRevisionSafety} \land \text{safe\_extension\_preserves}$$

---

## Bucket 27: Modularity Meta-Theorem — ∀ S âŠ† Constraints, projection_valid S

**Role:** Machine-certifies that EpArch is fully modular: there exists a single
universally-quantified theorem over all subsets of the seven constraints, and a
`PartialWellFormed` type that lets users opt into exactly k ≤ 7 constraints.

**Files:** `Minimality.lean` (definitions: `ConstraintSubset`, `PartialWellFormed`, `allConstraints`, `noConstraints`) + `Meta/Modular.lean` (theorems: `partial_no_constraints`, `modular`)

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

**Role:** Closes the claim that all 30 theorem clusters are individually certified:
26 clusters (constraint, goal, Tier 4, world) are user-selectable via `EpArchConfig`;
the remaining 4 (1 constraint-modularity meta-theorem cluster + 3 lattice-stability
clusters) are always enabled because they depend on no config gate. Given any
`EpArchConfig`, the engine computes exactly which clusters apply and provides
machine-checked justification for each enabled cluster. This includes 8 world-bundle
obligation clusters wiring `EpArchConfig.worlds` to proved obligation theorems in
`WorldCtx.lean` and `Adversarial/Obligations.lean`, 1 constraint-modularity cluster from
`Meta/Modular.lean`, and 3 lattice-stability clusters from `Meta/TheoremTransport.lean` (§8).

**Note on `.partial_observability`:** Now fully wired. `WorldCtx.partial_obs_no_omniscience`
formalizes the epistemic-gap argument: under partial observability there exists a proposition
that no agent can determine from observations alone — independent of the PRP cost-budget
argument. Together, PRP (cost) and partial observability (underdetermination) give two
orthogonal reasons terminal epistemic closure is unreachable.

**Files:** `Meta/ClusterRegistry.lean` (30-cluster tag registry, routing, per-family canonical lists) and `Meta/Config.lean` (witness carriers, `certify`, completeness theorems, named proof witnesses)

**Design:** `clusterEnabled cfg c : Bool` is the computable routing function. `showConfig cfg`
is `#eval`-able and returns the enabled cluster tag names (via `reprStr`). `certify cfg` returns a
`CertifiedProjection` that names every enabled cluster and carries genuine `ConstraintProof`
records for each Tier 2 forcing cluster.  Named proof witnesses (`cluster_forcing_*`,
`cluster_goal_*`, `cluster_tier4_*`, `cluster_world_*`) state and prove the exact proposition
for each cluster.

**Three-layer architecture:**
1. **Routing layer** — `clusterEnabled`, `enabled`, `complete`, `sound` (all clusters; `clusterValid c` returns a genuine proved proposition for every cluster, not `True`)
2. **Constraint proof layer** — `constraintProof`/`constraintWitnesses` (Tier 2 forcing clusters: real `ConstraintProof` with genuine proposition + proof; possible because `WorkingSystem` is monomorphic)
3. **Proof-content layer** — `cluster_*` universe-polymorphic theorems (all 30 clusters; 15 non-Tier2 clusters use private `prop_*` defs pinned at universe 0 in §4g-pre to avoid free universe variables in the `clusterValid` match)

### Definitions / Configuration Language

| Definition | File | Purpose |
|------------|------|---------|
| `ConstraintTag` | Meta/ClusterRegistry.lean | 7 constraint tags (distributed_agents … multi_agent_access) |
| `GoalTag` | Meta/ClusterRegistry.lean | 5 health-goal tags (safeWithdrawal … selfCorrection) |
| `WorldTag` | Meta/ClusterRegistry.lean | 8 world-bundle tags (lies_possible … ddos) |
| `EpArchConfig` | Meta/ClusterRegistry.lean | User-supplied config: lists of active constraints/goals/worlds |
| `ClusterTag` | Meta/ClusterRegistry.lean | 30 cluster tags spanning Tiers 2–4, world obligations, constraint-modularity, and lattice-stability |
| `clusterEnabled` | Meta/ClusterRegistry.lean | `EpArchConfig → ClusterTag → Bool` (computable routing); meta-modular and lattice always enabled |
| `clusterValid` | Meta/Config.lean | `ClusterTag → Prop` — genuine proved proposition for each of the 30 clusters; 15 clusters use `prop_*` defs pinned at universe 0 to eliminate free universe variables |
| `showConfig` | Meta/ClusterRegistry.lean | `EpArchConfig → List String` — `#eval`-able routing report |
| `ConstraintProof` | Meta/Config.lean | Proof-carrying record: `statement : Prop`, `proof : statement` (Tier 2 only) |
| `CertifiedProjection` | Meta/Config.lean | Proof-carrying record: enabled clusters + soundness + `constraintWitnesses` + `metaModularWitnesses` + `latticeWitnesses` + filtered enabled lists for all families |
| `certify` | Meta/Config.lean | `EpArchConfig → CertifiedProjection cfg` |

### Theorems

#### Soundness Theorem

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `clusterEnabled_sound` | Meta/Config.lean | `clusterEnabled cfg c = true → clusterValid c` | All enabled clusters are machine-proved |

#### Tier 2 Named Proof Witnesses (Forcing)

| Theorem | File | Statement | Role |
|---------|------|-----------|------|
| `cluster_forcing_distributed_agents` | Meta/Config.lean | `StructurallyForced W → handles_distributed_agents W → HasBubbles W` | Witness for `.forcing_distributed_agents` |
| `cluster_forcing_bounded_audit` | Meta/Config.lean | `StructurallyForced W → handles_bounded_audit W → HasTrustBridges W` | Witness for `.forcing_bounded_audit` |
| `cluster_forcing_export` | Meta/Config.lean | `StructurallyForced W → handles_export W → HasHeaders W` | Witness for `.forcing_export` |
| `cluster_forcing_adversarial` | Meta/Config.lean | `StructurallyForced W → handles_adversarial W → HasRevocation W` | Witness for `.forcing_adversarial` |
| `cluster_forcing_coordination` | Meta/Config.lean | `StructurallyForced W → handles_coordination W → HasBank W` | Witness for `.forcing_coordination` |
| `cluster_forcing_truth` | Meta/Config.lean | `StructurallyForced W → handles_truth_pressure W → HasRedeemability W` | Witness for `.forcing_truth` |
| `cluster_forcing_multi_agent` | Meta/Config.lean | `StructurallyForced W → handles_multi_agent W → HasGranularACL W` | Witness for `.forcing_multi_agent` |

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
| `cluster_world_spoofed_v` | Meta/Config.lean | `W_spoofedV → (V_spoof d ∨ consultation_suppressed a) → PathExists d → False` | `.spoofedV` | `AdversarialObligations.spoofed_V_blocks_path_of_W` |
| `cluster_world_lies_scale` | Meta/Config.lean | `W_lies_scale → W.export_cost < W.defense_cost` | `.lies_scale` | `AdversarialObligations.lies_scale_of_W` |
| `cluster_world_rolex_ddos` | Meta/Config.lean | `W_rolex_ddos → same_structure W.rolex_structure W.ddos_structure` | `.rolex_ddos` | `AdversarialObligations.rolex_ddos_structural_equivalence_of_W` |
| `cluster_world_ddos` | Meta/Config.lean | `W_ddos → (ladder_overloaded a ∨ V_channel_exhausted a ∨ E_field_poisoned a ∨ denial_triggered a) → verification_collapsed a` | `.ddos` | `AdversarialObligations.ddos_causes_verification_collapse_of_W` |

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

**Role:** Self-referential demonstration that Lean's own type-checking kernel is a valid, fully-grounded EpArch instantiation. Two layers are proved: (1) `LeanKernelCtx : WorldCtx` satisfies three W_* world-assumption bundles with kernel-specific interpretations (`sorry` ↔ lies, heartbeat ↔ bounded verification, proof irrelevance ↔ partial observability); (2) `LeanWorkingSystem : WorkingSystem` satisfies all seven architectural features, `PartialWellFormed allConstraints`, and `containsBankPrimitives` — both by direct construction and by the structural convergence path. Self-referential note: this file is type-checked by the same kernel it models.

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

`LeanWorkingSystem` is built from `withGroundedBehavior LeanGroundedBehavior {spec := LeanGroundedSystemSpec.toSystemSpec, …}`. All seven `Option GroundedXStrict` fields are `some`; all seven `HasX` predicates follow from `grounded_spec_contains_all`.

| Theorem | Statement | Evidence Source |
|---------|-----------|----------------|
| `lean_has_bubbles` | `HasBubbles LeanWorkingSystem` | `LeanGroundedBubbles` (Nat vs Int namespace disagreement) |
| `lean_has_trust_bridges` | `HasTrustBridges LeanWorkingSystem` | `LeanGroundedTrustBridges` (`import Init` trust bridge) |
| `lean_has_headers` | `HasHeaders LeanWorkingSystem` | `LeanGroundedHeaders` (`Nat.succ` type signature preserved) |
| `lean_has_revocation` | `HasRevocation LeanWorkingSystem` | `LeanGroundedRevocation` (sorry-tainted term → quarantine) |
| `lean_has_bank` | `HasBank LeanWorkingSystem` | `LeanGroundedBank` (InitDef produced and consumed) |
| `lean_has_redeemability` | `HasRedeemability LeanWorkingSystem` | `LeanGroundedRedeemability` (`#print axioms` audit path) |
| `lean_has_granular_acl` | `HasGranularACL LeanWorkingSystem` | `LeanGroundedAuthorization` (kernel/user ACL boundary) |

### Architecture Layer — Properties and Forcing

| Theorem | Statement | Route |
|---------|-----------|-------|
| `lean_implements_bank_primitives` | `containsBankPrimitives LeanWorkingSystem` | Direct: `∀ P, HasX` by inspection of `GroundedXStrict` fields |
| `lean_partial_wellformed` | `PartialWellFormed LeanWorkingSystem allConstraints` | Via `grounded_partial_wellformed LeanGroundedBehavior LeanGroundedSystemSpec` |
| `lean_satisfies_all_properties` | `SatisfiesAllProperties LeanWorkingSystem` | Via `grounded_behavior_satisfies_all LeanGroundedBehavior _` |
| `lean_structurally_forced` | `StructurallyForced LeanWorkingSystem` | Via `embedding_to_structurally_forced lean_forcing_embedding` |
| `lean_structural_convergence` | `containsBankPrimitives LeanWorkingSystem` | Indirect: `convergence_structural` via `StructurallyForced`; independently verified |
| `lean_kernel_forces_bank_primitives` | `containsBankPrimitives LeanWorkingSystem` | Citability alias; uses the direct route (`lean_implements_bank_primitives`) |

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

---
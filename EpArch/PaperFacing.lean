/-
Paper-Facing Surface

This module re-exports the canonical set of theorems that form the
stable API for the EpArch formalization.

## Strength Categories
- **Proved:** Derived theorems (fully proved)
- **Conditional:** Obligation theorems (`W_* → Mechanism`)
- **Spec:** Spec/interface axioms (design requirements)

Organization:
1. Core structural claims (spec)
2. Obligation theorems (conditional)
3. Health goals (proved, definitional)
4. Revision safety theorems (proved)
5. Gate theorems (proved)
6. Invariants (spec)
7. Agent constraints and PRP (proved)
8. Key predictions (conditional)
9. WorldCtx transport (proved)
10. Scope irrelevance (proved)
10b. Paper-facing transport gate (proved)
11. Feasibility (proved)
12. Meta-status proof pack (proved)
13. Multi-agent corroboration (proved)

When documenting claims, cite theorems from this file.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.WorldCtx
import EpArch.AdversarialObligations
import EpArch.Health
import EpArch.RevisionSafety
import EpArch.Theorems
import EpArch.Invariants
import EpArch.ScopeIrrelevance
import EpArch.Agent
import EpArch.Feasibility  -- Joint feasibility / non-vacuity
import EpArch.Meta.FalsifiableNotAuthorizable  -- Meta-status proof pack
import EpArch.Meta.TheoryCoreClaim  -- Optional stretch: theory_core claim token

namespace EpArch.PaperFacing

/-! ## 1. Core Structural Claims (Spec/Interface)

These define the architecture's type structure. They are design requirements,
not derived theorems.
-/

-- SEV Factorization: deposits have (S, E, V) structure
-- See: Basic.lean, Header.lean for Header structure

-- Bubble structure: scoped validation domains
-- See: Basic.lean for Bubble type

-- Bank operations: deposit, withdraw, challenge, repair
-- See: Bank.lean for LTS semantics

/-! ## 2. Obligation Theorems (Conditional)

These are the key conditional obligation theorems:
"If these world assumptions hold, then mechanism M follows."

**NOTE:** These are "assumption wrapper" theorems — they expose the W bundle
as an explicit premise. They do NOT derive mechanisms from first principles.
-/

-- WorldCtx core vocabulary (canonical world interface)
export EpArch (
  WorldCtx
)

export EpArch.WorldCtx (
  -- Derived concepts (context-parametric)
  Lie
  can_lie
  PartialObs
  NotDeterminedByObs
  RequiresSteps
  -- Assumption bundles
  W_lies_possible
  W_bounded_verification
  W_partial_observability
  W_asymmetric_costs
  -- Core obligation theorems
  lie_possible_of_W
  all_agents_can_lie_of_W
  bounded_audit_fails
  cost_asymmetry_of_W
  partial_obs_no_omniscience
)

-- Core world theorems (from WorldCtx)

-- Mechanism obligation theorems
export EpArch.AdversarialObligations (
  spoofed_V_blocks_path_of_W
  ddos_causes_verification_collapse_of_W
  collapse_causes_centralization_of_W
  lies_scale_of_W
  rolex_ddos_structural_equivalence_of_W
  ddos_to_centralization_of_W
)

-- Boundary condition countermeasures
export EpArch.AdversarialObligations (
  cheap_validator_blocks_V_attack_of_W
  trust_bridge_blocks_V_attack_of_W
  reversibility_neutralizes_τ_of_W
  E_inclusion_closes_expertise_gap_of_W
  cheap_constraint_blocks_V_spoof_of_W
)

-- Definitional cleanups
export EpArch (
  sophistication_monotonic
  sincerity_norms_irrelevant
  lies_structurally_possible
)

/-! ## 3. Health Goals (Proved, Definitional)

Health goals are definitional predicates over CoreOps.
They define what "healthy" means in terms of core operations.
Necessity theorems follow from definitions, not axioms.
-/

export EpArch (
  -- Health goals (definitional over CoreOps)
  SafeWithdrawalGoal
  ReliableExportGoal
  CorrigibleLedgerGoal
  SoundDepositsGoal
  SelfCorrectionGoal
  SelfCorrectingSystem

  -- Capability predicates (definitional)
  HasSubmitCapability
  HasRevisionCapability
  HasVerificationCapability
  HasSelfCorrectionCapability

  -- Necessity theorems (PROVED, not axioms)
  corrigible_needs_revision
  self_correction_needs_revision
  sound_deposits_needs_verification

  -- Combined
  FullSystemHealth
  self_correction_is_paper_facing
)

/-! ## 4. Revision Safety Theorems (Proved)

"Adding constraints doesn't break already-proved results."

Fully proved. `premise_strengthening` is basic propositional logic;
`safe_extension_preserves` uses Compatible commuting laws via `transport_core`.
-/

export EpArch.RevisionSafety (
  premise_strengthening
  safe_extension_preserves
)

/-! ## 5. Gate Theorems (Proved)

These are derived from the LTS semantics in StepSemantics.lean.
Fully proved, no axiom dependencies.
-/

-- Withdrawal requires three gates
-- See: Theorems.lean withdrawal_gates

-- Repair requires prior challenge
-- See: Theorems.lean repair_requires_prior_challenge

/-! ## 6. Invariants (Spec)

Protocol requirements for robust functioning.
Violations predict degradation, not impossibility.

These are design requirements that define what the protocol SHOULD maintain.
-/

export EpArch (
  grounded_no_withdrawal_without_acl    -- Proved theorem
  grounded_no_export_without_gate       -- Proved theorem
  challenge_requires_field_localization -- Proved theorem
  worldstate_requires_finite_τ          -- Proved theorem
)


/-! ## 7. Agent Constraints and PRP (Proved)

The agent layer captures embedded agency: imperfect agents operating under
permanent redeemability pressure.
-/

-- PRP consequences (proved theorems)
export EpArch.Agent (
  no_global_closure_of_PRP
  needs_revision_of_PRP
  needs_scoping_of_PRP
  needs_revalidation_of_PRP
  prp_incompatible_with_global_redeemability
)

-- Design-imposition theorems (proved via counterexample)
export EpArch.Agent (
  safe_withdrawal_needs_reversibility
  sound_deposits_need_cheap_validator
  reliable_export_needs_gate
)

-- Agent containment invariants (proved by trace induction)
export EpArch.Agent (
  truth_invariant_preserved
  gate_invariant_preserved
  truth_preserved_along_trace
  gate_preserved_along_trace
  agent_containment
)

-- Concrete pattern theorems (proved)
export EpArch.Agent (
  irreversibility_violates_safety
  safe_withdrawal_implies_reversibility
  no_validator_blocks_expensive_claims
  no_gate_allows_error_propagation
)


/-! ## 8. Key Predictions (Conditional)

The architecture predicts these attack patterns.
These are conditional on World assumption bundles.
-/

-- DDoS causes centralization (composed chain)
-- See: ddos_to_centralization_of_W

-- Lies scale: export cheaper than defense
-- See: lies_scale_of_W

-- Spoofed V blocks verification path
-- See: spoofed_V_blocks_path_of_W


/-! ## 9. WorldCtx Transport (Proved)

Transport theorems for world context extensions.
-/

-- WorldCtx lie transport (now proved, not axiom)
export EpArch (
  WorldCtx.transport_lies_possible
  WorldCtx.transport_lie_possible
)


/-! ## 10. Scope Irrelevance Theorems (Proved)

Turn "out of scope" prose into machine-checkable scope boundaries.
These prove that certain "fundamentals" are irrelevant-by-design.

Fully proved via model homomorphism / erasure lemmas.
-/

-- Substrate Independence
export EpArch.ScopeIrrelevance (
  Model
  ModelHom
  substrate_preserves_existence
)

-- Minimal Agency
export EpArch.ScopeIrrelevance (
  MinimalAgent
  agent_identity_suffices
)

-- Extra-State Erasure
export EpArch.ScopeIrrelevance (
  extra_state_erasure
  psychology_irrelevant
  consciousness_irrelevant
  embodiment_irrelevant
)

-- Traction-Implementation Irrelevance
export EpArch.ScopeIrrelevance (
  traction_modulation_confined
  traction_implementation_irrelevant
)


/-! ## Paper-Facing Transport Gate

**POLICY:** Any theorem mentioning extension-only fields must be transported
through `Compatible` / `transport_core` before being exported here.

The paper-facing surface uses ONLY:
1. Core theorems directly (from CoreSig/CoreOps), OR
2. Extension results transported via `Compatible` commuting laws

**Rationale:** This prevents semantic drift when extensions add fields.
If an extension redefines `selfCorrects`, the commuting law enforcement
in `Compatible` blocks it from reaching this surface unchanged.

**Checklist for new exports:**
- [ ] Does the theorem use only CoreSig types? → Export directly
- [ ] Does the theorem use ExtSig/ExtOps? → Must go through transport_core
- [ ] Is there a commuting law ensuring semantic preservation? → Required

See: `RevisionSafety.lean :: transport_core`, `CorePrims`, `Compatible`
-/

-- Revision Safety: transport_core is the gate for extension results
export EpArch.RevisionSafety (
  transport_core
  CorePrims
)


/-! ## 11. Feasibility / Non-Vacuity / Existence Under Constraints (Proved)

These theorems establish that the constraint+objective package is consistent
AND that success forces Bank primitives.

**Headline Theorem:** `existence_under_constraints`
- There EXISTS a working system (non-vacuity)
- That system is WellFormed and satisfies all properties (success)
- That system contains Bank primitives (forced by minimality)

**Buys:**
- "The core commitments are jointly satisfiable"
- "World constraint bundles have at least one witness"
- "There exists a successful working system"
- "Success forces Bank primitives"

**Does NOT buy:**
- "The real world is this model"
- "Uniqueness of realization"
- "Abduction from observation to system existence"
-/

-- Feasibility: full set of non-vacuity and existence theorems (cite in Appendix)
export EpArch.Feasibility (
  -- World-level feasibility
  world_bundles_feasible
  constraints_feasible
  -- Commitment-level feasibility
  commitments_feasible
  objectives_feasible
  -- System-level feasibility
  success_feasible
  -- Minimality alias
  goals_force_bank_primitives
  -- Headline theorem
  existence_under_constraints
  -- Legacy
  joint_feasible
)


/-! ## 12. Meta-Status Proof Pack (Proved)

The meta-level claims about the theory itself:
- (P1) Falsifiable: coherent countercontexts exist
- (P2) Not fully authorizable: underdetermination exists (credit required)
- (P3) Safe on credit: extension-safety prevents collapse

**Vocabulary Guard:**
- DO NOT say "never provable true" or "unprovable"
- Allowed: "not fully authorizable from observational surfaces"

**Headline Theorem:** `meta_status_proof_pack`

**Buys:**
- "Floor package is consistent (witness exists)"
- "Floor package is falsifiable (countercontext exists)"
- "Full authorization from obs is impossible (underdetermination)"
- "Extension doesn't collapse paper-facing claims"

**Does NOT buy:**
- "The real world is the witness"
- "The theory is unprovable"
- "People must accept it"
-/

-- Meta-status: falsifiable, not fully authorizable, safe on credit
export EpArch.Meta (
  -- Core definitions
  TheoryFloor
  TrivialCtx
  FullyAuthorizableByObs
  CreditRequired
  -- Pillar 1: Satisfiable + Falsifiable
  theory_floor_satisfiable
  theory_floor_falsifiable
  -- Pillar 2: Not fully authorizable
  theory_floor_not_fully_authorizable
  witness_requires_credit
  credit_required_implies_not_fully_authorizable
  theory_floor_implies_not_fully_authorizable
  witness_not_fully_authorizable
  -- Pillar 3: Safe on credit
  credit_safe_under_extension
  -- Headline theorem
  meta_status_proof_pack
  -- Optional Stretch: theory_core claim token (witness-specific)
  MetaClaim
  AddTheoryCore
  WitnessP0
  WitnessTheoryCoreCtx
  theory_core
  lift_notDeterminedByObs_theory_core
  witness_theory_core_not_determined
  witnessTheoryCoreCtx_satisfies_floor_bundles
  -- Universal Schema (no witness dependence)
  AddTheoryCoreFromPartialObs
  theory_core_token
  theory_core_token_not_determined
  witness_theory_core_not_determined'
)


/-! ## 13. Multi-Agent Corroboration (Proved)

Formal machinery for when multi-agent corroboration is required (conditional
minimality) and when it fails (common-mode/correlated compromise).

**Key Theorems:**
- T1: If NoSPoF goal and single-source attack possible, single attestation forbidden
- T3: Common-mode compromise breaks naive k-of-n corroboration
- T4: Diversity requirement for resilience

**Buys:**
- Formal reason "why 2-3 independent attestations beats one" (under independence interface)
- Formal reason "why corroboration can fail spectacularly" (common-mode / bubble infection)
- Conditional minimality: if NoSinglePointFailure goal, corroboration is forced

**Does NOT buy:**
- "Humans do this in practice" (no sociology)
- "The real world satisfies the independence interface" (no realism)
- "Corroboration guarantees truth" (only reduces risk under explicit constraints)
-/

-- Multi-agent corroboration theorems
export EpArch.Agent.Corroboration (
  -- Threat models (explicit toggles)
  SingleSourceAttack
  CommonModeAttack
  -- Acceptance rules
  SingleSourceAcceptance
  HasKWitnesses
  KOfNIndependentAcceptance
  -- T1: Necessity (single-source can accept false)
  single_source_can_accept_false
  no_spof_requires_multi_source
  -- T3: Common-mode breaks naive corroboration
  common_mode_breaks_naive_corroboration
  two_of_two_fails_under_common_mode
  -- T4: Diversity requirement
  common_mode_requires_diversity
  -- T2 components (sufficiency under independence bound)
  IndependenceBounded
  HonestImpliesTrue
  k_of_n_suffices_under_independence
  -- Headline package
  corroboration_package
)


/-! ## Section-to-Theorem Map

| Section | Key Theorems |
|---------|---------------|
| SEV structure | Header, SEVFactorization |
| Withdrawal gates | withdrawal_gates, canWithdrawAt_* |
| Gettier analysis | V-independence proxies in Theorems.lean |
| Export gating | grounded_no_export_without_gate |
| Bounded audit | bounded_audit_fails |
| Adversarial obligations | Obligation theorems |
| Health invariants | Health → necessity theorems |
| Scope irrelevance | ScopeIrrelevance theorems |

-/

end EpArch.PaperFacing

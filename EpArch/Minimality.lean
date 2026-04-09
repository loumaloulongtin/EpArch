/-
Minimality and Impossibility Theorems

This is where "only possible solution" becomes theorem-grade:
- Constraints + desiderata → must have these primitives
- Remove primitive X → cannot satisfy properties Y

The core claim is CONVERGENCE under constraints, not metaphysical necessity.
These theorems formalize that convergence.

## Central Role

This file contains the paper's HEADLINE RESULT: if a system is well-formed
and satisfies all operational properties (withdrawal-safety, export-gating,
revision-capability, temporal-expiry, redeemability-grounding), then it
necessarily contains the Bank primitives (scoped bubbles, header-bearing
deposits, redeemability, export gates, revision protocol).

This is convergence, not uniqueness: ANY working solution must contain
these structural elements, but implementations can differ.

## Key Definitions

- `Constraints` — typeclass capturing the minimal system predicates
- `WorkingSystem` — a system satisfying all operational properties
- `WellFormed` — no trivially-degenerate configurations
- `convergence_under_constraints'` — WorkingSystem + WellFormed → has all Bank primitives

## Dependencies

- **SystemSpec.lean:** provides the `SystemSpec` structure that `MinimalConstraints` wraps
- **Commitments.lean:** the axioms that are shown to be forced
- **ConcreteLedgerModel.lean:** proves `WorkingSystem` is nonempty (non-vacuity)
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments
import EpArch.SystemSpec

namespace EpArch

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ## Constraints Typeclass (Minimal Constraints)

The minimal constraints table has three columns:
  | Constraint | What It Forces | If Relaxed |

This typeclass captures the CONSTRAINT column. The "What It Forces" is captured
by the convergence theorem and impossibility theorems below. -/

/-- Predicate: agent controls acceptance for a bubble. -/
opaque controls_acceptance : Agent → Bubble → Prop

/-- Predicate: claim can be fully verified within available resources. -/
opaque can_fully_verify : PropLike → Prop

/-- Predicate: deposit is an adversarial injection (fabricated claim/header). -/
opaque is_adversarial_injection : Deposit PropLike Standard ErrorModel Provenance → Prop

/-- Predicate: deposit passed the bubble's acceptance protocol. -/
opaque passed_acceptance : Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop

/-- The minimal constraints encoded as a typeclass.
    Each field corresponds to one row of the constraint table.
    The semantic content captures the informal descriptions. -/
class Constraints (B : Bank (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop where

  /-- **Distributed agents**: No single agent controls all bubble acceptance.
      If relaxed: single agent control suffices; no Bank needed. -/
  distributed_agents : ¬∃ (controller : Agent), ∀ (B : Bubble), controls_acceptance controller B

  /-- **Bounded audit**: Some claims cannot be fully verified.
      If relaxed: unbounded audit; full revalidation always; no need for trust-based import. -/
  bounded_audit : ∃ (P : PropLike), ¬can_fully_verify P

  /-- **Export across boundaries**: Deposits propagate between distinct bubbles.
      If relaxed: isolated bubbles; coordination collapses but no contamination. -/
  export_across_boundaries : ∃ (B1 B2 : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance),
    B1 ≠ B2 ∧ exportDep B1 B2 d

  /-- **Adversarial/corruption pressure**: Adversarial deposits can pass acceptance.
      If relaxed: weaker V requirements; simpler hygiene.
      Note: The PRESSURE is that bad deposits sometimes succeed. -/
  adversarial_pressure : ∃ (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance),
    is_adversarial_injection d ∧ passed_acceptance B d

  /-- **Coordination need**: Multiple agents must rely on shared deposits.
      If relaxed: no coordination; each agent runs solo. -/
  coordination_need : ∃ (a1 a2 : Agent) (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance),
    a1 ≠ a2 ∧ withdraw a1 B d ∧ withdraw a2 B d

  /-- **Truth pressure (redeemability)**: Deposits can fail constraint-surface contact.
      If relaxed: self-agreement suffices; system drifts into unfalsifiable consensus. -/
  truth_pressure : ∃ (d : Deposit PropLike Standard ErrorModel Provenance),
    d.status = .Deposited ∧ ¬redeemable d


/-! ## Working System Abstraction -/

/-- A "working system" that coordinates under uncertainty.

    This abstracts over any system that successfully enables coordination
    while handling the constraints above. Such systems converge on
    Bank-like primitives. -/
structure WorkingSystem where
  /-- The system's architectural specification. -/
  spec : SystemSpec
  /-- System has shared records that agents can deposit into. -/
  has_shared_records : Bool
  /-- System enables agents to rely on each other's deposits. -/
  enables_reliance : Bool
  /-- System can recover from discovered errors (repair loop). -/
  supports_correction : Bool
  /-- System resists adversarial injection (counterfeit detection). -/
  resists_adversaries : Bool

/-- System achieves coordination: agents can reliably act together.
    Requires shared records + ability to rely on them.
    Note: See handles_coordination for the six-property formulation. -/
def achieves_coordination (W : WorkingSystem) : Prop :=
  W.has_shared_records ∧ W.enables_reliance

/-- System achieves bounded-audit operation: works without full verification.
    Note: See handles_bounded_audit for the six-property formulation. -/
def achieves_bounded_audit' (W : WorkingSystem) : Prop :=
  W.has_shared_records ∧ W.enables_reliance  -- can rely without re-verifying

/-- System achieves adversarial resilience: survives attacks.
    Note: See handles_adversarial for the six-property formulation. -/
def achieves_adversarial_resilience (W : WorkingSystem) : Prop :=
  W.supports_correction ∧ W.resists_adversaries

/-- System satisfies target properties: coordination + bounded-audit + adversarial resilience.
    Note: This checks only three aggregate properties; see SatisfiesAllProperties for the full six-property version. -/
def SatisfiesProperties (W : WorkingSystem) : Prop :=
  achieves_coordination W ∧ achieves_bounded_audit' W ∧ achieves_adversarial_resilience W


/-! ## Bank Primitives Predicate -/

/-- The primitives that constitute "Bank-like" architecture:
    deposits, headers, acceptance, withdrawal, export, repair. -/
structure BankPrimitives where
  /-- Has deposit/record storage -/
  has_deposits : Bool
  /-- Has structured headers (S/E/V/τ/ACL/Redeem) -/
  has_headers : Bool
  /-- Has acceptance protocol (governance gate) -/
  has_acceptance : Bool
  /-- Has withdrawal mechanism (reliance) -/
  has_withdrawal : Bool
  /-- Has export/import across boundaries -/
  has_export : Bool
  /-- Has repair loop (challenge → quarantine → repair/revoke) -/
  has_repair_loop : Bool

/-! ## Forced Feature Predicates

These are definitional predicates that inspect the WorkingSystem's
SystemSpec to determine if features are present. Each predicate
corresponds to one "What It Forces" entry in the constraints table. -/

/-- Predicate: system has scoped trust zones (bubbles), not a global ledger.
    Forced by: Distributed agents -/
def HasBubbles (W : WorkingSystem) : Prop := W.spec.has_bubble_separation = true

/-- Predicate: system has trust bridges (import-via-trust without full revalidation).
    Forced by: Bounded audit -/
def HasTrustBridges (W : WorkingSystem) : Prop := W.spec.has_trust_bridges = true

/-- Predicate: system has structured headers (S/E/V) + export gates.
    Forced by: Export across boundaries -/
def HasHeaders (W : WorkingSystem) : Prop := W.spec.preserves_headers = true

/-- Predicate: system has V-independence discipline + revocation mechanism.
    Forced by: Adversarial pressure -/
def HasRevocation (W : WorkingSystem) : Prop := W.spec.has_revocation = true

/-- Predicate: system has Bank (authorization ledger) + acceptance events.
    Forced by: Coordination need -/
def HasBank (W : WorkingSystem) : Prop := W.spec.has_shared_ledger = true

/-- Predicate: system has redeemability (constraint-surface contact).
    Forced by: Truth pressure -/
def HasRedeemability (W : WorkingSystem) : Prop := W.spec.has_redeemability = true

/-- A system contains Bank primitives iff it has all six forced features.
    This is what the convergence theorem claims systems must have.

    Note: Defined as a conjunction of Has* predicates,
    so `all_features_constitute_bank` follows definitionally. -/
def containsBankPrimitives (W : WorkingSystem) : Prop :=
  HasBubbles W ∧ HasTrustBridges W ∧ HasHeaders W ∧
  HasRevocation W ∧ HasBank W ∧ HasRedeemability W


/-! ## Six Operational Properties

These are the functional requirements that working systems must satisfy.
Each maps to one constraint in the table. -/

/-- System handles distributed agents: no single controller.
    Required when: Distributed agents constraint holds. -/
def handles_distributed_agents (W : WorkingSystem) : Prop :=
  W.has_shared_records = true  -- requires some form of shared records

/-- System handles bounded audit: can operate without full verification.
    Required when: Bounded audit constraint holds. -/
def handles_bounded_audit (W : WorkingSystem) : Prop :=
  W.enables_reliance = true  -- can rely without re-verifying

/-- System handles export: deposits can cross bubble boundaries.
    Required when: Export across boundaries constraint holds. -/
def handles_export (W : WorkingSystem) : Prop :=
  W.has_shared_records = true ∧ W.enables_reliance = true  -- records + reliance enables export

/-- System handles adversarial pressure: survives attacks.
    Required when: Adversarial pressure constraint holds. -/
def handles_adversarial (W : WorkingSystem) : Prop :=
  W.supports_correction = true ∧ W.resists_adversaries = true

/-- System handles coordination need: enables collective reliance.
    Required when: Coordination need constraint holds. -/
def handles_coordination (W : WorkingSystem) : Prop :=
  W.has_shared_records = true ∧ W.enables_reliance = true

/-- System handles truth pressure: deposits can fail constraint-surface contact.
    Required when: Truth pressure constraint holds. -/
def handles_truth_pressure (W : WorkingSystem) : Prop :=
  W.supports_correction = true  -- correction implies deposits can fail

/-- A working system satisfies ALL six operational properties. -/
def SatisfiesAllProperties (W : WorkingSystem) : Prop :=
  handles_distributed_agents W ∧
  handles_bounded_audit W ∧
  handles_export W ∧
  handles_adversarial W ∧
  handles_coordination W ∧
  handles_truth_pressure W


/-! ## Well-Formed Systems: Behavioral/Architectural Coherence

A system is "well-formed" if its behavioral capabilities are backed by
the corresponding architectural features. This is the key invariant that
allows the linking axioms to become theorems.

In a real system, you can't "handle distributed agents" without bubbles,
you can't "handle export" without headers, etc. The well-formedness predicate
captures this necessary coherence. -/

/-- A system is well-formed if behavioral capabilities ↔ architectural features.

    This is the DESIGN INVARIANT: systems claiming to handle a property
    must actually have the architectural feature that enables it, AND
    systems with the architectural feature must have the capability enabled.

    Note: This is not a circular definition. The behavioral predicates
    (handles_*) inspect boolean flags. The architectural predicates
    (Has*) inspect SystemSpec. Well-formedness connects these two layers
    BIDIRECTIONALLY, enabling proofs in both directions. -/
def WellFormed (W : WorkingSystem) : Prop :=
  -- Distributed agents handling ↔ bubbles
  (W.has_shared_records = true ↔ W.spec.has_bubble_separation = true) ∧
  -- Bounded audit handling ↔ trust bridges
  (W.enables_reliance = true ↔ W.spec.has_trust_bridges = true) ∧
  -- Export handling ↔ headers
  (W.has_shared_records = true ∧ W.enables_reliance = true ↔ W.spec.preserves_headers = true) ∧
  -- Adversarial handling ↔ revocation
  (W.supports_correction = true ∧ W.resists_adversaries = true ↔ W.spec.has_revocation = true) ∧
  -- Coordination handling ↔ bank
  (W.has_shared_records = true ∧ W.enables_reliance = true ↔ W.spec.has_shared_ledger = true) ∧
  -- Truth pressure handling ↔ redeemability
  (W.supports_correction = true ↔ W.spec.has_redeemability = true)


/-! ## Linking Theorems: Constraint → Forced Feature

Each theorem formalizes one row of the "What It Forces" column.
These are the load-bearing connections between operational requirements
and architectural primitives. -/

/-- Distributed agents → Bubbles. -/
theorem distributed_agents_require_bubbles (W : WorkingSystem) (h_wf : WellFormed W) :
  handles_distributed_agents W → HasBubbles W := by
  intro h_handles
  unfold handles_distributed_agents at h_handles
  unfold HasBubbles
  exact h_wf.1.mp h_handles

/-- Bounded audit → Trust bridges. -/
theorem bounded_audit_requires_trust_bridges (W : WorkingSystem) (h_wf : WellFormed W) :
  handles_bounded_audit W → HasTrustBridges W := by
  intro h_handles
  unfold handles_bounded_audit at h_handles
  unfold HasTrustBridges
  exact h_wf.2.1.mp h_handles

/-- Export across boundaries → Headers + gates. -/
theorem export_requires_headers (W : WorkingSystem) (h_wf : WellFormed W) :
  handles_export W → HasHeaders W := by
  intro h_handles
  unfold handles_export at h_handles
  unfold HasHeaders
  exact h_wf.2.2.1.mp h_handles

/-- Adversarial pressure → V-independence + revocation. -/
theorem adversarial_requires_revocation (W : WorkingSystem) (h_wf : WellFormed W) :
  handles_adversarial W → HasRevocation W := by
  intro h_handles
  unfold handles_adversarial at h_handles
  unfold HasRevocation
  exact h_wf.2.2.2.1.mp h_handles

/-- Coordination need → Bank + acceptance. -/
theorem coordination_requires_bank (W : WorkingSystem) (h_wf : WellFormed W) :
  handles_coordination W → HasBank W := by
  intro h_handles
  unfold handles_coordination at h_handles
  unfold HasBank
  exact h_wf.2.2.2.2.1.mp h_handles

/-- Truth pressure → Redeemability. -/
theorem truth_pressure_requires_redeemability (W : WorkingSystem) (h_wf : WellFormed W) :
  handles_truth_pressure W → HasRedeemability W := by
  intro h_handles
  unfold handles_truth_pressure at h_handles
  unfold HasRedeemability
  exact h_wf.2.2.2.2.2.mp h_handles


/-! ## Six Impossibility Theorems

Each theorem proves: if you lack the forced feature, you cannot satisfy
the corresponding operational property. -/

/-- Impossibility #1: No bubbles → cannot handle distributed agents. -/
theorem no_bubbles_implies_failure (W : WorkingSystem) (h_wf : WellFormed W) :
    ¬HasBubbles W → ¬handles_distributed_agents W := by
  intro h_no_bubbles h_handles
  have h_has_bubbles := distributed_agents_require_bubbles W h_wf h_handles
  exact h_no_bubbles h_has_bubbles

/-- Impossibility #2: No trust bridges → cannot handle bounded audit. -/
theorem no_trust_bridges_implies_failure (W : WorkingSystem) (h_wf : WellFormed W) :
    ¬HasTrustBridges W → ¬handles_bounded_audit W := by
  intro h_no_bridges h_handles
  have h_has_bridges := bounded_audit_requires_trust_bridges W h_wf h_handles
  exact h_no_bridges h_has_bridges

/-- Impossibility #3: No headers → cannot handle export. -/
theorem no_headers_implies_failure' (W : WorkingSystem) (h_wf : WellFormed W) :
    ¬HasHeaders W → ¬handles_export W := by
  intro h_no_headers h_handles
  have h_has_headers := export_requires_headers W h_wf h_handles
  exact h_no_headers h_has_headers

/-- Impossibility #4: No revocation → cannot handle adversarial pressure. -/
theorem no_revocation_implies_failure (W : WorkingSystem) (h_wf : WellFormed W) :
    ¬HasRevocation W → ¬handles_adversarial W := by
  intro h_no_revocation h_handles
  have h_has_revocation := adversarial_requires_revocation W h_wf h_handles
  exact h_no_revocation h_has_revocation

/-- Impossibility #5: No bank → cannot handle coordination. -/
theorem no_bank_implies_failure (W : WorkingSystem) (h_wf : WellFormed W) :
    ¬HasBank W → ¬handles_coordination W := by
  intro h_no_bank h_handles
  have h_has_bank := coordination_requires_bank W h_wf h_handles
  exact h_no_bank h_has_bank

/-- Impossibility #6: No redeemability → cannot handle truth pressure. -/
theorem no_redeemability_implies_failure (W : WorkingSystem) (h_wf : WellFormed W) :
    ¬HasRedeemability W → ¬handles_truth_pressure W := by
  intro h_no_redeem h_handles
  have h_has_redeem := truth_pressure_requires_redeemability W h_wf h_handles
  exact h_no_redeem h_has_redeem


/-! ## Global Impossibility and Convergence -/

/-- All six forced features together constitute Bank-like architecture.

    This is a definitional theorem: containsBankPrimitives
    is defined as the conjunction of the six Has* predicates. -/
theorem all_features_constitute_bank (W : WorkingSystem) :
  HasBubbles W → HasTrustBridges W → HasHeaders W →
  HasRevocation W → HasBank W → HasRedeemability W →
  containsBankPrimitives W := by
  intro h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Global impossibility: A system missing ANY forced feature cannot
    satisfy ALL properties.

    This is the summary impossibility theorem: you need all six features
    to handle all six constraints. -/
theorem missing_any_feature_implies_failure (W : WorkingSystem) (h_wf : WellFormed W) :
    (¬HasBubbles W ∨ ¬HasTrustBridges W ∨ ¬HasHeaders W ∨
     ¬HasRevocation W ∨ ¬HasBank W ∨ ¬HasRedeemability W) →
    ¬SatisfiesAllProperties W := by
  intro h_missing h_satisfies
  have ⟨h1, h2, h3, h4, h5, h6⟩ := h_satisfies
  cases h_missing with
  | inl h => exact h (distributed_agents_require_bubbles W h_wf h1)
  | inr h => cases h with
    | inl h => exact h (bounded_audit_requires_trust_bridges W h_wf h2)
    | inr h => cases h with
      | inl h => exact h (export_requires_headers W h_wf h3)
      | inr h => cases h with
        | inl h => exact h (adversarial_requires_revocation W h_wf h4)
        | inr h => cases h with
          | inl h => exact h (coordination_requires_bank W h_wf h5)
          | inr h => exact h (truth_pressure_requires_redeemability W h_wf h6)

/-- Main convergence theorem: under constraints, any working architecture
    contains the Bank primitives (all six forced features). -/
theorem convergence_under_constraints' (W : WorkingSystem) (h_wf : WellFormed W) :
    SatisfiesAllProperties W → containsBankPrimitives W := by
  intro h_satisfies
  have ⟨h1, h2, h3, h4, h5, h6⟩ := h_satisfies
  have hB := distributed_agents_require_bubbles W h_wf h1
  have hT := bounded_audit_requires_trust_bridges W h_wf h2
  have hH := export_requires_headers W h_wf h3
  have hR := adversarial_requires_revocation W h_wf h4
  have hK := coordination_requires_bank W h_wf h5
  have hD := truth_pressure_requires_redeemability W h_wf h6
  exact all_features_constitute_bank W hB hT hH hR hK hD


/-! ## Sharp Behavioral Equivalence

Systems with Bank primitives are "behaviorally equivalent" for coordination
purposes. Define the observation boundary explicitly, then show that
systems with identical primitives produce identical observations. -/

/-! ### Input Events -/

/-- Input events that a WorkingSystem can receive.
    These are the abstract analogues of CInputEvent in ConcreteLedgerModel.lean. -/
inductive Input where
  /-- Request to withdraw/rely on a deposit. -/
  | WithdrawRequest (agent_id : Nat) (bubble_id : Nat) (claim_id : Nat)
  /-- Request to export deposit across boundary. -/
  | ExportRequest (source_bubble : Nat) (target_bubble : Nat) (claim_id : Nat)
  /-- Challenge a deposit's validity. -/
  | ChallengeRequest (claim_id : Nat) (field : String)
  /-- Time advance. -/
  | TimeAdvance (ticks : Nat)
  deriving Repr, DecidableEq

/-! ### Observable Outcomes -/

/-- Observable outcomes from processing inputs.
    These are the abstract analogues of COutcome in ConcreteLedgerModel.lean. -/
inductive Observation where
  /-- Withdrawal succeeded. -/
  | WithdrawSuccess (claim_id : Nat)
  /-- Withdrawal denied with reason. -/
  | WithdrawDenied (reason : String)
  /-- Export succeeded. -/
  | ExportSuccess (claim_id : Nat) (target_bubble : Nat)
  /-- Export denied with reason. -/
  | ExportDenied (reason : String)
  /-- Challenge processed. -/
  | ChallengeProcessed (result : String)
  /-- Time advanced. -/
  | TimeAdvanced
  deriving Repr, DecidableEq

/-! ### Behavior Function -/

/-- The behavior of a WorkingSystem on an input.

    This is the KEY INSIGHT: behavior depends ONLY on the primitives.
    Two systems with the same primitives produce the same observations.

    The function is defined by cases on what primitives the system has.
    This makes the link between primitives and behavior DEFINITIONAL. -/
def Behavior (W : WorkingSystem) (i : Input) : Observation :=
  match i with
  | .WithdrawRequest _ _ claim_id =>
    -- Withdrawal requires: shared records + reliance
    if W.has_shared_records ∧ W.enables_reliance then
      .WithdrawSuccess claim_id
    else
      .WithdrawDenied "missing primitives"
  | .ExportRequest _ target claim_id =>
    -- Export requires: shared records + reliance
    if W.has_shared_records ∧ W.enables_reliance then
      .ExportSuccess claim_id target
    else
      .ExportDenied "missing primitives"
  | .ChallengeRequest _ field =>
    -- Challenge requires: correction support
    if W.supports_correction then
      .ChallengeProcessed s!"challenged field {field}"
    else
      .ChallengeProcessed "no correction support"
  | .TimeAdvance _ =>
    .TimeAdvanced

/-! ### Sharp Behavioral Equivalence -/

/-- Two systems are behaviorally equivalent iff they produce
    the same observations on ALL inputs.

    This is the SHARP definition: not "similar enough" but
    "identical on the observation boundary". -/
def BehaviorallyEquivalent (W1 W2 : WorkingSystem) : Prop :=
  ∀ i : Input, Behavior W1 i = Behavior W2 i

/-! ### Theorems -/

/-- Behavioral equivalence is reflexive. -/
theorem behavioral_equiv_refl (W : WorkingSystem) : BehaviorallyEquivalent W W := by
  intro i
  rfl

/-- Behavioral equivalence is symmetric. -/
theorem behavioral_equiv_symm (W1 W2 : WorkingSystem) :
    BehaviorallyEquivalent W1 W2 → BehaviorallyEquivalent W2 W1 := by
  intro h i
  exact (h i).symm

/-- Behavioral equivalence is transitive. -/
theorem behavioral_equiv_trans (W1 W2 W3 : WorkingSystem) :
    BehaviorallyEquivalent W1 W2 → BehaviorallyEquivalent W2 W3 →
    BehaviorallyEquivalent W1 W3 := by
  intro h12 h23 i
  exact (h12 i).trans (h23 i)

/-- Core lemma: systems with identical primitive flags behave identically.

    This is the computational content: Behavior only inspects
    has_shared_records, enables_reliance, and supports_correction.
    The resists_adversaries flag is included for completeness but not used by Behavior. -/
theorem same_flags_same_behavior (W1 W2 : WorkingSystem)
    (h_records : W1.has_shared_records = W2.has_shared_records)
    (h_reliance : W1.enables_reliance = W2.enables_reliance)
    (h_correction : W1.supports_correction = W2.supports_correction)
    (_h_adversaries : W1.resists_adversaries = W2.resists_adversaries) :
    BehaviorallyEquivalent W1 W2 := by
  intro i
  simp [Behavior]
  cases i with
  | WithdrawRequest agent_id bubble_id claim_id =>
    simp [h_records, h_reliance]
  | ExportRequest source target claim_id =>
    simp [h_records, h_reliance]
  | ChallengeRequest claim_id field =>
    simp [h_correction]
  | TimeAdvance ticks =>
    rfl

/-- Helper lemma: SatisfiesAllProperties fixes all behavioral flags.

    This is the key computational insight: if a system satisfies all properties,
    we know exactly what its flags must be. -/
theorem satisfies_all_fixes_flags (W : WorkingSystem) (h : SatisfiesAllProperties W) :
    W.has_shared_records = true ∧
    W.enables_reliance = true ∧
    W.supports_correction = true ∧
    W.resists_adversaries = true := by
  have ⟨h1, h2, _h3, h4, _h5, _h6⟩ := h
  -- h1: handles_distributed_agents W = (W.has_shared_records = true)
  -- h2: handles_bounded_audit W = (W.enables_reliance = true)
  -- h4: handles_adversarial W = (W.supports_correction = true ∧ W.resists_adversaries = true)
  unfold handles_distributed_agents at h1
  unfold handles_bounded_audit at h2
  unfold handles_adversarial at h4
  exact ⟨h1, h2, h4.1, h4.2⟩

/-- Main behavioral equivalence theorem: systems satisfying all properties behave identically.
    Proof: SatisfiesAllProperties fixes all flags, same flags = same behavior. -/
theorem working_systems_equivalent (W1 W2 : WorkingSystem) :
    SatisfiesAllProperties W1 → SatisfiesAllProperties W2 → BehaviorallyEquivalent W1 W2 := by
  intro h_sat1 h_sat2
  have ⟨h1_rec, h1_rel, h1_cor, h1_adv⟩ := satisfies_all_fixes_flags W1 h_sat1
  have ⟨h2_rec, h2_rel, h2_cor, h2_adv⟩ := satisfies_all_fixes_flags W2 h_sat2
  exact same_flags_same_behavior W1 W2
    (h1_rec.trans h2_rec.symm)
    (h1_rel.trans h2_rel.symm)
    (h1_cor.trans h2_cor.symm)
    (h1_adv.trans h2_adv.symm)

/-- Systems with Bank primitives are behaviorally equivalent for coordination.

    containsBankPrimitives implies the SystemSpec has all features, which
    (for well-formed systems) implies the behavioral flags are set correctly.

    Note: This requires bidirectional well-formedness to connect spec features
    to behavioral flags. The `mpr` direction of WellFormed gives us:
    spec feature = true → behavioral flag = true. -/
theorem bank_primitives_determine_behavior (W1 W2 : WorkingSystem)
    (h_wf1 : WellFormed W1) (h_wf2 : WellFormed W2) :
    containsBankPrimitives W1 → containsBankPrimitives W2 →
    BehaviorallyEquivalent W1 W2 := by
  intro h1 h2
  -- containsBankPrimitives unfolds to Has* conjunctions
  unfold containsBankPrimitives at h1 h2
  have ⟨hB1, hT1, _hH1, hR1, _hK1, hD1⟩ := h1
  have ⟨hB2, hT2, _hH2, hR2, _hK2, hD2⟩ := h2
  -- Has* are definitional: HasBubbles W = W.spec.has_bubble_separation = true
  unfold HasBubbles HasTrustBridges HasHeaders HasRevocation HasBank HasRedeemability at *
  -- Use bidirectional WellFormed to derive flag values from spec features
  -- WellFormed.1.mpr: spec.has_bubble_separation = true → has_shared_records = true
  have h1_rec : W1.has_shared_records = true := h_wf1.1.mpr hB1
  have h1_rel : W1.enables_reliance = true := h_wf1.2.1.mpr hT1
  have h1_cor : W1.supports_correction = true := h_wf1.2.2.2.2.2.mpr hD1
  -- For resists_adversaries, we need to extract from the revocation ↔
  -- WellFormed says: (supports_correction ∧ resists_adversaries) ↔ has_revocation
  have h1_adv_pair : W1.supports_correction = true ∧ W1.resists_adversaries = true :=
    h_wf1.2.2.2.1.mpr hR1
  have h1_adv : W1.resists_adversaries = true := h1_adv_pair.2
  -- Same for W2
  have h2_rec : W2.has_shared_records = true := h_wf2.1.mpr hB2
  have h2_rel : W2.enables_reliance = true := h_wf2.2.1.mpr hT2
  have h2_cor : W2.supports_correction = true := h_wf2.2.2.2.2.2.mpr hD2
  have h2_adv_pair : W2.supports_correction = true ∧ W2.resists_adversaries = true :=
    h_wf2.2.2.2.1.mpr hR2
  have h2_adv : W2.resists_adversaries = true := h2_adv_pair.2
  -- Now apply same_flags_same_behavior
  exact same_flags_same_behavior W1 W2
    (h1_rec.trans h2_rec.symm)
    (h1_rel.trans h2_rel.symm)
    (h1_cor.trans h2_cor.symm)
    (h1_adv.trans h2_adv.symm)


/-! ## Primitive Necessity Summary -/

/-- Summary structure: what primitives are forced by what constraints. -/
structure PrimitiveNecessity where
  constraint : String
  forced_primitive : String
  if_removed : String

/-- The minimal constraints table as data. -/
def minimalConstraintsTable : List PrimitiveNecessity := [
  ⟨"Distributed agents", "Bubbles (scoped domains)", "Single agent; personal certainty suffices"⟩,
  ⟨"Bounded audit", "Trust bridges", "Unbounded audit; full revalidation always possible"⟩,
  ⟨"Export across boundaries", "Headers (S/E/V) + export gating", "No export; isolated scopes"⟩,
  ⟨"Adversarial pressure", "Provenance discipline + revocation", "No adversaries; simpler hygiene"⟩,
  ⟨"Coordination need", "Bank (shared ledger)", "No coordination; Ladder suffices"⟩,
  ⟨"Truth pressure", "Redeemability reference", "No truth pressure; unfalsifiable consensus"⟩
]


/-! ========================================================================
    Structural Forcing Models
    ========================================================================

The forcing theorems above (`distributed_agents_require_bubbles`, etc.)
derive features from the `WellFormed` coherence package, which explicitly
states biconditionals like `has_shared_records ↔ has_bubble_separation`.
A fair criticism: those proofs are projections from assumed equivalences.

This section provides **independent, structurally-grounded proofs** for
each forcing direction.  Each model captures the essential structure of
one constraint scenario and proves an impossibility or invariance result
from that structure alone — no `WellFormed`, no biconditionals.

### Summary

| # | Constraint | Model | Theorem | Content |
|---|---|---|---|---|
| 1 | Distributed agents | `AgentDisagreement` | `flat_scope_impossible` | Single scope can't represent disagreeing agents |
| 2 | Bounded audit | `BoundedVerification` | `verification_only_import_incomplete` | Verification-only import can't handle all claims |
| 3 | Export | `DiscriminatingImport` | `uniform_import_nondiscriminating` | Without metadata, import can't distinguish claims |
| 4 | Adversarial | `MonotonicLifecycle` | `monotonic_no_exit` | Without revocation, accepted state is absorbing |
| 5 | Coordination | `PrivateOnlyStorage` | `private_storage_no_sharing` | Isolated storage blocks collective reliance |
| 6 | Truth pressure | `ClosedEndorsement` | `closed_system_unfalsifiable` | Without external contact, consensus is unfalsifiable |

After the six models, `StructurallyForced` packages the forward-direction
implications (capability → feature) and `convergence_structural` provides
a convergence theorem that does **not** depend on `WellFormed`.
-/


/-! ### 1. Distributed Agents → Scope Separation (Bubbles)

**Argument.**  If two agents have genuinely different acceptance criteria,
no single flat acceptance function can faithfully represent both.  The
system must partition into scopes (bubbles) where each scope has its own
acceptance gate.

**Proof technique.**  Contradiction: a single function that agrees with
agent 1 on the witness claim must accept it; but then it also agrees with
agent 2, who rejects it. -/

/-- Two agents whose acceptance criteria disagree on at least one claim. -/
structure AgentDisagreement where
  Claim : Type
  /-- Agent 1's acceptance criterion. -/
  accept₁ : Claim → Prop
  /-- Agent 2's acceptance criterion. -/
  accept₂ : Claim → Prop
  /-- Witness claim where they disagree. -/
  witness : Claim
  /-- Agent 1 accepts the witness. -/
  agent1_accepts : accept₁ witness
  /-- Agent 2 rejects the witness. -/
  agent2_rejects : ¬accept₂ witness

/-- No single predicate can simultaneously agree with two disagreeing agents.
    A flat (single-scope) system commits to one acceptance function for all agents.
    When agents disagree, that function cannot faithfully represent both.

    Consequence: scope separation (bubbles) is structurally forced. -/
theorem flat_scope_impossible (D : AgentDisagreement) :
    ¬∃ (f : D.Claim → Prop), (∀ c, f c ↔ D.accept₁ c) ∧ (∀ c, f c ↔ D.accept₂ c) := by
  intro ⟨f, hf₁, hf₂⟩
  exact D.agent2_rejects ((hf₂ D.witness).mp ((hf₁ D.witness).mpr D.agent1_accepts))


/-! ### 2. Bounded Audit → Trust Bridges

**Argument.**  When full verification has unbounded cost, some claims
exceed any fixed budget.  A verification-only import policy (re-verify
every import from scratch) cannot handle those claims.  To import them
the system needs a trust-based mechanism: accept based on the source
scope's endorsement rather than full reverification.

**Proof technique.**  The hard claim's cost exceeds the budget; omega
closes the Nat contradiction. -/

/-- A claim universe where at least one claim exceeds the verification budget. -/
structure BoundedVerification where
  Claim : Type
  /-- Cost to fully verify a claim. -/
  verify_cost : Claim → Nat
  /-- Maximum verification budget per import. -/
  budget : Nat
  /-- A claim that exceeds the budget. -/
  hard_claim : Claim
  exceeds_budget : verify_cost hard_claim > budget

/-- Verification-only import cannot handle all claims under bounded audit.
    At least one claim exceeds the budget and cannot be reverified.

    Consequence: a trust-based import mechanism (trust bridges) is forced. -/
theorem verification_only_import_incomplete (M : BoundedVerification) :
    ¬∀ c : M.Claim, M.verify_cost c ≤ M.budget := by
  intro h
  have h_within := h M.hard_claim
  exact absurd h_within (Nat.not_le_of_gt M.exceeds_budget)


/-! ### 3. Export Across Boundaries → Headers (Metadata)

**Argument.**  When deposits cross scope boundaries the receiving scope
must decide whether to accept each import.  If the receiver has no
metadata about the deposit (no headers), every deposit looks identical —
the import function is uniform.  A uniform function cannot discriminate
good imports from bad.

**Proof technique.**  A uniform function produces `f good = f bad`
by definition; but sound-and-complete import requires different answers
for good and bad claims. -/

/-- Two claims that must be distinguished on import. -/
structure DiscriminatingImport where
  Claim : Type
  /-- A claim the receiver should accept. -/
  good : Claim
  /-- A claim the receiver should reject. -/
  bad : Claim
  good_ne_bad : good ≠ bad

/-- A function that treats all inputs uniformly produces the same output
    on good and bad claims — it cannot discriminate.

    Consequence: structured metadata (headers) is forced for export. -/
theorem uniform_import_nondiscriminating (M : DiscriminatingImport)
    (f : M.Claim → Bool)
    (h_uniform : ∀ x y : M.Claim, f x = f y) :
    f M.good = f M.bad :=
  h_uniform M.good M.bad

/-- A sound-and-complete import policy must discriminate — but uniformity
    prevents discrimination.  No metadata-free import can be both sound
    and complete. -/
theorem no_sound_complete_uniform_import (M : DiscriminatingImport)
    (f : M.Claim → Bool)
    (h_uniform : ∀ x y : M.Claim, f x = f y)
    (h_sound : f M.bad = false)
    (h_complete : f M.good = true) :
    False := by
  have h_eq := h_uniform M.good M.bad
  rw [h_sound, h_complete] at h_eq
  exact Bool.noConfusion h_eq


/-! ### 4. Adversarial Pressure → Revocation

**Argument.**  When adversarial deposits can pass acceptance, the system
must be able to remove them after discovering the problem.  In a lifecycle
where the "accepted" state is absorbing (no revocation transition), a
deposit that reaches "accepted" stays there through any number of
transitions.  The bad deposit is permanently accepted.

**Proof technique.**  Induction on the number of transition steps. -/

/-- Iterate a function `n` times starting from an initial value. -/
def iter (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iter f n x)

/-- A lifecycle where the accepted state is absorbing (no exit transition). -/
structure MonotonicLifecycle where
  State : Type
  /-- The accepted state. -/
  accepted : State
  /-- The transition function. -/
  step : State → State
  /-- `accepted` is a fixed point: stepping from accepted returns accepted. -/
  absorbing : step accepted = accepted

/-- In a monotonic lifecycle, no sequence of transitions can escape
    the accepted state.  An adversarial deposit that passes acceptance
    stays accepted permanently.

    Consequence: a revocation mechanism is structurally forced. -/
theorem monotonic_no_exit (M : MonotonicLifecycle) (n : Nat) :
    iter M.step n M.accepted = M.accepted := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show M.step (iter M.step n M.accepted) = M.accepted
    rw [ih, M.absorbing]


/-! ### 5. Coordination Need → Shared Ledger (Bank)

**Argument.**  When multiple agents must rely on the same deposits,
those deposits must be stored somewhere both agents can access.  In a
private-only storage model (each agent's store is invisible to others),
no deposit is simultaneously accessible to two agents.

**Proof technique.**  Contradiction with the isolation axiom. -/

/-- A system where each agent has private, isolated storage. -/
structure PrivateOnlyStorage where
  Agent : Type
  Deposit : Type
  /-- Each agent's private store. -/
  has_access : Agent → Deposit → Prop
  /-- Two distinct agents. -/
  a₁ : Agent
  a₂ : Agent
  distinct : a₁ ≠ a₂
  /-- Isolation: a deposit accessible to one agent is NOT accessible to the other. -/
  isolation : ∀ d, has_access a₁ d → ¬has_access a₂ d

/-- In private-only storage, no deposit is accessible to both agents.
    Collective reliance on shared deposits is impossible.

    Consequence: shared storage (bank/ledger) is structurally forced. -/
theorem private_storage_no_sharing (M : PrivateOnlyStorage) :
    ¬∃ d, M.has_access M.a₁ d ∧ M.has_access M.a₂ d := by
  intro ⟨d, h₁, h₂⟩
  exact M.isolation d h₁ h₂


/-! ### 6. Truth Pressure → Redeemability

**Argument.**  In a closed endorsement system (no external constraint
surface), the only notion of "truth" is internal consensus.  Every claim
that passes consensus is true by definition — there is nothing external
it could fail against.  But truth pressure requires that some endorsed
claims CAN fail.  A closed system cannot satisfy truth pressure.

**Proof technique.**  Contradiction: the closure axiom says endorsed
claims are unfalsifiable, but truth pressure supplies one that is
endorsed AND falsifiable. -/

/-- A closed endorsement system: no external falsification mechanism. -/
structure ClosedEndorsement where
  Claim : Type
  /-- Internal endorsement (consensus). -/
  endorsed : Claim → Prop
  /-- External falsifiability (constraint-surface contact). -/
  externally_falsifiable : Claim → Prop
  /-- Closure: without external contact, no endorsed claim is falsifiable. -/
  closed : ∀ c, endorsed c → ¬externally_falsifiable c

/-- A closed system cannot exhibit truth pressure: no endorsed claim
    is simultaneously falsifiable.

    Consequence: external constraint-surface contact (redeemability)
    is structurally forced. -/
theorem closed_system_unfalsifiable (M : ClosedEndorsement) :
    ¬∃ c, M.endorsed c ∧ M.externally_falsifiable c := by
  intro ⟨c, h_end, h_fals⟩
  exact M.closed c h_end h_fals


/-! ## StructurallyForced: Forward-Direction Forcing Without WellFormed

`StructurallyForced` captures the same forward implications as `WellFormed`
but without the backward direction and without assuming biconditionals.

Where `WellFormed` assumes `handles_X ↔ HasY`, `StructurallyForced`
packages only the `handles_X → HasY` direction.  The structural models
above justify constructing these implications; the backward direction
(needed only for behavioral equivalence, not forcing) remains in
`WellFormed` for uses that require it.

Relationship to WellFormed:
- `WellFormed W → StructurallyForced W` (forward extraction, see below)
- `StructurallyForced` suffices for convergence and impossibility theorems
- `WellFormed` additionally enables `bank_primitives_determine_behavior`  -/

/-- A system is structurally forced if each operational capability implies
    the corresponding architectural feature.  Each field is independently
    justified by a structural forcing model. -/
structure StructurallyForced (W : WorkingSystem) : Prop where
  /-- Handling distributed agents requires scope separation.
      Justified by: `flat_scope_impossible` -/
  scope_forcing : handles_distributed_agents W → HasBubbles W
  /-- Handling bounded audit requires trust bridges.
      Justified by: `verification_only_import_incomplete` -/
  trust_forcing : handles_bounded_audit W → HasTrustBridges W
  /-- Handling export requires headers/metadata.
      Justified by: `uniform_import_nondiscriminating` and
      `no_sound_complete_uniform_import` -/
  header_forcing : handles_export W → HasHeaders W
  /-- Handling adversarial pressure requires revocation.
      Justified by: `monotonic_no_exit` -/
  revocation_forcing : handles_adversarial W → HasRevocation W
  /-- Handling coordination requires shared ledger.
      Justified by: `private_storage_no_sharing` -/
  bank_forcing : handles_coordination W → HasBank W
  /-- Handling truth pressure requires redeemability.
      Justified by: `closed_system_unfalsifiable` -/
  redeemability_forcing : handles_truth_pressure W → HasRedeemability W

/-- `WellFormed` implies `StructurallyForced` (forward direction extraction). -/
theorem wellformed_implies_structurally_forced (W : WorkingSystem) :
    WellFormed W → StructurallyForced W := by
  intro ⟨h1, h2, h3, h4, h5, h6⟩
  exact {
    scope_forcing := h1.mp
    trust_forcing := h2.mp
    header_forcing := h3.mp
    revocation_forcing := h4.mp
    bank_forcing := h5.mp
    redeemability_forcing := h6.mp
  }


/-! ## Forcing Embeddings: Translation Layer

The structural models above prove clean no-go lemmas on abstract scenarios.
`StructurallyForced` packages the forward implications (capability → feature).
The remaining gap: the `StructurallyForced` fields are narratively "justified by"
the structural models but not mechanically derived from them.

`ForcingEmbedding` closes this gap.  Each field says:

> "A system handling capability X either already has feature Y, or it
>  embeds the abstract scenario whose impossibility is already proven."

The derivation `embedding_to_structurally_forced` is then a generic,
mechanical combination: for each direction, take the `Or`, and in the
right branch apply the structural impossibility theorem to produce `False`.
The left branch is the feature itself.

The proof chain becomes:

    ForcingEmbedding ──┐
                       ├── StructurallyForced ──► convergence_structural
    Structural models ─┘

The design judgment ("a system without X facing constraint Y is in the
impossible scenario") now lives in the `ForcingEmbedding` instance,
localised and auditable.  The derivation is uniform and constructive
(no Classical reasoning — `Or.elim` is intuitionistic). -/

/-- Forcing embeddings: connects a `WorkingSystem` to the abstract
    structural models via an auditable disjunction.

    Each field says: a system handling the constraint EITHER already
    has the feature, OR instantiates the scenario proven impossible
    by the corresponding structural model.  Since the right disjunct
    is impossible, the feature holds. -/
structure ForcingEmbedding (W : WorkingSystem) : Prop where
  /-- Distributed agents: either bubbles exist, or disagreeing agents
      share a single flat scope — contradicted by `flat_scope_impossible`. -/
  scope_embed : handles_distributed_agents W →
    HasBubbles W ∨
    (∃ D : AgentDisagreement, ∃ f : D.Claim → Prop,
      (∀ c, f c ↔ D.accept₁ c) ∧ (∀ c, f c ↔ D.accept₂ c))
  /-- Bounded audit: either trust bridges exist, or ALL claims are
      within the verification budget — contradicted by
      `verification_only_import_incomplete`. -/
  trust_embed : handles_bounded_audit W →
    HasTrustBridges W ∨
    (∃ M : BoundedVerification, ∀ c, M.verify_cost c ≤ M.budget)
  /-- Export: either headers exist, or a uniform import function is both
      sound and complete — contradicted by
      `no_sound_complete_uniform_import`. -/
  header_embed : handles_export W →
    HasHeaders W ∨
    (∃ M : DiscriminatingImport, ∃ f : M.Claim → Bool,
      (∀ x y, f x = f y) ∧ f M.bad = false ∧ f M.good = true)
  /-- Adversarial: either revocation exists, or the accepted state can
      be escaped despite being absorbing — contradicted by
      `monotonic_no_exit`. -/
  revocation_embed : handles_adversarial W →
    HasRevocation W ∨
    (∃ M : MonotonicLifecycle, ∃ n, iter M.step n M.accepted ≠ M.accepted)
  /-- Coordination: either shared ledger exists, or isolated agents share
      a deposit — contradicted by `private_storage_no_sharing`. -/
  bank_embed : handles_coordination W →
    HasBank W ∨
    (∃ M : PrivateOnlyStorage, ∃ d, M.has_access M.a₁ d ∧ M.has_access M.a₂ d)
  /-- Truth pressure: either redeemability exists, or a closed system
      has an endorsed-and-falsifiable claim — contradicted by
      `closed_system_unfalsifiable`. -/
  redeemability_embed : handles_truth_pressure W →
    HasRedeemability W ∨
    (∃ M : ClosedEndorsement, ∃ c, M.endorsed c ∧ M.externally_falsifiable c)

/-- Mechanical derivation: `ForcingEmbedding` → `StructurallyForced`.

    Each field is derived by `Or.elim`: the left branch is the feature
    itself (`id`); the right branch feeds the scenario into the structural
    impossibility theorem, producing `False`, which closes any goal.
    Fully constructive — no `Classical.byContradiction`. -/
theorem embedding_to_structurally_forced (W : WorkingSystem) (E : ForcingEmbedding W) :
    StructurallyForced W where
  scope_forcing h :=
    (E.scope_embed h).elim id fun ⟨D, f, hf⟩ =>
      absurd ⟨f, hf⟩ (flat_scope_impossible D)
  trust_forcing h :=
    (E.trust_embed h).elim id fun ⟨M, hM⟩ =>
      absurd hM (verification_only_import_incomplete M)
  header_forcing h :=
    (E.header_embed h).elim id fun ⟨M, f, hu, hs, hc⟩ =>
      (no_sound_complete_uniform_import M f hu hs hc).elim
  revocation_forcing h :=
    (E.revocation_embed h).elim id fun ⟨M, n, hn⟩ =>
      absurd (monotonic_no_exit M n) hn
  bank_forcing h :=
    (E.bank_embed h).elim id fun ⟨M, d, hd⟩ =>
      absurd ⟨d, hd⟩ (private_storage_no_sharing M)
  redeemability_forcing h :=
    (E.redeemability_embed h).elim id fun ⟨M, c, hc⟩ =>
      absurd ⟨c, hc⟩ (closed_system_unfalsifiable M)


/-! ## Scenario Predicates: Enriching WorkingSystems with Structural Content

The structural models prove impossibility on abstract scenarios.
The `ForcingEmbedding` connects these to working systems via disjunctions.
For a system that already has all features (like `ConcreteWorkingSystem`),
`Or.inl` suffices — but the abstract models never fire.

Scenario predicates supply the missing piece: they enrich a `WorkingSystem`
with the concrete data needed to construct the abstract witnesses.  When a
system has a scenario predicate AND lacks the corresponding feature, a
right-branch embedding theorem proves the system instantiates the impossible
scenario — and the structural model fires for real.

This is how the abstract lemmas stop being decorative and become load-bearing. -/


/-! ### Scenario 1: Distributed Disagreement -/

/-- A system represents distributed disagreement if it carries two
    acceptance predicates over some claim type that genuinely disagree:
    agent 1 accepts a witness claim that agent 2 rejects.

    When such a system lacks bubbles, it is in the `AgentDisagreement`
    scenario: a single flat scope must represent both acceptance profiles
    simultaneously — which `flat_scope_impossible` proves impossible.

    This is not a hypothetical: any system that claims to "handle
    distributed agents" must accommodate disagreeing acceptance criteria
    (otherwise there's no distributed agency to handle). -/
structure RepresentsDisagreement (W : WorkingSystem) where
  /-- The claim type the agents reason over. -/
  Claim : Type
  /-- Agent 1's acceptance criterion. -/
  accept₁ : Claim → Prop
  /-- Agent 2's acceptance criterion. -/
  accept₂ : Claim → Prop
  /-- Witness claim where they disagree. -/
  witness : Claim
  /-- Agent 1 accepts the witness. -/
  agent1_accepts : accept₁ witness
  /-- Agent 2 rejects the witness. -/
  agent2_rejects : ¬accept₂ witness

/-- Extract the `AgentDisagreement` abstract model from a system that
    `RepresentsDisagreement`. -/
def RepresentsDisagreement.toDisagreement {W : WorkingSystem}
    (R : RepresentsDisagreement W) : AgentDisagreement where
  Claim := R.Claim
  accept₁ := R.accept₁
  accept₂ := R.accept₂
  witness := R.witness
  agent1_accepts := R.agent1_accepts
  agent2_rejects := R.agent2_rejects

/-- **Right-branch embedding (scope direction).**

    A system that represents distributed disagreement and lacks bubbles
    yields the `AgentDisagreement` scenario.  In a flat (single-scope) system
    the acceptance function must agree with both agents — but
    `flat_scope_impossible` proves this is contradictory.

    The hypothesis `flat_accept` is the embedding axiom: without scope
    separation, the system commits to a single acceptance predicate that
    purports to faithfully represent both agents.  The right branch of
    `ForcingEmbedding.scope_embed` is then constructible, and
    `embedding_to_structurally_forced` closes it via `flat_scope_impossible`.

    This theorem demonstrates the abstract model doing real work: the
    structural lemma is not decorative. -/
theorem disagreement_without_bubbles_embeds
    (W : WorkingSystem)
    (R : RepresentsDisagreement W)
    (_h_no_bubbles : ¬HasBubbles W)
    (flat_accept : R.Claim → Prop)
    (hf₁ : ∀ c, flat_accept c ↔ R.accept₁ c)
    (hf₂ : ∀ c, flat_accept c ↔ R.accept₂ c) :
    False :=
  let D := R.toDisagreement
  flat_scope_impossible D ⟨flat_accept, hf₁, hf₂⟩

/-- `ForcingEmbedding` for a system with distributed disagreement:
    the scope direction uses the right branch (structural model fires)
    when ¬HasBubbles; other directions use the feature directly.

    This is how you build a `ForcingEmbedding` instance for a deficient
    system — the scope field routes through `Or.inr`, and the structural
    impossibility carries the proof. -/
theorem disagreement_scope_embed
    (W : WorkingSystem) (R : RepresentsDisagreement W)
    (flat_accept : ¬HasBubbles W → R.Claim → Prop)
    (hflat₁ : ∀ h, ∀ c, flat_accept h c ↔ R.accept₁ c)
    (hflat₂ : ∀ h, ∀ c, flat_accept h c ↔ R.accept₂ c) :
    handles_distributed_agents W →
    HasBubbles W ∨
    (∃ D : AgentDisagreement, ∃ f : D.Claim → Prop,
      (∀ c, f c ↔ D.accept₁ c) ∧ (∀ c, f c ↔ D.accept₂ c)) := by
  intro _
  by_cases h : HasBubbles W
  · exact Or.inl h
  · exact Or.inr ⟨R.toDisagreement, flat_accept h, hflat₁ h, hflat₂ h⟩


/-! ### Scenario 2: Private-Only Coordination -/

/-- A system represents private-only coordination if it carries
    evidence that its storage layer, absent a shared ledger, isolates
    agents: deposits accessible to one agent are not accessible to the other.

    When such a system lacks a shared ledger (bank), it is in the
    `PrivateOnlyStorage` scenario: agents must share a deposit for
    coordination, but isolation prevents this — which
    `private_storage_no_sharing` proves impossible. -/
structure RepresentsPrivateCoordination (W : WorkingSystem) where
  /-- Agent type. -/
  Agent : Type
  /-- Deposit type. -/
  Deposit : Type
  /-- Access relation. -/
  has_access : Agent → Deposit → Prop
  /-- Two distinct agents needing coordination. -/
  a₁ : Agent
  a₂ : Agent
  distinct : a₁ ≠ a₂
  /-- Without a shared ledger, storage is isolated. -/
  isolation_without_bank : ¬HasBank W → ∀ d, has_access a₁ d → ¬has_access a₂ d

/-- Extract `PrivateOnlyStorage` from a system that
    `RepresentsPrivateCoordination` and lacks a shared ledger. -/
def RepresentsPrivateCoordination.toPrivateStorage {W : WorkingSystem}
    (R : RepresentsPrivateCoordination W) (h_no_bank : ¬HasBank W) :
    PrivateOnlyStorage where
  Agent := R.Agent
  Deposit := R.Deposit
  has_access := R.has_access
  a₁ := R.a₁
  a₂ := R.a₂
  distinct := R.distinct
  isolation := R.isolation_without_bank h_no_bank

/-- **Right-branch embedding (coordination direction).**

    A system that represents private-only coordination and lacks a bank
    yields the `PrivateOnlyStorage` scenario.  The system claims agents
    coordinate by sharing deposits, but storage is isolated —
    `private_storage_no_sharing` proves this is contradictory. -/
theorem private_coordination_without_bank_embeds
    (W : WorkingSystem)
    (R : RepresentsPrivateCoordination W)
    (h_no_bank : ¬HasBank W)
    (d : R.Deposit)
    (h₁ : R.has_access R.a₁ d) (h₂ : R.has_access R.a₂ d) :
    False :=
  let P := R.toPrivateStorage h_no_bank
  private_storage_no_sharing P ⟨d, h₁, h₂⟩

/-- `ForcingEmbedding` bank field for a system with private-only
    coordination: uses the right branch when ¬HasBank.

    The `shared_deposit` field provides the witness: agents claim to
    coordinate on this deposit, but the isolation axiom makes the
    scenario impossible. -/
theorem private_coordination_bank_embed
    (W : WorkingSystem) (R : RepresentsPrivateCoordination W)
    (shared_deposit : ¬HasBank W → R.Deposit)
    (h_access₁ : ∀ h, R.has_access R.a₁ (shared_deposit h))
    (h_access₂ : ∀ h, R.has_access R.a₂ (shared_deposit h)) :
    handles_coordination W →
    HasBank W ∨
    (∃ M : PrivateOnlyStorage, ∃ d, M.has_access M.a₁ d ∧ M.has_access M.a₂ d) := by
  intro _
  by_cases h : HasBank W
  · exact Or.inl h
  · exact Or.inr ⟨R.toPrivateStorage h, shared_deposit h,
      h_access₁ h, h_access₂ h⟩


/-! ## Convergence and Impossibility (Structural Versions) -/

/-- Convergence theorem (structural version): under structural forcing,
    any system satisfying all properties contains Bank primitives.

    This is the preferred convergence statement.  Unlike
    `convergence_under_constraints'`, it does **not** depend on
    assumed biconditionals — only on the forward-direction implications
    justified by the structural models. -/
theorem convergence_structural (W : WorkingSystem) (h_sf : StructurallyForced W) :
    SatisfiesAllProperties W → containsBankPrimitives W := by
  intro ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h_sf.scope_forcing h1, h_sf.trust_forcing h2, h_sf.header_forcing h3,
         h_sf.revocation_forcing h4, h_sf.bank_forcing h5, h_sf.redeemability_forcing h6⟩

/-- Structural impossibility: missing any feature blocks all-property satisfaction. -/
theorem structural_impossibility (W : WorkingSystem) (h_sf : StructurallyForced W) :
    (¬HasBubbles W ∨ ¬HasTrustBridges W ∨ ¬HasHeaders W ∨
     ¬HasRevocation W ∨ ¬HasBank W ∨ ¬HasRedeemability W) →
    ¬SatisfiesAllProperties W := by
  intro h_missing h_sat
  have h_bp := convergence_structural W h_sf h_sat
  unfold containsBankPrimitives at h_bp
  cases h_missing with
  | inl h => exact h h_bp.1
  | inr h => cases h with
    | inl h => exact h h_bp.2.1
    | inr h => cases h with
      | inl h => exact h h_bp.2.2.1
      | inr h => cases h with
        | inl h => exact h h_bp.2.2.2.1
        | inr h => cases h with
          | inl h => exact h h_bp.2.2.2.2.1
          | inr h => exact h h_bp.2.2.2.2.2

end EpArch

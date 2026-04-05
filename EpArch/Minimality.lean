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

end EpArch

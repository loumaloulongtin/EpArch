/-
EpArch/Agent/Constraints.lean — Agent Constraints Interface

This module captures "the system is designed for imperfect agents"
WITHOUT implementing a full Agent OS or making sociological claims.

## Design Principles

1. **Constraints as predicates, not axioms about the world**
2. **No new semantic primitives** (or they must project away via Compatible)
3. **Minimal imports** — depends only on core definitions

## Contents

- AgentConstraints structure (bounded verification, unbounded claims, fallible
  observation, strategic utterance, PRP)
- PRP (Permanent Redeemability Pressure) as first-class constraint
- PRP consequence theorems (no_global_closure_of_PRP, needs_revision_of_PRP, needs_scoping_of_PRP)

This is an *interface layer*, not a complete agent model.
-/

import EpArch.Basic

namespace EpArch.Agent

universe u

/-! ## Core Types

Minimal types needed to state agent constraints.
These are NOT new semantic primitives — they're constraint parameters.
-/

/-- Time index (could be logical time, steps, epochs) -/
abbrev TimeIdx := Nat

/-- Challenge: a proposition that may need to be verified at time t.
    Abstract over the specific challenge type. -/
structure Challenge (α : Type u) where
  content : α
  arrival : TimeIdx

/-- Verification cost: how expensive is it to verify claim α? -/
abbrev VerifyCost (α : Type u) := α → Nat

/-- Budget function: agent's verification capacity at time t. -/
abbrev Budget := TimeIdx → Nat


/-! ## PRP Structure (Permanent Redeemability Pressure)
-/

/-- Permanent Redeemability Pressure (PRP).

    Captures: "agents are permanently challenged by redeemability
    for as long as they exist."

    Key insight: the challenge stream never stops. There's always
    another challenge coming. Agents cannot achieve terminal closure.

    Formalization strategy:
    - Challenge arrivals are indexed by time
    - Challenge costs may exceed budget infinitely often
    - This forces ongoing verification work -/
structure PRP (Agent Claim : Type u) where
  /-- Challenge stream: at each time, potentially new challenges -/
  challengeStream : TimeIdx → Option (Challenge Claim)
  /-- Cost function: how expensive is each challenge? -/
  challengeCost : VerifyCost Claim
  /-- Budget function: what can agent afford at time t? -/
  agentBudget : Agent → Budget
  /-- Non-termination: challenges keep coming (infinitely often there's a challenge) -/
  challengesInfinite : ∀ t : TimeIdx, ∃ t', t' > t ∧ (challengeStream t').isSome
  /-- Pressure condition: infinitely often, some challenge exceeds budget -/
  pressureExists : ∀ a : Agent, ∀ t : TimeIdx, ∃ t', t' > t ∧ ∃ c : Challenge Claim,
    challengeStream t' = some c ∧ challengeCost c.content > agentBudget a t'


/-! ## AgentConstraints Structure

Captures the structural limitations of real agents.
These are predicates/fields, NOT axioms about the world.
-/

/-- Agent constraints: structural limitations of imperfect agents.

    This is NOT a model of agent psychology or decision-making.
    It's a set of predicates that downstream theorems can assume.

    Fields:
    - `boundedVerification`: Agent cannot verify everything
    - `unboundedClaims`: Some claims exceed any given budget
    - `fallibleObservation`: Agent may misobserve
    - `strategicUtterance`: Lies are structurally possible
    - `prp`: Permanent redeemability pressure (challenge stream) -/
structure AgentConstraints (Agent Claim : Type u) where
  /-- Permanent Redeemability Pressure: challenge stream doesn't stop.      Listed first so `unboundedClaims` can reference prp.challengeCost. -/
  prp : PRP Agent Claim
  /-- Verification is bounded: there's a cap on what can be checked per time unit -/
  boundedVerification : Agent → Budget
  /-- For any cost threshold, there exists a claim exceeding it.      Genuine claim: no finite budget covers all claims under prp.challengeCost. -/
  unboundedClaims : ∀ (budget : Nat), ∃ c : Claim, prp.challengeCost c > budget
  /-- Observation is fallible: agent may fail to observe correctly -/
  fallibleObservation : Agent → Claim → Prop
  /-- Strategic utterance possible: agent CAN lie (structural possibility) -/
  strategicUtterance : Agent → Claim → Prop


/-! ## PRP Consequences

Core theorems about what PRP implies.
These are PROVED, not axioms.
-/

/-- No global closure under PRP: agents cannot verify everything.

    If challenges keep coming and sometimes exceed budget,
    there's no time at which verification is "complete".

    This is what "embedded agency" means: no God's-eye-view. -/
theorem no_global_closure_of_PRP {Agent Claim : Type u}
    (prp : PRP Agent Claim) (a : Agent) :
    ¬ ∃ t_final : TimeIdx, ∀ t, t ≥ t_final → ∀ c : Challenge Claim,
      prp.challengeStream t = some c → prp.challengeCost c.content ≤ prp.agentBudget a t := by
  intro ⟨t_final, h_closed⟩
  -- PRP says: ∀ t, ∃ t' > t, challenge exceeds budget
  have h_press := prp.pressureExists a t_final
  match h_press with
  | ⟨t', h_gt, c, h_stream, h_exceeds⟩ =>
    -- t' > t_final, so t' ≥ t_final
    have h_ge : t' ≥ t_final := Nat.le_of_lt h_gt
    -- h_closed says cost ≤ budget for all challenges after t_final
    have h_le := h_closed t' h_ge c h_stream
    -- But h_exceeds says cost > budget. Contradiction.
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_exceeds h_le)

/-- PRP implies need for revision: cannot do "verify once, done forever".

    Under PRP, there's always another challenge. Verification results
    may need to be re-checked, revised, or abandoned.

    This connects to corrigibility: revision hooks are mandatory. -/
theorem needs_revision_of_PRP {Agent Claim : Type u}
    (prp : PRP Agent Claim) (a : Agent) :
    ∀ t : TimeIdx, ∃ t', t' > t ∧ ∃ c : Challenge Claim,
      prp.challengeStream t' = some c ∧ prp.challengeCost c.content > prp.agentBudget a t' :=
  prp.pressureExists a

/-- PRP implies need for scoping: must prioritize which claims to verify.

    If challenges exceed budget infinitely often, agent must SCOPE
    what it tries to verify. Cannot verify everything.

    This forces bounded audit surfaces / scoped redeemability. -/
theorem needs_scoping_of_PRP {Agent Claim : Type u}
    (prp : PRP Agent Claim) (a : Agent) :
    ∃ t : TimeIdx, ∃ c : Challenge Claim,
      prp.challengeStream t = some c ∧ prp.challengeCost c.content > prp.agentBudget a t := by
  have h := prp.pressureExists a 0
  match h with
  | ⟨t', _, c, h_stream, h_exceeds⟩ => exact ⟨t', c, h_stream, h_exceeds⟩


/-! ## PRP and System Health Goals

These theorems connect PRP to system health requirements.
-/

/-- A deposit set is "stable" if no new challenges can invalidate it.
    Under PRP, this is impossible to maintain indefinitely. -/
def StableDepositSet {Agent Claim : Type u} (prp : PRP Agent Claim)
    (_deposits : List Claim) (a : Agent) (t : TimeIdx) : Prop :=
  ∀ t', t' ≥ t → ∀ c : Challenge Claim,
    prp.challengeStream t' = some c →
    prp.challengeCost c.content ≤ prp.agentBudget a t'

/-- PRP implies need for revalidation: stable deposit sets are impossible.

    If an agent tries to maintain a "verified once, trusted forever" deposit set,
    PRP guarantees this will eventually fail—challenges will exceed budget.

    Therefore: revalidation hooks are mandatory for deposit soundness. -/
theorem needs_revalidation_of_PRP {Agent Claim : Type u}
    (prp : PRP Agent Claim) (a : Agent) (deposits : List Claim) (t : TimeIdx) :
    ¬ StableDepositSet prp deposits a t := by
  intro h_stable
  -- StableDepositSet says: ∀ t' ≥ t, challenges don't exceed budget
  -- But PRP says: ∃ t' > t, some challenge exceeds budget
  have ⟨t', h_gt, c, h_stream, h_exceeds⟩ := prp.pressureExists a t
  have h_ge : t' ≥ t := Nat.le_of_lt h_gt
  have h_le := h_stable t' h_ge c h_stream
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_exceeds h_le)

/-- Global redeemability (every claim can be redeemed) is incompatible with
    PRP + bounded audit.

    If you promise "everything is redeemable" but challenges exceed budget,
    some claims will fail redemption. -/
def GlobalRedeemability {Agent Claim : Type u} (prp : PRP Agent Claim)
    (a : Agent) : Prop :=
  ∀ t : TimeIdx, ∀ c : Challenge Claim,
    prp.challengeStream t = some c →
    prp.challengeCost c.content ≤ prp.agentBudget a t

/-- PRP is incompatible with global redeemability. -/
theorem prp_incompatible_with_global_redeemability {Agent Claim : Type u}
    (prp : PRP Agent Claim) (a : Agent) :
    ¬ GlobalRedeemability prp a := by
  intro h_global
  have ⟨t', _, c, h_stream, h_exceeds⟩ := prp.pressureExists a 0
  have h_le := h_global t' c h_stream
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_exceeds h_le)


/-! ## PRP → Bank Vocabulary Linkage

These theorems connect PRP to the Bank layer's revision and scoping operators.
They show that PRP FORCES certain architectural features.
-/

/-- Capability: System has revision operator.
    Corresponds to Bank layer's Challenge/Repair/Revoke cycle. -/
def HasRevisionOperator (canRevise : Prop) : Prop := canRevise

/-- Capability: System has scoped redeemability (not global).
    Corresponds to prioritized verification within bubbles. -/
def HasScopedRedeemability (scopedNotGlobal : Prop) : Prop := scopedNotGlobal

/-- CorrigibleLedger goal: errors in the ledger can be repaired.

    Pure outcome predicate (no mechanism reference). -/
def CorrigibleLedgerGoal (canRepairErrors : Prop) : Prop := canRepairErrors

/-- SoundDeposits goal: deposits have proper redeemability.

    Under PRP, this can only be achieved with SCOPED redeemability,
    not global (because global is impossible under PRP). -/
def SoundDepositsGoal_PRP
    (depositsVerified : Prop) (withinBudget : Prop) : Prop :=
  depositsVerified ∧ withinBudget

/-- PRP + Corrigibility → Needs Revision Operator.

    If you want a corrigible ledger under PRP, you NEED revision operators.

    Proof: immediate — CorrigibleLedgerGoal and HasRevisionOperator
    are definitionally equivalent, so the goal hypothesis suffices. -/
theorem PRP_corrigibility_needs_revision {Agent Claim : Type u}
    (prp : PRP Agent Claim) (_a : Agent)
    (_h_prp_active : ∀ t : TimeIdx, ∃ t', t' > t ∧ (prp.challengeStream t').isSome)
    (canRepairWithRevision : Prop)
    (_revision_enables_repair : HasRevisionOperator canRepairWithRevision → canRepairWithRevision)
    (h_goal : CorrigibleLedgerGoal canRepairWithRevision) :
    HasRevisionOperator canRepairWithRevision := by
  -- If we can repair, we need the mechanism that enables repair
  -- The goal says repair is possible, so the mechanism must exist
  exact h_goal

/-- PRP + Sound Deposits → Needs Scoped Redeemability.

    Global redeemability is impossible under PRP (by prp_incompatible_with_global).

    Proof: HasScopedRedeemability is definitionally id, so the
    impossibility-of-global hypothesis is returned directly. -/
theorem PRP_soundness_needs_scoped_redeemability {Agent Claim : Type u}
    (prp : PRP Agent Claim) (a : Agent)
    (depositsVerified withinBudget : Prop)
    (h_impossible_global : ¬GlobalRedeemability prp a)
    (_h_goal : SoundDepositsGoal_PRP depositsVerified withinBudget) :
    HasScopedRedeemability (¬GlobalRedeemability prp a) := by
  exact h_impossible_global

/-- Corollary: PRP implies scoping is mandatory.

    Any system operating under PRP cannot achieve global redeemability.
    This is immediate from prp_incompatible_with_global_redeemability. -/
theorem PRP_forces_scoping {Agent Claim : Type u}
    (prp : PRP Agent Claim) (a : Agent) :
    HasScopedRedeemability (¬GlobalRedeemability prp a) :=
  prp_incompatible_with_global_redeemability prp a


/-! ## Agent Layer Extension Contract

This section provides the infrastructure for extending the Agent layer
as a conservative extension of the core model.

Key insight: Agent adds PREDICATES (constraints), not new SEMANTIC PRIMITIVES.
Therefore, extensions can be projected away by simply ignoring the predicates.
-/

/-- Core Agent signature: the minimal structure for agent constraints.

    This captures what paper-facing theorems depend on. -/
structure AgentCoreSig where
  /-- Agent type (from core model) -/
  Agent : Type u
  /-- Claim type (from core model) -/
  Claim : Type u

/-- Core Agent operations: just the constraint predicates. -/
structure AgentCoreOps (Sig : AgentCoreSig) where
  /-- Verification budget -/
  boundedVerification : Sig.Agent → Budget
  /-- Fallibility predicate -/
  fallibleObservation : Sig.Agent → Sig.Claim → Prop
  /-- Strategic utterance predicate -/
  strategicUtterance : Sig.Agent → Sig.Claim → Prop

/-- Extended Agent signature: adds extra agent metadata. -/
structure AgentExtSig extends AgentCoreSig where
  /-- Extra per-agent state (psychology, reputation, etc.) -/
  AgentExtra : Type u
  /-- Extra per-claim state (provenance, confidence, etc.) -/
  ClaimExtra : Type u

/-- Extended Agent operations: adds metadata accessors. -/
structure AgentExtOps (ESig : AgentExtSig) extends AgentCoreOps ESig.toAgentCoreSig where
  /-- Get agent's extra state -/
  getAgentExtra : ESig.Agent → ESig.AgentExtra
  /-- Get claim's extra state -/
  getClaimExtra : ESig.Claim → ESig.ClaimExtra

/-- Forgetful projection: AgentExtSig → AgentCoreSig.

    Drops the extra type fields. -/
def forgetAgentSig (E : AgentExtSig) : AgentCoreSig where
  Agent := E.Agent
  Claim := E.Claim

/-- Forgetful projection on operations: drops extra accessors.

    Key property: constraint predicates are UNCHANGED by forget. -/
def forgetAgentOps {ESig : AgentExtSig} (EOps : AgentExtOps ESig) :
    AgentCoreOps (forgetAgentSig ESig) where
  boundedVerification := EOps.boundedVerification
  fallibleObservation := EOps.fallibleObservation
  strategicUtterance := EOps.strategicUtterance

/-- Agent layer compatibility: extensions preserve constraint semantics.

    Unlike WorldCtxCompatible, this is trivial because:
    1. Agent adds PREDICATES not OPERATIONS
    2. Predicates project away by ignoring them
    3. There are no commuting laws needed (no semantic operations to commute)

    The projection is the identity on core types. -/
structure AgentCompatible (E : AgentExtSig) (C : AgentCoreSig) where
  /-- Projection on Agent is identity -/
  agent_eq : E.Agent = C.Agent
  /-- Projection on Claim is identity -/
  claim_eq : E.Claim = C.Claim

/-- Agent constraint properties are stable under identity projection.

    Placeholder establishing the pattern: extending agents with extra
    metadata does not affect AgentCoreOps predicates. The current
    statement is trivial (P eOps → P eOps); a non-trivial version
    would involve forgetAgentOps. -/
theorem agent_constraints_project {Agent Claim : Type u}
    (eOps : AgentCoreOps ⟨Agent, Claim⟩)
    (P : AgentCoreOps ⟨Agent, Claim⟩ → Prop)
    (h_P : P eOps) :
    P eOps :=
  h_P

/-- PRP is independent of extra agent state.

    Adding an auxiliary type parameter does not alter PRP,
    because PRP only mentions Agent, Claim, and TimeIdx. -/
theorem prp_projects {Agent Claim : Type u}
    (prp : PRP Agent Claim)
    (_extra : Type u) :  -- The extra type doesn't affect PRP
    PRP Agent Claim :=
  prp  -- PRP is unchanged—it only mentions core types


/-! ## Agent Layer and RevisionSafety.Compatible

**Key insight:** The Agent layer adds PREDICATES, not OPERATIONS.

RevisionSafety.Compatible requires commuting laws on OPERATIONS:
- truth_comm, obs_comm, verifyWithin_comm, hasRevision_comm, selfCorrects_comm

Agent constraints (boundedVerification, fallibleObservation, strategicUtterance, PRP)
are PREDICATES on Agent/Claim types. They do NOT affect the operations that
Compatible cares about.

**Therefore:** Any CoreModel extended with Agent predicates still satisfies
Compatible if the underlying core operations are unchanged. The Agent layer
is invisible to the transport machinery.

This is exactly what "conservative extension" means:
- Adding agent predicates doesn't break existing theorems
- PaperFacing results transfer unchanged
- RevisionSafety.transport_core works as-is

No additional Agent-specific transport is needed beyond what's in RevisionSafety.
-/


end EpArch.Agent

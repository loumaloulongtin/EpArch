/-
EpArch.Basic — Basic Types (Core Ontology)

This file defines the foundational types for the Epistemic Architecture
formalization. Everything else in the project builds on these types.

## Domain Context

The EpArch model treats knowledge management as a banking system:

- **Agents** hold private beliefs (their "Ladder" state) and interact with
  a public ledger.
- **Claims** are propositions that agents want validated.
- **Deposits** package a Claim with validation metadata (a Header with
  Standard, ErrorModel, Provenance, temporal validity, access control, and
  redeemability). A Deposit is like a bank deposit: you submit a claim, it
  goes through validation, and if accepted, others can rely on ("withdraw") it.
- **Bubbles** are scoped validation domains — each with its own acceptance
  standards. Think of a scientific field, a legal jurisdiction, or a newsroom.
  Each bubble has its own Accept function and its own ledger of deposits.
- **Banks** (defined in the Bank module) are shared ledgers of deposits within a bubble.

The "Ladder vs Bank" distinction is central:
- **Ladder** (agent-side): An agent's internal traction state for a claim.
  Ignorance is the entry condition (no stance yet); Doubt, Belief, Certainty,
  and Denial are engaged stances reachable from Ignorance in any order —
  no traversal of intermediate steps is assumed or required.  This is private.
  The Ladder does not prescribe a universal update path; agent-specific overlays
  (human cognition, LLM confidence, institutional policy) fill in the dynamics.
- **Bank** (system-side): The shared ledger of validated deposits.
  This is public, challengeable, and redeemable.
The key claim: being CERTAIN (Ladder) is not the same as KNOWING
(having a valid Bank deposit). Certainty is private traction;
knowledge is public authorization.

## Type Design

All base types are minimal Nat-indexed inductives. This gives every type
a canonical inhabitant (e.g., `Bubble.mk 0`), `DecidableEq`, and `Repr`
without existence axioms — enabling fully constructive witnesses in
the EpArch.Concrete module family.

This file has no imports — it is the root of the dependency tree.
-/

namespace EpArch

universe u

/-- Propositions/claims P, Q, ...
    These are the things being deposited, challenged, withdrawn.
    Concrete: Nat-indexed for canonical inhabitants. -/
inductive Claim where
  | mk : Nat → Claim
  deriving DecidableEq, Repr, Inhabited

/-- Agents (individuals who hold traction states and perform withdrawals)
    Concrete: Nat-indexed for canonical inhabitants. -/
inductive Agent where
  | mk : Nat → Agent
  deriving DecidableEq, Repr, Inhabited

/-- Bubbles = scoped validation/authorization domains
    Each bubble has its own governance (Accept function).
    Concrete: Nat-indexed for canonical inhabitants. -/
inductive Bubble where
  | mk : Nat → Bubble
  deriving DecidableEq, Repr, Inhabited

/-- Time / staleness axis for τ / TTL
    Deposits have shelf life; τ tracks currentness.
    Concretized as Nat to enable τ_valid proofs. -/
abbrev Time : Type := Nat

/-- Access control list (who can withdraw / rely on a deposit)
    Concrete: Nat-indexed for canonical inhabitants. -/
inductive ACL where
  | mk : Nat → ACL
  deriving DecidableEq, Repr, Inhabited

/-- Constraint surface (the "world pushback" interface).
    Examples: experimental results, logical contradictions, physical laws.
    A constraint surface is external to any agent's consensus — it
    determines whether a claim can be redeemed regardless of who agrees.
    Concrete: Nat-indexed for canonical inhabitants. -/
inductive ConstraintSurface where
  | mk : Nat → ConstraintSurface
  deriving DecidableEq, Repr, Inhabited

/-- Context for acceptance decisions (bubble state, prior deposits, etc.)
    Concrete: Nat-indexed for canonical inhabitants. -/
inductive Context where
  | mk : Nat → Context
  deriving DecidableEq, Repr, Inhabited

/-- Domain: a practice area (science, law, finance, etc.)
    Used for domain-level claims about self-correction.
    Concrete: Nat-indexed for canonical inhabitants. -/
inductive Domain where
  | mk : Nat → Domain
  deriving DecidableEq, Repr, Inhabited


/-! ## Ladder Stages

The Ladder is the agent-side of the system — it tracks what traction level
an agent holds on a claim. This is PRIVATE internal state, completely separate
from the Bank (shared ledger).

The key conceptual point: an agent at Certainty (top of Ladder) may be
wrong, and an agent at Ignorance may be right. The Ladder says nothing
about whether the claim is validated in the Bank. This separation between
"traction" (Ladder) and "authorization" (Bank) is the core of the theory. -/

/-- Ladder stages: the agent's internal traction axis.

    Tracks what the agent currently treats as settled for inference and action.
    Ignorance is the entry condition: no engaged stance yet.
    The other four stages are reachable from Ignorance in any order —
    EpArch does not prescribe a universal update sequence.

    Kernel usage:
    - Ignorance and Certainty are theorem-active: `trace_cannot_elevate_ladder`
      and `bank_trace_cannot_discharge_closure` use them directly.
    - Entrenched = Certainty + closed review channel (see `Entrenched`).
    - Doubt, Belief, and Denial are reserved vocabulary for agent-specific
      overlays.  Their internal dynamics (update rules, ordering, transitions)
      are intentionally left open; the kernel only requires that any agent has
      exactly one stage per claim at any time (totality, via `agentTraction`). -/
inductive LadderStage where
  | Denial     -- active rejection; boundary hardened against import
  | Doubt      -- claim on radar but traction actively demoted
  | Ignorance  -- no traction; claim not even considered
  | Belief     -- action-guiding traction, still actively monitoring
  | Certainty  -- full traction, active monitoring ceased; review channel still open
  deriving DecidableEq, Repr, Inhabited

/-- The agent's private traction assignment: a function from claims to Ladder stages.
    This is the hook: `agentTraction a` is a first-class object representing
    agent `a`'s current traction map over all claims.  Its implementation is
    opaque — psychology, pattern-matching, neurology, and institutional policy all
    live below this interface.  The architecture only commits to:
    - Every agent has such a function (totality).
    - It maps each claim to exactly one stage (determinism).
    - It cannot be derived from Bank state (traction/authorization separation).

    The function can be thought of as modulated by the agent's internal processes;
    the opaqueness is intentional — different agent types (human, AI, institution)
    can implement it differently without affecting any revision-gate theorem. -/
opaque agentTraction : Agent → (Claim → LadderStage)

/-- ladder_stage: the current traction level of agent `a` for claim P.
    Defined as the output of the agent's own traction assignment.
    WHAT it is: `a`'s traction function applied to P.
    HOW it works: opaque via `agentTraction` — the hook for agent-specific modulation. -/
def ladder_stage (a : Agent) (P : Claim) : LadderStage :=
  agentTraction a P

/-- Certainty: agent a is at the top Ladder stage for claim P.
    Defined as: the agent's `ladder_stage` for P equals `LadderStage.Certainty`.

    Semantics: the agent has ceased active monitoring of P — it is treated as a
    closed premise, no longer subject to deliberative attention.
    "Can't go higher": `.Certainty` is the last constructor of `LadderStage`;
    there is no stage above it.
    "Doorbell still ringable": the review channel (`ignores_bank_signal`) is a
    separate opaque predicate; Certainty alone does NOT close the channel.
    Entrenchment = Certainty + closed channel (see `Entrenched`).

    Independence from Bank authorization: see §C1 in EpArch.Commitments.
    `innovation_allows_traction_without_authorization` (certainty_L ⊄ knowledge_B)
    `caveated_authorization_does_not_force_certainty` (knowledge_B ⊄ certainty_L). -/
def certainty_L (a : Agent) (P : Claim) : Prop :=
  ladder_stage a P = .Certainty

/-- Structural property: agent's review channel for P is disconnected.
    Opaque: this is a separate predicate from `certainty_L` — an agent at Certainty
    typically remains responsive to Bank signals (the normal, healthy state).
    Closing the channel requires an additional structural failure beyond
    reaching Certainty; it is never implied by Certainty alone. -/
opaque ignores_bank_signal : Agent → Claim → Prop

/-- Healthy Certainty: the agent is at the Ladder top AND the review channel
    is still open.  The doorbell can ring.
    `open_channel_certainty` is the non-pathological form of top-Ladder traction;
    it is what the theory expects of a well-functioning agent at Certainty.
    Contrast with `Entrenched`: same Certainty, but the channel has been closed. -/
def open_channel_certainty (a : Agent) (P : Claim) : Prop :=
  certainty_L a P ∧ ¬ignores_bank_signal a P

/-- Pathological Ladder state: Certainty that refuses revision when Bank status changes.

    Entrenchment is not a legitimate Ladder stage but a defect of Certainty:
    the agent holds full traction (ladder_stage a P = .Certainty) AND has
    structurally closed the Bank signal channel, so it cannot hear quarantine
    or revocation events.
    See `entrenchment_breaks_safe_withdrawal` for the consequence theorem. -/
def Entrenched (a : Agent) (P : Claim) : Prop :=
  certainty_L a P ∧ ignores_bank_signal a P  -- Certainty + closed review channel


/-! ## Deposit Status

A deposit goes through a lifecycle in the Bank:
Candidate → Deposited → (Quarantined → Revoked or Repaired).
Repaired deposits loop back to Candidate for revalidation, not to Deposited.
These statuses control what operations are available. For example, only
Deposited claims can be withdrawn (relied upon), and only Quarantined
claims can be repaired or revoked. See EpArch.Semantics.StepSemantics for the
operational transition system that enforces these rules.

The four minimal states are the architectural boundary: implementations
may use internal multi-stage pipelines between Candidate and Deposited,
but the architecture does not prescribe or observe those intermediate stages. -/

/-- Status of a deposit in the Bank lifecycle. -/
inductive DepositStatus where
  | Candidate    -- submitted, pending bank operator promotion
  | Deposited    -- live in the bank, withdrawable
  | Quarantined  -- suspended pending challenge resolution
  | Revoked      -- permanently withdrawn from circulation
  deriving DecidableEq, Repr


/-! ## Field Identifiers

The S/E/V factorization is central to the architecture. Every deposit's
header contains independently checkable fields. When a deposit fails,
the failure can be localized to a specific field — enabling targeted repair
instead of wholesale rejection. This is the "legibility" property:
the system can diagnose what went wrong and where.

The six fields are:
- **S (Standard)**: The acceptance threshold — how stringent is the bar?
- **E (Error Model)**: The known failure modes — what could go wrong?
- **V (Provenance)**: The chain of methods, sources, and independence.
- **τ (Temporal validity)**: Is this deposit still current? (Not wall-clock time.)
- **redeemability**: Can this claim be tested against reality?
- **acl (Access Control)**: Who is authorized to rely on this deposit? -/

/-- Field-localization targets for debugging/repair.
    When a deposit fails, diagnosis identifies WHICH field is broken. -/
inductive Field where
  | S           -- standard / threshold
  | E           -- error model / threat model
  | V           -- provenance / independence
  | τ           -- currentness / TTL
  | redeemability -- constraint surface contact
  | acl         -- access control
  deriving DecidableEq, Repr


/-! ## Lifecycle Steps -/

/-- Deposit lifecycle as a labeled transition system.
    Steps from initial withdrawal attempt through pushback, diagnosis,
    challenge, quarantine, and potential repair or revocation. -/
inductive LifecycleStep where
  | Withdraw      -- agent relies on deposit
  | Pushback      -- constraint surface or challenge resists
  | Diagnose      -- identify which field failed
  | Challenge     -- formal challenge submitted
  | Quarantine    -- deposit suspended
  | RepairOrRevoke -- fix the field or remove deposit
  | Redeposit     -- repaired deposit re-enters as Candidate
  deriving DecidableEq, Repr


/-! ## Deposit Kind -/

/-- DepositKind: determines how the TTL (τ) field should be assigned.

    Different classes of deposit age at different rates:
    - Structural: math proofs, definitions — shelf life is effectively unlimited
    - WorldState: empirical facts, schedules, positions — require periodic refresh
    - Adversarial: credentials, threat intel — TTL adapts to attacker capability
    - Institutional: policies, regulations — expire on governance events, not clocks -/
inductive DepositKind where
  | Structural    -- near-infinite TTL (proofs, definitions)
  | WorldState    -- finite TTL, requires refresh
  | Adversarial   -- adaptive TTL, attacker-dependent
  | Institutional -- event-driven TTL (governance changes)
  deriving DecidableEq, Repr

/-- TTL requirement by deposit kind. -/
def ttl_required : DepositKind → Bool
  | .Structural => false
  | .WorldState => true
  | .Adversarial => true
  | .Institutional => true


end EpArch

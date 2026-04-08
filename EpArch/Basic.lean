/-
EpArch — Basic Types (Core Ontology)

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
- **Banks** (defined in Bank.lean) are shared ledgers of deposits within a bubble.

The "Ladder vs Bank" distinction is central:
- **Ladder** (agent-side): An agent's internal certainty progression
  (Denial → Doubt → Ignorance → Belief → Certainty). This is private.
- **Bank** (system-side): The shared ledger of validated deposits.
  This is public, challengeable, and redeemable.
The paper's key claim: being CERTAIN (Ladder) is not the same as KNOWING
(having a valid Bank deposit). Certainty is private traction;
knowledge is public authorization.

## Type Design

All base types are minimal Nat-indexed inductives. This gives every type
a canonical inhabitant (e.g., `Bubble.mk 0`), `DecidableEq`, and `Repr`
without existence axioms — enabling fully constructive witnesses in
`ConcreteLedgerModel`. The wrappers carry no payload beyond their index;
semantics live in the structures and theorems that use them.

## File Dependencies

This file has no imports — it is the root of the dependency tree.
Almost every other file in the project imports Basic.lean.
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
    Ordered from active rejection to full commitment:
    Denial < Doubt < Ignorance < Belief < Certainty.
    Denial and Doubt are active negative states, not mere absence of traction. -/
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
    can implement it differently without affecting any paper-facing theorem. -/
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

    Independence from Bank authorization: see §C1 in Commitments.lean.
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
Candidate → Validated → Deposited → (Quarantined → Revoked or Repaired).
Repaired deposits loop back to Candidate for revalidation, not to Deposited.
These statuses control what operations are available. For example, only
Deposited claims can be withdrawn (relied upon), and only Quarantined
claims can be repaired or revoked. See StepSemantics.lean for the
operational transition system that enforces these rules.

Note: Some descriptions list only four statuses (Candidate, Deposited,
Quarantined, Revoked). The formalization adds a `Validated` intermediate
between Candidate and Deposited, splitting the acceptance step into
Validate_B + Accept_B for finer-grained lifecycle control. -/

/-- Status of a deposit in the Bank lifecycle. -/
inductive DepositStatus where
  | Candidate    -- submitted, not yet validated
  | Validated    -- passed validation, not yet accepted as deposited
  | Deposited    -- active in the bank
  | Quarantined  -- suspended pending challenge resolution
  | Revoked      -- permanently withdrawn from circulation
  deriving DecidableEq, Repr


/-! ## Acceptance Results -/

/-- Result of the Accept_B function (bubble governance decision). -/
inductive AcceptResult where
  | Rejected     -- does not meet bubble standards
  | Candidate    -- admitted for further validation
  | Deposited    -- fully accepted
  | Provisional  -- accepted with caveats / limited TTL
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


/-! ## Operating Modes -/

/-- Two operating modes for acting under uncertainty.

    - Cash: validate before acting — the Bank deposit exists before withdrawal
    - Credit: act on Ladder traction, validate retroactively

    Cash mode is safer but slower; Credit mode enables exploration before
    validation infrastructure exists. The architecture supports both; the
    choice affects which failure modes are accessible. -/
inductive OperatingMode where
  | Cash   -- validated before action; Bank-consulted
  | Credit -- act on traction; validate later
  deriving DecidableEq, Repr


/-! ## Defense Dynamics -/

/-- Defense postures: distinct mechanisms for responding to challenge.

    - Doubt: demote traction on the claim itself (Ladder adjustment)
    - Denial: block the challenging source at the ACL level (boundary hardening)

    These target different layers — Doubt is content-level, Denial is source-level.
    The cost structures differ: Denial is cheap but coarse; Doubt is precise but
    requires re-evaluation. -/
inductive DefensePosture where
  | Doubt  -- demote traction on claim
  | Denial -- block source at ACL level
  deriving DecidableEq, Repr

/-- Doubt targets the claim; Denial targets the source. -/
def defense_target : DefensePosture → String
  | .Doubt => "claim (traction demotion)"
  | .Denial => "source (ACL hardening)"


/-! ## Triage Categories -/

/-- Problem classification for intervention strategy.

    Three categories with different remediation paths:
    - InherentTradeoff: structural tension that cannot be eliminated (e.g., certainty
      outrunning validation under time pressure) — manage the tradeoff, don't fix it
    - ProtocolCorruption: a legitimate mechanism misbinding (e.g., echo chambers
      as export without revalidation) — fixable via repair operators
    - DesignGap: absent friction that prevents contamination (e.g., no provenance
      on export) — addressable by adding tooling or protocol steps -/
inductive TriageCategory where
  | InherentTradeoff    -- manage, don't fix
  | ProtocolCorruption  -- fixable via repair
  | DesignGap           -- addressable via tooling
  deriving DecidableEq, Repr


/-! ## Verdict Rubric -/

/-- Verdicts for falsification attempts against architectural commitments.

    - Absorbed: the challenge is structurally equivalent to the commitment under
      different labels — not a genuine falsifier
    - Deflected: the challenge targets a different claim than the one made
    - Holds: the commitment survives direct pressure
    - Broken: a genuine falsifier has been constructed -/
inductive FalsificationVerdict where
  | Absorbed   -- rival has the split under different names
  | Deflected  -- challenge attacks different claim
  | Holds      -- commitment survives pressure
  | Broken     -- clean falsifier found
  deriving DecidableEq, Repr

end EpArch

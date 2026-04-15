/-
EpArch.Adversarial.Concrete — Concrete Attack Mitigation Proofs

Four-step demonstration connecting the abstract attack vocabulary
(AdversarialBase) to the concrete kernel model (Concrete.Types):

- Step 1: The CDeposit type has four independent exploit-surface dimensions
  (V, τ, S, E). No structural constraint prevents attack-susceptible values;
  the gate theorems in Step 2 are the actual defense.

- Step 2: The compute_status gates are structurally un-bypassable. Proved
  theorems show that τ-expiry and V-stripping each block c_can_withdraw,
  and that header stripping prevents c_header_preserved from holding.

- Step 3: Each attack type from AdversarialBase is named against the gate
  that blocks it. The DDoS V-channel collapse is proved as a genuine
  derivation chain through CAuditChannel (capacity arithmetic → V = [] →
  V gate fires). A concrete FullStackAttack witness satisfies attack_succeeds.

- Step 4: The export gate conditions: c_valid_export requires revalidation or a
  trust bridge. Absent both, c_import_deposit returns none. Invocation order
  ("withdrawal must precede export") cannot be enforced architecturally for two
  independent reasons: (a) bounded verification — CAuditChannel capacity is finite,
  so trust-bridge transfers are legitimate and bypass the withdrawal-first sequence;
  (b) decentralization — bubble B has no read access to bubble A's withdrawal
  ledger; the claim "this was withdrawn from A" arrives only as content of the
  CExportRequest the agent constructs, and an agent could fabricate that content
  entirely. Both constraints are foundational, not relaxable. The delegation to the
  agent layer is therefore theorem-backed, not a design shortcut.
  EpArch proves the gate conditions are un-bypassable when invoked.
-/

import EpArch.Adversarial.Base
import EpArch.Concrete.Types

namespace EpArch.Adversarial.Concrete

open EpArch EpArch.ConcreteModel

/-! ========================================================================
    STEP 1 — EXPLOIT-SURFACE FIELDS ARE NOT STRUCTURALLY PREVENTED
    ========================================================================

    The CDeposit type does not prevent attack-susceptible field values. Each
    definition below names a specific exploit surface. The gate theorems proved
    in Step 2 are what block withdrawal; type-level exclusion plays no role. -/

/-- V stripped: a CDeposit with empty provenance chain — the V-spoofing attack surface. -/
def V_stripped_deposit : CDeposit :=
  { claim := "spoofed-claim", S := 100, E := ["known-error"], V := [], τ := 1000,
    cs := default }

/-- τ expired: a CDeposit whose τ falls below any non-trivial current_time — the τ-compression
    attack surface. At current_time ≥ 2, compute_status gives .Stale, not .Deposited. -/
def τ_expired_deposit : CDeposit :=
  { claim := "stale-claim", S := 100, E := ["known-error"], V := ["src"], τ := 1,
    cs := default }

/-- S zero: a CDeposit with no acceptance threshold — the standards-displacement surface.
    S = 0 means any claim clears the standard bar regardless of scrutiny. -/
def S_zero_deposit : CDeposit :=
  { claim := "proxy-claim", S := 0, E := ["known-error"], V := ["src"], τ := 1000,
    cs := default }

/-- E empty: a CDeposit with no error model — the diagnosis-blind surface.
    Without an error model, no failure mode can be named during challenge. -/
def E_empty_deposit : CDeposit :=
  { claim := "no-error-model", S := 100, E := [], V := ["src"], τ := 1000,
    cs := default }

/-- Fully stripped: S = 0, E = [], V = [] simultaneously. Witnesses c_header_stripped. -/
def fully_stripped_deposit : CDeposit :=
  { claim := "stripped-claim", S := 0, E := [], V := [], τ := 999, cs := default }

example : c_header_stripped fully_stripped_deposit := Or.inl rfl

/-! ========================================================================
    STEP 2 — THE GATES ARE STRUCTURALLY UN-BYPASSABLE
    ========================================================================

    Each theorem proves that a specific attack-relevant condition makes
    c_can_withdraw (or c_header_preserved) unreachable. The proofs unfold
    compute_status and case-split on its if-then-else branches. -/

/-- τ_expired_not_withdrawable: τ-expiry blocks withdrawal at the status gate.

    **Theorem shape:** d.τ ≤ t → ¬c_can_withdraw acl a B d t.

    **Proof strategy:** c_can_withdraw requires compute_status d t = .Deposited.
    With d.τ ≤ t, case-splitting on compute_status branches gives:
    - d.τ = 0 → .Revoked ≠ .Deposited (by decide)
    - d.τ ≤ t → .Stale ≠ .Deposited (by decide)
    - Remaining branches all have ¬(d.τ ≤ t) contradicting h (by omega). -/
theorem τ_expired_not_withdrawable {acl : CACL} {a : CAgent} {B : CBubble}
    (d : CDeposit) (t : CTime) (h : d.τ ≤ t) :
    ¬c_can_withdraw acl a B d t := by
  intro ⟨_, h_status, _⟩
  -- h_status : compute_status d t = CDepositStatus.Deposited
  -- d.τ ≤ t forces the first or second branch (.Revoked / .Stale), never .Deposited.
  unfold compute_status at h_status
  by_cases h0 : d.τ = 0
  · -- d.τ = 0 → .Revoked = .Deposited — false
    rw [if_pos h0] at h_status
    exact absurd h_status (by decide)
  · -- d.τ ≠ 0, d.τ ≤ t → .Stale = .Deposited — false
    rw [if_neg h0, if_pos h] at h_status
    exact absurd h_status (by decide)

/-- V_stripped_not_withdrawable: absent provenance blocks withdrawal at the status gate.

    **Theorem shape:** d.V.length = 0 → d.τ > t + 10 → ¬c_can_withdraw acl a B d t.

    **Proof strategy:** With d.τ > t + 10, the Revoked/Stale/Aging branches are
    arithmetic contradictions (omega). The Candidate branch fires when d.V.length = 0,
    giving .Candidate ≠ .Deposited (by decide). The .Deposited branch requires
    d.V.length ≠ 0, contradicting h_V (by omega). -/
theorem V_stripped_not_withdrawable {acl : CACL} {a : CAgent} {B : CBubble}
    (d : CDeposit) (t : CTime) (h_V : d.V.length = 0) (h_τ : d.τ > t + 10) :
    ¬c_can_withdraw acl a B d t := by
  intro ⟨_, h_status, _⟩
  -- h_status : compute_status d t = CDepositStatus.Deposited
  -- d.τ > t + 10 rules out the first three branches; d.V.length = 0 fires .Candidate.
  unfold compute_status at h_status
  -- Derive the three branch-exclusion facts from h_τ : t + 10 < d.τ.
  have hne0 : d.τ ≠ 0 := by
    intro h_eq; rw [h_eq] at h_τ; exact Nat.not_lt_zero _ h_τ
  have hgt_t : ¬(d.τ ≤ t) := fun h_le =>
    Nat.lt_irrefl t
      (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_add_right t 10) h_τ) h_le)
  have hgt_t10 : ¬(d.τ ≤ t + 10) := fun h_le =>
    Nat.lt_irrefl (t + 10) (Nat.lt_of_lt_of_le h_τ h_le)
  -- All three guards fail; d.V.length = 0 sends us to .Candidate ≠ .Deposited.
  rw [if_neg hne0, if_neg hgt_t, if_neg hgt_t10, if_pos h_V] at h_status
  exact absurd h_status (by decide)

/-- E_stripped_diagnosis_lost: a stripped header cannot simultaneously be preserved.

    **Theorem shape:** c_header_stripped d → ¬c_header_preserved d.

    **Proof strategy:** c_header_stripped is S = 0 ∨ E.length = 0 ∨ V.length = 0;
    c_header_preserved requires S > 0 ∧ E.length > 0 ∧ V.length > 0.
    Each disjunct omega-contradicts the corresponding positivity hypothesis. -/
theorem E_stripped_diagnosis_lost (d : CDeposit) (h : c_header_stripped d) :
    ¬c_header_preserved d := by
  intro ⟨hS, hE, hV⟩
  -- Each branch of c_header_stripped contradicts the matching positivity bound in c_header_preserved.
  unfold c_header_stripped at h
  cases h with
  | inl h => rw [h] at hS; exact Nat.lt_irrefl 0 hS
  | inr h =>
    cases h with
    | inl h => rw [h] at hE; exact Nat.lt_irrefl 0 hE
    | inr h => rw [h] at hV; exact Nat.lt_irrefl 0 hV

/-! ========================================================================
    STEP 3 — ATTACK-NAMED MITIGATIONS
    ========================================================================

    Each theorem names a step-2 result after the attack type it blocks. A
    concrete FullStackAttack witness satisfying attack_succeeds is also
    exhibited, connecting the abstract Bool-flag taxonomy (AdversarialBase)
    to concrete compute_status enforcement (ConcreteLedgerModel). -/

/-- τ_compressed_deposit_blocked: the τ-compression attack is blocked at the status gate.

    The τ-compression attack (AttackLevel.τCompress) shortens the decision window
    so τ expires before verification can complete. Any CDeposit with d.τ ≤ t is
    classified as .Stale (or .Revoked), never .Deposited. -/
theorem τ_compressed_deposit_blocked {acl : CACL} {a : CAgent} {B : CBubble}
    (d : CDeposit) (t : CTime) (h : d.τ ≤ t) :
    ¬c_can_withdraw acl a B d t :=
  τ_expired_not_withdrawable d t h

/-- V_spoof_deposit_blocked: the V-spoofing attack is blocked at the status gate.

    The V-spoofing attack (AttackLevel.VSpoof) injects a deposit with fabricated
    or absent provenance (d.V = []). When the deposit is otherwise fresh
    (d.τ > t + 10), compute_status falls through to .Candidate — never .Deposited. -/
theorem V_spoof_deposit_blocked {acl : CACL} {a : CAgent} {B : CBubble}
    (d : CDeposit) (t : CTime) (h_V : d.V.length = 0) (h_τ : d.τ > t + 10) :
    ¬c_can_withdraw acl a B d t :=
  V_stripped_not_withdrawable d t h_V h_τ

/-- pseudo_deposit_blocked_at_candidate_stage: a pseudo-deposit (V_was_spoofed = true)
    stalls at .Candidate lifecycle stage and cannot be withdrawn.

    A PseudoDeposit has V_was_spoofed = true — concretely, d.V = [].
    Absent provenance leaves the deposit in .Candidate status; withdrawal
    requires .Deposited. The gate is the same as V_spoof_deposit_blocked. -/
theorem pseudo_deposit_blocked_at_candidate_stage
    {acl : CACL} {a : CAgent} {B : CBubble}
    (d : CDeposit) (t : CTime) (h_V : d.V.length = 0) (h_τ : d.τ > t + 10) :
    ¬c_can_withdraw acl a B d t :=
  V_stripped_not_withdrawable d t h_V h_τ

/-! ### Concrete DDoS V-Channel Collapse -/

/-- overwhelmed_channel_collapses_V: an overwhelmed channel with a capacity deficit
    for the pending provenance chain returns an empty result.

    **Theorem shape:** c_channel_overwhelmed cc → sources.length > cc.capacity
                       → c_process_V cc sources = [].

    **Proof strategy:** c_process_V fires the else-branch when the if-guard
    `sources.length ≤ cc.capacity` fails. The guard fails because h_deficit gives
    `sources.length > cc.capacity`; if_neg + Nat.lt_irrefl close the goal. -/
theorem overwhelmed_channel_collapses_V (cc : CAuditChannel) (sources : CProvenance)
    (_ : c_channel_overwhelmed cc)
    (h_deficit : sources.length > cc.capacity) :
    c_process_V cc sources = [] := by
  unfold c_process_V
  rw [if_neg (fun h_le =>
    Nat.lt_irrefl cc.capacity (Nat.lt_of_lt_of_le h_deficit h_le))]

/-- ddos_V_channel_collapse_blocks_withdrawal: DDoS V-channel overload is traced
    all the way through to a blocked withdrawal at the concrete V gate.

    **Theorem shape:** c_channel_overwhelmed cc → sources.length > cc.capacity
                       → d.V = c_process_V cc sources → d.τ > t + 10
                       → ¬c_can_withdraw acl a B d t.

    Chain:
    1. c_channel_overwhelmed cc  — volume > capacity (DDoS active, Nat inequality)
    2. sources.length > cc.capacity — this deposit's V-check exceeds remaining capacity
    3. overwhelmed_channel_collapses_V → c_process_V cc sources = []  (channel math)
    4. h_V bridges channel to deposit: d.V = c_process_V cc sources
    5. d.V.length = 0 → V_stripped_not_withdrawable closes the goal

    h_V is the modeling bridge: it states that the deposit's V field was populated
    by routing through channel cc, so the collapsed channel result is what the
    deposit actually carries when it arrives at the withdrawal gate. -/
theorem ddos_V_channel_collapse_blocks_withdrawal
    {acl : CACL} {a : CAgent} {B : CBubble}
    (cc : CAuditChannel)
    (h_overwhelmed : c_channel_overwhelmed cc)
    (sources : CProvenance) (h_deficit : sources.length > cc.capacity)
    (d : CDeposit) (t : CTime)
    (h_V : d.V = c_process_V cc sources)
    (h_τ : d.τ > t + 10) :
    ¬c_can_withdraw acl a B d t := by
  have h_empty : c_process_V cc sources = [] :=
    overwhelmed_channel_collapses_V cc sources h_overwhelmed h_deficit
  have h_d_V : d.V.length = 0 := by rw [h_V, h_empty]; rfl
  exact V_stripped_not_withdrawable d t h_d_V h_τ

/-! ========================================================================
    STEP 4 — EXPORT GATE CONDITIONS
    ========================================================================

    CExportRequest packages a deposit with gate metadata (revalidated flag,
    trust bridge). It carries no agent and no proof of prior withdrawal —
    the model does not structurally enforce that an agent must successfully
    withdraw from the source bubble before constructing an export request.

    This is not a gap, and the delegation is not optional — it is forced by
    two independent constraints that are both foundational to the model.

    REASON 1 — BOUNDED VERIFICATION:
    (1) Verification capacity is bounded. CAuditChannel models a finite
        capacity/volume pair; the DDoS proofs in Step 3 use exactly this
        arithmetic. This is a foundational constraint of the model.
    (2) Full re-verification on every cross-bubble transfer is therefore not
        always possible. A received deposit may reference provenance sources
        that are no longer reachable, or revalidation cost may exceed available
        channel capacity.
    (3) The trust-bridge path in c_valid_export is the architecture's required
        response to (1)–(2). Epistemic equivalence certified by a mutually
        trusted party is legitimate precisely because full re-verification is
        not always available — not a shortcut.
    (4) A valid trust-bridge transfer need not reduce to a single
        withdraw-first protocol shape, so enforcing "withdrawal must precede
        export" as a universal structural invariant would rule out legitimate
        transfer topologies.

    REASON 2 — DECENTRALIZATION:
    (5) Bubbles are independent ledgers. Each bubble owns its own state;
        there is no shared cross-bubble withdrawal registry.
    (6) Bubble B has no read access to bubble A's ledger. The only evidence
        bubble B receives about events in bubble A is what the agent presents
        in the CExportRequest — specifically, the deposit value and gate flags.
    (7) An agent could therefore construct a CExportRequest carrying a deposit
        that was never withdrawn from A, labelling it with whatever provenance
        chain it chooses. "Deposit d was withdrawn from bubble A" is not a
        verifiable fact at the architecture level; it is an assertion by the
        agent.
    (8) Even infinite verification capacity does not resolve (5)–(7): the
        problem is not that verification is expensive, it is that the
        withdrawal record is not accessible to the receiving bubble at all.
        "Withdrawal must precede export" is unverifiable cross-bubble except
        in the degenerate case of a single-bubble system — which has no
        cross-bubble transfer to enforce.

    Both reasons independently force the same conclusion: invocation order
    must be delegated to the agent layer. EpArch's claim is therefore precise:
    the gate conditions themselves are un-bypassable. c_valid_export requires:
    (a) req.revalidated = true (deposit re-checked at destination), or
    (b) a trust bridge exists whose source matches the exporting bubble.
    Absent both, c_valid_export = false and c_import_deposit = none.

    Several legitimate engineering approaches can implement the agent-layer
    obligation — EpArch does not endorse or prohibit any of them. What it
    does establish is where each one sits in the stack:
    - A daemon or event-relay watching bubble A and writing withdrawal events
      into bubble B is a sound design choice. EpArch classifies it as an agent:
      it holds claims about A's state and asserts them into B's context, so the
      bank's gate conditions apply to its deposits. The invocation-order
      guarantee is now the daemon's protocol responsibility, not the bank's.
    - Replication is a sound design choice for availability, but it does not
      substitute for validation. A replication mechanism that copies epistemic
      state as-is propagates V, τ, and E faithfully — including malformed or
      fabricated values. Distinguishing valid from fabricated requires running
      the gate conditions, which is exactly what the replicating agent is
      responsible for doing before or after replication.
    - Merging bubbles A and B into a single bubble is a sound design choice
      when the accountability boundary between them is not needed. It removes
      the cross-bubble transfer problem by removing the boundary. The agent-
      layer obligation reappears as soon as a second bubble is introduced.
    - A cryptographic signature from bubble A certifying "d was withdrawn" is
      a sound design choice and a natural fit for the trust-bridge path. The
      entity that holds the verification key, checks revocation, and asserts
      "this signature is valid and was produced under the correct withdrawal
      conditions" is performing the epistemic act EpArch assigns to an agent.
      The crypto layer is the mechanism; the agent is the entity accountable
      for its correct use. EpArch does not specify which mechanism agents must
      use — that is precisely what it delegates.

    The bubble boundary is the epistemic accountability boundary. The agent
    layer is the right place for these decisions because agents have the
    deployment-specific context — topology, key infrastructure, replication
    strategy — that the architecture deliberately does not carry. EpArch
    proves the gates are sound regardless of which mechanism the agent uses
    to satisfy them. -/

/-- invalid_export_requires_reval_or_bridge: absent both revalidation and trust bridge,
    c_valid_export returns false.

    **Theorem shape:** req.revalidated = false → req.via_trust_bridge = none
                       → c_valid_export req = false.

    **Proof strategy:** c_valid_export unfolds to a || / && Boolean expression.
    Substituting false and none causes all components to evaluate to false; rfl
    closes via definitional reduction. -/
theorem invalid_export_requires_reval_or_bridge (req : CExportRequest)
    (h_no_reval : req.revalidated = false)
    (h_no_bridge : req.via_trust_bridge = none) :
    c_valid_export req = false := by
  unfold c_valid_export
  rw [h_no_reval, h_no_bridge]
  -- false || (none.isSome && none.any f) reduces to false = false definitionally
  rfl

/-- missing_export_gate_blocks_import: when c_valid_export returns false,
    c_import_deposit returns none — the deposit is not admitted to the target bubble.

    **Proof strategy:** c_import_deposit is if-then-else on c_valid_export; the false
    branch evaluates to none. rfl after rw [h] closes the goal. -/
theorem missing_export_gate_blocks_import (req : CExportRequest)
    (h : c_valid_export req = false) :
    c_import_deposit req = none := by
  unfold c_import_deposit
  -- c_valid_export req : Bool; case-split to reduce the if-then-else
  cases hb : c_valid_export req with
  | false => rfl
  | true  => exact absurd h (by rw [hb]; decide)

/-- V_spoof_blocks_cross_bubble_reliance: absent revalidation and trust bridge,
    c_import_deposit returns none — the export gate condition is not met.

    _h_V names the V-spoofing / collapse surface, but c_valid_export does not inspect
    V directly. It enforces the meta-level protocol gates (revalidation, trust bridge)
    that are supposed to compensate for potentially stripped provenance. V = [] is the
    motivation for why those gates matter, not a direct input to the gate check.

    Whether a deposit with V = [] is also un-withdrawable — and therefore the agent
    could not have assembled this export request honestly — is true in practice but
    is an agent-layer invariant, not proved here. Two independent constraints place
    it there: (a) bounded verification means trust-bridge transfers legitimately
    bypass the withdrawal-first sequence; (b) bubbles are decentralized — bubble B
    cannot read bubble A's ledger, so "this was withdrawn from A" is an unverifiable
    claim regardless of verification capacity. EpArch's claim is: if the request
    arrives at c_import_deposit without reval or bridge, it is rejected. -/
theorem V_spoof_blocks_cross_bubble_reliance (req : CExportRequest)
    (_h_V : req.deposit.V.length = 0)
    (h_no_reval : req.revalidated = false)
    (h_no_bridge : req.via_trust_bridge = none) :
    c_import_deposit req = none :=
  missing_export_gate_blocks_import req
    (invalid_export_requires_reval_or_bridge req h_no_reval h_no_bridge)

/-! ## Full-Stack Attack Witness -/

/-- A concrete FullStackAttack with all Bool flags set to true (all attack conditions active).
    The deposit carries V = [] (no provenance) and τ = 5 (expires by current_time 5). -/
private def concrete_full_stack_attack :
    FullStackAttack (PropLike := CProp) (Standard := CStandard)
      (ErrorModel := CErrorModel) (Provenance := CProvenance) :=
  { target := ⟨0⟩
    deposit :=
      { P      := "victim-claim"
        h      := { S := 100, E := ["known-error"], V := [], τ := 5,
                    acl := ⟨0⟩, redeem := ⟨0⟩ }
        bubble := ⟨0⟩
        status := .Candidate }
    τ_compressed     := true
    V_spoofed        := true
    cues_amplified   := true
    consultation_blocked := true
    expertise_exploited  := true }

/-- The concrete full-stack attack witness satisfies attack_succeeds.

    All Bool conditions hold simultaneously: τ_compressed, V_spoofed (and
    consultation_blocked), cues_amplified, expertise_exploited. This confirms
    attack_succeeds is non-vacuous at concrete type parameters. -/
theorem concrete_attack_succeeds : attack_succeeds concrete_full_stack_attack :=
  ⟨rfl, Or.inl rfl, rfl, rfl⟩

/-- full_stack_attack_concrete_blocked: the CDeposit analogous to the attack witness is
    blocked by the τ gate (τ = 5 ≤ 100 = current_time gives .Stale, not .Deposited).

    This names the end-to-end result: attack_succeeds fires on the Bool flags, but
    the matching deposit is blocked before withdrawal can be attempted. -/
theorem full_stack_attack_concrete_blocked (acl : CACL) (a : CAgent) (B : CBubble) :
    ¬c_can_withdraw acl a B
      { claim := "victim-claim", S := 100, E := ["known-error"], V := [],
        τ := 5, cs := default } 100 := by
  apply τ_expired_not_withdrawable
  -- Goal: (5 : CTime) ≤ 100
  decide

end EpArch.Adversarial.Concrete

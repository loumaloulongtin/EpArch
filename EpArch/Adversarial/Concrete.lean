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
  trust bridge whose gate passes — either the presenting agent matches a named
  authorized agent (.byAgent), or the request carries a credential that the bridge's
  token_ok predicate accepts (.byToken). Absent both, c_import_deposit returns none.
  The gate enforces transfer legitimacy — whether the receiving bubble has epistemic
  grounds to accept the claim — not invocation order. Deposits are epistemic claims,
  not tokens; there is no double-spending problem to sequence around. Bubbles never
  communicate directly; there is always an agent in the middle.
-/

import EpArch.Adversarial.Base
import EpArch.Adversarial.Obligations
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
    - Remaining branches all have ¬(d.τ ≤ t) contradicting h (Nat.lt_irrefl via Nat.lt_of_lt_of_le). -/
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
    arithmetic contradictions (Nat.lt_irrefl via Nat.lt_of_lt_of_le). The Candidate branch fires when d.V.length = 0,
    giving .Candidate ≠ .Deposited (by decide). The .Deposited branch requires
    d.V.length ≠ 0, contradicting h_V (Nat.lt_irrefl 0 after rw). -/
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
    Each disjunct rewrites the zero-equality into the positivity hypothesis, then
    Nat.lt_irrefl 0 closes the goal. -/
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
    trust bridge) and a presenting_agent identity. c_valid_export requires
    either revalidation at the destination or a passing trust bridge gate.
    Absent both, c_import_deposit returns none.

    The gate enforces transfer legitimacy: did a vetted agent vouch for this
    deposit (.byAgent: presenter identity matches), or does it carry a valid
    credential (.byToken: token_ok passes), or was it revalidated at the
    destination? Deposits are epistemic claims, not tokens — there is no
    double-spending problem and no resource to deplete. Bubbles never
    communicate directly; there is always an agent in the middle. -/

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
  -- false || none.any f reduces to false = false definitionally (Option.any on none)
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

    Whether a deposit with V = [] is also un-withdrawable is true in practice but
    is an agent-layer invariant, not proved here. EpArch's claim is: if the request
    arrives at c_import_deposit without reval or an authorized-agent bridge match,
    it is rejected. -/
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

/-! ========================================================================
    STEP 5A — CONCRETE W_lies_scale WITNESS
    ========================================================================

    c_export_cost = 1 (one submission step), c_verify_cost d = d.V.length + 1.
    The asymmetry is a Nat inequality proved by Nat.succ_lt_succ —
    no axiom required. This grounds W_lies_scale concretely: the W assumption
    has a machine-checked satisfying instance rather than remaining purely
    hypothetical. -/

section ConcreteObligationWitnesses
open EpArch.AdversarialObligations

/-- Concrete W_lies_scale: export costs 1 step; verifying a non-empty provenance
    chain costs V.length + 1 steps, which is strictly more.

    **Proof strategy:** `c_export_cost_lt_verify_cost d h` is `Nat.succ_lt_succ h`
    applied to `0 < d.V.length`. No assumption — the inequality is definitionally grounded. -/
def concrete_W_lies_scale (d : CDeposit) (h : 0 < d.V.length) : W_lies_scale :=
  { export_cost    := c_export_cost
    defense_cost   := c_verify_cost d
    asymmetry_holds := c_export_cost_lt_verify_cost d h }

/-- `lies_scale_of_W` fires on the concrete instance: 1 < 2 for τ_expired_deposit
    (which has V := ["src"], so V.length = 1 and c_verify_cost = 2). -/
theorem lies_scale_concrete :
    c_export_cost < c_verify_cost τ_expired_deposit :=
  lies_scale_of_W (concrete_W_lies_scale τ_expired_deposit (by decide))

/-! ========================================================================
    STEP 5B — CONCRETE BOUNDARY-CONDITION WITNESSES
    ========================================================================

    Three boundary-condition W bundles can be concretely discharged by
    constructing an explicit PathExists with all fields true.  The `full_path`
    helper shows that any Deposit type admits such a path — PathExists is a
    record of three Bools, none of which references the deposit's contents.

    W_E_inclusion and W_reversibility carry opaque predicates
    (verification_collapsed, τ_compress) that cannot be reduced to
    CDeposit-level arithmetic.  They are listed as open items below. -/

/-- Concrete W_cheap_validator: a reachable cheap validator always produces a
    valid path for any non-expired deposit (d.h.τ > 0).  The all-true Bool fields
    are abstract; `ttl_valid` is discharged by the explicit `h_τ` hypothesis. -/
def concrete_W_cheap_validator :
    W_cheap_validator (PropLike := CProp) (Standard := CStandard)
      (ErrorModel := CErrorModel) (Provenance := CProvenance) :=
  { cheap_validator_enables_path := fun _a _τ _d _h_cv h_τ =>
      ⟨{ provenance_ok := true, constraint_ok := true, ttl_valid := h_τ },
       ⟨rfl, rfl⟩⟩ }

/-- Concrete W_trust_bridge: a pre-established trust bridge provides a valid path
    for any non-expired deposit (d.h.τ > 0).  The bridge is an out-of-band route;
    `ttl_valid` is discharged by the explicit `h_τ` hypothesis. -/
def concrete_W_trust_bridge :
    W_trust_bridge (PropLike := CProp) (Standard := CStandard)
      (ErrorModel := CErrorModel) (Provenance := CProvenance) :=
  { trust_bridge_enables_path := fun _a _d _h_tb h_τ =>
      ⟨{ provenance_ok := true, constraint_ok := true, ttl_valid := h_τ },
       ⟨rfl, rfl⟩⟩ }

/-- Concrete W_cheap_constraint: a cheaply testable constraint surface provides
    a valid path for any non-expired deposit (d.h.τ > 0).  The test is independent
    of the V chain; `ttl_valid` is discharged by the explicit `h_τ` hypothesis. -/
def concrete_W_cheap_constraint :
    W_cheap_constraint (PropLike := CProp) (Standard := CStandard)
      (ErrorModel := CErrorModel) (Provenance := CProvenance) :=
  { cheap_test_enables_path := fun _d _h_ct h_τ =>
      ⟨{ provenance_ok := true, constraint_ok := true, ttl_valid := h_τ },
       ⟨rfl, rfl⟩⟩ }

/-- Concrete W_reversibility: a reversible deposit (transaction_reversible d = d.h.τ > 0)
    retains a valid path even after τ compression (t_compressed < t_orig).

    This is the key grounded witness: `transaction_reversible d` is definitionally
    `d.h.τ > 0`, which directly discharges `PathExists.ttl_valid`.  The proof field
    is not constructed by hand — it comes directly from the reversibility hypothesis. -/
def concrete_W_reversibility :
    W_reversibility (PropLike := CProp) (Standard := CStandard)
      (ErrorModel := CErrorModel) (Provenance := CProvenance) :=
  { reversibility_survives_τ_compress := fun _t_orig _t_compressed _d h_rev _h_compress =>
      ⟨{ provenance_ok := true, constraint_ok := true, ttl_valid := h_rev },
       ⟨rfl, rfl⟩⟩ }

/-! W_E_inclusion concrete witness is not discharged here.
    `E_includes_threat : Agent → Prop` cannot be grounded from the abstract `Agent`
    type (which is `Nat`-indexed with no E field). Grounding it requires either adding
    a capability field to abstract `Agent` or a separate predicate-bridge layer. -/

/-! ========================================================================
    STEP 5C — CONCRETE DDoS V-CHANNEL EXHAUSTION NAMED THEOREM
    ========================================================================

    `ddos_V_channel_collapse_blocks_withdrawal` (Step 3) traces the full
    concrete chain from `c_channel_overwhelmed` to `¬c_can_withdraw`.  Here
    we name that result explicitly as the concrete realization of the
    `V_channel_exhausted → ¬withdrawal_possible` obligation, and connect it
    to the W_ddos obligation layer by exhibiting the channel-collapse step
    that the abstract bundle's V_exhaustion_collapses field describes. -/

/-- concrete_V_channel_exhaustion_obligation: the concrete DDoS V-channel
    collapse is the observable effect that the abstract W_ddos bundle's
    `V_exhaustion_collapses` field models.

    Chain (concrete):
    1. `c_channel_overwhelmed cc`        — volume > capacity  (Nat def)
    2. `sources.length > cc.capacity`    — this deposit's V-check overflows
    3. `c_process_V cc sources = []`     — channel arithmetic (overwhelmed_channel_collapses_V)
    4. `d.V = []`                        — bridge via h_V
    5. `¬c_can_withdraw acl a B d t`     — V gate fires (V_stripped_not_withdrawable)

    This names the same chain as `ddos_V_channel_collapse_blocks_withdrawal`
    but makes explicit that it is the CONCRETE DISCHARGE of the abstract
    V_channel_exhausted → ¬has_path obligation. -/
theorem concrete_V_channel_exhaustion_obligation
    {acl : CACL} {a : CAgent} {B : CBubble}
    (cc : CAuditChannel)
    (h_overwhelmed : c_channel_overwhelmed cc)
    (sources : CProvenance) (h_deficit : sources.length > cc.capacity)
    (d : CDeposit) (t : CTime)
    (h_V : d.V = c_process_V cc sources)
    (h_τ : d.τ > t + 10) :
    ¬c_can_withdraw acl a B d t :=
  ddos_V_channel_collapse_blocks_withdrawal cc h_overwhelmed sources h_deficit d t h_V h_τ

end ConcreteObligationWitnesses

end EpArch.Adversarial.Concrete

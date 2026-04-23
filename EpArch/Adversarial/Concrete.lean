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
  A second gate, c_acl_import_deposit, applies the deposit's own ACL: if the
  presenting agent is not listed as an authorized exporter, the deposit is blocked
  regardless of the transfer gate result. This is the access-control layer, not a
  quality-defect gate: an ACL-restricted deposit can have perfect S, E, V, and τ.
  The combined gate enforces transfer legitimacy — whether the receiving bubble has
  epistemic grounds to accept the claim — not invocation order. Deposits are epistemic
  claims, not tokens; there is no double-spending problem to sequence around. Bubbles
  never communicate directly; there is always an agent in the middle.
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
    acl := ⟨[]⟩, cs := default }

/-- τ expired: a CDeposit whose τ falls below any non-trivial current_time — the τ-compression
    attack surface. At current_time ≥ 2, compute_status gives .Stale, not .Deposited. -/
def τ_expired_deposit : CDeposit :=
  { claim := "stale-claim", S := 100, E := ["known-error"], V := ["src"], τ := 1,
    acl := ⟨[]⟩, cs := default }

/-- S zero: a CDeposit with no acceptance threshold — the standards-displacement surface.
    S = 0 means any claim clears the standard bar regardless of scrutiny. -/
def S_zero_deposit : CDeposit :=
  { claim := "proxy-claim", S := 0, E := ["known-error"], V := ["src"], τ := 1000,
    acl := ⟨[]⟩, cs := default }

/-- E empty: a CDeposit with no error model — the diagnosis-blind surface.
    Without an error model, no failure mode can be named during challenge. -/
def E_empty_deposit : CDeposit :=
  { claim := "no-error-model", S := 100, E := [], V := ["src"], τ := 1000,
    acl := ⟨[]⟩, cs := default }

/-- Fully stripped: S = 0, E = [], V = [] simultaneously. Witnesses c_header_stripped. -/
def fully_stripped_deposit : CDeposit :=
  { claim := "stripped-claim", S := 0, E := [], V := [], τ := 999, acl := ⟨[]⟩, cs := default }

example : c_header_stripped fully_stripped_deposit := Or.inl rfl

/-- ACL restricted: a CDeposit marked for personal use only — the coconut oil pattern.
    The deposit is high-quality (S, E, V all present, τ fresh) but the ACL
    restricts export to the owner only. No other agent may receive it.
    All other header fields are valid; the restriction is a deliberate choice, not a defect. -/
def acl_restricted_deposit : CDeposit :=
  { claim := "secret-ingredient"
    S := 100
    E := ["recipe-exposure"]
    V := ["personal-experience", "grandmother"]
    τ := 1000
    acl := ⟨[{ agent_id := "owner", bubble_id := "*",
               claim_pattern := "*", permission := "export" }]⟩
    cs := default }

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

/-- overwhelmed_channel_collapses_V: a provenance chain that exceeds channel capacity
    returns an empty result from c_process_V.

    **Theorem shape:** sources.length > cc.capacity → c_process_V cc sources = [].

    Note: `c_channel_overwhelmed cc` (cc.volume > cc.capacity) is accepted as a
    parameter for contextual framing — it names the DDoS scenario — but is not
    used by the proof. The sufficient condition is `h_deficit` alone: the guard
    `sources.length ≤ cc.capacity` fails, firing the else-branch. The `_` binding
    reflects that `c_channel_overwhelmed` and `h_deficit` measure different things
    (`cc.volume` vs `sources.length`); both are relevant to the scenario, but only
    `h_deficit` participates in the arithmetic.

    **Proof strategy:** `c_process_V` fires the else-branch when the if-guard
    `sources.length ≤ cc.capacity` fails. `if_neg + Nat.lt_irrefl` close the goal. -/
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
    1. h_deficit : sources.length > cc.capacity — V-check exceeds capacity (sufficient condition)
    2. overwhelmed_channel_collapses_V → c_process_V cc sources = []  (channel arithmetic)
    3. h_V bridges channel to deposit: d.V = c_process_V cc sources
    4. d.V.length = 0 → V_stripped_not_withdrawable closes the goal

    h_overwhelmed (c_channel_overwhelmed cc) provides scenario framing — it names the DDoS
    context — but is threaded to overwhelmed_channel_collapses_V where it is also unused in
    the proof (see that theorem's doc). The active sufficient condition throughout is h_deficit.
    h_V is the modeling bridge: it states that the deposit's V field was populated by routing
    through channel cc, so the collapsed channel result is what the deposit actually carries
    when it arrives at the withdrawal gate. -/
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
    trust bridge) and a presenting_agent identity. Two gates apply in sequence:

    Gate A — transfer legitimacy (c_import_deposit / c_valid_export):
    Requires either revalidation at the destination or a passing trust bridge.
    Absent both, c_import_deposit returns none.

    Gate B — deposit-level access control (c_acl_import_deposit):
    Applies the deposit's own acl field. If the presenting agent is not listed
    as an authorized exporter, c_acl_import_deposit returns none regardless of
    the Gate A result. This blocks deliberate-restriction cases (the coconut oil
    pattern: a high-quality deposit the owner has chosen not to share) separately
    from quality-defect gates (V, τ, S, E).

    Did a vetted agent vouch for this deposit (.byAgent: presenter identity
    matches), or does it carry a valid credential (.byToken: token_ok passes),
    or was it revalidated at the destination? And is that agent listed in the
    deposit's own ACL? Deposits are epistemic claims, not tokens — there is no
    double-spending problem and no resource to deplete. Bubbles never communicate
    directly; there is always an agent in the middle. -/

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

/-- deposit_acl_blocks_import: a deposit whose own ACL does not permit the presenting
    agent is blocked at the full import gate, regardless of the transfer gate result.

    This is the coconut oil case: P is excellent; S, E, V all pass; τ is fresh;
    the block is a deliberate choice about who may receive the claim, not a quality failure.
    Even with a passing trust bridge or revalidation, `c_acl_import_deposit` returns none.

    Proof: unfold `c_acl_import_deposit`; `h_acl_denied` rewrites the ACL gate to false;
    `Bool.false_and` closes the conjunction to false regardless of the transfer gate. -/
theorem deposit_acl_blocks_import (req : CExportRequest)
    (h_acl_denied : c_deposit_allows_export req.deposit req.presenting_agent req.target = false) :
    c_acl_import_deposit req = none := by
  unfold c_acl_import_deposit
  rw [h_acl_denied, Bool.false_and]
  rfl

/-- Witness: `acl_restricted_deposit` is blocked for any non-owner agent.
    A presenting agent whose id is not "owner" finds no matching ACL entry. -/
example : c_deposit_allows_export acl_restricted_deposit
    { id := "child", beliefs := [], confidence := fun _ => 0 }
    { id := "child-kitchen", deposits := [] } = false := by
  unfold c_deposit_allows_export acl_restricted_deposit
  decide

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
        τ := 5, acl := ⟨[]⟩, cs := default } 100 := by
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

    Four boundary-condition W bundles are concretely discharged by deriving
    both PathExists proof fields (ttl_valid, status_live) from hypotheses.
    No Bool fields; no hand-set values.  W_E_inclusion remains undischarged
    (see open items at end of file). -/

/-- Concrete W_cheap_validator: for a non-revoked deposit with positive TTL, a reachable
    cheap validator produces a PathExists witness with both proof fields derived from
    preconditions.

    `h_cv : cheap_validator_reachable a d.h.τ` is definitionally `d.h.τ > 0` (grounded
    def in Base.lean) — used directly as `ttl_valid`. `h_s : d.status ≠ .Revoked` used
    as `status_live`. No Bool fields; no hand-set values. -/
def concrete_W_cheap_validator :
    W_cheap_validator (PropLike := CProp) (Standard := CStandard)
      (ErrorModel := CErrorModel) (Provenance := CProvenance) :=
  { cheap_validator_enables_path := fun _a _d h_cv h_s =>
      { ttl_valid := h_cv, status_live := h_s } }

/-- Concrete W_trust_bridge: a pre-established trust bridge provides a PathExists witness
    for a non-expired, non-revoked deposit. Both proof fields derived from preconditions.

    `h_τ : d.h.τ > 0` used as `ttl_valid`. `h_s : d.status ≠ .Revoked` used as
    `status_live`. The `_h_tb : trust_bridge_on_hand a` (opaque) cannot be further
    reduced at the abstract level — the bridge's existence is asserted by the W bundle
    hypothesis and does not derive from concrete deposit fields. -/
def concrete_W_trust_bridge :
    W_trust_bridge (PropLike := CProp) (Standard := CStandard)
      (ErrorModel := CErrorModel) (Provenance := CProvenance) :=
  { trust_bridge_enables_path := fun _a _d _h_tb h_τ h_s =>
      { ttl_valid := h_τ, status_live := h_s } }

/-- Concrete W_cheap_constraint: a cheaply testable constraint surface produces a
    PathExists witness with both proof fields derived from preconditions.

    `h_ct : constraint_cheaply_testable d` is definitionally `d.h.τ > 0` (grounded
    def in Base.lean) — used directly as `ttl_valid`. `h_s : d.status ≠ .Revoked`
    used as `status_live`. No Bool fields; no hand-set values. -/
def concrete_W_cheap_constraint :
    W_cheap_constraint (PropLike := CProp) (Standard := CStandard)
      (ErrorModel := CErrorModel) (Provenance := CProvenance) :=
  { cheap_test_enables_path := fun _d h_ct h_s =>
      { ttl_valid := h_ct, status_live := h_s } }

/-- Concrete W_reversibility: a reversible deposit retains a PathExists witness after
    τ compression, with both proof fields derived from preconditions.

    `h_rev : transaction_reversible d` is definitionally `d.h.τ > 0` (grounded def
    in Base.lean) — used directly as `ttl_valid`. `h_s : d.status ≠ .Revoked` used
    as `status_live`. This is the key grounded witness: the path field is not
    constructed by hand but flows directly from the reversibility hypothesis. -/
def concrete_W_reversibility :
    W_reversibility (PropLike := CProp) (Standard := CStandard)
      (ErrorModel := CErrorModel) (Provenance := CProvenance) :=
  { reversibility_survives_τ_compress := fun _t_orig _t_compressed _d h_rev _h_compress h_s =>
      { ttl_valid := h_rev, status_live := h_s } }



/-! ========================================================================
    STEP 5C — CONCRETE DDoS V-CHANNEL EXHAUSTION NAMED THEOREM
    ========================================================================

    `ddos_V_channel_collapse_blocks_withdrawal` (Step 3) traces the full
    concrete chain from `c_channel_overwhelmed` to `¬c_can_withdraw`.  Here
    we name that result explicitly as the concrete observable effect of the
    DDoS V-channel exhaustion vector in the abstract `W_ddos` bundle, and
    connect it to the abstract obligation layer by exhibiting the channel-collapse
    step that `ddos_overwhelms (.VChannelExhaustion)` describes.

    Note: the abstract `W_ddos.ddos_overwhelms` obligation gives
    `V_channel_exhausted a → ∃ channels, verification_collapsed a channels`
    (structural collapse, not ¬PathExists directly).  The `h_exhausts_tau`
    hypothesis (in `rolex_ddos_share_path_failure_structure`) and
    `collapsed_to_path_failure` complete the path-failure chain.
    This concrete theorem witnesses `¬c_can_withdraw` — the concrete correlate
    of verification collapse for the V-channel vector. The mapping from abstract
    `verification_collapsed` to concrete `¬c_can_withdraw` is the modeling
    bridge; this theorem sits on the concrete side of it. -/

/-- concrete_V_channel_exhaustion_obligation: the concrete DDoS V-channel
    collapse is the observable effect of the `V_channel_exhausted` arm of the
    abstract `W_ddos.ddos_overwhelms` disjunction.

    Chain (concrete):
    1. `c_channel_overwhelmed cc`        — volume > capacity  (Nat def)
    2. `sources.length > cc.capacity`    — this deposit's V-check overflows
    3. `c_process_V cc sources = []`     — channel arithmetic (overwhelmed_channel_collapses_V)
    4. `d.V = []`                        — bridge via h_V
    5. `¬c_can_withdraw acl a B d t`     — V gate fires (V_stripped_not_withdrawable)

    This names the same chain as `ddos_V_channel_collapse_blocks_withdrawal`
    but makes explicit that it is the concrete observable effect of the
    `V_channel_exhausted` arm of `W_ddos.ddos_overwhelms`.  The abstract
    obligation asserts
    `V_channel_exhausted a → ∃ channels, verification_collapsed a channels`
    (via `W_ddos.ddos_overwhelms`); this theorem witnesses
    the V-channel side of that collapse at the concrete `¬c_can_withdraw` level. -/
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


/-! ========================================================================
    OPEN ITEMS — PERMANENT EXTENSION POINTS
    ========================================================================

    The items below are intentionally left open in this repository.  They are
    not bugs or planned work — they mark the boundary where the abstract
    Deposit/Agent kernel ends and richer agent models begin.  Each one is an
    entry point for anyone interested in extending the formalization with
    concrete agent structure.

    ### 1. `E_includes_threat` remains opaque (Base.lean)

    `E_includes_threat : Agent → Prop` cannot be grounded as a `def` because
    the abstract `Agent` type is `Nat`-indexed with no capability or
    expertise field.  Grounding it requires either:
    - adding a capability/expertise field to abstract `Agent`, or
    - a separate predicate-bridge layer that maps `Agent` to a richer type
      carrying an E-field.
    Either route changes the agent model beyond what this kernel commits to.
    `W_E_inclusion` therefore has no concrete witness in this file.

    ### 2. `collapse_causes_centralization_of_W` is a field projection

    The obligation theorem `collapse_causes_centralization_of_W` extracts
    `W_collapse_centralization.exhaustion_triggers_delegation` directly.
    `verification_collapsed` is now a structural `def` (grounded in channel
    arithmetic), but `trust_centralized` remains opaque — it is a behavioral
    claim about which authority an agent delegates to, which depends on agent
    internals not modeled in this kernel.
    A concrete discharge requires an agent model that specifies when an
    agent's verification capacity is exhausted and when it delegates.

    ### 3. `lies_scale_of_W` is a field projection (with concrete satisfier)

    The obligation theorem `lies_scale_of_W` extracts
    `W_lies_scale.asymmetry_holds`.  Unlike item 2, this bundle *does* have
    a concrete satisfier: `concrete_W_lies_scale` in Step 5A above grounds
    the cost asymmetry via `c_export_cost_lt_verify_cost` with real Nat
    arithmetic.  The theorem body is still a field return, but the bundle
    is non-vacuously inhabited at the concrete layer.

    ### 4. `concrete_V_channel_exhaustion_obligation` is a named restatement

    The concrete DDoS V-channel exhaustion theorem (Step 5C) names the same
    chain as `ddos_V_channel_collapse_blocks_withdrawal` (Step 3).  It is
    not a deeper end-to-end discharge of the full abstract `W_ddos` bundle;
    it covers only the `V_channel_exhausted` arm of `W_ddos.ddos_overwhelms`.  The other three
    vectors (`ladder_overloaded`, `E_field_poisoned`, `denial_triggered`)
    remain opaque agent-level predicates.  Concretely discharging them
    requires an agent model that specifies traction formation, E-field
    noise thresholds, and trust-import dynamics respectively.

    ────────────────────────────────────────────────────────────────────────
    All four items converge on the same design boundary: the abstract kernel
    treats agents as unscripted (`Agent := Nat`-indexed, no internal fields).
    Any extension that adds agent-internal structure (expertise fields,
    verification budgets, traction dynamics, trust-delegation rules) can
    ground one or more of these items without changing the existing proof
    surface.  The modular architecture (Meta/Config.lean, ClusterRegistry)
    supports registering new clusters for such extensions.
    ======================================================================== -/


end EpArch.Adversarial.Concrete

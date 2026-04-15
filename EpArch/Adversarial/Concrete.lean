/-
EpArch.Adversarial.Concrete — Concrete Attack Mitigation Proofs

Three-step demonstration connecting the abstract attack vocabulary
(AdversarialBase) to the concrete kernel model (ConcreteLedgerModel):

- Step 1: The CDeposit type has four independent exploit-surface dimensions
  (V, τ, S, E). No structural constraint prevents attack-susceptible values;
  the gate theorems in Step 2 are the actual defense.

- Step 2: The compute_status gates are structurally un-bypassable. Proved
  theorems show that τ-expiry and V-stripping each block c_can_withdraw,
  and that header stripping prevents c_header_preserved from holding.

- Step 3: Each attack type from AdversarialBase is named against the gate
  that blocks it. A concrete FullStackAttack witness satisfies attack_succeeds;
  the matching CDeposit-level conditions are blocked by the step-2 gates.
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

/-- ddos_blocked_via_V_gate: DDoS-induced V-channel exhaustion is blocked at the V gate.

    A DDoS attack (AttackLevel.DDoS) overwhelms the audit channel so provenance
    checking cannot complete. The concrete outcome is d.V = [] (verification collapse).
    Any such deposit is blocked at .Candidate stage. The hypothesis
    `channel_overwhelmed c` makes the connection to AdversarialBase explicit. -/
theorem ddos_blocked_via_V_gate
    {acl : CACL} {a : CAgent} {B : CBubble}
    (c : AuditChannel) (_ : channel_overwhelmed c)
    (d : CDeposit) (t : CTime) (h_V : d.V.length = 0) (h_τ : d.τ > t + 10) :
    ¬c_can_withdraw acl a B d t :=
  V_stripped_not_withdrawable d t h_V h_τ

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

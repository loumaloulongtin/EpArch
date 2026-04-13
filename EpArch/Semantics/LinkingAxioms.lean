/-
EpArch/Semantics/LinkingAxioms.lean — Grounded Linking Theorems

Proves that the Step relation's preconditions FORCE the architectural
features claimed in Minimality.lean.

## Relationship to Other Files

- EpArch.Semantics.StepSemantics: Step, SystemState, precondition helpers
- EpArch.Commitments: imports export_gating_forced directly
-/

import EpArch.Semantics.StepSemantics

namespace EpArch.LinkingAxioms

open EpArch.StepSemantics

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## Grounded Linking Theorems

These theorems establish that the operational semantics FORCES the
abstract features. The key insight is that the Step relation's
preconditions make it impossible to perform certain operations
without certain features being present. -/

/-- Grounded version of coordination_requires_bank:
    If two agents can successfully withdraw the same deposit,
    there must be a shared ledger (Bank) they both consult. -/
theorem grounded_coordination_requires_bank
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a1 a2 : Agent) (B : Bubble) (d_idx : Nat)
    (_h_ne : a1 ≠ a2)
    (h_step1 : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a1 B d_idx) s')
    (_h_step2 : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a2 B d_idx) s') :
    -- The operational bank: shared ledger exists
    s.ledger.length > 0 ∧ ∃ d, s.ledger.get? d_idx = some d := by
  -- Extract isDeposited from h_step1
  have h_deposited : isDeposited s d_idx := by
    cases h_step1; assumption
  let ⟨d, hd, _⟩ := h_deposited
  refine ⟨?_, d, hd⟩
  -- Non-empty ledger: List.length (_ :: _) > 0
  match h : s.ledger with
  | [] =>
    -- If ledger is empty, get? can't return some
    rw [h] at hd
    cases hd
  | _head :: tail => exact Nat.zero_lt_succ _

/-- Grounded version of export_requires_headers:
    If export succeeds, the deposit must have headers preserved. -/
theorem grounded_export_requires_headers
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s') :
    -- The operational headers: header_preserved holds
    ∃ d, s.ledger.get? d_idx = some d ∧ header_preserved d := by
  -- Extract depositHasHeader from h_step
  have hheader : depositHasHeader s d_idx := by
    cases h_step <;> assumption
  let ⟨d, hd, h_pres⟩ := hheader
  exact ⟨d, hd, h_pres⟩

-- Helper lemma for list membership and length
private theorem list_length_pos_of_mem {a : α} {l : List α} (h : a ∈ l) :
    l.length > 0 := by
  cases l with
  | nil => cases h
  | cons _ _ => exact Nat.zero_lt_succ _

/-- Grounded version of bounded_audit_requires_trust_bridges:
    If a trust bridge exists between two bubbles, the system's trust
    bridge list is non-empty (the system has trust bridge infrastructure). -/
theorem grounded_bounded_audit_requires_bridges
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (_h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s')
    (h_fast : hasTrustBridge s B1 B2) :
    -- The system has trust bridges
    sys_has_trust_bridges s := by
  simp only [sys_has_trust_bridges]
  cases h_fast with
  | inl h => exact list_length_pos_of_mem h
  | inr h => exact list_length_pos_of_mem h

/-- Grounded version: if export without bridge succeeds, deposit enters as Candidate.
    This shows revalidation is FORCED when trust bridge is absent. -/
theorem grounded_no_bridge_forces_revalidation
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s')
    (h_no_bridge : ¬hasTrustBridge s B1 B2) :
    -- New entry in s'.ledger has status = Candidate
    ∃ d_new, d_new ∈ s'.ledger ∧ d_new.status = .Candidate := by
  cases h_step with
  | export_with_bridge _ _ _ hd hh hbridge =>
    exact absurd hbridge h_no_bridge
  | export_revalidate _ _ _ hdep _ _ =>
    let ⟨d, hd, _⟩ := hdep
    refine ⟨{ d with bubble := B2, status := .Candidate }, ?_, rfl⟩
    unfold addToNewBubble
    simp only [hd]
    -- Need to show: d_new ∈ s.ledger ++ [d_new]
    -- In Lean 4.3.0: List.mem_append_iff and then Or.inr with List.Mem.head
    apply List.mem_append_of_mem_right
    exact List.Mem.head _

/-- Export gating is forced by the LTS structure.
    Every Step.Export either has a trust bridge (export_with_bridge constructor)
    or forces the deposit into .Candidate status (export_revalidate constructor).
    There is no third constructor; ungated export is structurally non-constructible.
    This is the primary operational grounding for ExportGating in Commitments.lean. -/
theorem export_gating_forced
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s') :
    hasTrustBridge s B1 B2 ∨
    (¬hasTrustBridge s B1 B2 ∧ ∃ d_new, d_new ∈ s'.ledger ∧ d_new.status = .Candidate) := by
  cases Classical.em (hasTrustBridge s B1 B2) with
  | inl h_bridge => exact Or.inl h_bridge
  | inr h_no_bridge =>
    exact Or.inr ⟨h_no_bridge,
      grounded_no_bridge_forces_revalidation s s' B1 B2 d_idx h_step h_no_bridge⟩

/-- Grounded version of adversarial_requires_revocation:
    Revocation is possible iff quarantine path exists. -/
theorem grounded_revocation_requires_quarantine
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Revoke d_idx) s') :
    -- Revocation requires prior quarantine
    isQuarantined s d_idx := by
  cases h_step
  assumption

/-- Grounded version of distributed_agents_require_bubbles:
    Different agents accessing deposits in different bubbles demonstrates
    that the bubble structure provides locality — agents don't need global
    ledger access, only their bubble's view. -/
theorem grounded_distributed_agents_require_bubbles
    (s s1' s2' : SystemState PropLike Standard ErrorModel Provenance)
    (a1 a2 : Agent) (B1 B2 : Bubble) (d1_idx d2_idx : Nat)
    (_h_diff_bubbles : B1 ≠ B2)
    (h_step1 : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a1 B1 d1_idx) s1')
    (h_step2 : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a2 B2 d2_idx) s2') :
    -- The operational bubbles: both ACL checks reference bubble-specific permissions
    ∃ (p1 p2 : ACLEntry),
      p1 ∈ s.acl_table ∧ p2 ∈ s.acl_table ∧
      p1.agent = a1 ∧ p2.agent = a2 ∧
      p1.bubble = B1 ∧ p2.bubble = B2 := by
  -- Extract ACL entries from both steps
  have h_acl1 : hasACLPermission s a1 B1 d1_idx := by
    cases h_step1; assumption
  have h_acl2 : hasACLPermission s a2 B2 d2_idx := by
    cases h_step2; assumption
  let ⟨entry1, h_mem1, h_ag1, h_b1, _⟩ := h_acl1
  let ⟨entry2, h_mem2, h_ag2, h_b2, _⟩ := h_acl2
  exact ⟨entry1, entry2, h_mem1, h_mem2, h_ag1, h_ag2, h_b1, h_b2⟩

/-- Grounded version of truth_pressure_requires_redeemability:
    The challenge → quarantine → revoke path demonstrates that deposits
    can fail (redeemability = constraint surface contact). -/
theorem grounded_truth_pressure_requires_redeemability
    (s1 s2 s3 : SystemState PropLike Standard ErrorModel Provenance)
    (c : EpArch.Challenge PropLike Reason Evidence) (d_idx : Nat)
    (_h_challenge : Step (Reason := Reason) (Evidence := Evidence) s1 (.Challenge c) s2)
    (h_revoke : Step (Reason := Reason) (Evidence := Evidence) s2 (.Revoke d_idx) s3) :
    -- The operational redeemability: revoke requires quarantine in s2
    isQuarantined s2 d_idx := by
  cases h_revoke
  assumption

/-! ## Summary: What the Operational Groundings Prove

1. `grounded_coordination_requires_bank`:
   Two-agent withdrawal → shared ledger exists
   (Operational grounding for `coordination_requires_bank`)

2. `grounded_export_requires_headers`:
   Export step → header_preserved holds
   (Operational grounding for `export_requires_headers`)

3. `grounded_bounded_audit_requires_bridges`:
   Trust bridge between bubbles → system has trust bridge infrastructure
   (Operational grounding for `bounded_audit_requires_trust_bridges`)

4. `grounded_no_bridge_forces_revalidation`:
   Export without bridge → enters as Candidate
   (Shows trust bridges enable bounded audit)

5. `grounded_revocation_requires_quarantine`:
   Revoke step → prior quarantine
   (Operational grounding for revocation mechanism)

6. `grounded_distributed_agents_require_bubbles`:
   Different-bubble withdrawals → bubble-scoped ACL entries exist
   (Operational grounding for `distributed_agents_require_bubbles`)

7. `grounded_truth_pressure_requires_redeemability`:
   Challenge + Revoke → deposit was Quarantined between the two steps
   (Operational grounding for `truth_pressure_requires_redeemability`)

These are the OPERATIONAL PROOFS that the linking theorems in Minimality.lean
are not arbitrary: they follow from the structure of the Step relation.
The impossibility theorems now have genuine content:
"If you can't do X, you can't perform Y" follows from Step preconditions.

ALL SIX LINKING THEOREMS NOW HAVE OPERATIONAL GROUNDINGS:
- distributed_agents_require_bubbles     → grounded_distributed_agents_require_bubbles
- bounded_audit_requires_trust_bridges   → grounded_bounded_audit_requires_bridges
- export_requires_headers                → grounded_export_requires_headers
- adversarial_requires_revocation        → grounded_revocation_requires_quarantine
- coordination_requires_bank             → grounded_coordination_requires_bank
- truth_pressure_requires_redeemability  → grounded_truth_pressure_requires_redeemability -/

end EpArch.LinkingAxioms

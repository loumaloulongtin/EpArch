/-
EpArch/Semantics/LinkingAxioms.lean — Grounded Linking Theorems

Proves that the Step relation's preconditions FORCE the export-gating
feature used by Commitments.lean.

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

/-! ## Summary

- `grounded_no_bridge_forces_revalidation`: Export without bridge → deposit enters as Candidate.
- `export_gating_forced`: Every Export step either has a trust bridge or forces Candidate status.
  Imported by `Commitments.lean` as the operational grounding for ExportGating. -/

end EpArch.LinkingAxioms

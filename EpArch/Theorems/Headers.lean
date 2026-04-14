/-
EpArch.Theorems.Headers — Field Checkability and Header Diagnosability Theorems

System-state–level field checkability: `field_checkable`, `harder_without_headers`,
`header_improves_diagnosability`, and `header_localization_link`.
Grounded by the Diagnosability module (observable field sets) and the
Commitments module (`header_stripping_harder`, `DiagnosabilityScore`).
-/
import EpArch.Basic
import EpArch.Header
import EpArch.Commitments
import EpArch.Semantics.StepSemantics
import EpArch.Theorems.Diagnosability

namespace EpArch

open StepSemantics
open Diagnosability

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## Field Checkability -/

/-- A deposit's suspected field is structurally checkable iff the deposit header is present.
    The `Field` parameter is free because all SEV fields live in the header: once the
    header is present every named field is accessible.
    `field_checkable s d_idx f` is definitionally `depositHasHeader s d_idx`. -/
def field_checkable (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (_f : Field) : Prop :=
  depositHasHeader s d_idx

/-- Explicit isomorphism between field checkability and header presence.
    The `Field` parameter is universally free: present header ↔ all fields checkable.
    This makes the definitional equality visible at the type level and grounds
    `harder_without_headers` and `header_improves_diagnosability`. -/
theorem field_checkable_iff_header
    (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) (f : Field) :
    field_checkable s d_idx f ↔ depositHasHeader s d_idx :=
  Iff.rfl

/-- Theorem: Diagnosis is harder without headers.

    Without headers, no field is checkable — any challenge names a field as a
    guess, not a diagnosis from header inspection.  Proof routes through
    `field_checkable_iff_header` making the equivalence explicit. -/
theorem harder_without_headers
    (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat)
    (h : ¬depositHasHeader s d_idx)
    (c : EpArch.Challenge PropLike Reason Evidence) :
    ¬field_checkable s d_idx c.suspected :=
  fun hf => h ((field_checkable_iff_header s d_idx c.suspected).mp hf)


/-- Theorem: With headers, every challenge field is structurally checkable.
    Structural form of Commitment 7 (positive direction):
    `depositHasHeader → field_checkable`.  Dual to `harder_without_headers`.
    Proof routes through `field_checkable_iff_header`, symmetric to the negative direction. -/
theorem header_improves_diagnosability
    (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat)
    (h_header : depositHasHeader s d_idx)
    (c : EpArch.Challenge PropLike Reason Evidence) :
    field_checkable s d_idx c.suspected :=
  (field_checkable_iff_header s d_idx c.suspected).mpr h_header

/-- Header preservation enables field-specific localization.

    With headers, every challenge is field-specific (by `all_challenges_field_specific`)
    and the suspected field is checkable against the deposit's actual S/E/V structure.
    No `decide` on hardcoded constants — proof is structural. -/
theorem header_localization_link
    (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat)
    (h_header : depositHasHeader s d_idx)
    (c : EpArch.Challenge PropLike Reason Evidence) :
    challenge_is_field_specific c ∧ field_checkable s d_idx c.suspected :=
  ⟨all_challenges_field_specific c, h_header⟩



end EpArch

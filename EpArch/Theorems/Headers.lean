/-
EpArch.Theorems.Headers — Diagnosability Metrics and Header Theorems

System-state–level diagnosability scoring, field checkability, and the
connection between header presence and dispute convergence speed.
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

/-! ## Diagnosability Metrics -/

/-- Diagnosability type and scoring function.
    Score-based ordering measure.  For structural reasoning about field accessibility,
    use `field_checkable`. -/
structure Diagnosability where
  score : Nat

def diagScore (withHeader : Bool) : Diagnosability :=
  if withHeader then ⟨100⟩ else ⟨10⟩

/-- Ordering on diagnosability (for "harder" comparison). -/
def diagLE (d1 d2 : Diagnosability) : Prop := d1.score ≤ d2.score

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


/-! ## Dispute Convergence -/

/-- Convergence time bound.
    With headers, convergence takes at most k steps for some fixed k.
    Without headers, the bound is unbounded (or much larger). -/
def ConvergenceTimeBound : Nat := 3  -- placeholder bound for header-preserving resolution

/-- Localization score: 1 = perfectly localized, 0 = not localized.
    With headers, score = 1 (field-specific).
    Without headers, score = 0 (can only say "something is wrong"). -/
def LocalizationScoreValue (has_header : Bool) : Nat :=
  if has_header then 1 else 0

-- Note: Diagnosability and localization are now defined in Commitments.lean
-- using DiagnosabilityScore (capacity measure, not time measure).

/-- Header-stripped disputes are systematically harder.

    Headerless claims produce systematically harder disputes.
    "Harder" means lower diagnosability (fewer fields to inspect), not
    necessarily slower in wall-clock time.

    Proof: Header-preserved has diagnosability 3, header-stripped has 0.
    By definition, 0 < 3, so stripped is harder. -/
theorem header_stripped_harder (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    dispute B P → header_stripped d →
    systematically_harder header_preserved_diagnosability header_stripped_diagnosability := by
  intro _ _
  exact header_stripping_harder

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

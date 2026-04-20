/-
EpArch.Meta.LeanKernel.RepairLoop — Full S/E/V Lifecycle Witness

The Lean elaboration cycle is a concrete, self-contained instance of the
full EpArch deposit lifecycle. This file proves that instance: the tool
used to type-check this file is itself exhibiting the repair loop whose
structure the theorems below assert.

The mapping: S = the programmer's declared type signature; E = the
elaborator's challenge report (file, line, expected, actual); V = the
import list, where each entry is a grounding-chain node.

Main exports:
- LeanCandidateDeposit, LeanVFailure, LeanEFailure — deposit states
- v_failure_blocks_redemption — broken import severs the V chain
- e_failure_enables_localized_repair — error message targets Field.E
- no_error_means_global_repair_scope — stripped header = no targeting
- repair_scope_contracts_with_headers — headers strictly narrow scope
- lean_compiled_deposit, s_upgrade_on_compilation — kernel S-upgrade
- lean_cache_hit, source_change_reopens_repair_loop — ladder settlement
-/

import EpArch.Meta.LeanKernel.World
import EpArch.Theorems.Diagnosability

namespace EpArch.LeanKernelModel

open EpArch
open EpArch.Diagnosability
open EpArch.ConcreteModel

/-! ## Candidate Deposit and Failure Mode Types

Three thin type definitions covering the repair loop's starting state and
each failure mode. The content types (String, Nat) are open — they carry
the conceptual mapping to Lean's domain without fixing a particular encoding
of elaborator internals. -/

/-- A Lean theorem before elaboration: the S field is programmer-asserted.
    Body is present but unverified by the kernel.

    | EpArch field | Lean content                                          |
    |--------------|-------------------------------------------------------|
    | S (standard) | `typeSig` — the declared type; programmer's standard  |
    | V (provenance) | `imports` — the import list; each entry grounds a name |
    | payload      | `body` — the proof term, unverified                   | -/
structure LeanCandidateDeposit where
  /-- Declaration name -/
  name    : String
  /-- S: the declared type (programmer's standard) -/
  typeSig : String
  /-- V: import list (provenance chain) -/
  imports : List String
  /-- Proof term (unverified payload) -/
  body    : String

/-- V failure: a missing import severs the provenance chain.

    Structural invariant: `not_imported` asserts the broken module is
    genuinely absent from the candidate's import list. Without this field,
    the structure would be three unrelated strings — the invariant is what
    makes a `LeanVFailure` mean what it claims. -/
structure LeanVFailure where
  /-- The candidate whose V chain is broken -/
  candidate    : LeanCandidateDeposit
  /-- The module not in candidate.imports -/
  missing_mod  : String
  /-- The identifier that cannot be resolved -/
  broken_name  : String
  /-- Structural invariant: missing_mod is genuinely absent -/
  not_imported : missing_mod ∉ candidate.imports

/-- E failure: a type mismatch populates the E field with localization data.

    The four fields (file, line, expected, actual) are the elaborator's
    challenge record: `canTargetRepair true Field.E` holds because Field.E
    is observable in a deposit with a complete header. -/
structure LeanEFailure where
  /-- The candidate that failed elaboration -/
  candidate : LeanCandidateDeposit
  /-- Source file where the mismatch was detected -/
  file      : String
  /-- Line number of the offending expression -/
  line      : Nat
  /-- What the kernel expected at that position -/
  expected  : String
  /-- What the proof body actually provided -/
  actual    : String

/-! ## Lifecycle Theorems

Three theorems covering each failure mode and the clean state.
Each proof is one step: either extracting a structural invariant field or
delegating to an already-proved Diagnosability theorem. -/

/-- V failure blocks redemption.

    A broken import severs the V chain at name-resolution time — the
    elaborator cannot locate the referenced name and rejects the term before
    any proof is produced. This is an elaboration-grounding failure, earlier
    than and independent of any axiom-audit step. `#print axioms` is a
    later provenance-completeness tool; it is not the reason the candidate
    fails here.

    **Theorem shape:** the missing module is not in the candidate's import list.
    **Proof strategy:** extract the `not_imported` structural invariant field. -/
theorem v_failure_blocks_redemption (v : LeanVFailure) :
    v.missing_mod ∉ v.candidate.imports :=
  v.not_imported

/-- E failure enables localized repair.

    The elaborator's challenge record identifies the exact sub-expression
    at fault: (file, line, expected, actual). With that record present, the
    deposit has a complete header and Field.E is observable.
    `canTargetRepair true Field.E` holds by `full_can_repair_any`.

    **Theorem shape:** given an E failure, Field.E is a valid repair target.
    **Proof strategy:** delegate to `full_can_repair_any Field.E`; the E
    failure context confirms the has_header = true regime applies. -/
theorem e_failure_enables_localized_repair (_e : LeanEFailure) :
    canTargetRepair true Field.E :=
  full_can_repair_any Field.E

/-- Without an error message, no field can be targeted for repair.

    When the elaborator issues no challenge record (the deposit is stripped
    of its header), no field is observable and repair scope degenerates to
    full revocation.

    **Theorem shape:** ∀ f : Field, ¬canTargetRepair false f.
    **Proof strategy:** this is exactly `stripped_no_field_repair`. -/
theorem no_error_means_global_repair_scope :
    ∀ f : Field, ¬canTargetRepair false f :=
  stripped_no_field_repair

/-! ## Comparison Theorem: Headers Strictly Narrow Repair Scope

This is the key diagnosability result witnessed at the concrete Lean domain:
the elaborator's error message reduces repair scope from "everything in scope"
to one sub-expression. Witnessed at Field.E because that is the field the
error record populates. -/

/-- Headers strictly reduce repair scope.

    With the elaborator's error message (has_header = true), repair scope
    is the one sub-expression named by the error record. Without it
    (has_header = false), no field can be targeted.

    **Theorem shape:** ∃ f, canTargetRepair true f ∧ ¬canTargetRepair false f.
    **Proof strategy:** witness Field.E; left conjunct from `full_can_repair_any`,
    right conjunct from `stripped_no_field_repair`. -/
theorem repair_scope_contracts_with_headers :
    ∃ f : Field, canTargetRepair true f ∧ ¬canTargetRepair false f :=
  ⟨Field.E, full_can_repair_any Field.E, stripped_no_field_repair Field.E⟩

/-! ## S-Upgrade on Compilation

Successful compilation upgrades S from programmer-asserted to kernel-verified.
Modeled as a `LeanKernelCtx.Claim` in the clean-environment world (world = true).
`LeanKernelCtx.Truth true true` reduces to `true = true`, which is `rfl`.

Modeling note: this is a deliberate proxy-model encoding. The `rfl` proof term
captures the structural fact that in the clean-environment world a
kernel-certified claim is self-consistent. It is NOT a claim that Lean's actual
compilation judgment is definitionally this proposition — Lean's real elaborator
is a complex pipeline on `Expr` terms. The proxy model abstracts that pipeline
into a two-world Bool context so that structural properties (S-upgrade,
world-consistency) can be stated and proved without introspecting kernel source. -/

/-- A Lean declaration after successful compilation: S is kernel-verified.
    Maps the declaration to a clean-world (`true`) claim in `LeanKernelCtx`. -/
def lean_compiled_deposit (_d : LeanCandidateDeposit) : LeanKernelCtx.Claim :=
  true

/-- KERNEL S-UPGRADE THEOREM

    Successful compilation upgrades S from programmer-asserted to kernel-verified.
    In the proxy model, `LeanKernelCtx.Truth true true` is `true = true`.

    **Theorem shape:** LeanKernelCtx.Truth (lean_compiled_deposit d) (lean_compiled_deposit d).
    **Proof strategy:** `rfl` — the clean world certifies a clean claim. The content
    is in the proxy model's design; the proof term is intentionally thin. -/
theorem s_upgrade_on_compilation (d : LeanCandidateDeposit) :
    LeanKernelCtx.Truth (lean_compiled_deposit d) (lean_compiled_deposit d) :=
  -- Truth true true = (true = true); rfl closes it immediately
  rfl

/-! ## Ladder Settlement and Doorbell

The `.olean` staleness machinery from `World.lean` wired to the ladder and
LTS model. A cache hit is conditional settlement at `LadderStage.Certainty`:
Lean does not re-enter the repair loop while the `.olean` is fresh.
A source change is the revision doorbell: it forces the deposit to `.Stale`
and the kernel re-enters the loop from the top. RevisionSafety guarantees
the doorbell is never removed — a settled claim can always be rechallenged
if its grounding changes. -/

/-- Cache hit predicate: compiled epoch matches last-refresh epoch and source
    has not advanced past the compilation timestamp.

    When both conditions hold, Lean executes `Step.withdraw` against the cached
    `.olean` without re-elaborating — the ladder sits at `LadderStage.Certainty`. -/
def lean_cache_hit (r : OleanRecord) (current_epoch : CTime) : Prop :=
  r.compiled_at = r.last_refreshed ∧ ¬source_changed current_epoch r

/-- SOURCE CHANGE IS THE REVISION DOORBELL

    A changed source forces the `.olean` deposit to `.Stale`, requiring a new
    repair loop pass. This is ladder movement from `Certainty` back to
    re-verification — not entrenchment, but conditional settlement.

    **Theorem shape:** source_changed → compute_status = .Stale.
    **Proof strategy:** delegates entirely to `olean_stale_when_source_changed`
    from `World.lean`; no new content. The connection to the ladder framing
    is made explicit here. -/
theorem source_change_reopens_repair_loop (r : OleanRecord) (path : CProp)
    (current_epoch : CTime)
    (ht   : 0 < r.compiled_at)
    (hchg : source_changed current_epoch r) :
    compute_status (olean_as_deposit r path) current_epoch = .Stale :=
  olean_stale_when_source_changed r path current_epoch ht hchg

/-! ## Self-Referential Note

This file is itself an instance of the repair loop it proves.

It began as a candidate deposit — programmer-asserted S: "I believe this
witnesses the S/E/V repair loop." The Lean elaborator ran the three stages:

- V check: every `import` above resolved successfully — the V chain is intact.
- E challenges: the elaborator issued a challenge for each type mismatch found
  during elaboration. All challenges were resolved; E is now empty.
- S upgrade: the kernel type-checked the file. S is now kernel-verified.

The `.olean` was written. The ladder settled at `LadderStage.Certainty`.

The file being in the repo at all is proof the loop terminated in state 4 —
compiled clean, S upgraded, `.olean` written — and the cache is the proof
that the Lean kernel agrees.
-/

end EpArch.LeanKernelModel

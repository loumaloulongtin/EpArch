/-
EpArch.Meta.LeanKernel.SFailure — Lean Kernel S-Field Failure Taxonomy

Defines the Lean-specific S-failure taxonomy: the structured catalogue
of ways a Lean proof system can satisfy S-field properties vacuously or void-ably.

## Layers Covered

Layer 3 Kernel-Level S-Field Failure Taxonomy:
  Failure modes, void/vacuous witnesses, canonical cases, and the master
  \lean_S_failure_taxonomy\ theorem.

## Split from

EpArch.Meta.LeanKernelModel (original monolithic file).
World + Architecture layers (and OleanStaleness) are in
EpArch.Meta.LeanKernel.World.

-/
import EpArch.Meta.LeanKernel.World

namespace EpArch.LeanKernelModel

open EpArch

/-! ## Kernel-Level S-Field: Axiom Footprint as Standard

    The axiom footprint of a proof is its S field in the EpArch sense.
    `#print axioms some_theorem` is the kernel's S-field readout — a
    truthful record of what standard was applied at elaboration time.
    It is stamped on the claim, fixed, and not changeable per reader.

    S/E/V independence at the meta level:

    - V: the kernel genuinely elaborated this term (provenance is sound).
    - E: proof components are present; no detection gap.
    - S: the axiom level actually used — `allows_sorry`, `classical_only`,
         or `axiom_free`.

    Two distinct kinds of S-failure arise:

    1. **Relational** (axiom threshold mismatch): the same sorry-containing
       proof is acceptable to a development consumer and a S-failure for a
       publication consumer. Both V and E are sound. Only the consuming
       agent's required threshold differs.

    2. **Absolute/void** (`sorry ⊢ False`): when E already documents
       `sorryTainted` as revocable (`LeanGroundedRevocation`) and S is
       solely "sorry closed it", both structural conditions are present in
       the fields — `lean_S_is_void` is witnessed. This is a demonstration
       of field independence, not a prescription for agent acceptance policy.
-/

/-- Lean axiom levels: the S-field vocabulary for Lean proofs.
    Stamped by the kernel at elaboration time. Property of the claim. -/
inductive LeanAxiomLevel where
  | allows_sorry    -- sorryAx in the axiom closure (dev standard)
  | classical_only  -- Classical.choice / propext only; no sorryAx
  | axiom_free      -- kernel primitives only; `#print axioms` empty
  deriving DecidableEq, Repr

/-- Does a proof at `deposit_level` satisfy the `required_level` threshold
    for a specific consuming agent?

    `threshold_met : Prop` is the real semantic content; `clears : Bool` is an
    executable mirror; `clears_sound` bridges them.  EpArch records that the
    threshold relationship holds or fails; the ordering on `LeanAxiomLevel`
    (allows_sorry < classical_only < axiom_free) lives in the consuming agent's
    acceptance policy, outside EpArch's scope. -/
structure LeanStandardClearance where
  /-- The S value stamped on the proof: axiom level actually used. -/
  deposit_level  : LeanAxiomLevel
  /-- The minimum axiom level this consuming agent requires. -/
  required_level : LeanAxiomLevel
  /-- The real semantic content: does deposit_level satisfy required_level?
      EpArch records that this relation holds or fails; the ordering on
      LeanAxiomLevel lives in the consuming agent's policy. -/
  threshold_met  : Prop
  /-- Executable mirror of threshold_met for computable contexts. -/
  clears         : Bool
  /-- Sound bridge: the Bool is honest about the Prop. -/
  clears_sound   : clears = true ↔ threshold_met

/-- Kernel elaboration mode: how a declaration was accepted by the kernel.
    `genuinely_elaborated` is derived from `mode = .kernel`; the bridge
    requires a concrete enum comparison. -/
inductive ElabMode where
  | kernel   -- normal kernel elaboration path (no bypasses)
  | bypass   -- definitional bypass (e.g., `native_decide` shortcut)
  | admitted -- admitted via sorry / admit at this node
  deriving DecidableEq, Repr

/-- V-witness for a Lean Standard case: the kernel genuinely elaborated the term.

    `genuinely_elaborated` is derived from `mode = .kernel`. `kernel_sound` bridges
    the Bool mirror; construction of a non-`.kernel` case requires proving the Bool
    reflects the other mode. -/
structure LeanVWitness where
  /-- The declaration name whose provenance is being witnessed -/
  decl_name         : String
  /-- How the kernel accepted this term — the data backing V. -/
  mode              : ElabMode
  /-- Executable mirror: reflects `mode = .kernel`. -/
  kernel_elaborated : Bool
  /-- Sound bridge: the Bool must honestly reflect the mode comparison. -/
  kernel_sound      : kernel_elaborated = true ↔ mode = .kernel

/-- V genuinely elaborated iff the elaboration mode is `.kernel`.
    Derived from `mode`.
    `@[reducible]` makes this transparent to `decide` and definitional reduction. -/
@[reducible] def LeanVWitness.genuinely_elaborated (v : LeanVWitness) : Prop := v.mode = .kernel

/-- Typed kernel failure categories.
    `no_relevant_gap` in `LeanEWitness` derives from
    `relevant_failure ∈ documented_failures`. -/
inductive KernelFailure where
  | sorryAx             -- sorryAx in the axiom closure
  | inconsistent_axiom  -- user-supplied inconsistent axiom
  | opaque_bypass       -- opaque constant hiding a non-kernel proof
  deriving DecidableEq, Repr

/-- E-witness for a Lean Standard case: known failure modes are documented.

    `no_relevant_gap` derives from `relevant_failure ∈ documented_failures`;
    `adequate_sound` bridges the Bool mirror. Construction requires proving
    the membership claim at the `documented_failures` list. -/
structure LeanEWitness where
  /-- The failure mode this proof is exposed to — what E must cover. -/
  relevant_failure    : KernelFailure
  /-- Known failure modes documented in the error model (typed list). -/
  documented_failures : List KernelFailure
  /-- Executable mirror: reflects `relevant_failure ∈ documented_failures`. -/
  e_adequate          : Bool
  /-- Sound bridge: the Bool must honestly reflect the membership fact. -/
  adequate_sound      : e_adequate = true ↔ relevant_failure ∈ documented_failures

/-- E is adequate iff the relevant failure mode is on the documented list.
    Derived from data.
    `@[reducible]` makes this transparent to `decide` and definitional reduction. -/
@[reducible] def LeanEWitness.no_relevant_gap (e : LeanEWitness) : Prop :=
  e.relevant_failure ∈ e.documented_failures

/-- Lean Standard Case: the proof's S field doesn't clear a strict consumer.
    V and E remain sound — the only issue is S.

    Uses `LeanEWitness` and `LeanVWitness` carrying typed evidence for
    failure-mode coverage and kernel elaboration. -/
structure LeanStandardCase where
  decl_name   : String
  /-- V-field witness: kernel genuinely elaborated this term -/
  v_witness   : LeanVWitness
  /-- E-field witness: known failure modes are documented -/
  e_witness   : LeanEWitness
  s_clearance : LeanStandardClearance
  /-- S fails: the threshold relation is not met (Prop-level, not Bool = false) -/
  clearance_fails_cert : ¬s_clearance.threshold_met

def lean_S_fails (lsc : LeanStandardCase) : Bool := !lsc.s_clearance.clears

/-- A LeanStandardCase routes to S-failure.
    Proof: extracts `¬threshold_met` from `clearance_fails_cert` via Bool
    case-split on `clears` + `clears_sound` bridge — a genuine Prop negation. -/
theorem lean_standard_case_is_S_failure (lsc : LeanStandardCase) :
    lean_S_fails lsc = true := by
  simp only [lean_S_fails]
  cases h_eq : lsc.s_clearance.clears with
  | false => rfl
  | true => exact absurd (lsc.s_clearance.clears_sound.mp h_eq) lsc.clearance_fails_cert

/-- Canonical publication-mode failure: `allows_sorry` proof, `axiom_free` required.

    - `v_witness`: kernel genuinely elaborated the term (normal path)
    - `e_witness`: "sorryAx" is documented in `LeanGroundedRevocation`
    - `threshold_met = False`: allows_sorry does not satisfy axiom_free
    - `clearance_fails_cert = False.elim`: witnesses `¬False` -/
def canonical_sorry_publication_case (name : String) : LeanStandardCase :=
  { decl_name   := name,
    v_witness   := { decl_name         := name,
                     mode              := .kernel,
                     kernel_elaborated := true,
                     kernel_sound      := ⟨fun _ => rfl, fun _ => rfl⟩ },
    e_witness   := { relevant_failure    := .sorryAx,
                     documented_failures := [.sorryAx],
                     e_adequate          := true,
                     adequate_sound      := by decide },
    s_clearance := { deposit_level  := .allows_sorry,
                     required_level := .axiom_free,
                     threshold_met  := False,
                     clears         := false,
                     clears_sound   := ⟨Bool.noConfusion, False.elim⟩ },
    clearance_fails_cert := False.elim }

/-- Same proof, development-mode consumer: `allows_sorry` clears `allows_sorry`.
    `threshold_met` is `deposit_level = required_level` — a concrete enum equality,
    not `True`.  Both bridge directions close by `rfl`, consistent with the
    publication case which uses `Bool.noConfusion`/`False.elim`. -/
def canonical_sorry_dev_clearance : LeanStandardClearance :=
  { deposit_level  := .allows_sorry,
    required_level := .allows_sorry,
    threshold_met  := (.allows_sorry : LeanAxiomLevel) = .allows_sorry,
    clears         := true,
    clears_sound   := ⟨fun _ => rfl, fun _ => rfl⟩ }

/-- Relational S-failure at the kernel level.

    Same declaration. Same V (kernel_elaborated). Same E (sorryAx documented).
    Same axiom footprint.  Publication consumer: `¬threshold_met` (S-failure).
    Development consumer: `threshold_met = True` (clears).  What differs is the
    consuming agent's required threshold — outside EpArch's scope. -/
theorem lean_axiom_failure_is_relational (name : String) :
    lean_S_fails (canonical_sorry_publication_case name) = true ∧
    canonical_sorry_dev_clearance.threshold_met := by
  constructor
  · exact lean_standard_case_is_S_failure _
  · exact rfl

/-- Elaboration pattern for the sorry-closed-goal scenario.
    `testimony_only` in `LeanVacuousStandard` derives from
    `elab_pattern = .sorry_only`. -/
inductive ElabPattern where
  | sorry_only  -- proof closed solely by sorry; no independent kernel path
  | full_proof  -- main proof is complete (sorry may appear in subterms)
  deriving DecidableEq, Repr

/-- Absolute (void) S at the kernel level: `sorry ⊢ False`.

    E already documents `sorryTainted` as revocable in `LeanGroundedRevocation`
    (`witness_is_invalid`, `can_revoke`).  When S is solely "sorry closed it",
    both structural conditions (`e_documents_sorry` and `s_is_sorry_only`) are
    present in the fields — `lean_S_is_void` is witnessed structurally.

    `sorry_documented` derives from `LeanEWitness.no_relevant_gap`
    (`relevant_failure ∈ documented_failures`); `testimony_only` derives from
    `elab_pattern = .sorry_only`.

    EpArch records the field pattern. What consuming agents do with
    `lean_S_is_void` is outside the model's scope. -/
structure LeanVacuousStandard where
  decl_name              : String
  /-- E-witness: relevant failure (sorryAx) must be on the documented list. -/
  e_witness              : LeanEWitness
  /-- Structural cert: E documents the relevant failure at construction time. -/
  e_documents_sorry_cert : e_witness.e_adequate = true
  /-- How the proof was elaborated — the data backing the testimony condition. -/
  elab_pattern           : ElabPattern
  /-- Executable mirror: reflects `elab_pattern = .sorry_only`. -/
  s_is_sorry_only        : Bool
  /-- Sound bridge: the Bool must honestly reflect the pattern comparison. -/
  s_is_sorry_sound       : s_is_sorry_only = true ↔ elab_pattern = .sorry_only
  /-- Structural cert: S is sorry-only at construction time. -/
  s_is_sorry_only_cert   : s_is_sorry_only = true

/-- E documents the relevant failure iff it is on the documented list.
    Derived from `e_witness` data.
    `@[reducible]` makes this transparent to `decide` and definitional reduction. -/
@[reducible] def LeanVacuousStandard.sorry_documented (lvs : LeanVacuousStandard) : Prop :=
  lvs.e_witness.no_relevant_gap

/-- S is testimony-only iff the elaboration pattern is `sorry_only`.
    Derived from the pattern.
    `@[reducible]` makes this transparent to `decide` and definitional reduction. -/
@[reducible] def LeanVacuousStandard.testimony_only (lvs : LeanVacuousStandard) : Prop :=
  lvs.elab_pattern = .sorry_only

def lean_S_is_void (lvs : LeanVacuousStandard) : Prop :=
  lvs.testimony_only ∧ lvs.sorry_documented

/-- Void S is witnessed by the soundness bridges: `s_is_sorry_sound` and
    `adequate_sound` extract the Prop conditions from the Bool certs. -/
theorem lean_vacuous_standard_is_void (lvs : LeanVacuousStandard) :
    lean_S_is_void lvs :=
  ⟨lvs.s_is_sorry_sound.mp lvs.s_is_sorry_only_cert,
    lvs.e_witness.adequate_sound.mp lvs.e_documents_sorry_cert⟩
/-- Canonical void instance: a `sorry`-closed proof of `False`.
    `e_documents_sorry = true` is grounded in `LeanGroundedRevocation`:
    the same `.sorryTainted` constructor that makes `witness_is_invalid` fire
    is what S = "sorry closed it" refers to. -/
def canonical_sorry_false_case : LeanVacuousStandard :=
  { decl_name            := "sorry_closes_False",
    e_witness            := { relevant_failure    := .sorryAx,
                              documented_failures := [.sorryAx],
                              e_adequate          := true,
                              adequate_sound      := by decide },
    e_documents_sorry_cert := rfl,
    elab_pattern           := .sorry_only,
    s_is_sorry_only        := true,
    s_is_sorry_sound       := ⟨fun _ => rfl, fun _ => rfl⟩,
    s_is_sorry_only_cert   := rfl }

/-- Both kinds of S-failure, at the kernel level.

    Relational: same sorry-containing proof; one consuming agent's clearance
    fails, another's passes. S is a property of the claim; the threshold
    is a property of the consuming agent — outside EpArch's scope.

    Absolute/void: E + V together structurally witness `lean_S_is_void`.
    EpArch records both conditions in the fields; agent acceptance decisions
    are not modeled here. -/
theorem lean_S_failure_taxonomy (name : String) :
    lean_S_fails (canonical_sorry_publication_case name) = true ∧
    canonical_sorry_dev_clearance.threshold_met ∧
    lean_S_is_void canonical_sorry_false_case := by
  exact ⟨lean_standard_case_is_S_failure _, rfl,
        lean_vacuous_standard_is_void _⟩

/-- V and E evidence in a Lean S-failure: surfaces `mode = .kernel` and
    `relevant_failure ∈ documented_failures` directly from the canonical case. -/
theorem lean_s_failure_VE_data (name : String) :
    (canonical_sorry_publication_case name).v_witness.mode = .kernel ∧
    (canonical_sorry_publication_case name).e_witness.relevant_failure ∈
      (canonical_sorry_publication_case name).e_witness.documented_failures :=
  ⟨rfl, List.Mem.head _⟩


end EpArch.LeanKernelModel

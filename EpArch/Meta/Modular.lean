/-
EpArch/Meta/Modular.lean — Machine-Certified Modularity Meta-Theorem

Answers the question: "Is EpArch modular on its six operational constraints —
can you drop any constraint and have the remaining forcing theorems still hold?"

Scope: this file covers the six constraints in `Minimality.lean` only.
Health-goal modularity (∀-transport of SafeWithdrawal, ReliableExport, etc.)
is proved separately in `Meta/TheoremTransport.lean` and `Meta/Tier4Transport.lean`.

This file provides two pieces:

  (1) `PartialWellFormed W S` — a WellFormed type parameterized by a subset S of
      the six constraints. You only supply the biconditionals for the constraints
      you care about; the rest are not required.

  (2) `projection_valid S W` — the named target predicate: the conjunction of six
      guarded forcing implications, each guarded by "S selects this constraint."

  (3) `modular` — the universally-quantified meta-theorem:

        ∀ (S : ConstraintSubset) (W : WorkingSystem),
          PartialWellFormed W S → projection_valid S W

## Relationship to PartialWellFormed

  `PartialWellFormed W allConstraints` — all six biconditionals required,
  the strongest subset — is the natural replacement for the former `WellFormed`
  predicate (which has been removed).  Every existing `WellFormed`-gated proof
  can be re-stated as `PartialWellFormed W allConstraints`.

## What This Proves

  - You can remove constraint X by setting S.X := false.
  - `PartialWellFormed W S` with S.X = false requires nothing about X.
  - `modular` returns a guarded implication `false = true → ...` for X, which
    is vacuously true — the forcing theorem for X is not claimed.
  - The forcing theorems for all other constraints in S remain valid.

  This is a machine-certified proof, not a structural observation.
-/

import EpArch.Minimality

namespace EpArch.Meta.Modular

open EpArch


/-! ## Constraint Subset -/

/-- A subset of the six EpArch operational constraints, represented as a
    6-boolean vector. `true` = constraint included; `false` = dropped.

    Examples:
    - `allConstraints`  — all six included (recovers full WellFormed)
    - `noConstraints`   — none included (no forcing theorems claimed)
    - `⟨true, false, false, false, true, false⟩` — only distributed + coordination -/
structure ConstraintSubset where
  distributed    : Bool
  bounded_audit  : Bool
  export_across  : Bool
  adversarial    : Bool
  coordination   : Bool
  truth_pressure : Bool

/-- The full set of all six constraints. `PartialWellFormed W allConstraints` requires
    all six biconditionals — the strongest subset. -/
def allConstraints : ConstraintSubset := ⟨true, true, true, true, true, true⟩

/-- The empty subset. `PartialWellFormed W noConstraints` holds trivially. -/
def noConstraints : ConstraintSubset := ⟨false, false, false, false, false, false⟩


/-! ## Partial Well-Formedness -/

/-- `PartialWellFormed W S` is the fragment of `WellFormed W` required for
    the constraint subset S.

    For each constraint X:
    - If `S.X = true`,  the biconditional `handles_X W ↔ HasFeature_X W` is required.
    - If `S.X = false`, nothing is required for X.

    Requiring all six (S = allConstraints) is the strongest form.

    To "drop" constraint X from a product deployment: set S.X := false.
    The type system then stops requiring the X biconditional. -/
structure PartialWellFormed (W : WorkingSystem) (S : ConstraintSubset) : Prop where
  /-- Distributed agents ↔ HasBubbles (only required when S.distributed = true) -/
  wf_distributed    : S.distributed    = true → (handles_distributed_agents W ↔ HasBubbles W)
  /-- Bounded audit ↔ HasTrustBridges (only required when S.bounded_audit = true) -/
  wf_bounded_audit  : S.bounded_audit  = true → (handles_bounded_audit W ↔ HasTrustBridges W)
  /-- Export ↔ HasHeaders (only required when S.export_across = true) -/
  wf_export         : S.export_across  = true → (handles_export W ↔ HasHeaders W)
  /-- Adversarial ↔ HasRevocation (only required when S.adversarial = true) -/
  wf_adversarial    : S.adversarial    = true → (handles_adversarial W ↔ HasRevocation W)
  /-- Coordination ↔ HasBank (only required when S.coordination = true) -/
  wf_coordination   : S.coordination   = true → (handles_coordination W ↔ HasBank W)
  /-- Truth pressure ↔ HasRedeemability (only required when S.truth_pressure = true) -/
  wf_truth_pressure : S.truth_pressure = true → (handles_truth_pressure W ↔ HasRedeemability W)


/-! ## Trivial instance: empty subset -/

/-- `PartialWellFormed W noConstraints` holds for every system. -/
theorem partial_no_constraints (W : WorkingSystem) : PartialWellFormed W noConstraints :=
  { wf_distributed    := fun h => absurd h (by decide)
    wf_bounded_audit  := fun h => absurd h (by decide)
    wf_export         := fun h => absurd h (by decide)
    wf_adversarial    := fun h => absurd h (by decide)
    wf_coordination   := fun h => absurd h (by decide)
    wf_truth_pressure := fun h => absurd h (by decide) }


/-! ## The Modularity Target Predicate -/

/-- `projection_valid S W` — the named target of the modularity meta-theorem.

    For each constraint X in S (i.e., S.X = true), asserts that W satisfies
    the forcing implication for X. Constraints outside S are not claimed.

    This is a real exported definition, not just descriptive wording, so that
    downstream code (e.g. configuration engines, product-profile checkers) can
    reference the target by name. -/
def projection_valid (S : ConstraintSubset) (W : WorkingSystem) : Prop :=
  (S.distributed    = true → handles_distributed_agents W → HasBubbles W) ∧
  (S.bounded_audit  = true → handles_bounded_audit W → HasTrustBridges W) ∧
  (S.export_across  = true → handles_export W → HasHeaders W) ∧
  (S.adversarial    = true → handles_adversarial W → HasRevocation W) ∧
  (S.coordination   = true → handles_coordination W → HasBank W) ∧
  (S.truth_pressure = true → handles_truth_pressure W → HasRedeemability W)


/-! ## The Modularity Meta-Theorem -/

/-- **`modular` — the EpArch constraint-modularity meta-theorem.**

    For any subset S of the six constraints, any system with `PartialWellFormed W S`
    satisfies `projection_valid S W`: the forcing theorem holds for each constraint
    in S, and no claim is made about constraints outside S.

    Usage:
    - To drop constraint X: set S.X := false. The X-conjunct in `projection_valid`
      becomes `false = true → ...`, which is vacuously true.
    - The remaining conjuncts are live forcing implications backed by the
      biconditionals in `PartialWellFormed W S`. -/
theorem modular (S : ConstraintSubset) (W : WorkingSystem)
    (pwf : PartialWellFormed W S) : projection_valid S W :=
  ⟨fun hd h => (pwf.wf_distributed    hd).mp h,
   fun hb h => (pwf.wf_bounded_audit   hb).mp h,
   fun he h => (pwf.wf_export          he).mp h,
   fun ha h => (pwf.wf_adversarial     ha).mp h,
   fun hc h => (pwf.wf_coordination    hc).mp h,
   fun ht h => (pwf.wf_truth_pressure  ht).mp h⟩


end EpArch.Meta.Modular

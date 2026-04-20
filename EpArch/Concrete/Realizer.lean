/-
EpArch.Concrete.Realizer — System Realizer Interface

This module defines a minimal "system realizer" type: an object that
witnesses the satisfiability of the commitment bundle.

## Purpose

The Realizer is NOT a claim about "what systems look like."
It's a type-level packaging of the existence proof: there exists
at least one concrete model satisfying all core commitments.

## Design

- Thin interface: only fields we can populate from existing code
- Commitments as Prop field, not definitional equalities
- ConcreteRealizer witnesses via the EpArch.Concrete module family
- SuccessfulSystem bundles WorkingSystem + StructurallyForced + SatisfiesAllProperties

-/

import EpArch.Concrete.WorkingSystem
import EpArch.Minimality

namespace EpArch

/-! ## Realizer Interface (Commitment Bundle) -/

/-- A minimal "system realizer" object: bundles a proof that the
    objective/commitment bundle is satisfiable.

    This is thin by design—we only include what the concrete model
    already provides. The `commitments` field holds the proof that
    all core commitments are jointly satisfiable. -/
structure Realizer where
  /-- Proof that the core commitments are jointly satisfiable.
      The type is exactly what `all_commitments_satisfiable` proves. -/
  commitments :
    -- Commitment 1: Traction/Authorization split
    (∃ a B P, EpArch.ConcreteModel.c_certainty a P ∧ ¬EpArch.ConcreteModel.c_knowledge B P) ∧
    (∃ a B P, EpArch.ConcreteModel.c_knowledge B P ∧ ¬EpArch.ConcreteModel.c_certainty a P) ∧
    -- Commitment 2: Innovation and coordination are in genuine tension
    (∃ G : EpArch.ConcreteModel.CGlobalLedger, EpArch.ConcreteModel.c_supports_innovation G ∧ ¬EpArch.ConcreteModel.c_supports_coordination G) ∧
    -- Commitment 3: S/E/V factorization exists
    (∃ d : EpArch.ConcreteModel.CDeposit, d.S > 0 ∧ d.E.length > 0 ∧ d.V.length > 0) ∧
    -- Commitment 4: Consensus without redeemability is possible
    (∃ B d, EpArch.ConcreteModel.c_consensus B d.claim ∧ ¬EpArch.ConcreteModel.c_redeemable d) ∧
    -- Commitment 5: Export gating is required (ungated → revalidation or trust bridge)
    (∃ B1 B2 d, EpArch.ConcreteModel.c_ungated_export B1 B2 d →
      (EpArch.ConcreteModel.c_revalidated B2 d ∨ EpArch.ConcreteModel.c_trust_bridge B1 B2)) ∧
    -- Commitment 6: Repair loop with field localization exists
    (∃ (_ : EpArch.ConcreteModel.CDeposit) (c : EpArch.ConcreteModel.CChallenge), c.field ∈ ["S", "E", "V", "τ"]) ∧
    -- Commitment 7: Header-stripped claims lose diagnosability
    (∃ d : EpArch.ConcreteModel.CDeposit, EpArch.ConcreteModel.c_header_stripped d ∧ d.E.length = 0) ∧
    -- Commitment 8: Fresh and stale deposits differ
    (∃ d1 d2 t, EpArch.ConcreteModel.c_fresh d1 t ∧ EpArch.ConcreteModel.c_stale d2 t)


/-! ## Concrete Witness -/

/-- Canonical witness: the concrete ledger model already in the repo.

    This is a trivial wrapper—the work was done in EpArch.Concrete.Commitments.
    The Realizer just packages it into a stable type-level object. -/
def ConcreteRealizer : Realizer :=
  { commitments := EpArch.ConcreteModel.all_commitments_satisfiable }


/-! ## SuccessfulSystem Interface (Working System Bundle) -/

/-- A "successful working system": a WorkingSystem that is structurally forced
    and satisfies the full success bundle used by Minimality.

    This bundles:
    - A WorkingSystem
    - Proof it's StructurallyForced (capability → architectural feature)
    - Proof it satisfies all eight operational properties

    The existence of such a system is the "non-vacuity of success" claim. -/
structure SuccessfulSystem where
  /-- The underlying working system -/
  W : WorkingSystem
  /-- System is structurally forced (capability flags → spec features) -/
  sf : StructurallyForced W
  /-- System satisfies all eight operational properties -/
  sat : SatisfiesAllProperties W

/-- Canonical witness: the concrete working system.

    This bundles ConcreteWorkingSystem with its structural forcing and
    satisfaction proofs into a single object. -/
def ConcreteSuccessfulSystem : SuccessfulSystem where
  W := EpArch.ConcreteInstance.ConcreteWorkingSystem
  sf := EpArch.ConcreteInstance.concrete_structurally_forced
  sat := EpArch.ConcreteInstance.concrete_satisfies_all_properties

end EpArch

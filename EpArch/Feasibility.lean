/-
EpArch.Feasibility — Existence Under Constraints / Non-Vacuity Theorems

This module answers the existence question: are the constraint and commitment
bundles satisfiable, and does a working system exist that meets them?  It does
not carry the forcing story — that lives in EpArch.WorldBridges.

## Division of Labor

| Module              | Job                                                            |
|---------------------|----------------------------------------------------------------|
| EpArch.WorldBridges | Forcing theorems: W_* bundles → containsBankPrimitives         |
| EpArch.Feasibility  | Existence witnesses: ∃ W satisfying constraints + primitives   |

## Headline Theorems

- `world_bundles_feasible`: the three W_* bundles are jointly satisfiable
- `commitments_feasible`: the 8 architectural commitments are jointly satisfiable
- `existence_under_constraints_structural`: ∃ W, StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W
- `existence_under_constraints_embedding`: same, via ForcingEmbedding path

## Claim Budget

**Buys:**
- "The constraint+objective package is consistent (nonempty)"
- "There exists at least one working system meeting the success bundle"
- Non-vacuity for world bundles, commitments, and existence

**Does NOT buy:**
- The forcing direction (W_* → containsBankPrimitives) — see EpArch.WorldBridges
- "The real world literally is this model"
- "Uniqueness" (many realizations can exist)

-/

import EpArch.WorldWitness
import EpArch.Concrete.Realizer
import EpArch.Minimality
import EpArch.Convergence

namespace EpArch.Feasibility

/-! ## World Constraint Feasibility -/

/-- World constraint bundles are satisfiable (non-vacuity).

    Uses the WitnessCtx from EpArch.WorldWitness to show that the
    W_* bundles are jointly satisfiable.

    Note: We use `@WorldCtx.{0}` to fix the universe level to match WitnessCtx. -/
theorem world_bundles_feasible :
    ∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability := by
  refine ⟨EpArch.WorldWitness.WitnessCtx, ?_⟩
  exact EpArch.WorldWitness.all_bundles_satisfiable


/-! ## Commitment Feasibility -/

/-- Commitments are jointly satisfiable (named alias for external reference).

    This re-exports `all_commitments_satisfiable` under a consistent name. -/
theorem commitments_feasible :
    -- Commitment 1: Traction/Authorization split
    (∃ a B P, ConcreteModel.c_certainty a P ∧ ¬ConcreteModel.c_knowledge B P) ∧
    (∃ a B P, ConcreteModel.c_knowledge B P ∧ ¬ConcreteModel.c_certainty a P) ∧
    -- Commitment 2: Innovation and coordination are in genuine tension
    (∃ G, ConcreteModel.c_supports_innovation G ∧ ¬ConcreteModel.c_supports_coordination G) ∧
    -- Commitment 3: S/E/V factorization exists
    (∃ d : ConcreteModel.CDeposit, d.S > 0 ∧ d.E.length > 0 ∧ d.V.length > 0) ∧
    -- Commitment 4: Consensus without redeemability
    (∃ B d, ConcreteModel.c_consensus B d.claim ∧ ¬ConcreteModel.c_redeemable d) ∧
    -- Commitment 5: Export gating is required (ungated → revalidation or trust bridge)
    (∃ B1 B2 d, ConcreteModel.c_ungated_export B1 B2 d →
      (ConcreteModel.c_revalidated B2 d ∨ ConcreteModel.c_trust_bridge B1 B2)) ∧
    -- Commitment 6: Repair loop
    (∃ (_ : ConcreteModel.CDeposit) (c : ConcreteModel.CChallenge), c.field ∈ ["S", "E", "V", "τ"]) ∧
    -- Commitment 7: Header-stripped loses diagnosability
    (∃ d : ConcreteModel.CDeposit, ConcreteModel.c_header_stripped d ∧ d.E.length = 0) ∧
    -- Commitment 8: Fresh/stale differ
    (∃ d1 d2 t, ConcreteModel.c_fresh d1 t ∧ ConcreteModel.c_stale d2 t) :=
  ConcreteModel.all_commitments_satisfiable

/-- Non-vacuity: a Realizer exists. -/
theorem realizer_exists : Nonempty EpArch.Realizer := ⟨EpArch.ConcreteRealizer⟩


/-! ## Structural Convergence (Existence)

    These theorems prove existence: there is at least one concrete working system
    that is structurally forced, satisfies all properties, and contains Bank
    primitives.  For the forcing direction (W_* bundles → primitives), see
    EpArch.WorldBridges. -/
/-- Headline theorem (structural version): the concrete model is
    structurally forced, satisfies all properties, and contains Bank
    primitives — without going through WellFormed. -/
theorem existence_under_constraints_structural :
    ∃ W : WorkingSystem,
      StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W :=
  ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem,
   EpArch.ConcreteInstance.concrete_structurally_forced,
   EpArch.ConcreteInstance.concrete_satisfies_all_properties,
   EpArch.ConcreteInstance.concrete_structural_convergence⟩

/-- Headline theorem (embedding version): full chain from
    `ForcingEmbedding` through `StructurallyForced` to convergence. -/
theorem existence_under_constraints_embedding :
    ∃ W : WorkingSystem,
      ForcingEmbedding W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W :=
  ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem,
   EpArch.ConcreteInstance.concrete_forcing_embedding,
   EpArch.ConcreteInstance.concrete_satisfies_all_properties,
   EpArch.ConcreteInstance.concrete_structural_convergence⟩

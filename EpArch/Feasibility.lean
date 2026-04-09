/-
EpArch/Feasibility.lean — Existence Under Constraints / Non-Vacuity Theorems

This module packages existing witnesses into "system class is nonempty"
statements, providing non-vacuity and existence proofs for
the existence-under-constraints claim.

## Purpose

Natural objections to an epistemic systems framework:
- "Are these constraints even consistent? Maybe they're vacuous."
- "Does a system satisfying these properties actually exist?"

This module answers: Yes. The constraint bundles are satisfiable,
working systems exist, and success forces Bank primitives.

## Headline Theorem

`existence_under_constraints`: There exists a WorkingSystem that is
WellFormed, satisfies all operational properties, AND contains Bank primitives.

This packages non-vacuity + forced primitives into one citable result.

## Claim Budget

**Buys:**
- "The constraint+objective package is consistent (nonempty)"
- "There exists at least one working system meeting the success bundle"
- "Success forces Bank primitives" (via Minimality)

**Does NOT buy:**
- "The real world literally is this model"
- "Uniqueness" (many realizations can exist)
- "Abduction/inference from observed O to existence of S"

-/

import EpArch.WorldWitness
import EpArch.Realizer
import EpArch.Minimality

namespace EpArch.Feasibility

/-! ## World Constraint Feasibility -/

/-- World constraint bundles are satisfiable (non-vacuity).

    Uses the WitnessCtx from WorldWitness.lean to show that the
    W_* bundles are jointly satisfiable.

    Note: We use `@WorldCtx.{0}` to fix the universe level to match WitnessCtx. -/
theorem world_bundles_feasible :
    ∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability := by
  refine ⟨EpArch.WorldWitness.WitnessCtx, ?_⟩
  exact EpArch.WorldWitness.all_bundles_satisfiable

/-- Alias for backward compatibility -/
theorem constraints_feasible :
    ∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability :=
  world_bundles_feasible


/-! ## Commitment Feasibility -/

/-- Commitments are jointly satisfiable (named alias for external reference).

    This re-exports `all_commitments_satisfiable` under a consistent name. -/
theorem commitments_feasible :
    -- Commitment 1: Traction/Authorization split
    (∃ a B P, ConcreteModel.c_certainty a P ∧ ¬ConcreteModel.c_knowledge B P) ∧
    (∃ a B P, ConcreteModel.c_knowledge B P ∧ ¬ConcreteModel.c_certainty a P) ∧
    -- Commitment 2: No global ledger supports both
    (∃ G, ¬(ConcreteModel.c_supports_innovation G ∧ ConcreteModel.c_supports_coordination G)) ∧
    -- Commitment 3: S/E/V factorization exists
    (∃ d : ConcreteModel.CDeposit, d.S > 0 ∧ d.E.length > 0 ∧ d.V.length > 0) ∧
    -- Commitment 4: Consensus without redeemability
    (∃ B d, ConcreteModel.c_consensus B d.claim ∧ ¬ConcreteModel.c_redeemable d) ∧
    -- Commitment 5: Export gating
    True ∧
    -- Commitment 6: Repair loop
    (∃ _d c : ConcreteModel.CChallenge, c.field ∈ ["S", "E", "V", "τ"]) ∧
    -- Commitment 7: Header-stripped loses diagnosability
    (∃ d : ConcreteModel.CDeposit, ConcreteModel.c_header_stripped d ∧ d.E.length = 0) ∧
    -- Commitment 8: Fresh/stale differ
    (∃ d1 d2 t, ConcreteModel.c_fresh d1 t ∧ ConcreteModel.c_stale d2 t) :=
  ConcreteModel.all_commitments_satisfiable

/-- Objective bundle is satisfiable: there exists at least one Realizer.

    The Realizer packages the proof that all core commitments
    are simultaneously satisfiable. -/
theorem objectives_feasible : ∃ _ : EpArch.Realizer, True := by
  exact ⟨EpArch.ConcreteRealizer, trivial⟩


/-! ## System-Level Feasibility -/

/-- There exists at least one successful working system.

    This witnesses that the success bundle (WellFormed + SatisfiesAllProperties)
    is non-empty—there's at least one system that achieves it. -/
theorem success_feasible :
    ∃ W : WorkingSystem, WellFormed W ∧ SatisfiesAllProperties W := by
  refine ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem, ?_, ?_⟩
  · exact EpArch.ConcreteInstance.concrete_wellformed
  · exact EpArch.ConcreteInstance.concrete_satisfies_all_properties


/-! ## Minimality Alias -/

/-- Paper-facing name: success forces Bank primitives.

    Any working system that is WellFormed and satisfies all operational
    properties MUST contain Bank primitives. This is the minimality /
    forced-primitives direction. -/
theorem goals_force_bank_primitives :
    ∀ W : WorkingSystem, WellFormed W → SatisfiesAllProperties W → containsBankPrimitives W :=
  convergence_under_constraints'


/-! ## Headline Theorem: Existence Under Constraints -/

/-- Headline theorem: existence-under-constraints (non-vacuity + forced primitives).

    This headline theorem combines three results:
    - There EXISTS a working system (non-vacuity)
    - That system is WellFormed and satisfies all properties (success)
    - That system contains Bank primitives (forced by minimality)

    Together: the success bundle is non-empty, and success forces Bank primitives. -/
theorem existence_under_constraints :
    ∃ W : WorkingSystem,
      WellFormed W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W := by
  refine ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem, ?_⟩
  refine ⟨EpArch.ConcreteInstance.concrete_wellformed,
          EpArch.ConcreteInstance.concrete_satisfies_all_properties, ?_⟩
  exact goals_force_bank_primitives EpArch.ConcreteInstance.ConcreteWorkingSystem
    EpArch.ConcreteInstance.concrete_wellformed
    EpArch.ConcreteInstance.concrete_satisfies_all_properties


/-! ## Joint Feasibility (Legacy) -/

/-- Joint feasibility: world constraints and objectives are both nonempty.

    Kept for backward compatibility. The stronger `existence_under_constraints`
    is the preferred reference. -/
theorem joint_feasible :
    (∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability) ∧
    (∃ _ : EpArch.Realizer, True) := by
  exact ⟨constraints_feasible, objectives_feasible⟩


/-! ## Structural Convergence -/

/-- Paper-facing name (structural version): success forces Bank primitives
    without depending on WellFormed biconditionals. -/
theorem structural_goals_force_bank_primitives :
    ∀ W : WorkingSystem,
      StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W :=
  convergence_structural

/-- Headline theorem (structural version): the concrete model is
    structurally forced, satisfies all properties, and contains Bank
    primitives — without going through WellFormed. -/
theorem existence_under_constraints_structural :
    ∃ W : WorkingSystem,
      StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W := by
  refine ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem, ?_⟩
  refine ⟨EpArch.ConcreteInstance.concrete_structurally_forced,
          EpArch.ConcreteInstance.concrete_satisfies_all_properties, ?_⟩
  exact convergence_structural EpArch.ConcreteInstance.ConcreteWorkingSystem
    EpArch.ConcreteInstance.concrete_structurally_forced
    EpArch.ConcreteInstance.concrete_satisfies_all_properties

/-- Headline theorem (embedding version): full chain from
    `ForcingEmbedding` through `StructurallyForced` to convergence.
    This is the strongest form — the design judgment is localised
    in `concrete_forcing_embedding`, and the derivation is mechanical. -/
theorem existence_under_constraints_embedding :
    ∃ W : WorkingSystem,
      ForcingEmbedding W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W :=
  ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem,
   EpArch.ConcreteInstance.concrete_forcing_embedding,
   EpArch.ConcreteInstance.concrete_satisfies_all_properties,
   EpArch.ConcreteInstance.concrete_structural_convergence⟩

end EpArch.Feasibility

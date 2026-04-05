/-
EpArch/World.lean — World Layer for Obligation Theorems

This module provides the minimal substrate for converting mechanism axioms
into conditional obligation theorems of the form `W_assumption → mechanism_claim`.

## Design Philosophy (Post-WorldCtx Refactor)

World assumptions are NOT asserted as true. They parameterize obligation theorems.
The semantic content is now in WorldCtx.lean, which provides a parametric signature.

This module:
1. Re-exports WorldCtx type for backward compatibility
2. Maintains concrete local types for legacy code (marked deprecated)
3. Provides a canonical LocalCtx witness for non-vacuity

## Migration Guide

Old code:  `import EpArch.World` → uses local `World`, `Truth := True`
New code:  `import EpArch.WorldCtx` → uses `(C : WorldCtx)` parameter

The concrete stubs (Truth := True, etc.) are DEPRECATED.
Use WorldCtx parametric theorems for new work.

-/

import EpArch.Basic
import EpArch.WorldCtx

namespace EpArch.World

universe u

/-! ## Re-exports from WorldCtx -/

-- Core signature is now in WorldCtx
export EpArch (WorldCtx)

/-! ## Deprecated Local Types

These concrete types exist for backward compatibility.
New code should use (C : WorldCtx) parameters instead.
-/

/-- [DEPRECATED] Local concrete World type.
    Use WorldCtx.World parameter instead. -/
inductive World where
  | mk : Nat → World
  deriving DecidableEq, Repr, Inhabited

/-- [DEPRECATED] PropLike alias.
    Use EpArch.Claim directly or WorldCtx.Claim parameter instead.

    This alias exists only for backward compatibility. All new code should
    use EpArch.Claim (the canonical claim type defined in Basic.lean).

    The type parameter pattern in modules like Bank.lean:
      `variable {PropLike Standard ErrorModel Provenance : Type u}`
    should be understood as "for any PropLike instantiated to EpArch.Claim". -/
abbrev PropLike := EpArch.Claim

/-- [DEPRECATED] Local concrete Obs type.
    Use WorldCtx.Obs parameter instead. -/
inductive Obs where
  | mk : Nat → Obs
  deriving DecidableEq, Repr, Inhabited

/-! ## Deprecated Stub Semantics

These are the concrete stub implementations that should NOT be used
for obligation theorems. They exist only for legacy compatibility.

Use WorldCtx parametric versions for new code.
-/

/-- [DEPRECATED] Stub truth predicate.
    Use WorldCtx.Truth parameter instead. -/
def Truth (_ : World) (_ : PropLike) : Prop := True

/-- [DEPRECATED] Stub utterance predicate.
    Use WorldCtx.Utter parameter instead. -/
def Utter (_ : EpArch.Agent) (_ : PropLike) : Prop := True

/-- [DEPRECATED] Stub observation function.
    Use WorldCtx.obs parameter instead. -/
def obs (_ : World) : Obs := Obs.mk 0

/-- [DEPRECATED] Stub verification predicate.
    Use WorldCtx.VerifyWithin parameter instead. -/
def VerifyWithin (_ : World) (_ : PropLike) (_ : Nat) : Prop := True

/-- [DEPRECATED] Stub effective time.
    Use WorldCtx.effectiveTime parameter instead. -/
def effectiveTime (_ : World) : Nat := 100

/-- [DEPRECATED] Stub required steps.
    Use WorldCtx.RequiresSteps instead. -/
def requiredSteps (_ : PropLike) : Nat := 1


/-! ## Derived Concepts (Deprecated - Use WorldCtx versions) -/

/-- [DEPRECATED] Local Lie definition.
    Use WorldCtx.Lie instead. -/
def Lie (w : World) (a : EpArch.Agent) (P : PropLike) : Prop :=
  Utter a P ∧ ¬Truth w P

/-- [DEPRECATED] Local can_lie definition.
    Use WorldCtx.can_lie instead. -/
def can_lie (a : EpArch.Agent) : Prop :=
  ∃ w P, Lie w a P

/-- [DEPRECATED] Local PartialObs definition.
    Use WorldCtx.PartialObs instead. -/
def PartialObs (w0 w1 : World) : Prop :=
  obs w0 = obs w1

/-- [DEPRECATED] Local NotDeterminedByObs definition.
    Use WorldCtx.NotDeterminedByObs instead. -/
def NotDeterminedByObs (P : PropLike) : Prop :=
  ∃ w0 w1, PartialObs w0 w1 ∧ (Truth w0 P ↔ ¬Truth w1 P)

/-- [DEPRECATED] Local RequiresSteps definition.
    Use WorldCtx.RequiresSteps instead. -/
def RequiresSteps (w : World) (P : PropLike) (k : Nat) : Prop :=
  ∀ t, t < k → ¬VerifyWithin w P t


/-! ## World Assumption Bundles (Deprecated - Use WorldCtx versions)

These local bundles use the stub semantics and are deprecated.
Use WorldCtx.W_* bundles for new code.
-/

/-- [DEPRECATED] Bundle for "lies are possible" assumption.
    Use WorldCtx.W_lies_possible instead. -/
structure W_lies_possible where
  /-- There exist false propositions -/
  some_false : ∃ w P, ¬Truth w P
  /-- Agents can utter any proposition -/
  unrestricted_utterance : ∀ a P, Utter a P

/-- [DEPRECATED] Bundle for "verification is bounded" assumption.
    Use WorldCtx.W_bounded_verification instead. -/
structure W_bounded_verification where
  /-- Some propositions require significant verification effort -/
  verification_has_cost : ∃ P k, k > 0 ∧ ∀ w, RequiresSteps w P k

/-- [DEPRECATED] Bundle for "observations underdetermine truth" assumption.
    Use WorldCtx.W_partial_observability instead. -/
structure W_partial_observability where
  /-- Some truths are not determined by observations -/
  obs_underdetermines : ∃ P, NotDeterminedByObs P


/-! ## Legacy Theorems (Deprecated - Use WorldCtx versions)

These theorems use stub semantics and are deprecated.
For new code, use WorldCtx.lie_possible_of_W etc.
-/

/-- [DEPRECATED] Theorem: Lying is structurally possible under W_lies_possible.
    Use WorldCtx.lie_possible_of_W instead. -/
theorem lie_possible_of_W (W : W_lies_possible) :
    ∃ w a P, Lie w a P := by
  have ⟨w, P, h_false⟩ := W.some_false
  exact ⟨w, EpArch.Agent.mk 0, P, W.unrestricted_utterance _ _, h_false⟩

/-- [DEPRECATED] Theorem: Can_lie holds for all agents under W_lies_possible.
    Use WorldCtx.all_agents_can_lie_of_W instead. -/
theorem all_agents_can_lie_of_W (W : W_lies_possible) (a : EpArch.Agent) :
    can_lie a := by
  have ⟨w, P, h_false⟩ := W.some_false
  exact ⟨w, P, W.unrestricted_utterance _ _, h_false⟩

/-- [DEPRECATED] Theorem: Bounded audit fails when time is insufficient.
    Use WorldCtx.bounded_audit_fails instead. -/
theorem bounded_audit_fails (w : World) (P : PropLike) (k t : Nat) :
    RequiresSteps w P k → t < k → ¬VerifyWithin w P t := by
  intro h_requires h_lt
  exact h_requires t h_lt


/-! ## Obligation Theorem Pattern

Generic pattern: mechanism claims become conditional on world assumptions.

Old style (axiom):
  axiom mechanism_X : claim_X

New style (obligation theorem):
  theorem mechanism_X_of_W : W_X → claim_X

This makes the assumption explicit and auditable.

NOTE: The WorldCtx versions of these bundles and theorems are now canonical.
See WorldCtx.lean for parametric versions.
-/

/-- [DEPRECATED] Example cost asymmetry bundle.
    Use WorldCtx.W_asymmetric_costs instead. -/
structure W_asymmetric_costs where
  export_cost : Nat
  defense_cost : Nat
  asymmetry : export_cost < defense_cost

/-- [DEPRECATED] Example cost asymmetry theorem.
    Use WorldCtx.cost_asymmetry_of_W instead. -/
theorem cost_asymmetry_of_W (W : W_asymmetric_costs) :
    W.export_cost < W.defense_cost :=
  W.asymmetry


/-! ## LocalCtx: Deprecated Local Model as WorldCtx

This provides a WorldCtx instance using the deprecated local types,
allowing legacy code to interoperate with new WorldCtx-parametric code.
-/

/-- The deprecated local model as a WorldCtx.
    NOTE: This uses stub semantics and should not be relied upon for proofs. -/
def LocalCtx : EpArch.WorldCtx where
  World := World
  Agent := EpArch.Agent
  Claim := PropLike
  Obs := Obs
  Truth := Truth
  Utter := Utter
  obs := obs
  VerifyWithin := VerifyWithin
  effectiveTime := effectiveTime
  world_inhabited := ⟨World.mk 0⟩
  agent_inhabited := ⟨EpArch.Agent.mk 0⟩
  claim_inhabited := ⟨EpArch.Claim.mk 0⟩


end EpArch.World

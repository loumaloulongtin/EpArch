/-
EpArch/WorldWitness.lean — Nontrivial Witness Model for WorldCtx

This module provides a concrete instantiation of WorldCtx with nontrivial
semantics, proving that the W_* bundles are satisfiable (not vacuous).

## Purpose

The witness model is NOT a claim about "how the real world works."
It's a satisfiability proof: the axiom bundles we use in obligation
theorems are consistent—there exists at least one model satisfying them.

## Design

- World := Bool (two worlds: true-world and false-world)
- Claim := Bool (two claims: the claim and its negation)
- Truth w P := (w = P) — claim is true iff world matches
- Obs := Unit (all worlds look the same — maximal underdetermination)
- Agent := Unit (single agent suffices for witnesses)
- VerifyWithin w P t := t ≥ 1 — verification takes at least 1 step
- Utter is always true — agents can say anything

-/

import EpArch.WorldCtx

namespace EpArch.WorldWitness

/-! ## Witness Context Definition -/

/-- WitnessCtx: a nontrivial WorldCtx with Bool-valued worlds and claims.

    Key properties:
    - Truth is non-constant (depends on world/claim match)
    - Verification has cost (requires at least 1 step)
    - Observations underdetermine truth (all worlds look the same)
    - Lies are possible (can utter false claims) -/
def WitnessCtx : EpArch.WorldCtx where
  World := Bool
  Agent := Unit  -- single agent suffices for witnesses
  Claim := Bool
  Obs := Unit    -- all worlds look the same

  -- Truth: claim is true iff world matches claim value
  Truth := fun w P => w = P

  -- Utterance: agents can say anything
  Utter := fun _ _ => True

  -- Observation: constant (maximal underdetermination)
  obs := fun _ => ()

  -- Verification: requires at least 1 step
  VerifyWithin := fun _ _ t => t ≥ 1

  -- Effective time: constant (not used in witness proofs)
  effectiveTime := fun _ => 10

  -- Inhabitants
  world_inhabited := ⟨true⟩
  agent_inhabited := ⟨()⟩
  claim_inhabited := ⟨true⟩


/-! ## Bundle Satisfiability Proofs -/

/-- W_lies_possible is satisfiable in WitnessCtx.

    Proof: In WitnessCtx, Truth w P = (w = P).
    So Truth false true = (false = true) = False.
    Hence ¬Truth false true, and agents can utter anything. -/
theorem holds_W_lies_possible : WitnessCtx.W_lies_possible where
  some_false := ⟨false, true, fun h => Bool.noConfusion h⟩
  unrestricted_utterance := fun _ _ => trivial

/-- W_bounded_verification is satisfiable in WitnessCtx.

    Proof: In WitnessCtx, VerifyWithin w P t = (t ≥ 1).
    So RequiresSteps w P 1 = (∀ t, t < 1 → ¬(t ≥ 1)).
    For t = 0: 0 < 1 and ¬(0 ≥ 1), so this holds. -/
theorem holds_W_bounded_verification : WitnessCtx.W_bounded_verification where
  verification_has_cost := ⟨true, 1, by decide, fun _ => by
    simp only [EpArch.WorldCtx.RequiresSteps, WitnessCtx]
    intro t h_lt h_ge
    -- t < 1 means t = 0, but t ≥ 1 contradicts
    cases t with
    | zero => exact Nat.not_succ_le_zero 0 h_ge
    | succ n => exact Nat.not_lt_zero n (Nat.lt_of_succ_lt_succ h_lt)⟩

/-- W_partial_observability is satisfiable in WitnessCtx.

    Proof: In WitnessCtx, obs w = () for all w.
    So PartialObs true false holds (both map to ()).
    And Truth true true = (true = true) = True
    And Truth false true = (false = true) = False
    Hence NotDeterminedByObs true holds. -/
theorem holds_W_partial_observability : WitnessCtx.W_partial_observability where
  obs_underdetermines := ⟨true, true, false, rfl, by
    -- Need: (true = true) ↔ ¬(false = true)
    -- Both sides reduce to True, so this is True ↔ True
    simp only [WitnessCtx]
    constructor
    · intro _; exact fun h => nomatch h
    · intro _; trivial⟩


/-! ## Combined Witness

We can combine bundles to show they're jointly satisfiable. -/

/-- All three core bundles are jointly satisfiable. -/
theorem all_bundles_satisfiable :
    Nonempty WitnessCtx.W_lies_possible ∧
    Nonempty WitnessCtx.W_bounded_verification ∧
    Nonempty WitnessCtx.W_partial_observability :=
  ⟨⟨holds_W_lies_possible⟩, ⟨holds_W_bounded_verification⟩, ⟨holds_W_partial_observability⟩⟩


/-! ## Derived Theorem Instantiation

The generic theorems from WorldCtx can be instantiated at WitnessCtx. -/

/-- Lies are possible in WitnessCtx. -/
example : ∃ w a P, WitnessCtx.Lie w a P :=
  EpArch.WorldCtx.lie_possible_of_W WitnessCtx holds_W_lies_possible

/-- All agents can lie in WitnessCtx. -/
example (a : Unit) : WitnessCtx.can_lie a :=
  EpArch.WorldCtx.all_agents_can_lie_of_W WitnessCtx holds_W_lies_possible a


end EpArch.WorldWitness

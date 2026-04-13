/-
EpArch/Semantics/LTS.lean — Labeled Transition System Semantics

Generic LTS definitions used for revision safety proofs.
The EpArch-specific instantiation is in Semantics/StepSemantics.lean.

## Purpose

Provide the semantic foundation for revision safety theorems:
1. Generic LTS structure (State, Action, Step)
2. Trace semantics (reflexive-transitive closure)
3. Refinement as trace inclusion
4. Safety property preservation

This module provides proved infrastructure, not placeholders.
-/

namespace EpArch.LTS

universe u v

/-! ## Generic LTS Structure

A labeled transition system is defined by:
- State type
- Action (label) type
- Step relation: State → Action → State → Prop
-/

/-- Generic LTS: a labeled transition system. -/
structure LTS (State : Type u) (Action : Type v) where
  /-- Transition relation -/
  Step : State → Action → State → Prop

variable {State : Type u} {Action : Type v}

/-! ## Trace Semantics

A trace is a finite sequence of steps from s to s'.
This is the reflexive-transitive closure of Step.
-/

/-- Trace: sequence of steps from s to s' in LTS L. -/
inductive Trace (L : LTS State Action) : State → State → Prop where
  /-- Empty trace: s reaches s in zero steps (reflexivity). -/
  | nil : (s : State) → Trace L s s
  /-- Single step followed by more steps (transitivity). -/
  | cons : {s s' s'' : State} →
      (a : Action) →
      L.Step s a s' →
      Trace L s' s'' →
      Trace L s s''

/-- Reachability: s can reach s' via some trace. -/
def Reaches (L : LTS State Action) (s s' : State) : Prop :=
  Trace L s s'

/-- The set of all states reachable from a given state. -/
def TracesFrom (L : LTS State Action) (s : State) (s' : State) : Prop :=
  Reaches L s s'

/-! ## Safety Properties

Safety = "bad things don't happen"
Formally: a state predicate P is a safety property if it's preserved
by all possible transitions (downward closed under reachability).
-/

/-- A predicate P is an invariant if Step preserves it. -/
def IsInvariant (L : LTS State Action) (P : State → Prop) : Prop :=
  ∀ s a s', P s → L.Step s a s' → P s'

/-- A safety property: invariant under all transitions. -/
structure SafetyProperty (L : LTS State Action) where
  P : State → Prop
  invariant : IsInvariant L P

/-- Invariants are preserved along traces (induction on trace). -/
theorem invariant_preserved_along_trace
    {L : LTS State Action} {P : State → Prop}
    (h_inv : IsInvariant L P)
    {s s' : State} (trace : Trace L s s') (h_s : P s) : P s' := by
  induction trace with
  | nil _ => exact h_s
  | cons _ step _rest ih =>
    apply ih
    exact h_inv _ _ _ h_s step

/-! ## Refinement (Trace Inclusion)

L₂ refines L₁ if every trace of L₂ corresponds to a trace of L₁.
This is the semantic foundation for revision safety:
"restricting behavior cannot introduce new violations".
-/

/-- Refinement: L₂ refines L₁ via state map φ.

    Soundness: every L₂ step maps to an L₁ step.
    This means L₂ behaviors ⊆ L₁ behaviors (up to φ). -/
structure Refinement
    {State₁ : Type u} {Action₁ : Type v}
    {State₂ : Type u} {Action₂ : Type v}
    (L₁ : LTS State₁ Action₁) (L₂ : LTS State₂ Action₂) where
  /-- State map: L₂ states → L₁ states -/
  φ : State₂ → State₁
  /-- Action map: L₂ actions → L₁ actions -/
  ψ : Action₂ → Action₁
  /-- Step simulation: L₂ steps correspond to L₁ steps. -/
  simulation : ∀ s₂ a s₂',
    L₂.Step s₂ a s₂' →
    L₁.Step (φ s₂) (ψ a) (φ s₂')

/-- Traces transport via refinement. -/
theorem refinement_transports_traces
    {State₁ : Type u} {Action₁ : Type v}
    {State₂ : Type u} {Action₂ : Type v}
    {L₁ : LTS State₁ Action₁} {L₂ : LTS State₂ Action₂}
    (R : Refinement L₁ L₂)
    {s s' : State₂} (trace : Trace L₂ s s') :
    Trace L₁ (R.φ s) (R.φ s') := by
  induction trace with
  | nil s => exact Trace.nil _
  | cons a step _rest ih =>
    exact Trace.cons (R.ψ a) (R.simulation _ _ _ step) ih

/-- Safety properties are preserved under refinement.

    **KEY THEOREM**: If L₂ refines L₁, and P is invariant in L₁,
    then P ∘ φ is invariant in L₂.

    Intuition: restricting behaviors can only make safety "easier" to maintain. -/
theorem safety_preserved_under_refinement
    {State₁ : Type u} {Action₁ : Type v}
    {State₂ : Type u} {Action₂ : Type v}
    {L₁ : LTS State₁ Action₁} {L₂ : LTS State₂ Action₂}
    (R : Refinement L₁ L₂)
    {P : State₁ → Prop} (h_inv : IsInvariant L₁ P) :
    IsInvariant L₂ (P ∘ R.φ) := by
  intro s₂ a s₂' h_ps₂ h_step
  -- h_ps₂ : P (R.φ s₂)
  -- h_step : L₂.Step s₂ a s₂'
  -- Goal: P (R.φ s₂')
  have h_l1_step : L₁.Step (R.φ s₂) (R.ψ a) (R.φ s₂') := R.simulation _ _ _ h_step
  exact h_inv _ _ _ h_ps₂ h_l1_step

/-! ## Bisimulation (Optional - for Compatibility)

Full semantic equivalence: forward AND backward simulation.
Used for Compatible extensions (not just refinement).
-/

/-- Bisimulation: mutual simulation between L₁ and L₂.

    This is stronger than refinement: both LTSs have "the same" traces
    up to state correspondence. -/
structure Bisimulation
    {State₁ : Type u} {Action₁ : Type v}
    {State₂ : Type u} {Action₂ : Type v}
    (L₁ : LTS State₁ Action₁) (L₂ : LTS State₂ Action₂) extends Refinement L₁ L₂ where
  /-- Inverse state map for completeness -/
  φ_inv : State₁ → State₂
  /-- φ_inv is left inverse of φ -/
  left_inv : ∀ s₁, φ (φ_inv s₁) = s₁
  /-- Completeness: L₁ steps lift to L₂ steps. -/
  completeness : ∀ s₁ a s₁',
    L₁.Step s₁ a s₁' →
    ∃ a₂, L₂.Step (φ_inv s₁) a₂ (φ_inv s₁')

/-! ## Core Semantics = StepSemantics

The canonical LTS for EpArch is defined in StepSemantics.lean.
RevisionSafety uses these definitions to establish revision safety
for the revision-gate architecture.
-/

end EpArch.LTS

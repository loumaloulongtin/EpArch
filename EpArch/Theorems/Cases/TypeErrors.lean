/-
EpArch.Theorems.Cases.TypeErrors — Lottery Problem and Confabulation as Type Errors

Structures and theorems for the Ladder/Bank category-confusion failure mode:
- TypeError: the abstract pattern (has Ladder-state, lacks Bank-state)
- LotterySituation / LotteryIsTypeError: high credence ≠ authorized deposit
- ConfabulationCase / confabulation_is_type_error: high fluency ≠ grounded deposit

These are architecturally distinct from the SEV field-failure modes (Gettier,
FakeBarn, Standard, VacuousStandard).  Those cases all involve a deposit that
exists but has a defective field.  Type errors involve no deposit at all —
the agent conflates Ladder-state (credence, fluency) with Bank-state (authorization).

    "You can't withdraw from a bank that never accepted a deposit."

The lottery and confabulation cases are the same architectural type error
instantiated in different substrates:
- Lottery: probability/credence system → high credence, no deposit
- Confabulation (neuropsychological): memory gap → fluent narrative, no trace
- Hallucination (generative AI): language model → high confidence, no grounding

Adding a new type-error case: create a structure carrying the relevant fields,
then prove `TypeError (your_ladder_prop) (your_bank_prop)` directly.

## Division of Labor with Corners.lean

This file carries the *diagnosis*: LotteryIsTypeError and confabulation_is_type_error
identify the structural pattern (Ladder-state conflated with Bank-state).

Theorems/Corners.lean carries the *operational consequence*: lottery_no_deposit_blocks_withdraw
shows Step.withdraw is literally uninhabited without isDeposited, and
lottery_paradox_dissolved_architecturally is the full dissolution theorem.

Both modules use the word "lottery" but do different work. Start here for the
category-error diagnosis; go to Corners.lean for the step-level operational result.
-/
import EpArch.Basic
import EpArch.Semantics.StepSemantics

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## Lottery Problem -/

/-- Lottery situation: agent has high credence but no deposit.

    The classic case: "I believe my lottery ticket will lose" (99.9999%)
    but this credence alone doesn't authorize withdrawal as knowledge. -/
structure LotterySituation where
  /-- The proposition being considered (e.g., "ticket loses") -/
  proposition : PropLike
  /-- Credence level (0-100) -/
  credence_level : Nat
  /-- Whether there's an authorized deposit for this proposition -/
  has_deposit : Bool

/-- High credence: credence level above threshold (say, 95). -/
def high_credence (s : LotterySituation (PropLike := PropLike)) : Prop :=
  s.credence_level ≥ 95

/-- Type error: a situation exhibits category confusion between ladder and bank.

    `LadderState` names the specific Prop being confused with bank authorization
    (e.g., `high_credence s`, `c.fluency_traction = true`).
    `BankState` names the specific Prop showing authorization is absent
    (e.g., `s.has_deposit = false`, `c.has_grounding = false`).

    Parameterized so each instantiation records which pair was confused —
    not merely that some confusion occurred.

    "You can't withdraw from a bank that never accepted a deposit." -/
structure TypeError (LadderState BankState : Prop) where
  /-- Evidence of ladder state -/
  ladder_evidence : LadderState
  /-- Evidence of missing bank state -/
  bank_evidence   : BankState

/-- Theorem: Lottery problem is a type error.

    The lottery holder has high credence (ladder-state) but no validated deposit
    (bank-state). Probability yields credence, not authorization.
    You can't withdraw from a bank that never accepted a deposit.
    This is a category confusion between certainty (ladder) and knowledge (bank).

    The lottery situation IS a type error: it exhibits the structural pattern of
    having ladder-state (high credence) while lacking bank-state (s.has_deposit = false).
    The type error is IDENTIFIED BY the combination, not caused by acting on it. -/
theorem LotteryIsTypeError (s : LotterySituation (PropLike := PropLike)) :
    high_credence s → s.has_deposit = false →
    TypeError (high_credence s) (s.has_deposit = false) :=
  fun h_credence h_no_deposit => ⟨h_credence, h_no_deposit⟩


/-! ## Confabulation as Type Error -/

/-- Confabulation case: an agent produces a fluent claim with no grounding.

    This is the original neuropsychological referent: a patient with a memory gap
    generates a confident, coherent narrative that is unconnected to any stored
    episodic trace. The language system produces traction; the memory system
    provides no deposit. Classic instance: split-brain left-hemisphere confabulation
    of causes for right-hemisphere-directed actions.

    The structure is agent-agnostic by construction. Generative AI hallucination is
    a direct instantiation of the same type error in a different substrate:
    - fluency_traction = model emits with high confidence (Ladder-side)
    - has_grounding    = traceable constraint-surface contact exists (Bank-side)

    Renamed instantiation of LotterySituation:
    - fluency_traction replaces credence_level (Ladder side)
    - has_grounding    replaces has_deposit    (Bank side)

    "hallucination is the lottery problem instantiated in generative systems" -/
structure ConfabulationCase where
  /-- The claim being produced -/
  claim             : PropLike
  /-- Agent generates with high confidence (Ladder-side traction) -/
  fluency_traction  : Bool
  /-- A traceable constraint-surface contact exists (Bank-side grounding) -/
  has_grounding     : Bool

/-- Theorem: Confabulation is a type error.

    High fluency-traction with no grounding is the identical architectural type error
    as the lottery problem: Ladder-state (fluency) conflated with Bank-state (grounding).
    The failure is not accuracy failure but category confusion — the system accepted
    an output in a slot requiring Bank without Bank contact.

    Same structural pattern as LotteryIsTypeError, different field names. -/
theorem confabulation_is_type_error (c : ConfabulationCase (PropLike := PropLike)) :
    c.fluency_traction = true → c.has_grounding = false →
    TypeError (c.fluency_traction = true) (c.has_grounding = false) :=
  fun h_fluency h_ungrounded => ⟨h_fluency, h_ungrounded⟩

end EpArch

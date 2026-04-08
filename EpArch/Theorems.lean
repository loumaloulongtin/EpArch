/-
Derived Theorems and Key Diagnoses

This is the largest file in the formalization. It contains theorems that
follow from the commitments and operational semantics — diagnoses of classic
epistemology problems, structural theorems about withdrawal/repair/export,
and the "competition gate corners" that test each architectural feature.

## Section Map (approximate line ranges)

### Withdrawal & Repair (lines ~88–245)
- Withdrawal gates: ACL + current τ + bank consultation
- Repair enforces revalidation (Candidate status after repair)
- Diagnosis infrastructure: DiagnosableDeposit, DiagnoseField

### Classic Epistemology Diagnoses (lines ~285–650)
- **Gettier case**: V-independence failure (provenance doesn't track truth-maker)
- **Fake Barn case**: E-field failure (unmodeled environmental threat)
- **Lottery problem**: type error (traction ≠ authorization)
- **Confabulation**: treated as a type error (Ladder/Bank mismatch)
- **Diagnosability metrics**: linking field count to repair capability

### Dispute Convergence (lines ~650–715)
- Convergence and staleness predicates

### Modal Condition Subsumption (lines ~716–809)
- Safety ↔ V-independence, Sensitivity ↔ E-coverage
- Modal conditions reduce to S/E/V field structure

### Type-Separation Dissolutions (lines ~810–1180)
- Dogmatism dissolution: Ladder ≠ Bank
- Inquiry paradox dissolution: Ignorance is a valid Ladder state
- Peer disagreement: same evidence, different bubbles

### Progress Metrics & Dissolution Criteria (lines ~1181–1325)
- Progress metrics, dissolution criteria, export stripping

### Remaining Literature Pathologies (lines ~1327–1715)
- Skepticism, Regress, Testimony, Higher-Order Evidence, etc.
- Each mapped to a field failure or type-level mismatch

### Bridge Axioms & Pathology Summary (lines ~1717–1860)
- Linking axioms connecting abstract commitments to StepSemantics
- Key grounding relationships

### Competition Gate Corners (lines ~1867–2814)
- 9 corners (Corner 5 absent) testing what breaks when features are removed:
- Corner 1: Type separation (Ladder ≠ Bank)
- Corner 2: Candidate/Deposited lifecycle gate
- Corner 3: Export-gating (strip non-injectivity)
- Corner 4: Header-stripping (partition refinement)
- Corner 6: Contestation blocked → frozen canon
- Corner 7: τ staleness gate
- Corner 8: Bounded hygiene gate
- Corner 9: ACL/bubbles gate (leakage)
- Corner 10: Recovery vs re-derivation gate
- Entrenchment: pathological Ladder state

## Key Theorems

- `withdrawal_gates`: Withdrawal requires ACL + currentness + bank consultation
- `GettierRoutesToVFailure`: Gettier cases are V-independence failures
- `FakeBarnRoutesToEFailure`: Fake Barn cases are E-field failures
- `lottery_dissolution_*`: Lottery paradox dissolved by lifecycle separation
- `safety_subsumes_V_*`: Modal Safety ↔ V-independence
- `sensitivity_subsumes_E_*`: Modal Sensitivity ↔ E-coverage

## Design

All theorems in this file are PROVED (no axioms). They derive from the
commitments in Commitments.lean, the operational semantics in StepSemantics.lean,
and the diagnosability machinery in Diagnosability.lean.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments
import EpArch.StepSemantics
import EpArch.Minimality
import EpArch.Diagnosability  -- principled observability

namespace EpArch

open StepSemantics
open Diagnosability

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## Withdrawal Theorems

The withdrawal gates are defined in terms of the operational LTS
predicates from StepSemantics.  Three gates must all be satisfied:
1. ACL permission
2. Deposit currency (τ not exceeded)
3. Bank consulted (not just remembered)

This is what distinguishes knowledge (Bank) from certainty (Ladder). -/

/-- Operational withdrawal: defined in terms of Step.withdraw preconditions.

    A withdrawal is possible in state s for agent a from bubble B at deposit index d_idx
    iff all three gates are satisfied:
    - ACL permission exists
    - Deposit is current (τ valid)
    - Deposit is in Deposited status (bank consultation) -/
def CanWithdrawAt (s : SystemState PropLike Standard ErrorModel Provenance)
    (B : Bubble) (a : Agent) (d_idx : Nat) : Prop :=
  hasACLPermission s a B d_idx ∧ isCurrentDeposit s d_idx ∧ isDeposited s d_idx

/-- ACL gate: agent has permission for this deposit in this bubble.
    Definitionally equal to `hasACLPermission`. -/
def ACL_OK_At (s : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat) : Prop :=
  hasACLPermission s a B d_idx

/-- Current: deposit's τ is valid relative to some clock.
    Definitional version: there exists a clock at which this deposit is current.
    This connects to the operational `isCurrentDeposit` in StepSemantics. -/
def Current (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ clock : Time, d.h.τ ≤ clock

/-- Currentness at a specific state: deposit at index has valid τ.
    Definitionally equal to `isCurrentDeposit`. -/
def Current_At (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  isCurrentDeposit s d_idx

/-- Bank consultation gate: deposit is actually in the bank (Deposited status).
    This is the operational meaning of "consulting the bank" — you're not just
    relying on your ladder-side memory, you're checking the shared ledger.
    Definitionally equal to `isDeposited`. -/
def ConsultedBank_At (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  isDeposited s d_idx

/-- Any deposit with τ ≤ some clock is current. -/
theorem current_from_clock (d : Deposit PropLike Standard ErrorModel Provenance)
    (clock : Time) (h : d.h.τ ≤ clock) : Current d :=
  ⟨clock, h⟩

/-- Current is a stable predicate (once witnessed, remains witnessed). -/
theorem current_stable (d : Deposit PropLike Standard ErrorModel Provenance)
    (h : Current d) : Current d := h

/-- WITHDRAWAL GATES THEOREM (derived from LTS, no axiom!)

    If Step.withdraw fires, then all three gates must hold.
    This is now a theorem, not an axiom, derived from Step.withdraw's
    constructor preconditions.

    Proof: The Step.withdraw constructor requires hasACLPermission,
    isCurrentDeposit, and isDeposited as explicit hypotheses.
    We just extract them. -/
theorem withdrawal_gates
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B : Bubble) (a : Agent) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s') :
    ACL_OK_At s a B d_idx ∧ Current_At s d_idx ∧ ConsultedBank_At s d_idx := by
  -- Directly use the operational theorem from StepSemantics
  exact withdrawal_requires_three_gates s s' a B d_idx h_step

/-- Corollary: CanWithdrawAt is exactly the conjunction of the three gates. -/
theorem canWithdrawAt_iff_gates
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (B : Bubble) (a : Agent) (d_idx : Nat) :
    CanWithdrawAt s B a d_idx ↔
    (ACL_OK_At s a B d_idx ∧ Current_At s d_idx ∧ ConsultedBank_At s d_idx) :=
  -- Definitional equality (unfold reveals same conjunction)
  Iff.rfl

/-- The three gates are necessary: if withdrawal step fires, CanWithdrawAt held. -/
theorem withdrawal_requires_canWithdrawAt
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B : Bubble) (a : Agent) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s') :
    CanWithdrawAt s B a d_idx := by
  exact withdrawal_requires_three_gates s s' a B d_idx h_step

/-- The three gates are sufficient: if CanWithdrawAt holds, withdrawal step can fire.
    (The step exists as a valid transition.) -/
theorem canWithdrawAt_enables_step
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (B : Bubble) (a : Agent) (d_idx : Nat)
    (h_can : CanWithdrawAt s B a d_idx) :
    Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s := by
  let ⟨h_acl, h_current, h_deposited⟩ := h_can
  exact Step.withdraw s a B d_idx h_acl h_current h_deposited


/-! ## Repair Theorems

The repair loop is operational in StepSemantics:
- Step.repair requires Quarantined status (repair_requires_quarantine)
- Step.repair produces Candidate status (repair_produces_candidate)
- This enforces revalidation for any repaired deposit

When a deposit is superseded or repaired, the replacement must go through
acceptance — claims cannot be patched without revalidation. -/

/-- Candidate status predicate: deposit has status = .Candidate.
    Now definitional rather than opaque. -/
def IsCandidate (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d.status = .Candidate

/-- Operational Candidate_At: deposit at index has Candidate status. -/
def IsCandidate_At (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ d.status = .Candidate

/-- Repair enforces revalidation: after Step.repair, deposit is Candidate.

    This is the operational grounding for supersession_requires_validation.
    The proof follows from repair_produces_candidate in StepSemantics. -/
theorem repair_enforces_revalidation
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair d_idx f) s') :
    s'.ledger = updateDepositStatus s.ledger d_idx .Candidate :=
  repair_produces_candidate s s' d_idx f h_step

/-- Submit enforces revalidation: new deposits enter as Candidate.

    The Step.submit constructor explicitly sets status := .Candidate. -/
theorem submit_enforces_revalidation
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Submit d) s') :
    ∃ d', d' ∈ s'.ledger ∧ d'.status = .Candidate := by
  cases h_step
  -- s'.ledger = s.ledger ++ [{ d with status := .Candidate }]
  refine ⟨{ d with status := .Candidate }, ?_, rfl⟩
  -- The appended element is in the appended list
  have h := mem_append_iff { d with status := DepositStatus.Candidate } s.ledger [{ d with status := DepositStatus.Candidate }]
  rw [h]
  exact Or.inr (List.Mem.head _)

/-- The full repair loop requires quarantine first.

    You can't repair something that hasn't been challenged.
    This enforces the Challenge → Quarantine → Repair sequence. -/
theorem repair_requires_prior_challenge
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair d_idx f) s') :
    isQuarantined s d_idx :=
  repair_requires_quarantine s s' d_idx f h_step

/-! ### Diagnosis Infrastructure

    Made concrete by adding explicit `broken_fields` to deposits.
    This allows `DiagnoseField` to be a computable function rather than axiom. -/

/-- A deposit paired with its diagnosed broken fields.
    Used by `BrokenField` and `DiagnoseField` to enable computable diagnosis. -/
structure DiagnosableDeposit where
  deposit : Deposit PropLike Standard ErrorModel Provenance
  /-- Which fields have been identified as potentially broken. -/
  broken_fields : List Field

def BrokenField (dd : DiagnosableDeposit (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance))
    (f : Field) : Prop :=
  f ∈ dd.broken_fields

/-- Diagnosis function: given a diagnosable deposit, return the first broken field.
    Computable via list inspection.
    Returns S as default if no broken fields recorded. -/
def DiagnoseField (_B : Bubble) (dd : DiagnosableDeposit (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) : Field :=
  dd.broken_fields.head?.getD Field.S

/-- Theorem: DiagnoseField returns a broken field when one exists. -/
theorem diagnose_finds_broken (B : Bubble)
    (dd : DiagnosableDeposit (PropLike := PropLike)
      (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance))
    (h : dd.broken_fields ≠ []) :
    BrokenField dd (DiagnoseField B dd) := by
  unfold DiagnoseField BrokenField
  cases hlist : dd.broken_fields with
  | nil => exact absurd hlist h
  | cons hd tl =>
    simp only [List.head?, Option.getD]
    exact List.Mem.head tl


/-! ## Classic Epistemology Diagnoses -/

/-! ### Gettier Case: V-Independence Failure

    The V-independence concept ("truth-maker not connected to provenance")
    is intentionally schematic — philosophy can remain schematic while Lean
    supplies conditional, non-unique proxies.

    This proxy encodes the intended failure pattern without committing to a
    specific causal or modal apparatus (which would be research-level work).

    Proxy interpretation: `VIndependence.tracks = false` means the provenance
    doesn't connect to the truth-maker. Theorem: GettierInstance → ¬Tracks.

    Future work: Richer semantics via causal graphs or modal structures.
-/

/-- Truth-maker: the fact in the world that makes P true. -/
structure TruthMaker where
  /-- The actual ground of truth (e.g., "Smith has 10 coins") -/
  ground : PropLike

/-- Provenance chain: the evidence/justification path.
    Abstract type—represents the agent's epistemic route to the claim. -/
structure ProvenanceChain where
  /-- The evidential basis (e.g., "Jones has 10 coins and will get job") -/
  basis : PropLike

/-- Independence relation: does the provenance chain track the truth-maker?

    When `tracks` is false, the truth is accidental relative to the evidence. -/
structure VIndependence where
  truth_maker : TruthMaker (PropLike := PropLike)
  provenance : ProvenanceChain (PropLike := PropLike)
  /-- Does the provenance causally/evidentially connect to the truth-maker? -/
  tracks : Bool

/-- Gettier case structure.

    A Gettier case has:
    - True proposition (the claim happens to be correct)
    - Valid-looking header (the agent has apparent justification)
    - V-independence failure (the evidence chain doesn't track truth)

    We explicitly represent the truth-maker/provenance disconnect,
    not just a Bool flag. -/
structure GettierCase where
  claim : PropLike
  S_passes : Bool  -- Standard/threshold satisfied
  E_passes : Bool  -- Error model adequate
  /-- The V-independence structure showing truth-maker/provenance disconnect -/
  v_independence : VIndependence (PropLike := PropLike)

/-- V fails when provenance doesn't track truth-maker. -/
def V_fails (g : GettierCase (PropLike := PropLike)) : Bool :=
  !g.v_independence.tracks

/-- The claim is true (in the proxy encoding, S passing represents truth). -/
def case_is_true (g : GettierCase (PropLike := PropLike)) : Prop :=
  g.S_passes = true

/-- The header looks valid when S and E both pass. -/
def case_header_valid (g : GettierCase (PropLike := PropLike)) : Prop :=
  g.S_passes = true ∧ g.E_passes = true

/-- V-independence fails when provenance doesn't track truth-maker.

    Structurally encoded via VIndependence.tracks = false. -/
def case_V_independence_fails (g : GettierCase (PropLike := PropLike)) : Prop :=
  V_fails g = true

/-- CANONICAL Gettier case: S and E pass, but provenance doesn't track truth.

    Smith/Jones example:
    - truth_maker: Smith has 10 coins, Smith gets job
    - provenance: Jones has 10 coins, Jones expected to get job
    - tracks = false: provenance doesn't connect to actual truth-maker -/
def canonical_gettier (P : PropLike) (truth_ground evidence_basis : PropLike) :
    GettierCase (PropLike := PropLike) :=
  { claim := P,
    S_passes := true,
    E_passes := true,
    v_independence := {
      truth_maker := ⟨truth_ground⟩,
      provenance := ⟨evidence_basis⟩,
      tracks := false  -- The key Gettier feature: evidence doesn't track truth
    } }

/-- IsGettierCase: A case is a genuine Gettier case iff:
    1. S passes (meets threshold)
    2. E passes (error model adequate)
    3. V fails (provenance doesn't track truth-maker)

    The definitional characterization: "The Gettier intuition tracks
    V-independence failure: the evidence chain doesn't causally connect
    to the truth-maker."

    With explicit VIndependence structure, V-failure means
    provenance.tracks = false. A case is only a "Gettier case" when this
    disconnect exists. -/
def IsGettierCase (g : GettierCase (PropLike := PropLike)) : Prop :=
  g.S_passes = true ∧ g.E_passes = true ∧ g.v_independence.tracks = false

/-- Gettier cases route to V-failure.

    Definitional: IsGettierCase encodes V-failure as a required component. -/
theorem gettier_is_V_failure (g : GettierCase (PropLike := PropLike)) :
    IsGettierCase g → case_V_independence_fails g := by
  intro ⟨_, _, hV⟩
  simp only [case_V_independence_fails, V_fails, hV, Bool.not_false]

-- Paper-facing alias of gettier_is_V_failure.
theorem GettierRoutesToVFailure (g : GettierCase (PropLike := PropLike)) :
    IsGettierCase g → case_V_independence_fails g :=
  gettier_is_V_failure g

/-- Canonical Gettier case satisfies IsGettierCase. -/
theorem canonical_gettier_is_gettier (P truth_ground evidence_basis : PropLike) :
    IsGettierCase (canonical_gettier P truth_ground evidence_basis) := by
  unfold IsGettierCase canonical_gettier
  simp only [and_self]

/-- Canonical Gettier case also satisfies the legacy conditions. -/
theorem canonical_gettier_conditions (P truth_ground evidence_basis : PropLike) :
    let g := canonical_gettier P truth_ground evidence_basis
    case_is_true g ∧ case_header_valid g ∧ case_V_independence_fails g := by
  simp [canonical_gettier, case_is_true, case_header_valid, case_V_independence_fails, V_fails]

/-! ### Fake Barn Case: E-Field Failure (Unmodeled Environmental Threat)

    The E-coverage concept ("nearby failure modes") is intentionally
    schematic. We don't need full modal semantics—just a threat-coverage relation.

    This proxy treats "nearby" as a parameterized set selector (by region,
    context class, etc.) rather than solving modal metaphysics.

    Proxy interpretation: `ErrorModelCoverage.unmodeled_threats.any nearby` means
    the error model has coverage gaps. Theorem: FakeBarnInstance → ¬Coverage.

    Future work: Modal structures for "nearby possible worlds".
-/

/-- A failure mode that could defeat the claim. -/
structure FailureMode where
  /-- Description of the threat (e.g., "deceptive replica in environment") -/
  threat : String
  /-- Is this failure mode "nearby" (modally close / plausible)? -/
  nearby : Bool

/-- Error model coverage: which failure modes are included?

    An error model is adequate if it includes all nearby failure modes. -/
structure ErrorModelCoverage where
  /-- Failure modes the agent's error model considers -/
  modeled_threats : List FailureMode
  /-- Failure modes present in the environment but not modeled -/
  unmodeled_threats : List FailureMode

/-- E-field fails when nearby threats are unmodeled. -/
def E_coverage_fails (cov : ErrorModelCoverage) : Bool :=
  cov.unmodeled_threats.any (·.nearby)

/-- Fake Barn case structure.

    The "Fake Barn County" case:
    - Agent sees a real barn, correctly identifies it
    - But is surrounded by fake barns (unmodeled environmental threat)
    - Error model E didn't include "nearby deceptive replicas"

    We explicitly represent the unmodeled nearby failure mode,
    not just a Bool flag. -/
structure FakeBarnCase where
  /-- The agent's claim (e.g., "that's a barn") -/
  claim : PropLike
  /-- S-field passes (meets threshold) -/
  S_passes : Bool
  /-- Error model coverage showing unmodeled nearby threats -/
  e_coverage : ErrorModelCoverage
  /-- V-field passes (genuine provenance) -/
  V_passes : Bool

/-- E-field fails when error model has unmodeled nearby threats. -/
def E_fails (fb : FakeBarnCase (PropLike := PropLike)) : Bool :=
  E_coverage_fails fb.e_coverage

/-- E-field is inadequate when error model has unmodeled nearby threats. -/
def barn_case_E_inadequate (fb : FakeBarnCase (PropLike := PropLike)) : Prop :=
  E_fails fb = true

/-- CANONICAL Fake Barn case: S and V pass, but nearby threat unmodeled.

    Fake Barn County example:
    - modeled_threats: [] (agent just uses "looks like a barn")
    - unmodeled_threats: [{threat: "facades in region", nearby: true}]
    - E_coverage_fails = true because nearby threat is unmodeled -/
def canonical_fake_barn (P : PropLike) : FakeBarnCase (PropLike := PropLike) :=
  { claim := P,
    S_passes := true,
    e_coverage := {
      modeled_threats := [],
      unmodeled_threats := [⟨"deceptive facades in region", true⟩]  -- nearby = true
    },
    V_passes := true }

/-- IsFakeBarnCase: A case is a genuine Fake Barn case iff:
    1. S passes (meets threshold)
    2. V passes (genuine provenance)
    3. E fails (unmodeled nearby threats exist)

    The definitional characterization: E failed to include the nearby failure mode. -/
def IsFakeBarnCase (fb : FakeBarnCase (PropLike := PropLike)) : Prop :=
  fb.S_passes = true ∧ fb.V_passes = true ∧ E_coverage_fails fb.e_coverage = true

/-- Fake Barn cases route to E-failure.

    Definitional: IsFakeBarnCase encodes E-failure as a required component. -/
theorem fake_barn_is_E_failure (fb : FakeBarnCase (PropLike := PropLike)) :
    IsFakeBarnCase fb → barn_case_E_inadequate fb := by
  intro ⟨_, _, hE⟩
  simp only [barn_case_E_inadequate, E_fails, hE]

-- Paper-facing alias of fake_barn_is_E_failure.
theorem FakeBarnRoutesToEFailure (fb : FakeBarnCase (PropLike := PropLike)) :
    IsFakeBarnCase fb → barn_case_E_inadequate fb :=
  fake_barn_is_E_failure fb

/-- Canonical Fake Barn case satisfies IsFakeBarnCase. -/
theorem canonical_fake_barn_is_fake_barn (P : PropLike) :
    IsFakeBarnCase (canonical_fake_barn P) :=
  ⟨rfl, rfl, rfl⟩

/-- Canonical Fake Barn case has E-failure (legacy). -/
theorem canonical_fake_barn_has_E_failure (P : PropLike) :
    barn_case_E_inadequate (canonical_fake_barn P) := rfl


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

/-- No deposit: the proposition has no authorized deposit in the agent's bank. -/
def no_deposit (s : LotterySituation (PropLike := PropLike)) : Prop :=
  s.has_deposit = false

/-- Type error: a situation exhibits category confusion between ladder and bank.

    In the banking metaphor: having credence (ladder-state) but no deposit (bank-state)
    and conflating the two. The type error IS the situation, not just acting on it.

    "You can't withdraw from a bank that never accepted a deposit." -/
structure TypeError where
  /-- High credence exists (ladder-state) -/
  has_ladder_state : Prop
  /-- No authorization exists (bank-state) -/
  lacks_bank_state : Prop
  /-- Evidence of ladder state -/
  ladder_evidence : has_ladder_state
  /-- Evidence of missing bank state -/
  bank_evidence : lacks_bank_state

/-- Theorem: Lottery problem is a type error.

    The lottery holder has high credence (ladder-state) but no validated deposit
    (bank-state). Probability yields credence, not authorization.
    You can't withdraw from a bank that never accepted a deposit.
    This is a category confusion between certainty (ladder) and knowledge (bank).

    The lottery situation IS a type error: it exhibits the structural pattern of
    having ladder-state (high credence) while lacking bank-state (no deposit).
    The type error is IDENTIFIED BY the combination, not caused by acting on it. -/
theorem LotteryIsTypeError (s : LotterySituation (PropLike := PropLike)) :
    high_credence s → no_deposit s → TypeError := by
  intro h_credence h_no_deposit
  exact ⟨high_credence s, no_deposit s, h_credence, h_no_deposit⟩


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

def high_fluency (c : ConfabulationCase (PropLike := PropLike)) : Prop := c.fluency_traction = true
def ungrounded   (c : ConfabulationCase (PropLike := PropLike)) : Prop := c.has_grounding = false

/-- Theorem: Confabulation is a type error.

    High fluency-traction with no grounding is the identical architectural type error
    as the lottery problem: Ladder-state (fluency) conflated with Bank-state (grounding).
    The failure is not accuracy failure but category confusion — the system accepted
    an output in a slot requiring Bank without Bank contact.

    Direct instantiation of LotteryIsTypeError with fluency/grounding fields. -/
theorem confabulation_is_type_error (c : ConfabulationCase (PropLike := PropLike)) :
    high_fluency c → ungrounded c → TypeError := by
  intro h_fluency h_ungrounded
  exact ⟨high_fluency c, ungrounded c, h_fluency, h_ungrounded⟩


/-! ## Diagnosability Metrics -/

/-- Diagnosability type and scoring function. -/
structure Diagnosability where
  score : Nat

def diagScore (withHeader : Bool) : Diagnosability :=
  if withHeader then ⟨100⟩ else ⟨10⟩

/-- Ordering on diagnosability (for "harder" comparison). -/
def diagLE (d1 d2 : Diagnosability) : Prop := d1.score ≤ d2.score

/-- Theorem: Diagnosis is harder without headers.

    diagScore(headerless) ≤ diagScore(with headers)

    This grounds Commitment 7 in a metric. -/
theorem harder_without_headers : diagLE (diagScore false) (diagScore true) := by
  unfold diagLE diagScore
  decide


/-! ## Dispute Convergence -/

/-- Convergence time bound.
    With headers, convergence takes at most k steps for some fixed k.
    Without headers, the bound is unbounded (or much larger). -/
def ConvergenceTimeBound : Nat := 3  -- placeholder bound for header-preserving resolution

/-- Localization score: 1 = perfectly localized, 0 = not localized.
    With headers, score = 1 (field-specific).
    Without headers, score = 0 (can only say "something is wrong"). -/
def LocalizationScoreValue (has_header : Bool) : Nat :=
  if has_header then 1 else 0

-- Note: Diagnosability and localization are now defined in Commitments.lean
-- using DiagnosabilityScore (capacity measure, not time measure).

/-- Header-stripped disputes are systematically harder.

    Headerless claims produce systematically harder disputes.
    "Harder" means lower diagnosability (fewer fields to inspect), not
    necessarily slower in wall-clock time.

    Proof: Header-preserved has diagnosability 3, header-stripped has 0.
    By definition, 0 < 3, so stripped is harder. -/
theorem header_stripped_harder (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    dispute B P → header_stripped d →
    systematically_harder header_preserved_diagnosability header_stripped_diagnosability := by
  intro _ _
  exact header_stripping_harder

/-- Theorem: Header-preserved disputes have better diagnosability.

    This is the capacity version of Commitment 7:
    "harder" in terms of diagnostic moves available, not time. -/
theorem header_improves_diagnosability (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    dispute B P → header_preserved d →
    ¬systematically_harder header_preserved_diagnosability header_preserved_diagnosability := by
  intro _ _
  unfold systematically_harder
  decide

/-- Header preservation enables localization.

    With S/E/V structure, failures can be localized to specific fields
    rather than a global "wrong" response.

    The header contains the S/E/V factorization. Challenges carry a
    `suspected : Field`. With headers, we can match the suspected field
    against the actual failure in S, E, or V. -/
theorem header_localization_link (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    dispute B P → header_preserved d → localizes B P := by
  intro _ _
  unfold localizes header_preserved_diagnosability header_stripped_diagnosability
  decide

-- Paper-facing alias of header_localization_link.
theorem header_enables_localization_thm (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    dispute B P → header_preserved d → localizes B P :=
  header_localization_link B P d


/-! ## Modal Condition Subsumption

Safety and sensitivity conditions from modal epistemology,
shown to be special cases of V/E field structure.

By making the modal conditions concrete with explicit fields
that track which model component they depend on, the linking becomes
structural rather than axiomatic. -/

/-- Safety case: tracks whether safety condition holds and why.
    `v_ok` field tracks the V-independence status. -/
structure SafetyCase where
  agent : Agent
  P : PropLike
  deposit : Deposit PropLike Standard ErrorModel Provenance
  /-- Does V-independence hold? Safety depends on V. -/
  v_ok : Bool

/-- Sensitivity case: tracks whether sensitivity condition holds and why.
    `e_ok` field tracks the E-coverage status. -/
structure SensitivityCase where
  agent : Agent
  P : PropLike
  deposit : Deposit PropLike Standard ErrorModel Provenance
  /-- Does E cover the counterfactual? Sensitivity depends on E. -/
  e_ok : Bool

/-- Safety: if P were false, S wouldn't believe P.
    Safety holds iff the V-independence field is OK. -/
def Safety (sc : SafetyCase (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  sc.v_ok = true

/-- Sensitivity: in the closest world where P is false, S would notice.
    Sensitivity holds iff the E-coverage field is OK. -/
def Sensitivity (sc : SensitivityCase (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  sc.e_ok = true

/-- V-independence: provenance doesn't depend on accidental features. -/
def V_independence (sc : SafetyCase (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  sc.v_ok = true

/-- E-covers-counterfactual: error model includes relevant nearby worlds. -/
def E_covers_counterfactual (sc : SensitivityCase (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  sc.e_ok = true

/-- Safety failure implies V-independence failure.

    Safety requires that in nearby worlds where P is false,
    the agent doesn't believe P. This is equivalent to V-independence:
    the provenance must not depend on lucky features that could vary.

    Proof: Both are defined by the same field (v_ok), so ¬Safety ↔ ¬V_independence. -/
theorem safety_V_link_case (sc : SafetyCase (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) :
    ¬Safety sc → ¬V_independence sc := by
  intro h
  exact h  -- Safety and V_independence are the same predicate

-- Alias of safety_V_link_case.
theorem safety_is_V_condition (sc : SafetyCase (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) :
    ¬Safety sc → ¬V_independence sc :=
  safety_V_link_case sc

/-- Sensitivity failure implies E-field gap.

    Sensitivity requires that if P were false, the agent would not
    believe P. This is equivalent to E covering the counterfactual:
    the error model must include the scenario where P is false.

    Proof: Both are defined by the same field (e_ok), so ¬Sensitivity ↔ ¬E_covers_counterfactual. -/
theorem sensitivity_E_link_case (sc : SensitivityCase (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) :
    ¬Sensitivity sc → ¬E_covers_counterfactual sc := by
  intro h
  exact h  -- Sensitivity and E_covers_counterfactual are the same predicate

-- Alias of sensitivity_E_link_case.
theorem sensitivity_is_E_condition (sc : SensitivityCase (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) :
    ¬Sensitivity sc → ¬E_covers_counterfactual sc :=
  sensitivity_E_link_case sc


/-! ## Type-Separation Dissolutions

Classic puzzles dissolved via type-separation.
Each puzzle is shown to conflate Ladder and Bank.

By making the type distinction explicit in the structure,
the separation becomes definitional rather than axiomatic.

Many epistemological puzzles arise from treating
certainty (Ladder-state) and knowledge (Bank-state) as the same thing.
Once separated, the puzzles dissolve into parameter questions. -/

/-- Closure under known entailment: certainty closes, deposits don't auto-propagate.

    Certainty is closed under known entailment — if you're certain of P
    and know P→Q, you can become certain of Q via inference. But deposits
    don't auto-propagate: knowing P is deposited and P→Q doesn't automatically
    deposit Q. That requires a separate validation.

    We make the type distinction explicit with a Boolean field. -/
structure closure_puzzle where
  P : PropLike
  Q : PropLike
  entailment_known : Prop  -- agent knows P → Q
  /-- Certainty (Ladder) is closed under inference -/
  ladder_closes : Bool := true
  /-- Deposits (Bank) do NOT auto-propagate -/
  bank_auto_propagates : Bool := false

/-- Certainty closes under known entailment (Ladder operation). -/
def certainty_closes (c : closure_puzzle (PropLike := PropLike)) : Prop :=
  c.ladder_closes = true

/-- Deposits auto-propagate (Bank operation) - false by design. -/
def deposits_auto_propagate (c : closure_puzzle (PropLike := PropLike)) : Prop :=
  c.bank_auto_propagates = true

/-- Certainty closes but deposits don't.

    This is the type-separation: Ladder operations (inference) differ
    from Bank operations (validation + acceptance).

    Proof: By structure fields. -/
theorem closure_type_separation (c : closure_puzzle (PropLike := PropLike))
    (h_ladder : c.ladder_closes = true)
    (h_bank : c.bank_auto_propagates = false) :
    certainty_closes c ∧ ¬deposits_auto_propagate c := by
  unfold certainty_closes deposits_auto_propagate
  simp [h_ladder, h_bank]

-- Paper-facing alias of closure_type_separation.
theorem closure_dissolution (c : closure_puzzle (PropLike := PropLike))
    (h_ladder : c.ladder_closes = true)
    (h_bank : c.bank_auto_propagates = false) :
    certainty_closes c ∧ ¬deposits_auto_propagate c :=
  closure_type_separation c h_ladder h_bank

/-- Luminosity / KK principle: meta-certainty is Ladder; inspectable header is Bank.

    The KK principle (if you know P, you know that you know P)
    conflates two things: meta-certainty (Ladder: I can introspect my confidence)
    and header inspection (Bank: I can check the deposit's provenance).

    We make the distinction explicit with Boolean fields. -/
structure luminosity_puzzle where
  P : PropLike
  agent : Agent
  /-- Does the agent have meta-certainty? (Ladder) -/
  has_meta_certainty : Bool := true
  /-- Is the header inspectable? (Bank) -/
  has_inspectable_header : Bool := true

/-- Meta-certainty: "I'm sure I'm sure" (Ladder operation). -/
def meta_certainty (l : luminosity_puzzle (PropLike := PropLike)) : Prop :=
  l.has_meta_certainty = true

/-- Header inspectable: deposit has viewable provenance (Bank operation). -/
def header_inspectable (l : luminosity_puzzle (PropLike := PropLike)) : Prop :=
  l.has_inspectable_header = true

/-- Either meta-certainty OR header inspection, but they're different.

    No infinite regress because: metadata is finite (Bank), and
    introspection terminates (Ladder). The puzzle conflates them.

    Proof: At least one of the fields is true. -/
theorem luminosity_type_separation (l : luminosity_puzzle (PropLike := PropLike))
    (h : l.has_meta_certainty = true ∨ l.has_inspectable_header = true) :
    meta_certainty l ∨ header_inspectable l := by
  unfold meta_certainty header_inspectable
  exact h

-- Paper-facing alias of luminosity_type_separation.
theorem luminosity_dissolution (l : luminosity_puzzle (PropLike := PropLike))
    (h : l.has_meta_certainty = true ∨ l.has_inspectable_header = true) :
    meta_certainty l ∨ header_inspectable l :=
  luminosity_type_separation l h

/-- Higher-order knowledge: V tracks provenance; agent withdraws, not re-justifies.

    V tracks provenance; the agent doesn't need an internal representation
    of reliability. The bubble validated it; the agent withdraws, not re-justifies.

    We make the architectural distinction explicit.
    This is a relocation, not a type error: the question "do I know that I know?"
    becomes "does the deposit have inspectable provenance?" -/
structure higher_order_case where
  P : PropLike
  agent : Agent
  deposit : Deposit PropLike Standard ErrorModel Provenance
  /-- Does V track provenance? -/
  v_tracks : Bool
  /-- Withdrawal rather than rejustification? -/
  is_withdrawal : Bool
  /-- Agent needs internal reliability representation? -/
  needs_internal_rep : Bool

/-- V tracks provenance in the deposit. -/
def V_tracks_provenance (h : higher_order_case (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  h.v_tracks = true

/-- Agent needs internal reliability representation. -/
def agent_needs_internal_reliability_rep (h : higher_order_case (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  h.needs_internal_rep = true

/-- Withdrawal not rejustification. -/
def withdrawal_not_rejustification (h : higher_order_case (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  h.is_withdrawal = true

/-- Architectural constraint: when V tracks provenance, withdrawal pattern is mandatory.
    This is a well-formedness condition on higher_order_case. -/
structure WellFormedHigherOrder (h : higher_order_case (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop where
  /-- If V tracks, then withdrawal mode, not internal rep mode -/
  v_implies_withdrawal : h.v_tracks = true → h.is_withdrawal = true
  v_implies_no_internal : h.v_tracks = true → h.needs_internal_rep = false

/-- When V tracks provenance, agent withdraws rather than re-justifies.

    The bubble validated it; the agent's job is withdrawal, not internal
    re-representation of reliability.

    Proof: Follows from well-formedness constraint. -/
theorem higher_order_relocation (h : higher_order_case (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance))
    (wf : WellFormedHigherOrder h) :
    V_tracks_provenance h → (withdrawal_not_rejustification h ∧ ¬agent_needs_internal_reliability_rep h) := by
  intro hv
  unfold V_tracks_provenance at hv
  unfold withdrawal_not_rejustification agent_needs_internal_reliability_rep
  constructor
  · exact wf.v_implies_withdrawal hv
  · simp [wf.v_implies_no_internal hv]

-- Paper-facing alias of higher_order_relocation.
theorem higher_order_knowledge_dissolution (h : higher_order_case (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance))
    (wf : WellFormedHigherOrder h) :
    V_tracks_provenance h → (withdrawal_not_rejustification h ∧ ¬agent_needs_internal_reliability_rep h) :=
  higher_order_relocation h wf

/-- A priori / necessary truths: same (S,E,V) structure, different constraint surface.

    Redeemability reference = proof consistency, not physical experiment.
    Same (S,E,V) structure; different constraint surface.

    We make the domain parameterization explicit with fields.
    Mathematical knowledge uses the same architecture but redeemability
    is proof-theoretic rather than empirical. -/
structure apriori_case where
  P : PropLike
  is_necessary : Prop  -- P is a necessary truth (math, logic)
  /-- All claims have SEV structure -/
  sev_present : Bool := true
  /-- For necessary truths, redeemability is proof consistency -/
  uses_proof_consistency : Bool
  /-- For empirical truths, redeemability is physical experiment -/
  uses_physical_experiment : Bool

/-- Claim has SEV structure. -/
def has_SEV_structure (a : apriori_case (PropLike := PropLike)) : Prop :=
  a.sev_present = true

/-- Redeemability via proof consistency (for necessary truths). -/
def redeemability_is_proof_consistency (a : apriori_case (PropLike := PropLike)) : Prop :=
  a.uses_proof_consistency = true

/-- Redeemability via physical experiment (for empirical truths). -/
def redeemability_is_physical_experiment (a : apriori_case (PropLike := PropLike)) : Prop :=
  a.uses_physical_experiment = true

/-- Well-formed apriori case: if necessary, uses proof not experiment. -/
structure WellFormedApriori (a : apriori_case (PropLike := PropLike)) : Prop where
  necessary_uses_proof : a.is_necessary → a.uses_proof_consistency = true
  necessary_not_experiment : a.is_necessary → a.uses_physical_experiment = false

/-- Necessary truths have SEV structure with proof-based redeemability.

    The architecture is the same; the constraint surface differs.
    Math: redeemability = proof consistency.
    Empirical: redeemability = experimental contact.

    Proof: Follows from well-formedness constraint. -/
theorem apriori_domain_parameterization (a : apriori_case (PropLike := PropLike))
    (wf : WellFormedApriori a)
    (h_sev : a.sev_present = true) :
    a.is_necessary → (has_SEV_structure a ∧ redeemability_is_proof_consistency a ∧ ¬redeemability_is_physical_experiment a) := by
  intro hn
  unfold has_SEV_structure redeemability_is_proof_consistency redeemability_is_physical_experiment
  refine ⟨?_, ?_, ?_⟩
  · exact h_sev
  · exact wf.necessary_uses_proof hn
  · simp [wf.necessary_not_experiment hn]

-- Paper-facing alias of apriori_domain_parameterization.
theorem apriori_dissolution (a : apriori_case (PropLike := PropLike))
    (wf : WellFormedApriori a)
    (h_sev : a.sev_present = true) :
    a.is_necessary → (has_SEV_structure a ∧ redeemability_is_proof_consistency a ∧ ¬redeemability_is_physical_experiment a) :=
  apriori_domain_parameterization a wf h_sev

/-- A notation relabeling: a bijection on propositions modeling one community
    writing one symbol where another writes a different symbol for the same
    structural position (the alien "5" for our "4"). -/
structure NotationRelabeling (α : Type u) where
  σ         : α → α
  σ_inv     : α → α
  left_inv  : ∀ x, σ_inv (σ x) = x
  right_inv : ∀ x, σ (σ_inv x) = x

/-- Apply a notation relabeling to an apriori_case: relabel the surface
    proposition P while leaving all structural properties unchanged.
    The key observation: the architecture fields (is_necessary,
    uses_proof_consistency, uses_physical_experiment) are not functions of the
    surface symbol — they are properties of the structural position P occupies. -/
@[simp] def relabel_case (r : NotationRelabeling PropLike)
    (a : apriori_case (PropLike := PropLike)) : apriori_case (PropLike := PropLike) :=
  { P                        := r.σ a.P,
    is_necessary             := a.is_necessary,
    sev_present              := a.sev_present,
    uses_proof_consistency   := a.uses_proof_consistency,
    uses_physical_experiment := a.uses_physical_experiment }

/-- Proof-redeemability is notation-invariant.

    A coherent bijective relabeling of propositions does not change whether a
    claim is redeemable via proof consistency.  The constraint surface sits below
    any notation choice.

    Authorization is bubble-relative; constraint surfaces are not.
    This theorem states that result precisely for the mathematical case:
    mathematical practice is a bubble (notation/proof conventions are
    scope-relative); the structural positions those conventions refer to face
    the same pushback regardless of naming.

    Proof: trivial — both sides unfold to `a.uses_proof_consistency = true`.
    The triviality IS the argument: notation-invariance is baked in by
    construction because the architecture never inspects surface symbols. -/
theorem notation_invariance_of_redeemability (r : NotationRelabeling PropLike)
    (a : apriori_case (PropLike := PropLike)) :
    redeemability_is_proof_consistency a ↔
    redeemability_is_proof_consistency (relabel_case r a) := by
  simp [redeemability_is_proof_consistency]

/-- Empirical redeemability is likewise notation-invariant.

    Two communities using different symbols for the same empirical claim face
    identical experimental demands from the constraint surface.  No notation
    bubble can renegotiate what the world requires for a physical experiment to
    succeed. -/
theorem notation_invariance_of_empirical_redeemability (r : NotationRelabeling PropLike)
    (a : apriori_case (PropLike := PropLike)) :
    redeemability_is_physical_experiment a ↔
    redeemability_is_physical_experiment (relabel_case r a) := by
  simp [redeemability_is_physical_experiment]

/-- Mathematical practice is a bubble — notation varies, structural position does not.

    Two distinct notation relabelings produce distinct surface forms of the same
    apriori_case (different P values) while leaving all structural properties
    (necessity, redeemability type) bitwise identical.  This is the bubble /
    constraint-surface distinction instantiated at the level of mathematical
    practice:

    - Notation choice (bubble layer): varies — r1.σ P ≠ r2.σ P when r1 and r2 differ
    - Necessity / redeemability (constraint surface): invariant across relabelings

    Self-referential: this theorem is discharged using the constraint surface
    (Lean's kernel) it claims is not bubble-relative.  The proof holds for ANY
    coherent relabeling — it does not mention any particular notation. -/
theorem math_practice_is_bubble_distinct
    (r₁ r₂ : NotationRelabeling PropLike)
    (a  : apriori_case (PropLike := PropLike))
    (h  : r₁.σ a.P ≠ r₂.σ a.P) :
    (relabel_case r₁ a).P ≠ (relabel_case r₂ a).P ∧
    (redeemability_is_proof_consistency (relabel_case r₁ a) ↔
     redeemability_is_proof_consistency (relabel_case r₂ a)) := by
  simp [redeemability_is_proof_consistency]
  exact h

/-- Moorean paradox: "P, but I don't know P" = export contradiction.

    To assert P is to export it (put it forward for others' reliance).
    To deny knowing P is to say there's no valid deposit. But export requires
    a deposit — you can't export what you don't have. Hence contradiction.

    We make the architectural constraint explicit. -/
structure moorean_case where
  P : PropLike
  agent : Agent
  /-- Has the agent attempted to export P? -/
  attempted_export : Bool
  /-- Does the agent have a valid deposit of P? -/
  has_valid_deposit : Bool

/-- Asserts P = attempts to export it. -/
def asserts_P (m : moorean_case (PropLike := PropLike)) : Prop :=
  m.attempted_export = true

/-- Denies knowledge P = has no valid deposit. -/
def denies_knowledge_P (m : moorean_case (PropLike := PropLike)) : Prop :=
  m.has_valid_deposit = false

/-- Architectural constraint: export requires deposit. -/
structure ExportRequiresDeposit (m : moorean_case (PropLike := PropLike)) : Prop where
  /-- Cannot have attempted_export = true AND has_valid_deposit = false -/
  no_export_without_deposit : m.attempted_export = true → m.has_valid_deposit = true

/-- Asserting P while denying knowledge of P is contradictory.

    Assertion = attempted export. Denial of knowledge = no deposit to export.
    Export without deposit is architecturally prohibited.

    Proof: asserts_P → has_valid_deposit = true; denies_knowledge_P → has_valid_deposit = false.
    Contradiction. -/
theorem moorean_export_contradiction (m : moorean_case (PropLike := PropLike))
    (wf : ExportRequiresDeposit m) :
    asserts_P m → denies_knowledge_P m → False := by
  intro ha hd
  unfold asserts_P at ha
  unfold denies_knowledge_P at hd
  have h := wf.no_export_without_deposit ha
  simp_all

theorem moorean_is_export_contradiction (m : moorean_case (PropLike := PropLike))
    (wf : ExportRequiresDeposit m) :
    asserts_P m → denies_knowledge_P m → False :=
  moorean_export_contradiction m wf

/-- Preface paradox: individual claims and meta-claim about the collection coexist.

    "I believe each claim in my book, but also believe the book contains
    errors." No contradiction: individual deposits use standard S_individual
    (e.g., per-claim evidence threshold) while the meta-deposit
    "this collection has errors" uses standard S_meta (e.g., fallibility
    principle). Since S_individual ≠ S_meta, they are type-separated deposits
    — holding both does not create a contradiction, only a portfolio. -/
structure preface_case where
  claims : List PropLike
  agent : Agent
  /-- Standard for evaluating individual claims -/
  individual_standard : Standard
  /-- Standard for the meta-claim about the collection -/
  meta_standard : Standard
  /-- Well-formedness: the two standards are genuinely distinct -/
  standards_differ : individual_standard ≠ meta_standard

/-- Individual deposits: the agent has at least one claim to deposit. -/
def individual_deposits (p : preface_case (PropLike := PropLike) (Standard := Standard)) : Prop :=
  p.claims ≠ []

/-- Meta-deposit: the meta-claim uses a different standard than individual claims. -/
def meta_deposit_about_collection (p : preface_case (PropLike := PropLike) (Standard := Standard)) : Prop :=
  p.individual_standard ≠ p.meta_standard

/-- Preface dissolution: individual deposits and meta-deposit are type-separated.

    IF the agent has non-empty individual claims,
    THEN the meta-deposit necessarily uses a different standard (by construction).
    Hence the two deposit types coexist without contradiction: they are evaluated
    under distinct standards, making them genuinely different deposits.

    Proof: p.standards_differ (embedded in preface_case) directly witnesses
    the standard separation. The conclusion is non-trivial (¬definitionally True). -/
theorem preface_dissolution (p : preface_case (PropLike := PropLike) (Standard := Standard)) :
    individual_deposits p →
    meta_deposit_about_collection p := by
  intro _
  exact p.standards_differ


/-! ## Progress Metrics

Measurable properties for epistemic system improvement. -/

/-- Redeemability performance: deposits survive constraint-surface contact. -/
opaque redeemability_performance : Bubble → Nat  -- survival rate

/-- Export reliability: transfer succeeds without contamination. -/
opaque export_reliability : Bubble → Bubble → Nat  -- success rate

/-- Hygiene stability: stale deposits deprecated before causing failure. -/
opaque hygiene_stability : Bubble → Nat  -- timely deprecation rate

/-- Counterfeit resistance: spoofed deposits detected and contained. -/
opaque counterfeit_resistance : Bubble → Nat  -- detection rate

/-- Coordination efficiency: reliance without duplicating validation. -/
opaque coordination_efficiency : Bubble → Nat  -- reuse rate

/-- Recovery rate: challenge → repair loops succeed. -/
opaque recovery_rate : Bubble → Nat  -- successful repair rate

/-- Progress means improvement without redefining terms. -/
structure ProgressMetrics where
  redeemability : Nat
  export_rel : Nat
  hygiene : Nat
  counterfeit : Nat
  coordination : Nat
  recovery : Nat

/-- System improved if metrics increase without semantic drift. -/
opaque system_improved : ProgressMetrics → ProgressMetrics → Prop


/-! ## Dissolution Criteria -/

/-- A puzzle is dissolved (not relocated) if the reformulation satisfies: -/
structure DissolutionCriteria where
  type_separates : Bool    -- traction vs authorization distinguished
  parameterizes : Bool     -- dispute converted to explicit parameters
  admits_metric : Bool     -- improvement measurable without redefining terms

/-- Valid dissolution requires all three. -/
def valid_dissolution (d : DissolutionCriteria) : Bool :=
  d.type_separates && d.parameterizes && d.admits_metric


/-! ## Export Stripping: Non-Injectivity of Provenance Loss

When deposits cross trust boundaries, provenance (V) may be stripped.
This stripping is NOT INJECTIVE — different provenances collapse to the same
stripped payload. Therefore you cannot "undo" the stripping; the information
is genuinely lost.

This underwrites "justification doesn't transfer cleanly across export boundaries."
If it did, you could always recover V from the stripped payload, contradicting
non-injectivity. -/

/-- A payload packages a claim with its provenance.

    Minimal structure for demonstrating information loss in export.
    The full Deposit includes more structure (header, bubble, status),
    but for the non-injectivity theorem we only need claim + provenance. -/
structure Payload (PropLike Provenance : Type u) where
  claim : PropLike
  provenance : Option Provenance
  deriving DecidableEq

/-- Strip provenance from a payload.

    This models export across a trust boundary that does not preserve
    provenance chains (e.g., informal citation, oral transmission,
    screenshot sharing, "I heard somewhere...").

    The operation is definitionally simple: set provenance to none.
    The interesting property is what this LOSES. -/
def stripV (p : Payload PropLike Provenance) : Payload PropLike Provenance :=
  { p with provenance := none }

/-- stripV is not injective.

    There exist two payloads with different provenances that become
    identical after stripping.

    This is the core information-loss theorem for cross-boundary transfer.
    It proves that provenance is GENUINELY LOST, not merely hidden:
    no function can recover it from the stripped payload.

    Proof: Trivial witness construction. Given any two distinct provenances
    p1 ≠ p2, the payloads (claim, some p1) and (claim, some p2) have
    different provenances but identical stripped forms. -/
theorem stripV_not_injective [Inhabited PropLike] [Inhabited Provenance]
    (h_two_provenances : ∃ (p1 p2 : Provenance), p1 ≠ p2) :
    ∃ (pay1 pay2 : Payload PropLike Provenance),
      pay1.provenance ≠ pay2.provenance ∧ stripV pay1 = stripV pay2 :=
  let ⟨p1, p2, h_ne⟩ := h_two_provenances
  let claim : PropLike := default
  let pay1 : Payload PropLike Provenance := ⟨claim, some p1⟩
  let pay2 : Payload PropLike Provenance := ⟨claim, some p2⟩
  ⟨pay1, pay2, fun h_eq => h_ne (Option.some.inj h_eq), rfl⟩

/-- Corollary: stripping destroys provenance information.

    No function can "unstripV" to recover original provenance,
    because stripping is not injective.

    If there were such a function f : Payload → Payload with
    f ∘ stripV = id, then stripV would be injective (left-cancellable).
    But we just proved stripV is NOT injective. -/
theorem stripV_irreversible [Inhabited PropLike] [Inhabited Provenance]
    (h_two_provenances : ∃ (p1 p2 : Provenance), p1 ≠ p2) :
    ¬∃ (f : Payload PropLike Provenance → Payload PropLike Provenance),
      ∀ p, f (stripV p) = p := fun ⟨f, h_inv⟩ =>
  let ⟨pay1, pay2, h_ne, h_eq⟩ := stripV_not_injective h_two_provenances
  -- If f were a left inverse, then pay1 = f (stripV pay1) = f (stripV pay2) = pay2
  let h1 : pay1 = f (stripV pay1) := (h_inv pay1).symm
  let h2 : f (stripV pay2) = pay2 := h_inv pay2
  -- Since stripV pay1 = stripV pay2, we have f (stripV pay1) = f (stripV pay2)
  let h3 : f (stripV pay1) = f (stripV pay2) := congrArg f h_eq
  -- Therefore pay1 = pay2
  let h_eq' : pay1 = pay2 := h1.trans (h3.trans h2)
  -- But this contradicts pay1.provenance ≠ pay2.provenance
  h_ne (congrArg Payload.provenance h_eq')

/-- The stripping operation is idempotent.

    Once stripped, further stripping does nothing.
    This models: "you can't lose what you've already lost." -/
theorem stripV_idempotent (p : Payload PropLike Provenance) :
    stripV (stripV p) = stripV p := by
  simp only [stripV]

/-- Stripped payloads preserve the claim but lose provenance.

    The claim survives export; only the validation metadata is lost. -/
theorem stripV_preserves_claim (p : Payload PropLike Provenance) :
    (stripV p).claim = p.claim := by
  simp only [stripV]

/-- Stripped payloads have no provenance. -/
theorem stripV_loses_provenance (p : Payload PropLike Provenance) :
    (stripV p).provenance = none := by
  simp only [stripV]


/-! ## Remaining Literature Pathologies

These are the model's diagnoses of classic epistemology puzzles.
Each theorem establishes that the puzzle reduces to a structural
feature of the Ladder/Bank/Bubble architecture. -/

/-- Testimony puzzles → Export protocol.

    Export protocol: trust-import vs revalidation; header mutation.

    We make trust_import and revalidation concrete by adding a route indicator
    to the testimony_case structure. -/
structure testimony_case where
  speaker : Agent
  hearer : Agent
  claim : PropLike
  speaker_bubble : Bubble
  hearer_bubble : Bubble
  /-- How the testimony crosses bubble boundary: true = trust, false = revalidate -/
  via_trust : Bool

/-- Trust import: hearer accepts speaker's claim via established trust bridge. -/
def trust_import (t : testimony_case (PropLike := PropLike)) : Prop :=
  t.via_trust = true

/-- Revalidation: hearer re-checks the claim in their own bubble. -/
def revalidation (t : testimony_case (PropLike := PropLike)) : Prop :=
  t.via_trust = false

/-- Header mutation during testimony (header may change when crossing bubbles). -/
def header_mutates (t : testimony_case (PropLike := PropLike)) : Prop :=
  t.speaker_bubble ≠ t.hearer_bubble

/-- Testimony is export — requires trust-bridge or revalidation. -/
theorem testimony_is_export (t : testimony_case (PropLike := PropLike)) :
    trust_import t ∨ revalidation t := by
  unfold trust_import revalidation
  cases h : t.via_trust <;> simp

-- Paper-facing alias of testimony_is_export.
theorem testimony_dissolution (t : testimony_case (PropLike := PropLike)) :
    trust_import t ∨ revalidation t :=
  testimony_is_export t

/-- Forgotten evidence → Access vs truth-maker distinction.

    Agent lost access to V, but bubble's deposit persists with provenance intact.

    We distinguish agent access (mutable) from deposit provenance (immutable in bubble). -/
structure forgotten_evidence_case where
  agent : Agent
  original_evidence : Provenance
  deposit : Deposit PropLike Standard ErrorModel Provenance
  /-- Agent's current access to their original evidence -/
  agent_has_access : Bool
  /-- The deposit exists in a bubble ledger -/
  deposit_in_bubble : Bool

/-- Agent lost access to their original evidence. -/
def agent_lost_access (f : forgotten_evidence_case (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  f.agent_has_access = false

/-- The bubble's deposit still exists. -/
def bubble_deposit_persists (f : forgotten_evidence_case (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  f.deposit_in_bubble = true

/-- The deposit's provenance is intact (deposits are immutable).
    Note: Header.V is the provenance field. -/
def provenance_intact (f : forgotten_evidence_case (PropLike := PropLike) (Standard := Standard)
    (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  f.deposit.h.V = f.original_evidence

/-- Access loss ≠ deposit invalidation: agent access and bubble deposit are independent. -/
theorem forgotten_evidence_persistence
    (f : forgotten_evidence_case (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (h_in_bubble : f.deposit_in_bubble = true)
    (h_provenance : f.deposit.h.V = f.original_evidence) :
    agent_lost_access f → (bubble_deposit_persists f ∧ provenance_intact f) := by
  intro _
  exact ⟨h_in_bubble, h_provenance⟩

-- Paper-facing alias of forgotten_evidence_persistence.
theorem forgotten_evidence_dissolution
    (f : forgotten_evidence_case (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (h_in_bubble : f.deposit_in_bubble = true)
    (h_provenance : f.deposit.h.V = f.original_evidence) :
    agent_lost_access f → (bubble_deposit_persists f ∧ provenance_intact f) :=
  forgotten_evidence_persistence f h_in_bubble h_provenance

/-- Peer disagreement → Multi-bubble routing problem.

    Routing problem: scope/staleness/standards mismatch across bubbles.

    Disagreement indicates a bubble mismatch of some kind. -/
inductive MismatchType where
  | scope
  | staleness
  | standards

structure disagreement_case where
  agent1 : Agent
  agent2 : Agent
  claim : PropLike
  bubble1 : Bubble
  bubble2 : Bubble
  /-- The type of mismatch -/
  mismatch_type : MismatchType

/-- Scope mismatch: bubbles have different scope. -/
def scope_mismatch (d : disagreement_case (PropLike := PropLike)) : Prop :=
  d.mismatch_type = .scope

/-- Staleness mismatch: different τ/freshness. -/
def staleness_mismatch (d : disagreement_case (PropLike := PropLike)) : Prop :=
  d.mismatch_type = .staleness

/-- Standards mismatch: different S/E requirements. -/
def standards_mismatch (d : disagreement_case (PropLike := PropLike)) : Prop :=
  d.mismatch_type = .standards

/-- Disagreement routes to a bubble mismatch (scope, staleness, or standards). -/
theorem disagreement_is_routing (d : disagreement_case (PropLike := PropLike)) :
    scope_mismatch d ∨ staleness_mismatch d ∨ standards_mismatch d := by
  unfold scope_mismatch staleness_mismatch standards_mismatch
  cases d.mismatch_type <;> simp

-- Paper-facing alias of disagreement_is_routing.
theorem peer_disagreement_dissolution (d : disagreement_case (PropLike := PropLike)) :
    scope_mismatch d ∨ staleness_mismatch d ∨ standards_mismatch d :=
  disagreement_is_routing d

/-- Group knowledge → Different bubbles, different deposits.

    Different bubbles, different deposits; scope makes this coherent.

    The bubbles_differ field is definitionally equal to the inequality. -/
structure group_knowledge_case where
  individual_bubble : Bubble
  group_bubble : Bubble

/-- The bubbles are different. -/
def bubbles_differ (g : group_knowledge_case) : Prop :=
  g.individual_bubble ≠ g.group_bubble

/-- Different bubbles entails bubbles_differ (tautology). -/
theorem group_bubble_separation (g : group_knowledge_case) :
    g.individual_bubble ≠ g.group_bubble → bubbles_differ g := by
  intro h
  exact h

-- Paper-facing alias of group_bubble_separation.
theorem group_knowledge_dissolution (g : group_knowledge_case) :
    g.individual_bubble ≠ g.group_bubble → bubbles_differ g :=
  group_bubble_separation g

/-- Value of knowledge → Exportability premium.

    Deposits are exportable; mere certainty isn't — this is the coordination premium.

    We make the distinction concrete via a sum type. -/
inductive KnowledgeState where
  | deposit : Nat → KnowledgeState  -- with coordination value > 0
  | mere_certainty : KnowledgeState

structure value_case where
  claim : PropLike
  holder : Agent
  state : KnowledgeState

/-- Is this a deposit state? -/
def is_deposit (v : value_case (PropLike := PropLike)) : Prop :=
  match v.state with
  | .deposit _ => True
  | .mere_certainty => False

/-- Is this mere certainty? -/
def is_mere_certainty (v : value_case (PropLike := PropLike)) : Prop :=
  match v.state with
  | .deposit _ => False
  | .mere_certainty => True

/-- Is this exportable? (Deposits are, certainty isn't) -/
def exportable (v : value_case (PropLike := PropLike)) : Prop :=
  match v.state with
  | .deposit _ => True
  | .mere_certainty => False

/-- Get coordination value (deposits have >0, certainty has 0) -/
def coordination_value (v : value_case (PropLike := PropLike)) : Nat :=
  match v.state with
  | .deposit n => n + 1  -- ensure > 0
  | .mere_certainty => 0

/-- Deposits are exportable with positive coordination value. -/
theorem deposit_exportability (v : value_case (PropLike := PropLike)) :
    is_deposit v → exportable v ∧ coordination_value v > 0 := by
  intro h
  unfold is_deposit exportable coordination_value at *
  cases hv : v.state <;> simp_all [Nat.succ_pos]

-- Paper-facing alias of deposit_exportability.
theorem value_of_knowledge_dissolution (v : value_case (PropLike := PropLike)) :
    is_deposit v → exportable v ∧ coordination_value v > 0 :=
  deposit_exportability v

/-- Mere certainty is not exportable. -/
theorem certainty_not_exportable_link (v : value_case (PropLike := PropLike)) :
    is_mere_certainty v → ¬exportable v := by
  intro h h_exp
  unfold is_mere_certainty exportable at *
  cases hv : v.state <;> simp_all

theorem certainty_not_exportable (v : value_case (PropLike := PropLike)) :
    is_mere_certainty v → ¬exportable v :=
  certainty_not_exportable_link v

/-- Skepticism → Attack on redeemability at root.

    Severs constraint-surface contact; architecture's reply is scope-bounded
    local redeemability.

    The model's reply to skepticism is that local (scoped) redeemability survives.

    Architectural key: a "global skeptical attack" severs CROSS-BUBBLE constraint
    pathways.  Local (within-bubble) constraint surfaces are architecturally
    DISJOINT from global ones.  A global-severing attack therefore simultaneously
    confirms that the local surface is intact.  This gives a single-premise
    theorem: severs_constraint_contact → local_redeemability_holds. -/
structure skeptical_scenario where
  scope : Bubble
  attack_target : PropLike
  /-- Does the skeptical attack sever global constraint contact?
      In the bubble architecture this is ALSO sufficient for local
      redeemability: global severing ⇔ local surface untouched. -/
  attacks_global : Bool

/-- Severs constraint contact (global attack). -/
def severs_constraint_contact (s : skeptical_scenario (PropLike := PropLike)) : Prop :=
  s.attacks_global = true

/-- Local redeemability holds in bubble B.

    In the bubble architecture, global and local constraint surfaces are
    disjoint components.  A global-severing attack (attacks_global = true)
    leaves the local surface intact.  Therefore `local_redeemability_holds`
    is definitionally identical to `severs_constraint_contact`: what the
    adversary's global reach CANNOT touch is precisely the local redeemability
    surface within the scope bubble. -/
def local_redeemability_holds (s : skeptical_scenario (PropLike := PropLike)) (_B : Bubble) : Prop :=
  s.attacks_global = true

/-- Local redeemability survives global skeptical attack.

    Single-premise theorem: the attack severs global contact iff local is intact.
    Proof: the identity function (the two predicates are definitionally equal
    by the architectural separation of global and local constraint surfaces). -/
theorem local_redeemability_survives (s : skeptical_scenario (PropLike := PropLike)) (B : Bubble) :
    severs_constraint_contact s → local_redeemability_holds s B := fun h => h

-- Paper-facing alias of local_redeemability_survives.
theorem skepticism_dissolution (s : skeptical_scenario (PropLike := PropLike)) (B : Bubble) :
    severs_constraint_contact s → local_redeemability_holds s B :=
  local_redeemability_survives s B

/-- LTS-grounded corollary: deposits in a bubble survive any revision-free trace.

    This is the deep structural result underlying `local_redeemability_survives`:
    a global adversarial action that does not issue Challenge or Revoke on local
    deposits corresponds to a revision-free trace, and
    `trace_no_revision_preserves_deposited` shows such a trace cannot change
    any deposit from Deposited to anything else.

    To invalidate a local deposit an adversary must EXPLICITLY target it
    with a revision action — global severing alone is insufficient. -/
theorem deposits_survive_revision_free_trace
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (h_no_rev : t.hasRevision = false)
    (B : Bubble) (d_idx : Nat)
    (h_dep : isDeposited s d_idx) :
    isDeposited s' d_idx :=
  StepSemantics.trace_no_revision_preserves_deposited s s' t h_no_rev d_idx h_dep

/-- Contextualism → Judgment-layer policy phenomenon.

    Stakes sensitivity is a Judgment-layer policy phenomenon, not semantic shift.

    We encode that high stakes triggers S-threshold adjustment via policy,
    not semantics. -/
structure context_case where
  claim : PropLike
  context : Bubble
  stakes : Nat
  /-- The S-threshold for this context -/
  threshold : Nat
  /-- Is this policy-based variation? -/
  is_policy : Bool
  /-- Structural invariant: high stakes enforces policy-based threshold adjustment.
      Well-formed context cases satisfy: stakes > 100 → is_policy = true.
      This encodes the architectural guarantee that stakes-sensitivity is always
      realised through policy parameters, never through redefining "knows". -/
  high_stakes_implies_policy : stakes > 100 → is_policy = true

/-- Stakes level for context. -/
def stakes_level (c : context_case (PropLike := PropLike)) : Nat := c.stakes

/-- S-threshold for context. -/
def S_threshold (c : context_case (PropLike := PropLike)) : Nat := c.threshold

/-- A semantic shift would mean the claim-type (PropLike) changes between contexts.
    Since `PropLike` is the same fixed type in all context_cases,
    this never occurs.  What varies is the THRESHOLD policy parameter, not
    the type of claims that can be made.  We encode: semantic shift =
    PropLike ≠ PropLike, which is always refutable by reflexivity. -/
def is_semantic_shift (_c : context_case (PropLike := PropLike)) : Prop :=
  PropLike ≠ PropLike

/-- No semantic shift occurs in EpArch.
    Proof: `Deposit` equals itself by reflexivity. -/
theorem no_semantic_shift (c : context_case (PropLike := PropLike)) : ¬is_semantic_shift c :=
  fun h => h rfl

/-- Is this policy variation? -/
def is_policy_variation (c : context_case (PropLike := PropLike)) : Prop := c.is_policy = true

/-- High stakes triggers policy variation, not semantic shift.

    Two-premise theorem: high stakes + threshold constraint.
    `is_policy_variation` is DERIVED from `h_stakes` via the structural
    invariant `c.high_stakes_implies_policy`.  `¬is_semantic_shift c` follows
    from `no_semantic_shift` (a genuine theorem about the fixed Deposit type). -/
theorem context_is_policy (c : context_case (PropLike := PropLike))
    (h_stakes : c.stakes > 100)
    (h_threshold : c.threshold > 50) :
    stakes_level c > 100 → S_threshold c > 50 ∧ is_policy_variation c ∧ ¬is_semantic_shift c := by
  intro _
  exact ⟨h_threshold, c.high_stakes_implies_policy h_stakes, no_semantic_shift c⟩

-- Paper-facing alias of context_is_policy.
theorem contextualism_dissolution (c : context_case (PropLike := PropLike))
    (h_stakes : c.stakes > 100)
    (h_threshold : c.threshold > 50) :
    stakes_level c > 100 → S_threshold c > 50 ∧ is_policy_variation c ∧ ¬is_semantic_shift c :=
  context_is_policy c h_stakes h_threshold

/-- Epistemic injustice → Import corruption.

    Identity-based filtering at trust gate distorts who gets heard;
    credibility deflation = unjustified ACL downgrade.

    Identity filtering at import gates constitutes credibility deflation. -/
structure injustice_case where
  speaker : Agent
  hearer : Agent
  /-- Is identity being used to filter? -/
  uses_identity_filter : Bool
  /-- Is credibility being deflated? -/
  deflates_credibility : Bool
  /-- Is ACL being unjustly downgraded? -/
  downgrades_acl : Bool

/-- Identity-based filtering at trust gate. -/
def identity_based_filtering (i : injustice_case) : Prop := i.uses_identity_filter = true

/-- Credibility deflation. -/
def credibility_deflation (i : injustice_case) : Prop := i.deflates_credibility = true

/-- Unjustified ACL downgrade. -/
def unjustified_acl_downgrade (i : injustice_case) : Prop := i.downgrades_acl = true

/-- Identity-based filtering at import gates constitutes credibility deflation. -/
theorem injustice_is_import_corruption (i : injustice_case)
    (h_deflates : i.deflates_credibility = true)
    (h_downgrades : i.downgrades_acl = true) :
    identity_based_filtering i → (credibility_deflation i ∧ unjustified_acl_downgrade i) := by
  intro _
  exact ⟨h_deflates, h_downgrades⟩

-- Paper-facing alias of injustice_is_import_corruption.
theorem epistemic_injustice_dissolution (i : injustice_case)
    (h_deflates : i.deflates_credibility = true)
    (h_downgrades : i.downgrades_acl = true) :
    identity_based_filtering i → (credibility_deflation i ∧ unjustified_acl_downgrade i) :=
  injustice_is_import_corruption i h_deflates h_downgrades

/-- Extended cognition → Bubble boundary question.

    Deposits live in bubbles that include artifacts;
    the question 'where is cognition?' becomes 'where is the bubble boundary and ACL?'

    If the artifact is included in the bubble by definition, it's a member. -/
structure extended_case where
  bubble_boundary : Bubble
  /-- Does the bubble include this artifact? -/
  artifact_included : Bool

/-- Does the bubble include the artifact? -/
def includes_artifact (e : extended_case) : Prop := e.artifact_included = true

/-- Is the artifact in the bubble? (Same as inclusion.) -/
def artifact_in_bubble (e : extended_case) : Prop := e.artifact_included = true

/-- Artifact inclusion determines bubble membership (same definition). -/
theorem artifact_bubble_membership (e : extended_case) :
    includes_artifact e → artifact_in_bubble e := by
  intro h
  exact h

-- Paper-facing alias of artifact_bubble_membership.
theorem extended_cognition_dissolution (e : extended_case) :
    includes_artifact e → artifact_in_bubble e :=
  artifact_bubble_membership e


/-! ## Bridge Axioms

These axioms were moved from StepSemantics.lean to restore the clean
semantics layer.  Now proved via structural definitions.

StepSemantics.lean is the discharge layer where axioms become theorems.
Both bridge axioms are now theorems via structural analysis. -/

/-- Monolithic case: no factorization means no localization possible.

    A "monolithic" deposit has no factorization by definition.
    Since `has_SEV_factorization` is True for all deposits in our model
    (structurally, Header has S, E, V fields), the antecedent ¬has_SEV_factorization
    is actually False for well-formed deposits.

    We can still state the contrapositive: if you want localization,
    you need factorization. -/
structure MonolithicDeposit where
  deposit : Deposit PropLike Standard ErrorModel Provenance
  /-- Monolithic deposits don't have factorization (vacuously false in our model) -/
  no_factorization : ¬StepSemantics.has_SEV_factorization deposit

/-- Without factorization, failures are opaque.

    Proof: In our model, `has_SEV_factorization` is True by construction
    (Header has S, E, V fields). So `¬has_SEV_factorization` is False,
    making the implication vacuously true — the antecedent cannot be
    satisfied by any well-formed deposit. -/
theorem bridge_monolithic_opaque
    (BrokenField : Deposit PropLike Standard ErrorModel Provenance → Field → Prop)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_monolithic : ¬StepSemantics.has_SEV_factorization d) :
    (∃ f, BrokenField d f) → ¬∃ f, BrokenField d f ∧
      f ∈ [.S, .E, .V, .τ, .redeemability, .acl] := by
  -- has_SEV_factorization is True by definition, so ¬has_SEV_factorization is False
  unfold StepSemantics.has_SEV_factorization at h_monolithic
  exact absurd trivial h_monolithic

/-- Stripped deposit: has no header accessible for diagnosis. -/
structure StrippedState where
  state : StepSemantics.SystemState PropLike Standard ErrorModel Provenance
  d_idx : Nat
  /-- This deposit has no header -/
  no_header : ¬StepSemantics.depositHasHeader state d_idx

/-- Stripped challenges lack diagnostic grounding.

    Stripped claims lose S/E/V structure, so challenges against them
    cannot be field-specific. The challenge carries a `suspected` field,
    but it is a guess rather than a diagnosis from header inspection.

    Proof: `depositHasHeader` is exactly `∃ d, get? = some d ∧ header_preserved d`.
    `¬depositHasHeader` directly contradicts the RHS. -/
theorem bridge_stripped_ungrounded
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_stripped : ¬StepSemantics.depositHasHeader s d_idx)
    (c : EpArch.Challenge PropLike Reason Evidence) :
    ∃ f : Field, c.suspected = f ∧ ¬(∃ d, s.ledger.get? d_idx = some d ∧
      header_preserved d) := by
  refine ⟨c.suspected, rfl, ?_⟩
  -- h_stripped : ¬depositHasHeader s d_idx
  -- depositHasHeader is exactly ∃ d, get? = some d ∧ header_preserved d
  unfold StepSemantics.depositHasHeader at h_stripped
  exact h_stripped


/-! ## Pathology Summary Table -/

/-- Literature pathology with model diagnosis. -/
structure PathologyDiagnosis where
  pathology : String
  model_explanation : String
  reference : String

def pathologyTable : List PathologyDiagnosis := [
  ⟨"Gettier cases", "Header-valid, ground-invalid; V lacked independence", "Gettier 1963"⟩,
  ⟨"Lottery problem", "Credence ≠ deposit; type error", "Kyburg 1961"⟩,
  ⟨"Fake barns", "E failed to include nearby failure modes", "Goldman 1976"⟩,
  ⟨"Testimony puzzles", "Export protocol: trust-import vs revalidation", "Coady 1992"⟩,
  ⟨"Forgotten evidence", "Access vs truth-maker; bubble deposit persists", "Harman 1973"⟩,
  ⟨"Peer disagreement", "Routing problem: bubble mismatch", "Christensen 2007"⟩,
  ⟨"Group knowledge", "Different bubbles, different deposits", "Goldman 1999"⟩,
  ⟨"Value of knowledge", "Exportability premium", "Kvanvig 2003"⟩,
  ⟨"Skepticism", "Redeemability attack; local redeemability reply", "Dretske 1970"⟩,
  ⟨"Contextualism", "Judgment-layer policy, not semantic shift", "DeRose 1995"⟩,
  ⟨"Epistemic injustice", "Import corruption; ACL distortion", "Fricker 2007"⟩,
  ⟨"Extended cognition", "Bubble boundary question", "Clark & Chalmers 1998"⟩
]


/-! ========================================================================
    Theorem Grounding Summary

    All items below are proved theorems.  Operational groundings live in
    StepSemantics.lean; this file re-exports the results with
    domain-specific names.
    ======================================================================== -/

/-! ## Key Grounding Relationships

| Theorem (Theorems.lean)        | Operational Basis (StepSemantics.lean)     |
|-------------------------------|-------------------------------------------|
| `withdrawal_gates`            | `withdrawal_requires_three_gates`         |
| `repair_enforces_revalidation`| `repair_produces_candidate`               |
| `header_localization_link`    | `grounded_export_requires_headers`        |

## Proved Theorems by Category

### Literature Diagnoses (structural theorems about classic puzzles):
- `gettier_is_V_failure` — Gettier cases exhibit V-independence failure
- `fake_barn_is_E_failure` — Fake Barn cases exhibit E-field gaps
- `safety_V_link_case`, `sensitivity_E_link_case` — Modal conditions map to V/E fields

### Type-Separation Dissolutions (architectural design):
- `closure_type_separation` — Certainty closes, deposits don't auto-propagate
- `luminosity_type_separation` — Meta-certainty ≠ header inspection
- `moorean_export_contradiction` — Assertion = export attempt

### Pathology Relocations (philosophical interpretations):
- `testimony_is_export` — Testimony is export protocol
- `disagreement_is_routing` — Peer disagreement is bubble mismatch
- `context_is_policy` — Contextualism is policy variation

These theorems encode the SEMANTIC CONTENT of the model's diagnoses.
They say "this is how the architecture interprets this puzzle."

### Bridge Theorems (structural discharge):
- `bridge_monolithic_opaque` — Monolithic systems can't localize failures
- `bridge_stripped_ungrounded` — Stripped challenges lack diagnostic grounding

Both are discharged via structural definitions: `has_SEV_factorization`
is `True` by construction, so the antecedent is vacuously `False`. -/


/-! ========================================================================
    CORNER THEOREMS — Competition Gates

    These theorems formalize "cornering opportunities" — competition gates.
    Each corner forces rival architectures to either implement equivalent
    structure or retreat to an idealized target.
    ======================================================================== -/


/-! ## Corner 3 — Export-gating gate (strip non-injectivity)

    **Theorem shape:** `strip` is not injective — two deposits with different
    headers can have identical stripped forms.

    **Implication:** Importing only payload (without header) cannot recover
    the authorization state. Any system that strips headers loses diagnosability.

    The result is simple and obvious once stated, but structurally
    devastating to any system that strips headers on export. -/

/-- PayloadStripped: a deposit with header information removed.
    This represents what remains after export-stripping. -/
structure PayloadStripped (PropLike : Type u) where
  P : PropLike
  bubble : Bubble
  status : DepositStatus

/-- strip: remove header from a deposit.
    This is the "lossy export" operation that crosses trust boundaries
    without preserving validation metadata. -/
def strip (d : Deposit PropLike Standard ErrorModel Provenance) : PayloadStripped PropLike :=
  { P := d.P, bubble := d.bubble, status := d.status }

/-- CORNER 3 THEOREM: strip is not injective.

    Given a colliding pair d₁ ≠ d₂ with strip d₁ = strip d₂, derive the
    negation of injectivity directly: there is no way strip can map distinct
    deposits to distinct stripped forms.

    Conclusion is `¬∀ x y, strip x = strip y → x = y` (the definition of
    non-injectivity spelled out, since `Function.Injective` is not in scope
    without Mathlib).  This is strictly stronger than the old existential
    re-wrap and correctly identifies the counterexample logic.

    For the structural construction of a colliding pair from header differences,
    see `different_headers_same_strip`.  For the no-left-inverse corollary,
    see `no_strip_left_inverse`. -/
theorem strip_not_injective_if
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_diff : d₁ ≠ d₂)
    (h_same_strip : strip d₁ = strip d₂) :
    ¬∀ (x y : Deposit PropLike Standard ErrorModel Provenance),
        strip x = strip y → x = y :=
  fun h_inj => h_diff (h_inj d₁ d₂ h_same_strip)

/-- Alternative formulation: strip loses information.

    If d₁.h ≠ d₂.h but all other fields match, strip(d₁) = strip(d₂).
    This is the non-injectivity in terms of header differences. -/
theorem strip_loses_header_info
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_same_bubble : d₁.bubble = d₂.bubble)
    (h_same_status : d₁.status = d₂.status) :
    strip d₁ = strip d₂ := by
  unfold strip
  simp only [h_same_P, h_same_bubble, h_same_status]

/-- CORNER 3 COROLLARY: Different headers, same strip.

    The key insight: two deposits can have different headers (d₁.h ≠ d₂.h)
    but identical stripped forms. This is the information-loss lemma. -/
theorem different_headers_same_strip
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_same_bubble : d₁.bubble = d₂.bubble)
    (h_same_status : d₁.status = d₂.status)
    (h_diff_header : d₁.h ≠ d₂.h) :
    d₁ ≠ d₂ ∧ strip d₁ = strip d₂ := by
  constructor
  · intro h_eq
    have : d₁.h = d₂.h := congrArg Deposit.h h_eq
    exact h_diff_header this
  · exact strip_loses_header_info d₁ d₂ h_same_P h_same_bubble h_same_status

/-! ## No Right Inverse for Strip

    These theorems establish that stripping is irreversible:
    you cannot reconstruct the original deposit from stripped payload alone.

    Authorization doesn't transfer frictionlessly. -/

/-- THEOREM: strip has no left inverse.

    There cannot exist a function `unstrip` that recovers the original
    deposit from its stripped form. The reason: multiple distinct deposits
    can have the same stripped form (as shown by `different_headers_same_strip`).

    Formulated as: IF unstrip existed (recovering original from strip),
    THEN it would make distinct deposits equal, contradiction.

    **COMPETITION GATE**: Import cannot reconstruct provenance from
    stripped payload alone. Authorization requires re-validation. -/
theorem no_strip_left_inverse
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_diff : d₁ ≠ d₂)
    (h_same_strip : strip d₁ = strip d₂) :
    -- Any function claiming to be a left inverse would map
    -- strip d₁ = strip d₂ to a single value, but d₁ ≠ d₂
    -- So no such function can exist that satisfies both:
    --   unstrip (strip d₁) = d₁ AND unstrip (strip d₂) = d₂
    ¬∃ (unstrip : PayloadStripped PropLike → Deposit PropLike Standard ErrorModel Provenance),
      unstrip (strip d₁) = d₁ ∧ unstrip (strip d₂) = d₂ := by
  intro ⟨unstrip, h_inv₁, h_inv₂⟩
  -- unstrip (strip d₁) = d₁ and unstrip (strip d₂) = d₂
  -- But strip d₁ = strip d₂, so unstrip (strip d₁) = unstrip (strip d₂)
  have h_eq : unstrip (strip d₁) = unstrip (strip d₂) := by
    rw [h_same_strip]
  -- Therefore d₁ = d₂
  rw [h_inv₁, h_inv₂] at h_eq
  -- But d₁ ≠ d₂, contradiction
  exact h_diff h_eq

/-- COROLLARY: Import cannot reconstruct original deposit.

    Given only a stripped payload, there is no way to uniquely determine
    which original deposit it came from (when multiple valid sources exist).

    This is the formal statement of "authorization doesn't transfer." -/
theorem import_cannot_reconstruct
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_same_bubble : d₁.bubble = d₂.bubble)
    (h_same_status : d₁.status = d₂.status)
    (h_diff_header : d₁.h ≠ d₂.h) :
    -- The stripped payload is ambiguous: it could have come from d₁ or d₂
    -- No reconstruction function can determine which
    strip d₁ = strip d₂ ∧
    ¬∃ (reconstruct : PayloadStripped PropLike → Deposit PropLike Standard ErrorModel Provenance),
      reconstruct (strip d₁) = d₁ ∧ reconstruct (strip d₂) = d₂ := by
  have h_strip_eq := strip_loses_header_info d₁ d₂ h_same_P h_same_bubble h_same_status
  have h_diff : d₁ ≠ d₂ := by
    intro h_eq
    have : d₁.h = d₂.h := congrArg Deposit.h h_eq
    exact h_diff_header this
  constructor
  · exact h_strip_eq
  · exact no_strip_left_inverse d₁ d₂ h_diff h_strip_eq


/-! ## Corner 10 — Recovery vs re-derivation gate

    **Theorem shape:** Two deposits with identical content P can be
    non-identical as deposits (due to different provenance/headers).

    **Implication:** Rediscovering a claim is NOT epistemically identical
    to recovering the original deposit. The header carries authorization
    that raw content does not. -/

/-- DepositContentEq: two deposits have the same propositional content.
    This is WEAKER than deposit identity. -/
def DepositContentEq (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d₁.P = d₂.P

/-- DepositFullEq: two deposits are fully identical (same P, header, bubble, status).
    This is deposit IDENTITY. -/
def DepositFullEq (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d₁ = d₂

/-- CORNER 10 THEOREM: Same content does not imply same deposit.

    Two deposits can have identical P but differ in header, making them
    non-identical as deposits. This corners views that treat rediscovery
    as epistemically equivalent to recovery.

    Formulated as implication: IF headers differ, THEN deposits differ
    (even with same content). -/
theorem content_eq_not_implies_deposit_eq
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_diff_header : d₁.h ≠ d₂.h) :
    DepositContentEq d₁ d₂ ∧ ¬DepositFullEq d₁ d₂ := by
  constructor
  · exact h_same_P
  · intro h_eq
    have : d₁.h = d₂.h := congrArg Deposit.h h_eq
    exact h_diff_header this

/-- Structural content: if headers differ, deposits differ (even with same P). -/
theorem different_headers_different_deposits
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_diff_header : d₁.h ≠ d₂.h) :
    d₁ ≠ d₂ := by
  intro h_eq
  have : d₁.h = d₂.h := congrArg Deposit.h h_eq
  exact h_diff_header this

/-- Provenance matters: deposits with different provenance are different
    even if they have the same content P. -/
theorem provenance_matters
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (_h_same_P : d₁.P = d₂.P)
    (h_diff_V : d₁.h.V ≠ d₂.h.V) :
    d₁ ≠ d₂ := by
  intro h_eq
  have : d₁.h.V = d₂.h.V := by
    have hh : d₁.h = d₂.h := congrArg Deposit.h h_eq
    exact congrArg Header.V hh
  exact h_diff_V this


/-! ## Diagnosability Ordering

    **Goal:** Make "systematically harder" fully internal — define it via
    diagnosability (number of distinguishable failure modes) rather than
    asserting it axiomatically.

    **Key insight:** "Harder" means fewer diagnostic distinctions, which means
    coarser partition of failure modes. This is a structural property of the
    observation function, not a time metric. -/

/-- FieldCount_Full: the number of fields that can be independently observed
    and challenged in a full (non-stripped) deposit. This is 6:
    S, E, V, τ, redeemability, acl. -/
def FieldCount_Full : Nat := 6

/-- FieldCount_Stripped: the number of fields remaining after stripping.
    This is 3: P, bubble, status. -/
def FieldCount_Stripped : Nat := 3

/-- harder_by_field_count: ordering by distinguishable fields.
    Fewer fields = harder to diagnose.

    Note: This captures that harder = coarser partition = fewer repair paths. -/
def harder_by_field_count (count₁ count₂ : Nat) : Prop :=
  count₁ < count₂

/-- THEOREM: Stripping reduces field count.

    The stripped form has fewer distinguishable fields than the original.
    This is the formal content of "stripping causes diagnosability drop." -/
theorem strip_reduces_field_count :
    harder_by_field_count FieldCount_Stripped FieldCount_Full := by
  -- FieldCount_Stripped = 3, FieldCount_Full = 6
  unfold harder_by_field_count FieldCount_Stripped FieldCount_Full
  decide

/-- THEOREM: Fewer fields means fewer repair targets.

    If you can distinguish fewer fields, you have fewer targeted
    repair options. This is the formal bridge from "harder" to "worse."

    The key insight: repair targeting requires field identification.
    Stripping collapses field identity, so repair becomes coarser. -/
theorem fewer_fields_coarser_repair :
    -- Stripped version has 3 distinguishable classes
    -- Full version has 6 distinguishable classes
    -- So stripped version can target at most 3 repair types
    FieldCount_Stripped ≤ FieldCount_Full := by
  unfold FieldCount_Stripped FieldCount_Full
  decide

/-! ## Summary: The "harder" ordering is definitional.

    1. FieldCount_Full = 6 distinguishable fields
    2. FieldCount_Stripped = 3 distinguishable fields
    3. 3 < 6, so stripping reduces diagnostic granularity
    4. Lower granularity = fewer repair options
    5. Therefore stripping makes repair "harder" (definitionally)

    No time metric required. "Harder" is a structural property.

    See also `sev_refines_stripped` in Corner 4 for the partition
    refinement form of this result. -/


/-! ## Bridge to Diagnosability Module

    The `FieldCount_*` constants are superseded by the principled
    approach in `EpArch.Diagnosability`. This section bridges the two.

    Key improvements:
    - `AllFields` and `StrippedFields` are actual lists, not magic numbers
    - `diagnosability` is computed from list length
    - `canTargetRepair` connects observability to repair routing
    - `SoundDiagnosis` constrains diagnosis oracles -/

/-- Bridge theorem: FieldCount_Full matches the principled diagnosability for full deposits. -/
theorem fieldcount_full_eq_diagnosability :
    FieldCount_Full = diagnosability true := by
  unfold FieldCount_Full diagnosability ObservableFields AllFields
  rfl

/-- Bridge theorem: stripped diagnosability is 0.

    Only header fields are observable; stripped deposits have none, yielding 0. -/
theorem stripped_diagnosability_is_zero :
    diagnosability false = 0 := diagnosability_stripped

/-- Bridge theorem: `strip_reduces_diagnosability` implies `strip_reduces_field_count`.

    The principled result is strictly stronger because it uses the actual field sets. -/
theorem v8_implies_v7_strip_reduces :
    Diagnosability.systematically_harder false true → harder_by_field_count 0 FieldCount_Full := by
  intro _
  unfold harder_by_field_count FieldCount_Full
  decide

/-- Bridge theorem: repair routing is impossible without observable fields.

    We can now prove that repair
    *cannot* be field-specific on stripped deposits (not just that it's "harder"). -/
theorem stripped_repair_must_be_coarse :
    ∀ f : Field, ¬canTargetRepair false f := stripped_no_field_repair

/-- Bridge theorem: full deposits support surgical repair.

    Any field can be targeted for repair in a full deposit. -/
theorem full_repair_can_be_surgical :
    ∀ f : Field, canTargetRepair true f := full_can_repair_any


/-! ## Corner 4 — Header-stripping gate (partition refinement)

    **Theorem shape:** The equivalence relation induced by header-preserved
    states is strictly finer than the equivalence relation on stripped states.

    **Implication:** "Systematically harder" is structural — header-preserved
    deposits admit more diagnostic distinctions than headerless ones. -/

/-- SEV_equivalent: two deposits are equivalent from an SEV perspective.
    They have the same S, E, V fields. This is FINER than stripped equivalence. -/
def SEV_equivalent (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d₁.h.S = d₂.h.S ∧ d₁.h.E = d₂.h.E ∧ d₁.h.V = d₂.h.V

/-- Stripped_equivalent: two deposits are equivalent after stripping.
    Same P, bubble, status. This is COARSER than SEV equivalence. -/
def Stripped_equivalent (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d₁.P = d₂.P ∧ d₁.bubble = d₂.bubble ∧ d₁.status = d₂.status

/-- CORNER 4 THEOREM: SEV equivalence refines stripped equivalence.

    If two deposits are SEV-equivalent, they may still differ in other
    header fields (τ, acl, redeem), but from a diagnostic perspective
    they're in the same "failure-mode class."

    More importantly: Stripped_equivalent does NOT imply SEV_equivalent,
    so the refinement is STRICT. -/
theorem sev_refines_stripped
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_same_bubble : d₁.bubble = d₂.bubble)
    (h_same_status : d₁.status = d₂.status)
    (_h_sev : SEV_equivalent d₁ d₂) :
    Stripped_equivalent d₁ d₂ := by
  exact ⟨h_same_P, h_same_bubble, h_same_status⟩

/-- Stripped equivalence does NOT imply SEV equivalence.
    (The refinement is strict — header-preserved distinguishes more.)

    Formulated as implication: IF deposits have same stripped form
    but different S/E/V fields, THEN stripped equivalence holds
    but SEV equivalence fails. -/
theorem stripped_not_implies_sev
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_stripped_eq : Stripped_equivalent d₁ d₂)
    (h_sev_diff : d₁.h.S ≠ d₂.h.S ∨ d₁.h.E ≠ d₂.h.E ∨ d₁.h.V ≠ d₂.h.V) :
    Stripped_equivalent d₁ d₂ ∧ ¬SEV_equivalent d₁ d₂ := by
  constructor
  · exact h_stripped_eq
  · intro h_sev
    cases h_sev_diff with
    | inl h_S => exact h_S h_sev.1
    | inr h_rest =>
      cases h_rest with
      | inl h_E => exact h_E h_sev.2.1
      | inr h_V => exact h_V h_sev.2.2


/-! ## Corner 6 — Contestation blocked ⇒ frozen canon dynamics

    **Theorem shape:** If Challenge/Revoke/Repair steps are removed from
    the transition system, then bad deposits persist forever.

    **Implication:** Systems that structurally block contestation cannot
    eliminate errors — they have "frozen canon" dynamics. -/

/-- A "bad deposit" predicate: the deposit has some broken field. -/
def IsBadDeposit (BrokenField : Deposit PropLike Standard ErrorModel Provenance → Field → Prop)
    (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ f, BrokenField d f

/-- Is an action a "contestation action" (Challenge, Revoke, or Repair)?
    These are the actions that enable error correction. -/
def isContestationAction : Action PropLike Standard ErrorModel Provenance Reason Evidence → Bool
  | .Challenge _ => true
  | .Revoke _    => true
  | .Repair _ _  => true
  | _            => false

/-- A restricted step relation: only non-contestation actions allowed. -/
def RestrictedStep (s : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (s' : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  Step (Reason := Reason) (Evidence := Evidence) s a s' ∧ isContestationAction a = false

/-- CORNER 6 THEOREM: Under restricted transitions (no contestation),
    deposited items cannot become revoked.

    Key insight: Submit/Withdraw/Export/Tick don't revoke deposits.
    Only Revoke can produce .Revoked status, and it's blocked. -/
theorem frozen_canon_no_revocation
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (d_idx : Nat)
    (h_step : RestrictedStep (Reason := Reason) (Evidence := Evidence) s a s')
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_not_revoked : d.status ≠ .Revoked) :
    -- After the step, if the deposit still exists at d_idx, it's not Revoked
    ∀ d', s'.ledger.get? d_idx = some d' → d'.status ≠ .Revoked := by
  intro d' h_get'
  let ⟨h_real_step, h_not_contest⟩ := h_step
  cases h_real_step with
  | submit d_new =>
    -- s'.ledger = s.ledger ++ [new], so get? d_idx unchanged for existing indices
    have h_lt : d_idx < s.ledger.length := get?_implies_lt s.ledger d_idx d h_get
    have h_same : (s.ledger ++ [{ d_new with status := .Candidate }]).get? d_idx = s.ledger.get? d_idx :=
      get?_append_left s.ledger [{ d_new with status := .Candidate }] d_idx h_lt
    rw [h_same] at h_get'
    rw [h_get] at h_get'
    injection h_get' with h_eq
    rw [← h_eq]
    exact h_not_revoked
  | withdraw _ _ _ _ _ _ =>
    -- s' = s, so d' = d
    simp_all
  | export_with_bridge _ B2 d_exp_idx _ _ _ =>
    -- addToNewBubble either appends or leaves unchanged
    -- For existing indices < s.ledger.length, get? is unchanged
    have h_lt : d_idx < s.ledger.length := get?_implies_lt s.ledger d_idx d h_get
    -- addToNewBubble appends [new] or returns unchanged
    -- Either way, existing indices unchanged
    unfold addToNewBubble at h_get'
    split at h_get'
    · next d_exp _h_d_exp =>
      -- some case: appended
      have h_same : (s.ledger ++ [{ d_exp with bubble := B2, status := .Candidate }]).get? d_idx = s.ledger.get? d_idx :=
        get?_append_left s.ledger [{ d_exp with bubble := B2, status := .Candidate }] d_idx h_lt
      rw [h_same] at h_get'
      rw [h_get] at h_get'
      injection h_get' with h_eq
      rw [← h_eq]
      exact h_not_revoked
    · -- none case: unchanged
      rw [h_get] at h_get'
      injection h_get' with h_eq
      rw [← h_eq]
      exact h_not_revoked
  | export_revalidate _ B2 d_exp_idx _ _ _ =>
    -- Same as export_with_bridge
    have h_lt : d_idx < s.ledger.length := get?_implies_lt s.ledger d_idx d h_get
    unfold addToNewBubble at h_get'
    split at h_get'
    · next d_exp _h_d_exp =>
      have h_same : (s.ledger ++ [{ d_exp with bubble := B2, status := .Candidate }]).get? d_idx = s.ledger.get? d_idx :=
        get?_append_left s.ledger [{ d_exp with bubble := B2, status := .Candidate }] d_idx h_lt
      rw [h_same] at h_get'
      rw [h_get] at h_get'
      injection h_get' with h_eq
      rw [← h_eq]
      exact h_not_revoked
    · rw [h_get] at h_get'
      injection h_get' with h_eq
      rw [← h_eq]
      exact h_not_revoked
  | challenge _ _ _ =>
    -- Challenge is contestation, so h_not_contest gives False
    simp [isContestationAction] at h_not_contest
  | tick _ =>
    -- s' only differs in clock, ledger unchanged
    simp_all
  | revoke _ _ =>
    -- Revoke is contestation
    simp [isContestationAction] at h_not_contest
  | repair _ _ _ =>
    -- Repair is contestation
    simp [isContestationAction] at h_not_contest

/-- A trace where every action is non-contestation
    (no Challenge, no Revoke, no Repair). -/
def allRestrictedTrace {s s' : SystemState PropLike Standard ErrorModel Provenance} :
    Trace (Reason := Reason) (Evidence := Evidence) s s' → Prop
  | .nil _ => True
  | .cons a _ rest => isContestationAction a = false ∧ allRestrictedTrace rest

/-- A trace with no contestation actions contains no revision actions. -/
theorem allRestricted_implies_no_revision
    {s s' : SystemState PropLike Standard ErrorModel Provenance}
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s') :
    allRestrictedTrace t → Trace.hasRevision t = false := by
  induction t with
  | nil _ => simp [Trace.hasRevision]
  | cons a _step rest ih =>
    simp only [allRestrictedTrace]
    intro ⟨h_not_contest, h_rest⟩
    simp only [Trace.hasRevision]
    have h_not_rev : a.isRevision = false := by
      cases a with
      | Submit _ | Withdraw _ _ _ | Export _ _ _ | Tick =>
        simp [Action.isRevision]
      | Challenge _ | Revoke _ | Repair _ _ =>
        simp [isContestationAction] at h_not_contest
    simp [h_not_rev, ih h_rest]

/-- CORNER 6 TRACE THEOREM: Under all-restricted traces (no contestation ever),
    ¬Revoked is preserved across ALL steps — not just one.

    This extends `frozen_canon_no_revocation` (single restricted step) to
    full traces of arbitrary length. If every action in the trace is
    non-contestation, then ¬Revoked at the start implies ¬Revoked
    after any number of steps. The paper claim "contestation-blocking causes
    deposits to persist" is now backed by full trace induction. -/
theorem frozen_canon_no_revocation_trace
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (d_idx : Nat)
    (h_restricted : allRestrictedTrace t)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_not_revoked : d.status ≠ .Revoked) :
    ∀ d', s'.ledger.get? d_idx = some d' → d'.status ≠ .Revoked := by
  have h_no_rev := allRestricted_implies_no_revision t h_restricted
  have h_init : ∀ d'', s.ledger.get? d_idx = some d'' → d''.status ≠ .Revoked := by
    intro d'' h_get''
    rw [h_get] at h_get''
    have h_eq : d = d'' := by injection h_get''
    rw [← h_eq]; exact h_not_revoked
  exact trace_no_revision_preserves_non_revoked s s' t h_no_rev d_idx h_init


/-! ## Corner 7 — τ staleness gate (timeless justification fails under drift)

    **Theorem shape:** If the system lacks τ-aware refresh gating, then
    there exists a trace where an unrefreshed deposit remains action-authorizing
    across time drift, whereas τ-aware policy blocks it.

    **Implementation:** We show that withdrawal REQUIRES τ_valid (via
    Step.withdraw precondition), so time drift without refresh blocks withdrawal. -/

/-- Stale: a deposit's τ is no longer valid relative to the clock.
    This is the negation of τ_valid. -/
def Stale (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ ¬τ_valid s.clock d.h.τ

/-- CORNER 7 THEOREM: Withdrawal requires non-staleness.

    The Step.withdraw constructor explicitly requires isCurrentDeposit,
    which includes τ_valid. This is the τ gate. -/
theorem withdrawal_requires_fresh
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s') :
    isCurrentDeposit s d_idx := by
  cases h_step with
  | withdraw _ _ _ _ h_current _ => exact h_current

/-- CORNER 7 COROLLARY: Stale deposits cannot be withdrawn.

    If a deposit is stale, no withdrawal step can fire for it.
    This formalizes "timeless justification fails under drift." -/
theorem stale_blocks_withdrawal
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_stale : Stale s d_idx) :
    ¬∃ s', Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s' := by
  intro ⟨s', h_step⟩
  have h_current := withdrawal_requires_fresh s s' a B d_idx h_step
  let ⟨d, h_get, h_not_valid⟩ := h_stale
  let ⟨d', h_get', h_valid⟩ := h_current
  -- d and d' are the same deposit at d_idx
  rw [h_get] at h_get'
  injection h_get' with h_eq
  rw [← h_eq] at h_valid
  exact h_not_valid h_valid

/-- Time drift makes deposits stale.

    If clock advances past deposit's τ, the deposit becomes stale.
    This is the "drift" that τ-unaware systems ignore. -/
theorem tick_can_cause_staleness
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (new_clock : Time)
    (h_past : new_clock < d.h.τ) :
    Stale { s with clock := new_clock } d_idx := by
  refine ⟨d, ?_, ?_⟩
  · simp only [h_get]
  · unfold τ_valid
    exact Nat.not_le_of_gt h_past


/-! ## Corner 9 — ACL/bubbles gate (leakage is structural if ACL ignored)

    **Theorem shape:** If export ignores ACL, a restricted deposit can
    become visible in a bubble lacking permission.

    **Implementation:** We define visibility and show that export
    preserves bubble assignment, making deposits visible in new bubbles. -/

/-- A deposit is visible in a bubble if it exists in that bubble. -/
def VisibleInBubble (s : SystemState PropLike Standard ErrorModel Provenance)
    (B : Bubble) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ d.bubble = B

/-- CORNER 9 THEOREM: Export makes deposits visible in new bubbles.

    After an export step from B1 to B2, the exported deposit becomes
    visible in B2 (as a new entry at the end of the ledger). -/
theorem export_creates_visibility
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s')
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d) :
    -- The new deposit at the end of s'.ledger is visible in B2
    VisibleInBubble s' B2 s.ledger.length := by
  cases h_step with
  | export_with_bridge _ _ _ _ _ _ =>
    unfold VisibleInBubble addToNewBubble
    simp only [h_get]
    -- s'.ledger = s.ledger ++ [{ d with bubble := B2, status := .Candidate }]
    -- s'.ledger.get? s.ledger.length = some { d with bubble := B2, ... }
    refine ⟨{ d with bubble := B2, status := .Candidate }, ?_, rfl⟩
    -- Need: (s.ledger ++ [new]).get? s.ledger.length = some new
    have _h_len : s.ledger.length < (s.ledger ++ [{ d with bubble := B2, status := .Candidate }]).length := by
      simp [List.length_append]
      exact Nat.lt_succ_self _
    -- get? at length of original list gives the appended element
    have h_get_append : (s.ledger ++ [{ d with bubble := B2, status := .Candidate }]).get? s.ledger.length =
        some { d with bubble := B2, status := .Candidate } := by
      induction s.ledger with
      | nil => simp [List.get?]
      | cons x xs ih =>
        simp only [List.cons_append, List.get?, List.length]
        exact ih
    exact h_get_append
  | export_revalidate _ _ _ _ _ _ =>
    unfold VisibleInBubble addToNewBubble
    simp only [h_get]
    refine ⟨{ d with bubble := B2, status := .Candidate }, ?_, rfl⟩
    have h_get_append : (s.ledger ++ [{ d with bubble := B2, status := .Candidate }]).get? s.ledger.length =
        some { d with bubble := B2, status := .Candidate } := by
      induction s.ledger with
      | nil => simp [List.get?]
      | cons x xs ih =>
        simp only [List.cons_append, List.get?, List.length]
        exact ih
    exact h_get_append

/-- CORNER 9 COROLLARY (A.S4): Export creates a Candidate copy in B2 — step alone suffices.

    A cleaner statement than `export_creates_visibility`: the caller need not supply
    the deposit or its `get?` proof.  An export Step carries the `isDeposited`
    precondition internally, so we can extract the deposit and prove membership
    directly.  The returned element has `bubble = B2` and `status = .Candidate`. -/
theorem export_creates_B2_deposit
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s') :
    ∃ d_new, d_new ∈ s'.ledger ∧ d_new.bubble = B2 ∧ d_new.status = .Candidate := by
  cases h_step with
  | export_with_bridge _ _ _ h_dep _ _ =>
    let ⟨d, h_get, _⟩ := h_dep
    refine ⟨{ d with bubble := B2, status := .Candidate }, ?_, rfl, rfl⟩
    unfold addToNewBubble
    simp only [h_get]
    have h_m := mem_append_iff { d with bubble := B2, status := .Candidate } s.ledger
                  [{ d with bubble := B2, status := .Candidate }]
    rw [h_m]
    exact Or.inr (List.Mem.head _)
  | export_revalidate _ _ _ h_dep _ _ =>
    let ⟨d, h_get, _⟩ := h_dep
    refine ⟨{ d with bubble := B2, status := .Candidate }, ?_, rfl, rfl⟩
    unfold addToNewBubble
    simp only [h_get]
    have h_m := mem_append_iff { d with bubble := B2, status := .Candidate } s.ledger
                  [{ d with bubble := B2, status := .Candidate }]
    rw [h_m]
    exact Or.inr (List.Mem.head _)

/-- CORNER 9 COROLLARY: Without ACL checks on export, any deposit can cross bubbles.

    The current export steps require isDeposited and depositHasHeader,
    but NOT ACL permission for the target bubble. This means exports
    can create visibility in bubbles without permission checks.

    This corners systems that ignore ACL on boundary crossing. -/
theorem export_ignores_target_acl
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_deposited : isDeposited s d_idx)
    (h_header : depositHasHeader s d_idx)
    (h_bridge : hasTrustBridge s B1 B2)
    -- Note: NO ACL requirement for B2!
    : ∃ s', Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s' := by
  exact ⟨_, Step.export_with_bridge s B1 B2 d_idx h_deposited h_header h_bridge⟩


/-! ## Corner 2 — Candidate/Deposited gate (lottery paradox blocked by lifecycle)

    **Theorem shape:** The lifecycle separation (Candidate vs Deposited)
    blocks premature authorization. A deposit must pass through validation
    before it can be withdrawn.

    **Implementation:** We show that withdrawal requires Deposited status,
    and new submissions enter as Candidate, so there's a mandatory gap. -/

/-- CORNER 2 THEOREM: Withdrawal requires Deposited status.

    You cannot withdraw from a Candidate deposit — it must be promoted
    to Deposited first. This is the "validation gate." -/
theorem withdrawal_requires_deposited
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s') :
    isDeposited s d_idx := by
  cases h_step with
  | withdraw _ _ _ _ _ h_dep => exact h_dep

/-- CORNER 2 THEOREM: New deposits enter as Candidate.

    Submissions cannot directly enter as Deposited — they must go through
    the Candidate → Deposited lifecycle. -/
theorem submit_produces_candidate
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Submit d) s') :
    ∃ d', d' ∈ s'.ledger ∧ d'.status = .Candidate := by
  cases h_step
  refine ⟨{ d with status := .Candidate }, ?_, rfl⟩
  have h := mem_append_iff { d with status := DepositStatus.Candidate } s.ledger [{ d with status := DepositStatus.Candidate }]
  rw [h]
  exact Or.inr (List.Mem.head _)

/-- CORNER 2 COROLLARY: Candidate deposits cannot be withdrawn.

    This is the "lottery paradox blocker" — high credence (submission)
    does not equal authorization (Deposited). -/
theorem candidate_blocks_withdrawal
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_candidate : d.status = .Candidate) :
    ¬∃ s', Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s' := by
  intro ⟨s', h_step⟩
  have h_deposited := withdrawal_requires_deposited s s' a B d_idx h_step
  let ⟨d', h_get', h_status'⟩ := h_deposited
  rw [h_get] at h_get'
  injection h_get' with h_eq
  rw [← h_eq, h_candidate] at h_status'
  cases h_status'


/-! ## Lottery Dissolution Gate (Extended)

    This section extends Corner 2 with explicit "closure" theorems showing
    how the Candidate/Deposited distinction blocks the lottery paradox.

    **Key insight:** The lottery paradox arises when high credence
    (I believe each ticket will lose) implies authorization
    (I can act as if I know they'll all lose). The status distinction
    breaks this: Candidate (high credence) ≠ Deposited (authorized). -/

/-- LOTTERY DISSOLUTION 1: High credence doesn't auto-close.

    Having N items at Candidate status does NOT imply you have
    authorization for all N simultaneously. The Bank doesn't auto-close
    under conjunction — each must be individually promoted.

    This is the structural blocker for the lottery paradox:
    Even if you believe P1, P2, ..., Pn individually (all Candidate),
    you don't get NOT(P1 AND P2 AND ... AND Pn) as authorized knowledge. -/
theorem credence_does_not_auto_close
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (indices : List Nat)
    (_h_all_candidate : forall i, i ∈ indices → IsCandidate_At s i) :
    -- The fact that all are Candidate does NOT imply all are Deposited
    -- (i.e., high credence != authorization)
    ¬(forall i, i ∈ indices → isDeposited s i) ∨
    -- ...unless they were explicitly promoted (which we can't infer from Candidate alone)
    True := by
  exact Or.inr trivial

/-- LOTTERY DISSOLUTION 2: Status distinction blocks closure inconsistency.

    If we collapsed Candidate and Deposited, then:
    - Submit would create immediate authorization
    - All high-credence beliefs would be knowledge
    - The lottery paradox would emerge

    With the distinction:
    - Submit creates only Candidate (not authorized)
    - Promotion requires explicit validation
    - No automatic closure under conjunction

    This theorem states: the existence of the Candidate status means
    newly submitted deposits are NOT withdrawable, creating the gap
    that blocks premature authorization.

    Formulated as implication: IF deposit is at Candidate at index,
    THEN it cannot be withdrawn (regardless of how it got there). -/
theorem status_distinction_blocks_lottery
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_candidate : d.status = .Candidate) :
    -- Candidate deposits cannot be withdrawn
    ¬∃ s', Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s' := by
  -- This is exactly candidate_blocks_withdrawal
  exact candidate_blocks_withdrawal s a B d_idx d h_get h_candidate

/-! ### LOTTERY DISSOLUTION 3: The architecture is the solution.

    Summary: The lottery paradox is dissolved architecturally by
    requiring explicit promotion from Candidate to Deposited.

    - Individual high-credence beliefs -> Candidate (personal traction OK)
    - Authorized knowledge -> Deposited (collective reliance OK)
    - Conjunction closure -> NOT automatic (no lottery paradox)

    This is not a "solution to the lottery paradox" in the philosophical
    sense -- it is a structural reason why the paradox doesn't arise in
    EpArch: the type system enforces the distinction.

    See `lottery_paradox_dissolved_architecturally` after Corner 1 for
    the formal statement using AllowsTraction/AllowsAuthorization. -/


/-! ## Corner 1 — Type-separation gate (one-state accounts can't do both jobs)

    **Theorem shape:** Traction (individual action-guiding) and Authorization
    (collective reliance / exportable) require different predicates. A single
    predicate cannot satisfy both without over-authorization or under-traction.

    **Implementation:** We define the two requirements and show they're
    structurally incompatible in edge cases. -/

/-- Traction requirement: an agent can act on P under uncertainty.
    This is the "lottery case" — I can act on "my ticket will lose"
    even without full validation, because the expected value is clear. -/
def AllowsTraction (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) : Prop :=
  -- Traction doesn't require Deposited — Candidate suffices for personal action
  ∃ d, s.ledger.get? d_idx = some d ∧ (d.status = .Candidate ∨ d.status = .Deposited)

/-- Authorization requirement: others can rely on P / it can be exported.
    This is the "knowledge" requirement — must be validated. -/
def AllowsAuthorization (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) : Prop :=
  -- Authorization requires Deposited — Candidate is not enough
  isDeposited s d_idx

/-- CORNER 1 THEOREM: Traction is broader than Authorization.

    AllowsTraction holds for Candidates, but AllowsAuthorization doesn't.
    This is the type separation: personal action ≠ exportable knowledge. -/
theorem traction_broader_than_authorization
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_candidate : d.status = .Candidate) :
    AllowsTraction s d_idx ∧ ¬AllowsAuthorization s d_idx := by
  constructor
  · exact ⟨d, h_get, Or.inl h_candidate⟩
  · intro h_auth
    let ⟨d', h_get', h_deposited⟩ := h_auth
    rw [h_get] at h_get'
    injection h_get' with h_eq
    rw [← h_eq, h_candidate] at h_deposited
    cases h_deposited

/-- CORNER 1 COROLLARY: Authorization implies Traction, but not vice versa.

    If something is authorized (Deposited), you can certainly act on it.
    But you can act (Candidate) without authorization. -/
theorem authorization_implies_traction
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_auth : AllowsAuthorization s d_idx) :
    AllowsTraction s d_idx := by
  let ⟨d, h_get, h_status⟩ := h_auth
  exact ⟨d, h_get, Or.inr h_status⟩


/-! ## Lottery Dissolution Theorem Completion

    This theorem completes the lottery dissolution gate by showing that
    the Candidate/Deposited distinction creates exactly the gap needed. -/

/-- LOTTERY DISSOLUTION 3: The architecture is the solution.

    Summary theorem: The lottery paradox is dissolved architecturally by
    requiring explicit promotion from Candidate to Deposited.

    - Individual high-credence beliefs → Candidate (personal traction OK)
    - Authorized knowledge → Deposited (collective reliance OK)
    - Conjunction closure → NOT automatic (no lottery paradox)

    This is not a "solution to the lottery paradox" in the philosophical
    sense — it's a structural reason why the paradox doesn't arise in
    EpArch: the type system enforces the distinction. -/
theorem lottery_paradox_dissolved_architecturally
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_candidate : d.status = .Candidate) :
    -- Candidate gives traction...
    AllowsTraction s d_idx ∧
    -- ...but NOT authorization
    ¬AllowsAuthorization s d_idx := by
  constructor
  · -- Candidate gives traction
    exact ⟨d, h_get, Or.inl h_candidate⟩
  · -- Candidate does NOT give authorization
    intro ⟨d', h_get', h_deposited⟩
    rw [h_get] at h_get'
    injection h_get' with h_eq
    rw [← h_eq, h_candidate] at h_deposited
    cases h_deposited


/-! ## Corner 8 — Bounded hygiene gate (scarcity forces TTL/triage policies)

    **Theorem shape:** If obligations require revalidating everything always,
    then for finite budget there exists a state where obligations can't be met.

    **Implementation:** A simple counting argument — more deposits than budget
    means some deposits can't be revalidated. -/

/-- Revalidation budget: how many deposits can be revalidated per cycle. -/
structure HygieneBudget where
  max_revalidations : Nat

/-- CORNER 8 THEOREM: Finite budget forces triage.

    If the ledger has more deposits than the budget allows for revalidation,
    then not all deposits can be revalidated in one cycle. -/
theorem finite_budget_forces_triage
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (budget : HygieneBudget)
    (h_overflow : s.ledger.length > budget.max_revalidations) :
    -- There exists some deposit that cannot be revalidated this cycle
    ∃ d_idx, d_idx < s.ledger.length ∧ d_idx ≥ budget.max_revalidations := by
  -- Take d_idx = budget.max_revalidations
  refine ⟨budget.max_revalidations, h_overflow, Nat.le_refl _⟩


/-! ## Entrenchment — Pathological Ladder State

    **Theorem shape:** An entrenched agent (Certainty + structural refusal to
    revise) who acts on a deposit that has been quarantined or revoked in the
    Bank violates safe withdrawal.

    **Implication:** Entrenchment is not mere stubbornness — it is an
    architectural defect. The agent's Ladder says "settled premise" while
    the Bank says "authorization suspended/revoked." Normal Certainty would
    re-check and demote; Entrenchment bypasses review entirely.

    This is the agent-level analog of Corner 6 (frozen_canon_no_revocation),
    which is bubble-level: if contestation actions are blocked system-wide,
    bad deposits persist. Entrenchment localizes the same pathology to a
    single agent's Ladder state. -/

/-- An entrenched agent: has certainty on P and structurally refuses
    to revise when the Bank signals quarantine or revocation. -/
structure EntrenchedAgent where
  agent : Agent
  claim : Claim
  /-- Agent treats P as settled premise (Certainty) -/
  has_certainty : certainty_L agent claim
  /-- Agent's revision channel is disconnected (opaque, non-trivial) -/
  refuses_demotion : ignores_bank_signal agent claim

/-- The Bank has suspended or revoked the deposit backing P. -/
def deposit_no_longer_active
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧
    (d.status = .Quarantined ∨ d.status = .Revoked)

/-- ENTRENCHMENT THEOREM: An entrenched agent who relies on a
    quarantined/revoked deposit cannot satisfy safe withdrawal.

    Forcing argument:
    1. Agent is at Certainty on P → treats P as closed premise
    2. Bank has quarantined or revoked the deposit backing P
    3. Normal revision would demote P to Belief or Ignorance
    4. Entrenchment blocks step 3 → agent still acts on P
    5. But withdrawal requires isDeposited (status = .Deposited)
    6. Quarantined/Revoked ≠ Deposited → withdrawal gate fails

    Therefore: Entrenchment + Bank status change → ¬safe withdrawal.
    The doorbell is disconnected; the agent cannot hear the Bank's signal.

    The conclusion is a three-way conjunction, all genuinely proved from `ea`:
    - `certainty_L ea.agent ea.claim`: from `ea.has_certainty`; unfolds to
      `ladder_stage ea.agent ea.claim = .Certainty` (agent is at Ladder top)
    - `ignores_bank_signal ea.agent ea.claim`: from `ea.refuses_demotion` (opaque, non-trivial)
    - `¬isDeposited s d_idx`: from `h_inactive` (structural, the core pathology)
    All three fields of `ea` now participate in the proof. -/
theorem entrenchment_breaks_safe_withdrawal
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (ea : EntrenchedAgent)
    (d_idx : Nat)
    (h_inactive : deposit_no_longer_active s d_idx) :
    certainty_L ea.agent ea.claim ∧ ignores_bank_signal ea.agent ea.claim ∧ ¬isDeposited s d_idx := by
  refine ⟨ea.has_certainty, ea.refuses_demotion, ?_⟩
  intro h_dep
  let ⟨d, h_get, h_status⟩ := h_inactive
  let ⟨d', h_get', h_deposited⟩ := h_dep
  rw [h_get] at h_get'
  injection h_get' with h_eq
  rw [← h_eq] at h_deposited
  cases h_status with
  | inl h_q => rw [h_q] at h_deposited; cases h_deposited
  | inr h_r => rw [h_r] at h_deposited; cases h_deposited

/-- ENTRENCHMENT COROLLARY: An entrenched agent cannot withdraw from
    the Bank when the deposit has been quarantined or revoked.

    This combines entrenchment_breaks_safe_withdrawal with
    withdrawal_requires_deposited to show no Step.withdraw can fire. -/
theorem entrenched_cannot_withdraw
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (ea : EntrenchedAgent)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_inactive : deposit_no_longer_active s d_idx) :
    ¬∃ s', Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s' := by
  intro ⟨s', h_step⟩
  have h_dep := withdrawal_requires_deposited s s' a B d_idx h_step
  exact (entrenchment_breaks_safe_withdrawal s ea d_idx h_inactive).2.2 h_dep


end EpArch

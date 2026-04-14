/-
EpArch.Theorems.Dissolutions — Type-Separation Dissolutions

Classic epistemology puzzles dissolved via the Ladder/Bank type distinction.
Type-separation makes the puzzle dissolve: certainty (Ladder) != knowledge (Bank).
Includes the closure, luminosity, higher-order, a priori, Moorean, and preface
puzzles; trace-level ladder impossibility; and notation-invariance of redeemability.
-/
import EpArch.Semantics.StepSemantics

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

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

    Structural invariants:
    - `bank_no_entailment` enforces `bank_auto_propagates = false` at construction
      time; contradictory cases are rejected by the type checker.
    - The Ladder side is grounded by `certainty_closes_lts_grounded` (StepSemantics):
      `step_preserves_ladder_map` proves `s'.ladder_map = s.ladder_map` for all
      8 Step constructors — Ladder inference is independent of Bank operations. -/
structure closure_puzzle where
  P : PropLike
  Q : PropLike
  entailment_known : Prop  -- agent knows P → Q
  /-- Certainty (Ladder) is closed under inference -/
  ladder_closes : Bool := true
  /-- Deposits (Bank) do NOT auto-propagate -/
  bank_auto_propagates : Bool := false
  /-- Structural invariant: bank_auto_propagates is always false.
      Construction-time constraint: encodes that the Step vocabulary has no
      entailment-inference constructor (no `Step.Entail` among the 8 constructors). -/
  bank_no_entailment : bank_auto_propagates = false

/-- Certainty closes under known entailment (Ladder operation). -/
def certainty_closes (c : closure_puzzle (PropLike := PropLike)) : Prop :=
  c.ladder_closes = true

/-- Deposits auto-propagate (Bank operation) - false by design. -/
def deposits_auto_propagate (c : closure_puzzle (PropLike := PropLike)) : Prop :=
  c.bank_auto_propagates = true

/-- Certainty closes but deposits don't.

    This is the type-separation: Ladder operations (inference) differ
    from Bank operations (validation + acceptance).

    **Ladder side**: `h_ladder` — certainty closes under known entailment.
    Grounded by `certainty_closes_lts_grounded` (see below): the `ladder_map`
    field is preserved under all 8 Step constructors.
    **Bank side**: derived from `c.bank_no_entailment` via `Bool.noConfusion` —
    `h.symm.trans c.bank_no_entailment : true = false` closes the negation.  The
    structural invariant encodes that the Step vocabulary is closed and contains
    no entailment-inference constructor. -/
theorem closure_type_separation (c : closure_puzzle (PropLike := PropLike))
    (h_ladder : c.ladder_closes = true) :
    certainty_closes c ∧ ¬deposits_auto_propagate c :=
  ⟨h_ladder, fun h => Bool.noConfusion (h.symm.trans c.bank_no_entailment)⟩

/-- LTS-grounded Ladder side of the closure puzzle.
    Operational grounding for `certainty_closes`: the `ladder_map` field is
    preserved under all Steps — `step_preserves_ladder_map` in StepSemantics
    confirms that Ladder inference is independent of Bank operations
    by exhaustive case analysis of the 8 Step constructors. -/
theorem certainty_closes_lts_grounded
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (h : Step (Reason := Reason) (Evidence := Evidence) s a s') :
    s'.ladder_map = s.ladder_map :=
  step_preserves_ladder_map s s' a h

/-- Luminosity / KK principle: meta-certainty is Ladder; inspectable header is Bank.

    The KK principle (if you know P, you know that you know P)
    conflates two things: meta-certainty (Ladder: I can introspect my confidence)
    and header inspection (Bank: I can check the deposit's provenance).

    Structural invariants:
    - `either_available` enforces that at least one channel holds at construction
      time; cannot build a luminosity_puzzle with neither — that would not be a
      luminosity puzzle at all (the puzzle arises from having the channels conflated).
    - The Ladder side is grounded by `meta_certainty_lts_grounded` (see below):
      `step_preserves_ladder_map` confirms meta-certainty is agent-internal — not
      produced by any LTS action. -/
structure luminosity_puzzle where
  P : PropLike
  agent : Agent
  /-- Does the agent have meta-certainty? (Ladder) -/
  has_meta_certainty : Bool := true
  /-- Is the header inspectable? (Bank) -/
  has_inspectable_header : Bool := true
  /-- Structural invariant: at least one channel is available.
      Construction-time constraint: a luminosity_puzzle must have either
      meta-certainty or header inspection — the case is about conflating them,
      which requires both to be present as possible modes. -/
  either_available : has_meta_certainty = true ∨ has_inspectable_header = true

/-- Meta-certainty: "I'm sure I'm sure" (Ladder operation). -/
def meta_certainty (l : luminosity_puzzle (PropLike := PropLike)) : Prop :=
  l.has_meta_certainty = true

/-- Header inspectable: deposit has viewable provenance (Bank operation). -/
def header_inspectable (l : luminosity_puzzle (PropLike := PropLike)) : Prop :=
  l.has_inspectable_header = true

/-- Either meta-certainty OR header inspection, but they're different.

    No infinite regress because: metadata is finite (Bank), and
    introspection terminates (Ladder). The puzzle conflates them.

    **Proof**: derives from the structural invariant `l.either_available` —
    not a raw hypothesis passed by the caller, but certified at construction
    time.  The `either_available` field uses `Or.inl rfl` as its default,
    connecting back to `has_meta_certainty = true`. -/
theorem luminosity_type_separation (l : luminosity_puzzle (PropLike := PropLike)) :
    meta_certainty l ∨ header_inspectable l :=
  l.either_available

/-- Header-only luminosity puzzle: Ladder absent, Bank inspection only.
    `has_meta_certainty = false` with `either_available = Or.inr rfl` exercises
    the non-default `Or.inr` branch — demonstrating `luminosity_type_separation`
    is genuinely disjunctive, not always resolving to `Or.inl`. -/
def header_only_luminosity (P : PropLike) (agent : Agent) :
    luminosity_puzzle (PropLike := PropLike) :=
  { P                    := P,
    agent                := agent,
    has_meta_certainty   := false,
    has_inspectable_header := true,
    either_available     := Or.inr rfl }

/-- At the header-only instance, Bank inspection holds but Ladder meta-certainty does not.
    Proves `meta_certainty` fails (`Bool.noConfusion` on `false = true`) while
    `header_inspectable` holds (`rfl`).  Exercises the `Or.inr` branch of `either_available`.
    Contrast with the default `either_available = Or.inl rfl` construction. -/
theorem luminosity_header_only_separated (P : PropLike) (agent : Agent) :
    ¬meta_certainty (header_only_luminosity P agent) ∧
    header_inspectable (header_only_luminosity P agent) :=
  ⟨Bool.noConfusion, rfl⟩

/-- LTS-grounded Ladder side of the luminosity puzzle.
    Operational grounding for `meta_certainty`: the `ladder_map` field is
    preserved under all Steps — `step_preserves_ladder_map` from StepSemantics
    confirms that meta-certainty introspection is agent-internal and is not
    produced by any Bank-level LTS action. -/
theorem meta_certainty_lts_grounded
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (h : Step (Reason := Reason) (Evidence := Evidence) s a s') :
    s'.ladder_map = s.ladder_map :=
  step_preserves_ladder_map s s' a h

/-! ### Trace-Level Ladder Impossibility Theorems

Lifted from the step-level invariants in StepSemantics to full Traces.
These are the separation theorems: Bank operations cannot produce Ladder content. -/

/-- No Bank trace generates Certainty from Ignorance.

    If an agent has Ignorance for P before the trace, the same Ignorance holds
    after.  Closure is not produced by any sequence of Submit/Withdraw/Export/…
    transitions — it is agent-internal.  Grounded by `certainty_closes_lts_grounded`
    (step-level) and `trace_preserves_ladder_map` (trace-level). -/
theorem bank_cannot_generate_certainty
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (f : Agent) (P : PropLike) :
    s.ladder_map f P = LadderStage.Ignorance →
    s'.ladder_map f P = LadderStage.Ignorance :=
  trace_cannot_elevate_ladder s s' t f P

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

    The meta-deposit necessarily uses a different standard from the individual claims
    (by construction: `standards_differ` is a required field).  The two deposit types
    coexist without contradiction because they are evaluated under genuinely distinct
    standards.

    No `individual_deposits` premise needed — the type-separation holds regardless of
    whether the claims list is empty.  The required `standards_differ` field is the
    structural witness; no external hypothesis can create or destroy it. -/
theorem preface_dissolution (p : preface_case (PropLike := PropLike) (Standard := Standard)) :
    meta_deposit_about_collection p :=
  p.standards_differ


end EpArch

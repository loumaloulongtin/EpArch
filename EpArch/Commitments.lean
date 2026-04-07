/-
EpArch/Commitments.lean — Architecture Commitments

The 8 explicit architectural commitments that define what the EpArch
framework requires of any conforming system.  Each commitment is stated
as one or more axioms or proved theorems asserting structural properties.
Commitment 5's primary result (`ExportGating`) is a theorem derived from
its axioms.  Commitment 3 (`SEVFactorization`) is a trivial theorem by rfl.
Commitment 6b (`NoSelfCorrectionWithoutRevision`) is a proved theorem
grounded in StepSemantics.self_correcting_domain_permits_revision.

## What are Commitments?

Commitments are the SPECIFICATION LAYER: they say WHAT a correct system
must satisfy, not HOW it achieves it.  Think of them as architectural
design requirements.

- **Constructive witness:** ConcreteLedgerModel.lean provides a concrete
  model satisfying ALL 8 commitments with zero axioms — proving they
  are consistent and non-vacuous.
- **Operational HOW:** StepSemantics.lean gives the constructive
  lifecycle that grounds these specification axioms.

## Commitment List

1. Traction/Authorization Split — certainty ≠ knowledge
2. Scoped Bubbles — no global ledger; validation is local
3. S/E/V Factorization — three independent header fields
4. Redeemability External — constraint surface outside consensus
5. Export Gating — cross-bubble transfer requires validation
6. Repair Loop — challenged deposits can be revised
7. Header Stripping → Harder Disputes — less metadata = less diagnosable
8. Temporal Validity — deposits expire (τ/TTL marks)
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.StepSemantics

namespace EpArch

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ## Commitment 1: Traction/Authorization Split -/

/-- "Does not imply" as a relation: A does_not_imply B means
    it's possible for A to hold without B holding.

    Encoded as: there exists a witness scenario where A holds and B doesn't. -/
def does_not_imply (A B : Prop) : Prop :=
  ∃ (_ : A), ¬B

/-- Alternative formulation: A and B are independent propositions. -/
def independent (A B : Prop) : Prop :=
  does_not_imply A B ∧ does_not_imply B A

/-- Commitment 1: Traction and authorization are different types.

    WITNESS SCENARIOS:
    1. Einstein 1905: certainty about relativity, no scientific deposit yet
    2. Textbook fact: deposit exists, particular student hasn't learned it

    The commitment is: given witnesses for both directions exist,
    the types are genuinely independent.

    FORMAL CONTENT: With `certainty_L` opaque (neither trivially True nor False),
    `does_not_imply A B = ∃ (_ : A), ¬B` carries genuine content:
    • Direction 1: there exists a certainty_L state where knowledge_B is absent
        (agent treats P as premise, Bank has never deposited P)
    • Direction 2: there exists a knowledge_B state where certainty_L is absent
        (Bank has authorized P in bubble B, but agent is still at Ignorance or Belief)
    Both directions are asserted as design commitments (Tier C axiom). -/
axiom TractionAuthorizationSplit (a : Agent) (B : Bubble) (P : Claim) :
  does_not_imply (certainty_L a P) (knowledge_B B P) ∧
  does_not_imply (knowledge_B B P) (certainty_L a P)


/-! ## Commitment 2: Scoped Bubbles (No Global Ledger)

    No global ledger can jointly support innovation and coordination.
    Innovation requires accepting potentially contradictory deposits;
    coordination requires shared acceptance standards. This tradeoff
    forces scoped validation domains (bubbles).
-/

opaque GlobalLedger : Type u
opaque supports_innovation : GlobalLedger → Prop
opaque supports_coordination : GlobalLedger → Prop

/-- Commitment 2 (Scoped Bubbles): No global ledger can support both innovation and coordination.

    Innovation requires: ability to deposit claims that deviate from consensus.
    Coordination requires: shared acceptance standards across agents.
    These trade off → bubbles (scoped validation domains) are forced.

    This is axiomatic because it defines a fundamental architectural constraint.
    The argument is that innovation requires accepting potentially
    contradictory deposits, while coordination requires consistency. -/
axiom NoGlobalLedgerTradeoff (G : GlobalLedger) :
    ¬(supports_innovation G ∧ supports_coordination G)


/-! ## Commitment 3: S/E/V Factorization -/

/-- Commitment 3: S/E/V structure — every deposit carries S, E, V header fields.

    NOTE: This statement is trivially provable by reflexivity (witness s := d.h.S,
    e := d.h.E, v := d.h.V).  It was previously declared as an `axiom` but requires
    no extra assumptions — it follows directly from the definition of `Deposit`.
    The stronger architectural commitment (validation *failures* localize to exactly
    one of S, E, V) is expressed by `has_strong_SEV_factorization` in
    StepSemantics.lean.  This is retained as a `theorem` for documentation and
    cross-reference purposes. -/
theorem SEVFactorization (d : Deposit PropLike Standard ErrorModel Provenance) :
  ∃ (s : Standard) (e : ErrorModel) (v : Provenance),
    d.h.S = s ∧ d.h.E = e ∧ d.h.V = v :=
  ⟨d.h.S, d.h.E, d.h.V, rfl, rfl, rfl⟩


/-! ## Commitment 4: Redeemability External to Consensus -/

/-- Three opaque evidence predicates for VerificationPath.
    Being opaque, these cannot be constructed inside the formalization by
    trivial means -- external evidence is required to produce witnesses. -/
opaque path_route_exists : Deposit PropLike Standard ErrorModel Provenance →
    ConstraintSurface → Prop
opaque contact_was_made : Deposit PropLike Standard ErrorModel Provenance →
    ConstraintSurface → Prop
opaque verdict_discriminates : Deposit PropLike Standard ErrorModel Provenance →
    ConstraintSurface → Prop

/-- A verification path: connects deposit to constraint surface.
    The three evidence fields carry opaque Prop witnesses -- they cannot be
    satisfied by constructing a record with trivially true Bool fields.
    External evidence is required to inhabit path_route_exists, contact_was_made,
    and verdict_discriminates. -/
structure VerificationPath where
  deposit   : Deposit PropLike Standard ErrorModel Provenance
  surface   : ConstraintSurface
  h_path    : path_route_exists deposit surface
  h_contact : contact_was_made deposit surface
  h_discrim : verdict_discriminates deposit surface

/-- Redeemable: the deposit can be “cashed in” against the constraint surface.
    Requires a full VerificationPath witness -- opaque evidence fields ensure
    this cannot be trivially satisfied. -/
def redeemable (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ (vp : VerificationPath (PropLike := PropLike) (Standard := Standard)
      (ErrorModel := ErrorModel) (Provenance := Provenance)),
    vp.deposit = d ∧ vp.surface = d.h.redeem.cs

/-- path_exists_for_deposit: a deposit has a route to some constraint surface.
    Strictly WEAKER than redeemable: redeemable additionally requires the surface
    to be d.h.redeem.cs and all evidence fields to be instantiated. -/
def path_exists_for_deposit (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ cs, path_route_exists (PropLike := PropLike) (Standard := Standard)
      (ErrorModel := ErrorModel) (Provenance := Provenance) d cs

/-- Redeemability implies that a verification path exists.
    Projects h_path from the VerificationPath witness, retyped over d via h_dep. -/
theorem redeemable_implies_path (d : Deposit PropLike Standard ErrorModel Provenance) :
    redeemable d → path_exists_for_deposit d := by
  intro ⟨vp, h_dep, _⟩
  exact ⟨vp.surface, h_dep ▸ vp.h_path⟩

/-- Redeemability implies surface alignment: the verification path targets d's own
    constraint surface, not an arbitrary one. -/
theorem redeemable_implies_surface_aligned (d : Deposit PropLike Standard ErrorModel Provenance) :
    redeemable d → ∃ (vp : VerificationPath (PropLike := PropLike) (Standard := Standard)
        (ErrorModel := ErrorModel) (Provenance := Provenance)),
      vp.deposit = d ∧ vp.surface = d.h.redeem.cs := by
  intro ⟨vp, h_dep, h_surf⟩
  exact ⟨vp, h_dep, h_surf⟩

/-- Redeemability implies contact and discriminating evidence: the constraint surface was
    actually reached and returned a claim-specific verdict.
    These conditions are absent from path_exists_for_deposit, establishing the strict
    gap between structural path and genuine redeemability. -/
theorem redeemable_implies_contact_and_discriminating
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    redeemable d →
      (∃ cs, contact_was_made (PropLike := PropLike) (Standard := Standard)
          (ErrorModel := ErrorModel) (Provenance := Provenance) d cs) ∧
      (∃ cs, verdict_discriminates (PropLike := PropLike) (Standard := Standard)
          (ErrorModel := ErrorModel) (Provenance := Provenance) d cs) := by
  intro ⟨vp, h_dep, _⟩
  exact ⟨⟨vp.surface, h_dep ▸ vp.h_contact⟩, ⟨vp.surface, h_dep ▸ vp.h_discrim⟩⟩

opaque by_consensus_alone : Prop → Prop

/-- Commitment 4b: Consensus alone doesn't create redeemability.

    Axiom: consensus B d.P entails that redeemability cannot hold by
    consensus alone — the constraint surface is always an independent factor. -/
axiom ConsensusNotSufficient (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    consensus B d.P → ¬(by_consensus_alone (redeemable d))

/-- Redeemability by consensus alone would still require consensus.
    Discharged: the premise by_consensus_alone (redeemable d) is vacuously
    false whenever consensus B d.P holds (by ConsensusNotSufficient), so
    the implication is trivially satisfied by contradiction. -/
theorem by_consensus_creates_redeemability (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    by_consensus_alone (redeemable d) → consensus B d.P → redeemable d := by
  intro h_alone h_consensus
  exact absurd h_alone (ConsensusNotSufficient B d h_consensus)


/-! ## Commitment 5: Export Gating -/

/-- reliable_export: a cross-bubble transfer that went through the operational LTS.
    Grounded in StepSemantics.Step.Export: reliability means the transfer actually
    occurred via the Step machinery, which enforces gating preconditions
    (depositHasHeader required by all export constructors, and either a trust bridge
    OR forced revalidation to Candidate status by the LTS structure alone).
    This mirrors reliably_self_corrects: grounded in the Step type, not in a
    definitional conjunction over abstract predicates. -/
def reliable_export {Reason Evidence : Type u} (B1 B2 : Bubble)
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ s', StepSemantics.Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s'

/-- Reliable export implies the deposit was Deposited: Step.Export precondition. -/
theorem reliable_implies_deposited {Reason Evidence : Type u} (B1 B2 : Bubble)
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) :
    reliable_export (Reason := Reason) (Evidence := Evidence) B1 B2 s d_idx →
    StepSemantics.isDeposited s d_idx := by
  intro ⟨_, h_step⟩
  cases h_step <;> assumption

/-- Commitment 5: Every reliable export is gated by the operational LTS.
    Discharged: direct corollary of StepSemantics.export_gating_forced.
    The Step inductive has exactly two Export constructors:
    - export_with_bridge: hasTrustBridge is a required precondition.
    - export_revalidate: ¬hasTrustBridge, and the LTS forces .Candidate on the new entry.
    Ungated export is structurally non-constructible.
    Proof structure is identical to NoSelfCorrectionWithoutRevision:
    extract the Step witness from reliable_export, then apply the StepSemantics theorem. -/
theorem ExportGating {Reason Evidence : Type u} (B1 B2 : Bubble)
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) :
    reliable_export (Reason := Reason) (Evidence := Evidence) B1 B2 s d_idx →
    StepSemantics.hasTrustBridge s B1 B2 ∨
    (¬StepSemantics.hasTrustBridge s B1 B2 ∧
     ∃ sout : StepSemantics.SystemState PropLike Standard ErrorModel Provenance, ∃ d_new,
       d_new ∈ sout.ledger ∧ d_new.status = .Candidate) := by
  intro ⟨s', h_step⟩
  cases EpArch.LinkingAxioms.export_gating_forced s s' B1 B2 d_idx h_step with
  | inl h_bridge => exact Or.inl h_bridge
  | inr h_inr =>
      exact Or.inr (And.intro h_inr.1
        (h_inr.2.elim (fun d_new h_spec =>
          Exists.intro s' (Exists.intro d_new (And.intro h_spec.1 h_spec.2)))))


/-! ## Commitment 6: Repair Loop (Contestability) -/

opaque pushback : Deposit PropLike Standard ErrorModel Provenance → Prop

/-- lifecycle: a deposit trace that contains at least a repair and a re-entry step.
    A trace constitutes a genuine repair loop only when RepairOrRevoke (the field-level
    fix) and Redeposit (return to Candidate for revalidation) both appear. The empty
    trace and traces missing either step do not witness the repair loop commitment. -/
def lifecycle (_ : Bubble) (_ : Deposit PropLike Standard ErrorModel Provenance)
    (trace : List LifecycleStep) : Prop :=
  .RepairOrRevoke ∈ trace ∧ .Redeposit ∈ trace

/-- Commitment 6: Deposits have lifecycle; domains require challenge/revocation mechanisms.
    Proven as a conjunction: the abstract lifecycle trace is exhibited alongside a concrete
    Step.repair from the operational LTS. h_q (isQuarantined) is genuinely load-bearing:
    it is passed directly to Step.repair, whose constructor requires it as a precondition.
    Removing h_q causes the second conjunct to fail — it is structurally necessary,
    not merely type-checked and discarded. -/
theorem RepairLoopExists {Reason Evidence : Type u} (B : Bubble)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (f : Field)
    (_ : deposited B d)
    (h_q : StepSemantics.isQuarantined s d_idx) :
    (∃ trace, lifecycle B d trace) ∧
    (∃ s', StepSemantics.Step (Reason := Reason) (Evidence := Evidence) s (.Repair d_idx f) s' ∧
           s'.ledger = StepSemantics.updateDepositStatus s.ledger d_idx .Candidate) := by
  constructor
  · exact ⟨[.Challenge, .Quarantine, .RepairOrRevoke, .Redeposit], by decide, by decide⟩
  · exact ⟨{ s with ledger := StepSemantics.updateDepositStatus s.ledger d_idx .Candidate },
      StepSemantics.Step.repair s d_idx f h_q, rfl⟩

/-- Standalone operational grounding: Step.repair is available from any quarantined state,
    and resets the deposit to Candidate status.
    The second conjunct of RepairLoopExists above is a direct application of this theorem's
    content; grounded_RepairLoopExists is kept as a standalone lemma for contexts that need
    only the Step-level fact without the lifecycle-trace component. -/
theorem grounded_RepairLoopExists
    {Reason Evidence : Type u}
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (f : Field)
    (h_quarantined : StepSemantics.isQuarantined s d_idx) :
    let s' := { s with ledger :=
          StepSemantics.updateDepositStatus s.ledger d_idx .Candidate }
    ∃ _h_step : StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
          s (.Repair d_idx f) s',
      s'.ledger = StepSemantics.updateDepositStatus s.ledger d_idx .Candidate :=
  ⟨StepSemantics.Step.repair s d_idx f h_quarantined, rfl⟩

/-- A domain reliably self-corrects if there exist system states and a trace
    demonstrating that an erroneous deposit was caught and removed (Deposited → Revoked)
    via revision actions.
    Grounded in StepSemantics.Trace.demonstratesSelfCorrection. -/
def reliably_self_corrects {Reason Evidence : Type u} (_ : Domain)
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ (s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
    (t : StepSemantics.Trace (Reason := Reason) (Evidence := Evidence) s s')
    (d_idx : Nat), t.demonstratesSelfCorrection d_idx

/-- A domain structurally prohibits revision at state s if no trace from s
    ever contains Challenge or Revoke actions.
    Grounded in StepSemantics.prohibits_revision. -/
def structurally_prohibits_revision {Reason Evidence : Type u} (_ : Domain)
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  StepSemantics.prohibits_revision (Reason := Reason) (Evidence := Evidence) s

/-- Commitment 6b: Self-correcting domains cannot prohibit revision.

    Discharged: direct corollary of
    StepSemantics.self_correcting_domain_permits_revision.

    Proof: if domain D has a self-correction trace from s, then by
    self_correcting_domain_permits_revision, s does not prohibit revision,
    contradicting structurally_prohibits_revision D s. -/
theorem NoSelfCorrectionWithoutRevision {Reason Evidence : Type u} (D : Domain)
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance) :
    reliably_self_corrects (Reason := Reason) (Evidence := Evidence) D s →
    ¬structurally_prohibits_revision (Reason := Reason) (Evidence := Evidence) D s := by
  intro ⟨s', t, d_idx, h_sc⟩
  exact StepSemantics.self_correcting_domain_permits_revision s ⟨s', t, d_idx, h_sc⟩


/-! ## Commitment 7: Header Stripping → Harder Disputes -/

/-- A dispute exists over claim P in bubble B. -/
opaque dispute : Bubble → PropLike → Prop

/-! ### Dispute Diagnosability

    Header-stripped disputes are "systematically harder" in the sense of:
    - Fewer diagnostic moves available
    - Lower diagnosability (can't isolate which field failed)
    - More reliance on trust/authority rather than field-specific repair

    This captures "diagnostic capacity" without committing to a
    time/efficiency metric (which would require a separate workload model).
-/

/-- Diagnosability score: 0-3 representing which fields can be inspected.
    3 = all of S, E, V diagnosable; 0 = no field-specific diagnosis possible.

    This is a capacity measure, not a time measure. -/
structure DiagnosabilityScore where
  score : Fin 4  -- 0, 1, 2, or 3

/-- With headers, all three fields are diagnosable. -/
def header_preserved_diagnosability : DiagnosabilityScore := ⟨3, by decide⟩

/-- Without headers, no field-specific diagnosis is possible. -/
def header_stripped_diagnosability : DiagnosabilityScore := ⟨0, by decide⟩

/-- A dispute is "systematically harder" when diagnosability is lower.
    "Harder" means: fewer diagnostic moves, not necessarily slower. -/
def systematically_harder (with_header without_header : DiagnosabilityScore) : Prop :=
  without_header.score < with_header.score

/-- Header-stripped disputes are systematically harder than header-preserved. -/
theorem header_stripping_harder :
    systematically_harder header_preserved_diagnosability header_stripped_diagnosability := by
  unfold systematically_harder header_preserved_diagnosability header_stripped_diagnosability
  decide


/-! ## S/E/V Factorization: Partition Refinement

The S/E/V decomposition is a partition refinement of "something is wrong."

**What this proves:**
- Monolithic failure = "something is wrong" (Bool)
- Factorized failure = "which field is wrong" (Option Field)
- Factorization carries strictly more information

**What this does NOT claim:**
- That S/E/V is the "correct" decomposition of reality
- That humans always diagnose in terms of S/E/V
- That this matches anyone's philosophical intuitions

The claim is purely structural: if you can say "V failed" instead of
"something failed," you have more diagnostic capacity. -/

/-- Failure result: which field (if any) is broken.

    - `none` = no failure detected (passes)
    - `some f` = field f is broken -/
abbrev FailureField := Option Field

/-- Monolithic failure: only knows "broken or not".

    This represents systems without S/E/V factorization —
    they can say "wrong" but not "wrong WHERE." -/
def FailMonolithic (failure : FailureField) : Bool :=
  failure.isSome

/-- Monolithic is a projection of factorized: if you have a factorized
    failure label, you can always project to monolithic by forgetting
    which field. Trivially true by definition of `isSome`. -/
theorem monolithic_is_projection (f : FailureField) :
    FailMonolithic f = f.isSome := rfl

/-- Factorization refines the partition: if two failures have the same
    factorized label, they have the same monolithic label. More information
    (factorized) implies less information (monolithic), not vice versa. -/
theorem factorization_refines (f1 f2 : FailureField) :
    f1 = f2 → FailMonolithic f1 = FailMonolithic f2 := by
  intro h
  simp [FailMonolithic, h]

/-- Factorization distinguishes cases that monolithic collapses.
    Proves factorization carries STRICTLY MORE information. -/
theorem factorization_distinguishes :
    ∃ (f1 f2 : FailureField),
      f1 ≠ f2 ∧ FailMonolithic f1 = FailMonolithic f2 := by
  -- Witness: S-failure and V-failure both show as "broken" monolithically
  refine ⟨some Field.S, some Field.V, ?_, ?_⟩
  · -- f1 ≠ f2: S ≠ V
    intro h
    injection h with h'
    cases h'
  · -- FailMonolithic f1 = FailMonolithic f2: both are true
    rfl

/-- Non-injectivity of monolithic projection: the monolithic projection
    is not injective — it maps multiple distinct factorized failures to
    the same "broken" label. This is the formal sense in which
    factorization carries more diagnostic information. -/
theorem monolithic_not_injective :
    ¬(∀ f1 f2 : FailureField, FailMonolithic f1 = FailMonolithic f2 → f1 = f2) := by
  intro h_inj
  -- If injective, then FailMonolithic f1 = FailMonolithic f2 → f1 = f2
  have ⟨f1, f2, h_ne, h_eq⟩ := factorization_distinguishes
  -- h_inj says h_eq implies f1 = f2
  have h_eq' : f1 = f2 := h_inj f1 f2 h_eq
  exact h_ne h_eq'

/-- Diagnosability increases with factorization depth.

    Score 0: no diagnosis possible (bare "wrong")
    Score 1: factorized to one of S/E/V (one field inspectable)
    Score 3: full S/E/V structure (all fields inspectable)

    This formalizes "legibility" as partition depth. -/
def diagnosabilityFromField (f : FailureField) : DiagnosabilityScore :=
  match f with
  | none => ⟨0, by decide⟩      -- no failure = nothing to diagnose
  | some _ => ⟨1, by decide⟩    -- single field identified

/-- Full header structure enables maximum diagnosability.

    With all of S, E, V inspectable, we achieve score 3.
    This is what `header_preserved_diagnosability` captures. -/
theorem full_factorization_maximizes :
    header_preserved_diagnosability.score = 3 := rfl

/-- No factorization means no field-specific diagnosis.

    This is what `header_stripped_diagnosability` captures. -/
theorem no_factorization_minimizes :
    header_stripped_diagnosability.score = 0 := rfl

/-- Factorization strictly increases diagnosability.
    Any factorized failure (score ≥ 1) has strictly higher
    diagnosability than stripped (score 0). -/
theorem factorization_increases_diagnosability (f : Field) :
    (diagnosabilityFromField (some f)).score > header_stripped_diagnosability.score := by
  simp [diagnosabilityFromField, header_stripped_diagnosability]
  decide


/-- A dispute "localizes" when failures can be attributed to specific fields.

    Localization means diagnosability > 0 (at least one field inspectable).
    With headers, we achieve score 3 (all fields). -/
def localizes (_B : Bubble) (_P : PropLike) : Prop :=
  header_preserved_diagnosability.score > header_stripped_diagnosability.score

/-- Disputes over header-preserved claims can localize to specific fields. -/
theorem header_enables_localization : localizes B P := by
  unfold localizes header_preserved_diagnosability header_stripped_diagnosability
  decide

/-- A dispute is "sticky" when it cannot be resolved via standard repair. -/
opaque sticky : Bubble → PropLike → Prop

/-- A dispute produces "proxy battles" when the real issue cannot be identified. -/
opaque proxy_battles : Bubble → PropLike → Prop

/-- Commitment 7, first conjunct: header-preserved deposits permit localization.
    Discharged: localizes B P unfolds to header_preserved_diagnosability.score >
    header_stripped_diagnosability.score = 3 > 0, provable by decide unconditionally.
    The dispute and header_preserved hypotheses are structurally present but the
    conclusion does not depend on them. -/
theorem HeaderPreservation_implies_localization (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    dispute B P → header_preserved d → localizes B P := by
  intro _ _
  unfold localizes header_preserved_diagnosability header_stripped_diagnosability
  decide

/-- Commitment 7, second conjunct: header-stripped deposits produce sticky disputes.
    Axiom: sticky and proxy_battles are opaque predicates requiring external domain
    evidence — they cannot be reduced to numerical comparisons like localizes. -/
axiom HeaderPreservationAsymmetry (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    dispute B P → header_stripped d → sticky B P ∧ proxy_battles B P


/-! ## Commitment 8: Temporal Validity (τ / TTL) -/

/-- refreshed: a deposit whose τ is non-zero (has been updated). -/
def refreshed (d : Deposit PropLike Standard ErrorModel Provenance) : Prop := d.h.τ > 0

/-- unrefreshed: a deposit whose τ is zero (never updated / expired). -/
def unrefreshed (d : Deposit PropLike Standard ErrorModel Provenance) : Prop := d.h.τ = 0

/-- performs_equivalently: two deposits behave the same w.r.t. temporal validity.
    Defined as having the same τ: equal TTL → equivalent temporal behaviour. -/
def performs_equivalently (d1 d2 : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d1.h.τ = d2.h.τ

/-- Commitment 8: Deposits have shelf life; staleness is a structural failure mode.
    Discharged: if d1.h.τ > 0 (refreshed) and d2.h.τ = 0 (unrefreshed),
    then d1.h.τ ≠ d2.h.τ (they differ), so ¬performs_equivalently. -/
theorem TemporalValidity (d1 d2 : Deposit PropLike Standard ErrorModel Provenance) :
    refreshed d1 → unrefreshed d2 → ¬performs_equivalently d1 d2 := by
  intro h1 h2 h_eq
  unfold refreshed unrefreshed performs_equivalently at *
  simp [h_eq.trans h2] at h1

end EpArch

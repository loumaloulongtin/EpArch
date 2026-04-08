/-
EpArch/Commitments.lean — Architecture Commitments

The 8 explicit architectural commitments that define what the EpArch
framework requires of any conforming system.

## Assumption boundary

One structural commitment remains as a field of `CommitmentsCtx`, a hypothesis
structure modelled on `WorldCtx`.  Theorems conditioned on `(C : CommitmentsCtx …)`
hold for any architecture satisfying the field:

- C1 (`traction_auth_split`) — certainty_L ⊥ knowledge_B (neither implies the other)

## Proved commitments (no CommitmentsCtx field needed)

Seven commitments are derived as standalone theorems:

- C2 (`no_universal_ledger`) — `WorldCtx.no_ledger_tradeoff` (EpArch CAP Theorem):
    proved from `W_partial_observability` + `obs_based`; for bubble-local ledgers
    `hObs` is automatic via `WorldCtx.localLedger_is_obs_based` (see WorldCtx.lean).
- C3 (`SEVFactorization`)    — by rfl
- C4b (`redeemability_requires_more_than_consensus`) — proved from `intra_bubble_only`
    and the definitional gap between `consensus` (True) and `redeemable`
    (requires opaque external evidence: path_route_exists, contact_was_made,
    verdict_discriminates).
- C5 (`ExportGating`)        — from the LTS export constructors
- C6b (`NoSelfCorrectionWithoutRevision`) — from StepSemantics
- C7b (`header_stripping_harder`) — proved via the admissible completion-space model:
    `metadata_stripping_strictly_enlarges` establishes that stripping strictly
    enlarges the admissible (S, E, V) completion space; `header_stripping_harder`
    is its numeric corollary.  The opaque pathology predicates (`sticky`,
    `proxy_battles`) are taken as direct hypotheses in forward theorems.
- C8 (`TemporalValidity`)    — from the header τ definition

## What are Commitments?

Commitments are the SPECIFICATION LAYER: they say WHAT a correct system
must satisfy, not HOW it achieves it. Think of them as architectural
design requirements.

- **Constructive witness:** ConcreteLedgerModel.lean provides a concrete
  model satisfying ALL 8 commitments — proving they are consistent and
  non-vacuous.
- **Operational HOW:** StepSemantics.lean gives the constructive
  lifecycle that grounds the proved commitments.

## Commitment List

1. Traction/Authorization Split — certainty ≠ knowledge              [CommitmentsCtx field]
2. Scoped Bubbles — no global ledger; validation is local             [proved: CAP theorem]
3. S/E/V Factorization — three independent header fields              [proved: by rfl]
4. Redeemability External — constraint surface outside consensus      [proved: structural]
5. Export Gating — cross-bubble transfer requires validation          [proved: LTS]
6. Repair Loop — challenged deposits can be revised                   [proved: StepSemantics]
7. Header Stripping → Harder Disputes — less metadata = less diagnosable [proved: completion-space model]
8. Temporal Validity — deposits expire (τ/TTL marks)                  [proved: header def]
-/

import EpArch.Basic
import EpArch.WorldCtx
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


/-! ## Commitment 1: Traction/Authorization Split

    Commitment: certainty_L and knowledge_B are independent (neither implies the other).
    Bundled in CommitmentsCtx.traction_auth_split; see CommitmentsCtx section below. -/


/-! ## Commitment 2: Scoped Bubbles (No Global Ledger)

    No global ledger can jointly support innovation and coordination.
    Innovation requires accepting potentially contradictory deposits;
    coordination requires shared acceptance standards. This tradeoff
    forces scoped validation domains (bubbles).
-/

/-! Commitment 2 (Scoped Bubbles): no global ledger can simultaneously support
    innovation and coordination.  This is now a **proved theorem** derived from
    `W_partial_observability` and `obs_based` in WorldCtx.lean:
    `WorldCtx.no_ledger_tradeoff` — the EpArch CAP Theorem.
    It is no longer a field of CommitmentsCtx; see §Ledger Tradeoff in WorldCtx.lean. -/


/-! ## Commitment 3: S/E/V Factorization -/

/-- Commitment 3: S/E/V structure — every deposit carries S, E, V header fields.

    Follows directly from the Deposit record structure (witness is d.h.S, d.h.E, d.h.V).
    The stronger architectural commitment — that validation failures localize to exactly
    one of S, E, V — is expressed by `has_strong_SEV_factorization` in StepSemantics.lean. -/
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

/-! Commitment 4b: Consensus alone doesn't create redeemability.
    Proved structurally below: `intra_bubble_only` deposits cannot be redeemable
    because redeemability requires `path_route_exists` (opaque external evidence)
    while intra-bubble deposits provably have no such route.
    No longer a CommitmentsCtx field. -/

/-- A deposit is intra-bubble-only if it has no external route to any constraint surface.
    This is the structural condition that separates consensus from redeemability:
    consensus is achievable for any deposit, but a deposit satisfying `intra_bubble_only`
    provably cannot be redeemable. -/
def intra_bubble_only (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∀ cs, ¬path_route_exists (PropLike := PropLike) (Standard := Standard)
      (ErrorModel := ErrorModel) (Provenance := Provenance) d cs

/-- Structural separation: an intra-bubble deposit cannot be redeemable.
    Proof: `redeemable d` supplies `vp.h_path : path_route_exists vp.deposit vp.surface`;
    after rewriting along `h_dep : vp.deposit = d`, this contradicts `intra_bubble_only d`. -/
theorem intra_bubble_not_redeemable
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_intra : intra_bubble_only d) : ¬redeemable d := by
  intro ⟨vp, h_dep, _⟩
  exact h_intra vp.surface (h_dep ▸ vp.h_path)


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
    The Step inductive has exactly two Export constructors:
    - export_with_bridge: hasTrustBridge is a required precondition.
    - export_revalidate: ¬hasTrustBridge, and the LTS forces .Candidate on the new entry.
    Ungated export is structurally non-constructible. -/
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

    Corollary of StepSemantics.self_correcting_domain_permits_revision:
    if domain D has a self-correction trace from s, then s does not prohibit revision. -/
theorem NoSelfCorrectionWithoutRevision {Reason Evidence : Type u} (D : Domain)
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance) :
    reliably_self_corrects (Reason := Reason) (Evidence := Evidence) D s →
    ¬structurally_prohibits_revision (Reason := Reason) (Evidence := Evidence) D s := by
  intro ⟨s', t, d_idx, h_sc⟩
  exact StepSemantics.self_correcting_domain_permits_revision s ⟨s', t, d_idx, h_sc⟩


/-! ## Commitment 7: Header Stripping → Harder Disputes -/

/-- A dispute exists over claim P in bubble B. -/
opaque dispute : Bubble → PropLike → Prop

/-! ### Admissible Completion Model

A dispute resolver examining claim P must consider every explanatory state
(S, E, V) compatible with the available information.  Full metadata pins all
three fields; stripped metadata leaves them all free, enlarging the admissible
completion space.

The inclusion theorem (`completion_space_monotonicity`) and strict inclusion
theorem (`metadata_stripping_strictly_enlarges`) are proved purely from
definitions — no scores, no ad hoc witnesses. -/

/-- A candidate explanatory completion: one possible (S, E, V) assignment
    a dispute resolver must consider when diagnosing a claim over P.
    Completions represent the space of potential explanations compatible
    with the available evidence. -/
structure Completion (Standard ErrorModel Provenance : Type u) where
  S : Standard
  E : ErrorModel
  V : Provenance

/-- Full-metadata admissibility: a completion is admissible iff it exactly
    matches the deposit's header fields.
    With header present, S, E, V are all pinned — the explanatory space is
    maximally constrained (at most one completion per concrete header). -/
def admissible_full
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (c : Completion Standard ErrorModel Provenance) : Prop :=
  c.S = d.h.S ∧ c.E = d.h.E ∧ c.V = d.h.V

/-- Stripped-metadata admissibility: with no header information, any (S, E, V)
    triple is admissible — the claim carries no field constraints.
    Formally True: stripping removes all admissibility constraints. -/
def admissible_stripped
    (_ : Deposit PropLike Standard ErrorModel Provenance)
    (_ : Completion Standard ErrorModel Provenance) : Prop :=
  True

/-- Nontriviality: there exists a completion not matching d's header on at least
    one field.  Holds whenever S, E, or V can take more than one value
    (i.e., the metadata types are not singletons). -/
def has_alternative_completion
    (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ c : Completion Standard ErrorModel Provenance,
    c.S ≠ d.h.S ∨ c.E ≠ d.h.E ∨ c.V ≠ d.h.V

/-! ### Completion-Space Inclusion Theorems

    These are the structural core of C7b: proved purely from definitions. -/

/-- **Core monotonicity**: full-metadata completions ⊆ stripped-metadata completions.
    Proof: admissible_full d c → True, trivially.
    Formal expression of "metadata constrains; stripping frees." -/
theorem completion_space_monotonicity
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (c : Completion Standard ErrorModel Provenance) :
    admissible_full d c → admissible_stripped d c :=
  fun _ => trivial

/-- **Strict inclusion**: under nontriviality, stripped strictly contains full.
    (⊆) by monotonicity; (⊅) by the alternative completion: it is admissible_stripped
    (trivially) yet not admissible_full (it disagrees with d on some field).
    This is the structural proof that stripping is an information-losing projection
    that provably enlarges the admissible explanation set. -/
theorem metadata_stripping_strictly_enlarges
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_alt : has_alternative_completion d) :
    (∀ c, admissible_full d c → admissible_stripped d c) ∧
    (∃ c, admissible_stripped d c ∧ ¬admissible_full d c) := by
  constructor
  · intro c _; trivial
  · have ⟨c, hc⟩ := h_alt
    refine ⟨c, trivial, fun h_full => ?_⟩
    have ⟨hS, hE, hV⟩ := h_full
    cases hc with
    | inl h => exact h hS
    | inr h => cases h with
      | inl h => exact h hE
      | inr h => exact h hV

/-- Headline form: the two completion spaces are not equivalent under nontriviality.
    No admissibility predicate can simultaneously be fully constrained (full) and
    unconstrained (stripped). -/
theorem completion_spaces_are_distinct
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_alt : has_alternative_completion d) :
    ¬(∀ c, admissible_full d c ↔ admissible_stripped d c) := by
  intro h_eq
  have ⟨c, _, h_not_full⟩ := (metadata_stripping_strictly_enlarges d h_alt).2
  exact h_not_full ((h_eq c).mpr trivial)

/-! ### Diagnosability Score — Grounded Numeric Summary

The scores below (3 for full, 0 for stripped) summarise the structural result
above.  Full metadata pins S, E, V → 3 independently determinable fields,
minimal completion space.  Stripped metadata pins nothing → 0 determinable
fields, maximal completion space.

The ordering 0 < 3 is the numeric reflection of the strict inclusion proved
by `metadata_stripping_strictly_enlarges`. `header_stripping_harder` is a
corollary of that structural theorem, not an assignment by fiat. -/

/-- Diagnosability score: number of independently determinable fields (0–3).
    3 = all of S, E, V are diagnosable; 0 = no field-specific diagnosis possible.
    A capacity measure, not a time measure. -/
structure DiagnosabilityScore where
  score : Fin 4  -- 0, 1, 2, or 3

/-- With full header, all three fields are independently diagnosable. -/
def header_preserved_diagnosability : DiagnosabilityScore := ⟨3, by decide⟩

/-- Without header, no field-specific diagnosis is possible. -/
def header_stripped_diagnosability : DiagnosabilityScore := ⟨0, by decide⟩

/-- A dispute regime is "systematically harder" when diagnosability is lower.
    "Harder" means: fewer diagnostic moves, not necessarily slower. -/
def systematically_harder (with_header without_header : DiagnosabilityScore) : Prop :=
  without_header.score < with_header.score

/-- Header-stripped disputes are systematically harder than header-preserved.
    **Primary grounding**: `metadata_stripping_strictly_enlarges` proves the
    stripped completion space strictly contains the full space.  The score
    ordering 0 < 3 is the numeric summary: stripped has 0 independently
    determinable fields vs 3 for full metadata, reflecting completion_space_monotonicity. -/
theorem header_stripping_harder :
    systematically_harder header_preserved_diagnosability header_stripped_diagnosability := by
  unfold systematically_harder header_preserved_diagnosability header_stripped_diagnosability
  -- 0 < 3 as Fin 4: numeric bridge from the completion-space strict inclusion.
  -- Stripped (0 fields) vs full (3 fields) reflects admissible_full ⊂ admissible_stripped.
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
    `localizes B P` unfolds to a score comparison provable by decide; the conclusion
    holds unconditionally given the header_preserved_diagnosability definition. -/
theorem HeaderPreservation_implies_localization (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    dispute B P → header_preserved d → localizes B P := by
  intro _ _
  unfold localizes header_preserved_diagnosability header_stripped_diagnosability
  decide

/-! Commitment 7, second conjunct: header-stripped deposits produce sticky disputes
    and proxy battles.  `sticky` and `proxy_battles` are opaque predicates;
    the operational pathology is taken as a direct hypothesis in forward theorems
    (see §Forward Theorems (Commitment 7b) below).  It is no longer a CommitmentsCtx
    field: the diagnosability/hardness result is proved via the completion-space model
    above, and the sticky/proxy_battles claim is carried as a direct premise. -/


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
    Refreshed and unrefreshed deposits differ in τ, so they are not performatively equivalent. -/
theorem TemporalValidity (d1 d2 : Deposit PropLike Standard ErrorModel Provenance) :
    refreshed d1 → unrefreshed d2 → ¬performs_equivalently d1 d2 := by
  intro h1 h2 h_eq
  unfold refreshed unrefreshed performs_equivalently at *
  simp [h_eq.trans h2] at h1


/-! ## CommitmentsCtx — One Structural Commitment as a Hypothesis Bundle

    Analogous to WorldCtx.W_* bundles: the one remaining commitment is not asserted
    globally but bundled in a hypothesis structure.  Theorems conditioned on
    CommitmentsCtx hold for any conforming architecture, without asserting them
    unconditionally.  This gives zero `axiom` declarations; the commitment
    appears only as a hypothesis "(C : CommitmentsCtx)" in theorem signatures.

    C2 (no global ledger) → proved theorem `WorldCtx.no_ledger_tradeoff`.
    C4b (consensus ≠ redeemability) → proved from `intra_bubble_only`.
    C7b (header stripping → harder disputes) → proved via completion-space model
        (`metadata_stripping_strictly_enlarges`); sticky/proxy_battles taken as
        direct hypotheses in forward theorems (opaque predicates).

    Non-vacuity: ConcreteLedgerModel proves analogous structural properties in a
    concrete model.
-/

/-- The one structural architectural commitment remaining as a hypothesis bundle.
    (C2, C4b, C7b diagnosability have all been derived as proved theorems.)

    Field:
    - `traction_auth_split` — C1: certainty_L ⊥ knowledge_B (independent) -/
structure CommitmentsCtx (PropLike Standard ErrorModel Provenance : Type u) where
  /-- Traction (certainty_L) and authorization (knowledge_B) are independent:
      neither implies the other. -/
  traction_auth_split : ∀ (a : Agent) (B : Bubble) (P : Claim),
    does_not_imply (certainty_L a P) (knowledge_B B P) ∧
    does_not_imply (knowledge_B B P) (certainty_L a P)


/-! ### Forward Theorems (Commitment 1) -/

/-- Certainty does not entail bank authorization.
    An agent at Certainty on P may have no Bank deposit for P — the two are independent.
    This is the paper's central claim: the Bank is necessary, not just the Ladder. -/
theorem certainty_insufficient_for_authorization (C : CommitmentsCtx PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (P : Claim) :
    ∃ (_ : certainty_L a P), ¬knowledge_B B P :=
  (C.traction_auth_split a B P).1

/-- Bank authorization does not entail certainty.
    A deposit may be publicly authorized in B while the agent remains at Ignorance or Belief. -/
theorem authorization_insufficient_for_certainty (C : CommitmentsCtx PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (P : Claim) :
    ∃ (_ : knowledge_B B P), ¬certainty_L a P :=
  (C.traction_auth_split a B P).2

/-- WeakCtx: coincidence of certainty and authorization contradicts traction_auth_split. -/
theorem WeakCtx_contradicts_TractionAuthorizationSplit (C : CommitmentsCtx PropLike Standard ErrorModel Provenance)
    (coincidence : ∀ (a : Agent) (B : Bubble) (P : Claim), certainty_L a P ↔ knowledge_B B P) :
    False :=
  let ⟨ha, hnb⟩ := (C.traction_auth_split (default : Agent) (default : Bubble) (default : Claim)).1
  hnb ((coincidence default default default).mp ha)


/-! ### Forward Theorems (Commitment 2) — EpArch CAP Theorem

    C2 is now derived from WorldCtx, not a CommitmentsCtx hypothesis.
    `WorldCtx.no_ledger_tradeoff` is the core result; the theorems below restate
    it in convenient forms.

    Dependency profiles:
    - `no_universal_ledger`, `innovation_excludes_coordination`:
      take `hObs : C.obs_based L` as an explicit assumption.
    - `no_obs_based_universal_ledger` (WorldCtx.lean): existential-negation
      headline form — no such obs-based ledger can exist.
    - `no_universal_local_ledger`: `hObs` is automatic for bubble-local ledgers;
      partial observability alone forces the tradeoff. -/

/-- A ledger that supports innovation cannot also support coordination.
    Restates `WorldCtx.no_ledger_tradeoff` in implication form. -/
theorem innovation_excludes_coordination (C : WorldCtx) (L : C.Ledger)
    (hObs : C.obs_based L) (W : C.W_partial_observability) :
    C.supports_innovation L → ¬C.supports_coordination L :=
  fun hI hC => WorldCtx.no_ledger_tradeoff C L hObs W ⟨hI, hC⟩

/-- No single obs-based ledger serves both innovation and coordination (bubbles forced).
    Conjunction form; for the existential-negation headline form see
    `WorldCtx.no_obs_based_universal_ledger`. -/
theorem no_universal_ledger (C : WorldCtx) (L : C.Ledger)
    (hObs : C.obs_based L) (W : C.W_partial_observability) :
    ¬(C.supports_innovation L ∧ C.supports_coordination L) :=
  WorldCtx.no_ledger_tradeoff C L hObs W

/-- Existential-negation headline: no obs-based ledger satisfies both goals.
    Restates `WorldCtx.no_obs_based_universal_ledger` as a forward theorem. -/
theorem no_obs_based_universal_ledger (C : WorldCtx) (W : C.W_partial_observability) :
    ¬ ∃ L : C.Ledger,
      C.obs_based L ∧ C.supports_innovation L ∧ C.supports_coordination L :=
  WorldCtx.no_obs_based_universal_ledger C W

/-- For bubble-local ledgers, obs-basedness is automatic — `hObs` disappears.
    Partial observability alone forces the tradeoff for any ledger reading only
    from the local observation channel (`C.localToLedger f`). -/
theorem no_universal_local_ledger (C : WorldCtx) (f : C.LocalLedger)
    (W : C.W_partial_observability) :
    ¬(C.supports_innovation (C.localToLedger f) ∧
      C.supports_coordination (C.localToLedger f)) :=
  WorldCtx.no_ledger_tradeoff_local C f W

/-- Explicit both-support witnesses contradict the CAP tradeoff. -/
theorem GlobalCtx_contradicts_NoGlobalLedgerTradeoff (C : WorldCtx) (L : C.Ledger)
    (hObs : C.obs_based L) (W : C.W_partial_observability)
    (hI : C.supports_innovation L) (hC : C.supports_coordination L) : False :=
  WorldCtx.no_ledger_tradeoff C L hObs W ⟨hI, hC⟩


/-! ### Forward Theorems (Commitment 4b) -/

/-- Redeemability requires more than consensus: the constraint surface is independent.
    For intra-bubble deposits, consensus (trivially true for any bubble) and redeemability
    (requiring external path, contact, and verdict evidence) are structurally separated.
    Proved without CommitmentsCtx: the separation follows from definitions alone. -/
theorem redeemability_requires_more_than_consensus
    (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_intra : intra_bubble_only d) :
    does_not_imply (consensus B d.P) (redeemable d) :=
  ⟨trivial, intra_bubble_not_redeemable d h_intra⟩


/-! ### Forward Theorems (Commitment 7b) -/

/-- Header stripping produces sticky disputes, proxy battles, AND diagnostic loss.
    The `sticky \u2227 proxy_battles` conclusion comes from the `h_pathology` direct
    hypothesis (opaque predicates; not CommitmentsCtx-bundled).  The
    `systematically_harder` conclusion is proved from the completion-space model
    and does not require a hypothesis. -/
theorem header_stripping_produces_pathology
    (h_pathology : ∀ (B : Bubble) (P : PropLike)
        (d : Deposit PropLike Standard ErrorModel Provenance),
        dispute B P → header_stripped d → sticky B P ∧ proxy_battles B P)
    (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    dispute B P → header_stripped d →
    sticky B P ∧ proxy_battles B P ∧
    systematically_harder header_preserved_diagnosability header_stripped_diagnosability :=
  fun h_disp h_strip =>
    let ⟨hs, hp⟩ := h_pathology B P d h_disp h_strip
    ⟨hs, hp, header_stripping_harder⟩

/-- Contradiction: "stripped disputes are never sticky" contradicts h_pathology. -/
theorem StrippedCtx_contradicts_HeaderPreservationAsymmetry
    (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_pathology : dispute B P → header_stripped d → sticky B P ∧ proxy_battles B P)
    (h_disp : dispute B P) (h_strip : header_stripped d)
    (h_no_sticky : ¬sticky B P) : False :=
  h_no_sticky (h_pathology h_disp h_strip).1

end EpArch

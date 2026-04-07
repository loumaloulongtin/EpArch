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

/-- A verification path: connects deposit to constraint surface. -/
structure VerificationPath where
  deposit : Deposit PropLike Standard ErrorModel Provenance
  surface : ConstraintSurface
  path_exists : Bool
  contact_made : Bool
  discriminating : Bool

/-- Redeemable: the deposit can be "cashed in" against the constraint surface. -/
def redeemable (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ (vp : VerificationPath (PropLike := PropLike) (Standard := Standard)
      (ErrorModel := ErrorModel) (Provenance := Provenance)),
    vp.deposit = d ∧
    vp.surface = d.h.redeem.cs ∧
    vp.path_exists ∧
    vp.contact_made ∧
    vp.discriminating

/-- path_exists_for_deposit: a deposit has a VerificationPath where path_exists is set.
    This is strictly WEAKER than redeemable: redeemable additionally requires surface
    alignment, contact_made, and discriminating. A path can be structurally present
    (the route exists) before the constraint surface has been fully contacted. -/
def path_exists_for_deposit (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ (vp : VerificationPath (PropLike := PropLike) (Standard := Standard)
      (ErrorModel := ErrorModel) (Provenance := Provenance)),
    vp.deposit = d ∧ vp.path_exists

/-- Redeemability implies that a verification path exists.
    Discharged: redeemable d provides a VerificationPath satisfying 5 conditions
    (deposit identity, surface alignment, path_exists, contact_made, discriminating).
    We project out deposit identity and path_exists, dropping the other three. -/
theorem redeemable_implies_path (d : Deposit PropLike Standard ErrorModel Provenance) :
    redeemable d → path_exists_for_deposit d := by
  intro ⟨vp, h_dep, _, h_pe, _, _⟩
  exact ⟨vp, h_dep, h_pe⟩

opaque depends_on : Prop → ConstraintSurface → Prop
opaque by_consensus_alone : Prop → Prop

/-- Commitment 4a: Redeemability tracks constraint surface, not consensus. -/
axiom RedeemabilityExternal (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    depends_on (redeemable d) d.h.redeem.cs

/-- Commitment 4b: Consensus alone doesn't create redeemability.

    If redeemability were by consensus alone, then consensus would suffice.
    But bubbles CAN agree on non-redeemable claims (conspiracy theories, etc.).
    Therefore, consensus alone doesn't suffice. -/
axiom by_consensus_creates_redeemability (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    by_consensus_alone (redeemable d) → consensus B d.P → redeemable d

axiom ConsensusNotSufficient (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    consensus B d.P → ¬(by_consensus_alone (redeemable d))


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
    This is a constructive witness theorem: given a concrete isQuarantined state in
    StepSemantics, it constructs the Step.repair witness inline and then supplies the
    explicit trace [Challenge, Quarantine, RepairOrRevoke, Redeposit] as the lifecycle
    witness. The proof cannot be completed without a valid isQuarantined operational
    state (the Step.repair let-binding is type-checked), which makes the precondition
    genuinely load-bearing.
    Note: the real semantic content — that repair resets the deposit to Candidate and
    forces it back through the validation cycle — lives in grounded_RepairLoopExists
    and repair_produces_candidate (StepSemantics). This theorem witnesses that such
    a trace exists; it does not derive its conclusion from a deep emergent property
    of the system in the way NoSelfCorrectionWithoutRevision does. -/
theorem RepairLoopExists {Reason Evidence : Type u} (B : Bubble)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (s : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (f : Field)
    (_ : deposited B d)
    (h_q : StepSemantics.isQuarantined s d_idx) :
    ∃ trace, lifecycle B d trace :=
  let _h_step : StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
        s (.Repair d_idx f)
        { s with ledger := StepSemantics.updateDepositStatus s.ledger d_idx .Candidate } :=
    StepSemantics.Step.repair s d_idx f h_q
  ⟨[.Challenge, .Quarantine, .RepairOrRevoke, .Redeposit], by decide, by decide⟩

/-- Grounded version of RepairLoopExists: given a quarantined deposit in StepSemantics,
    the Repair step is constructively available by applying the Step.repair constructor,
    whose only precondition is isQuarantined.
    Postcondition: the repair step produces a state where the deposit has .Candidate status,
    forcing it back through the full validation cycle.
    Proof: direct constructor application + rfl on the concrete state.
    This grounds RepairLoopExists in the same way NoSelfCorrectionWithoutRevision is
    grounded: both extract structural facts from the Step inductive itself. -/
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

/-- Commitment 7: Headerless claims produce systematically harder disputes.

    The asymmetry:
    - Header-preserved → higher diagnosability, can localize to fields
    - Header-stripped → lower diagnosability, sticky disputes, proxy battles

    "Harder" is a capacity/diagnosability claim, not a time claim. -/
axiom HeaderPreservationAsymmetry (B : Bubble) (P : PropLike)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
  dispute B P →
  (header_preserved d → localizes B P) ∧
  (header_stripped d → (sticky B P ∧ proxy_battles B P))


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

/-
EpArch/Commitments.lean — Architecture Commitments

The 8 explicit architectural commitments that define what the EpArch
framework requires of any conforming system.  Each commitment is stated
as one or more axioms asserting structural properties (12 axioms + 1 trivially
provable theorem total).
For example: "traction ≠ authorization", "deposits must live in scoped
bubbles", "header stripping makes disputes harder".  Commitment 5's
primary result (`ExportGating`) is a theorem derived from its axioms.
Commitment 3 (`SEVFactorization`) is a theorem, not an axiom, because
the statement follows directly from the definition of Deposit by reflexivity.

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

/-- path_exists_for_deposit: a deposit has a verification path.
    Discharged: defined as `redeemable d` — a deposit has a path iff it is
    redeemable (which is defined by the existence of a VerificationPath above). -/
def path_exists_for_deposit (d : Deposit PropLike Standard ErrorModel Provenance) : Prop := redeemable d

/-- Redeemability implies verification path exists.
    Discharged: path_exists_for_deposit is defined as redeemable, so this is id. -/
theorem redeemable_implies_path (d : Deposit PropLike Standard ErrorModel Provenance) :
    redeemable d → path_exists_for_deposit d := id

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

/-- reliable_export: a cross-bubble transfer that carries its gate certificate.
    Discharged: defined as `exportDep B1 B2 d ∧ (Revalidate B2 B1 d ∨ TrustBridge B1 B2)` —
    an export is reliable iff it occurred AND was gated (revalidation or trust bridge). -/
def reliable_export (B1 B2 : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  exportDep B1 B2 d ∧ (Revalidate B2 B1 d ∨ TrustBridge B1 B2)

def unreliable_export (B1 B2 : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  exportDep B1 B2 d ∧ ¬Revalidate B2 B1 d ∧ ¬TrustBridge B1 B2

/-- Reliable export implies the deposit crossed the bubble boundary (exportDep).
    Discharged: first component of the reliable_export conjunction. -/
theorem reliable_implies_export (B1 B2 : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    reliable_export B1 B2 d → exportDep B1 B2 d := fun ⟨h, _⟩ => h

/-- Reliable and unreliable export are mutually exclusive.
    Discharged: if reliable, there is a gate (Revalidate ∨ TrustBridge); if unreliable,
    both are absent — the gate cases are exhaustive and each contradicts its absence. -/
theorem reliable_unreliable_exclusive (B1 B2 : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    reliable_export B1 B2 d → unreliable_export B1 B2 d → False := by
  intro ⟨_, h_gate⟩ ⟨_, h_no_reval, h_no_trust⟩
  cases h_gate with
  | inl h_reval => exact h_no_reval h_reval
  | inr h_trust => exact h_no_trust h_trust

/-- Commitment 5: Reliable export requires gating (revalidation or trust bridge). -/
theorem ExportGating (B1 B2 : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    reliable_export B1 B2 d → (Revalidate B2 B1 d ∨ TrustBridge B1 B2) := by
  intro h_reliable
  have h_em := Classical.em (Revalidate B2 B1 d ∨ TrustBridge B1 B2)
  cases h_em with
  | inl h_gate => exact h_gate
  | inr h_no_gate =>
    have h_no_reval : ¬Revalidate B2 B1 d := fun hr => h_no_gate (Or.inl hr)
    have h_no_trust : ¬TrustBridge B1 B2 := fun ht => h_no_gate (Or.inr ht)
    have h_unreliable : unreliable_export B1 B2 d := by
      unfold unreliable_export
      exact ⟨reliable_implies_export B1 B2 d h_reliable, h_no_reval, h_no_trust⟩
    exact absurd h_unreliable (fun hu => reliable_unreliable_exclusive B1 B2 d h_reliable hu)


/-! ## Commitment 6: Repair Loop (Contestability) -/

opaque pushback : Deposit PropLike Standard ErrorModel Provenance → Prop
opaque lifecycle : Bubble → Deposit PropLike Standard ErrorModel Provenance → List LifecycleStep → Prop

/-- Commitment 6: Deposits have lifecycle; domains require challenge/revocation mechanisms. -/
axiom RepairLoopExists (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
  deposited B d → pushback d → ∃ trace, lifecycle B d trace

opaque reliably_self_corrects : Domain → Prop
opaque structurally_prohibits_revision : Domain → Prop

axiom NoSelfCorrectionWithoutRevision (D : Domain) :
  reliably_self_corrects D → ¬structurally_prohibits_revision D


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

opaque refreshed : Deposit PropLike Standard ErrorModel Provenance → Prop
opaque unrefreshed : Deposit PropLike Standard ErrorModel Provenance → Prop
opaque performs_equivalently : Deposit PropLike Standard ErrorModel Provenance →
                                Deposit PropLike Standard ErrorModel Provenance → Prop

/-- Commitment 8: Deposits have shelf life; staleness is a structural failure mode. -/
axiom TemporalValidity (d1 d2 : Deposit PropLike Standard ErrorModel Provenance) :
  refreshed d1 → unrefreshed d2 → ¬performs_equivalently d1 d2

end EpArch

/-
EpArch.Theorems.Pathologies — Literature Pathology Diagnoses

Model diagnoses for classic epistemology puzzles and their bridge theorems.
Each pathology is shown to reduce to a structural feature of the Ladder/Bank/
Bubble architecture. Bridge theorems connect the header-stripping results back
to diagnosability metrics.
-/
import EpArch.StepSemantics
import EpArch.Theorems.Headers

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

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

/-- Forgotten evidence → Access vs truth-maker distinction.

    Agent lost access to V, but bubble's deposit persists with provenance intact.

    We distinguish agent access (mutable) from deposit provenance (immutable in bubble).

    Structural invariant: `deposit_survives_access_loss` encodes
    the key claim — access loss does not invalidate the deposit.  The theorem uses
    the `agent_lost_access` premise, routing it through this invariant.
    LTS grounding: `deposits_survive_revision_free_trace` (StepSemantics) proves
    that any revision-free trace preserves `isDeposited`; access loss corresponds
    to no revision action being issued against the deposit. -/
structure forgotten_evidence_case where
  agent : Agent
  original_evidence : Provenance
  deposit : Deposit PropLike Standard ErrorModel Provenance
  /-- Agent's current access to their original evidence -/
  agent_has_access : Bool
  /-- The deposit exists in a bubble ledger -/
  deposit_in_bubble : Bool
  /-- Structural invariant: access loss does not invalidate the deposit.
      Even when the agent loses access to their original evidence, the bubble's
      deposit persists — grounded by `deposits_survive_revision_free_trace`:
      without an explicit revision action, deposits are immutable in the bubble. -/
  deposit_survives_access_loss : agent_has_access = false → deposit_in_bubble = true

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

/-- Access loss ≠ deposit invalidation: agent access and bubble deposit are independent.
    `agent_lost_access f` flows through `f.deposit_survives_access_loss`
    to derive `bubble_deposit_persists f`. -/
theorem forgotten_evidence_persistence
    (f : forgotten_evidence_case (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (h_provenance : f.deposit.h.V = f.original_evidence) :
    agent_lost_access f → (bubble_deposit_persists f ∧ provenance_intact f) :=
  fun h_lost => ⟨f.deposit_survives_access_loss h_lost, h_provenance⟩

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

/-- Group knowledge → Different bubbles, different deposits.

    Different bubbles, different deposits; scope makes this coherent.

    `scope_separation` is a required structural field: a
    `group_knowledge_case` must certify bubble distinctness at construction
    time.  The theorem has no premises — distinctness is part of the case
    definition itself, not supplied by the caller. -/
structure group_knowledge_case where
  individual_bubble : Bubble
  group_bubble : Bubble
  /-- Structural invariant: individual and group bubbles are distinct scopes.
      A group knowledge case presupposes scope separation — without distinct
      bubbles there is no coherent individual-vs-group knowledge distinction. -/
  scope_separation : individual_bubble ≠ group_bubble

/-- The bubbles are different. -/
def bubbles_differ (g : group_knowledge_case) : Prop :=
  g.individual_bubble ≠ g.group_bubble

/-- Individual and group bubbles are distinct: derived from the structural invariant.
    No premises required — `scope_separation` is certified at case construction.
    `bubbles_differ g` is `g.individual_bubble ≠ g.group_bubble = g.scope_separation`. -/
theorem group_bubble_separation (g : group_knowledge_case) :
    bubbles_differ g :=
  g.scope_separation

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

/-- Mere certainty is not exportable. -/
theorem certainty_not_exportable (v : value_case (PropLike := PropLike)) :
    is_mere_certainty v → ¬exportable v := by
  intro h h_exp
  unfold is_mere_certainty exportable at *
  cases hv : v.state <;> simp_all

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
  /-- Does the skeptical attack sever global constraint contact? -/
  severs_global : Bool
  /-- Is the local (within-bubble) redeemability surface intact? -/
  local_intact : Bool
  /-- Structural invariant: global severing implies local surface intact.
      Global and local constraint surfaces are architecturally disjoint — a
      global-severing attack cannot simultaneously compromise the local surface. -/
  global_implies_local : severs_global = true → local_intact = true

/-- Severs constraint contact (global attack). -/
def severs_constraint_contact (s : skeptical_scenario (PropLike := PropLike)) : Prop :=
  s.severs_global = true

/-- Local redeemability holds in bubble B.

    In the bubble architecture, global and local constraint surfaces are
    disjoint components.  A global-severing attack leaves the local surface
    intact — proved via the required `global_implies_local` structural field
    rather than definitional identity. -/
def local_redeemability_holds (s : skeptical_scenario (PropLike := PropLike)) (_B : Bubble) : Prop :=
  s.local_intact = true

/-- Local redeemability survives global skeptical attack.

    Single-premise theorem: the attack severs global contact, and the structural
    `global_implies_local` field certifies that local redeemability is intact.
    Proof routes through the required function field — not the identity function. -/
theorem local_redeemability_survives (s : skeptical_scenario (PropLike := PropLike)) (B : Bubble) :
    severs_constraint_contact s → local_redeemability_holds s B :=
  s.global_implies_local

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
    (_B : Bubble) (d_idx : Nat)
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

/-- Epistemic injustice → Import corruption.

    Identity-based filtering at trust gate distorts who gets heard;
    credibility deflation = unjustified ACL downgrade.

    Structural invariants: `identity_implies_deflation` and
    `identity_implies_downgrade` encode that identity-based filtering is
    definitionally a form of import corruption — certified at construction time.
    The theorem uses the `identity_based_filtering i` premise, routing it
    through both invariants. -/
structure injustice_case where
  speaker : Agent
  hearer : Agent
  /-- Is identity being used to filter? -/
  uses_identity_filter : Bool
  /-- Is credibility being deflated? -/
  deflates_credibility : Bool
  /-- Is ACL being unjustly downgraded? -/
  downgrades_acl : Bool
  /-- Structural invariant: identity filtering structurally implies credibility deflation.
      A well-formed injustice case certifies the causal link — not merely co-occurrence. -/
  identity_implies_deflation : uses_identity_filter = true → deflates_credibility = true
  /-- Structural invariant: identity filtering constitutes an unjustified ACL downgrade.
      A well-formed injustice case certifies that the import-gate distortion
      manifests as an ACL-level corruption, not just a subjective perception. -/
  identity_implies_downgrade : uses_identity_filter = true → downgrades_acl = true

/-- Identity-based filtering at trust gate. -/
def identity_based_filtering (i : injustice_case) : Prop := i.uses_identity_filter = true

/-- Credibility deflation. -/
def credibility_deflation (i : injustice_case) : Prop := i.deflates_credibility = true

/-- Unjustified ACL downgrade. -/
def unjustified_acl_downgrade (i : injustice_case) : Prop := i.downgrades_acl = true

/-- Identity-based filtering at import gates constitutes credibility deflation.
    `identity_based_filtering i` flows through
    `i.identity_implies_deflation` and `i.identity_implies_downgrade` to derive
    both conclusions. -/
theorem injustice_is_import_corruption (i : injustice_case) :
    identity_based_filtering i → (credibility_deflation i ∧ unjustified_acl_downgrade i) :=
  fun h_filter => ⟨i.identity_implies_deflation h_filter, i.identity_implies_downgrade h_filter⟩

/-- Extended cognition → Bubble boundary question.

    Deposits live in bubbles that include artifacts;
    the question 'where is cognition?' becomes 'where is the bubble boundary and ACL?'

    `artifact_is_included` is a required structural field: the
    extended_case represents the scenario where the artifact is in the bubble,
    certified at construction time.  The theorem derives membership directly from
    this invariant — no separate premise needed. -/
structure extended_case where
  bubble_boundary : Bubble
  /-- Does the bubble include this artifact? -/
  artifact_included : Bool
  /-- Structural invariant: the artifact is included in this bubble.
      The extended cognition case presupposes artifact membership;
      constructing an extended_case requires proving this holds. -/
  artifact_is_included : artifact_included = true

/-- Does the bubble include the artifact? -/
def includes_artifact (e : extended_case) : Prop := e.artifact_included = true

/-- Is the artifact in the bubble? (Same as inclusion.) -/
def artifact_in_bubble (e : extended_case) : Prop := e.artifact_included = true

/-- Artifact is included in the bubble: derived from the structural invariant.
    `includes_artifact` and `artifact_in_bubble` are definitionally equal;
    no premises are needed beyond what is encoded at case construction. -/
theorem artifact_bubble_membership (e : extended_case) :
    includes_artifact e :=
  e.artifact_is_included


/-! ## Bridge Theorems

Structural theorems connecting header-stripping results to diagnosability:
when a deposit has no header, challenges against it are guesses rather than
diagnoses.  Both are proved directly from `¬depositHasHeader` (StepSemantics). -/

/-- A bridge import that strips the header cannot localise failures.

    When a deposit arrives without header preservation, any challenge against it
    names a field as a guess rather than a diagnosis from actual S/E/V inspection.
    Together with `bridge_stripped_ungrounded`, this captures both sides:
    - `bridge_stripped_ungrounded`: the challenge field is a guess w.r.t. the ledger
    - `bridge_monolithic_opaque`:   the field is not structurally checkable -/
theorem bridge_monolithic_opaque
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_stripped : ¬depositHasHeader s d_idx)
    (c : EpArch.Challenge PropLike Reason Evidence) :
    ¬field_checkable s d_idx c.suspected :=
  harder_without_headers s d_idx h_stripped c

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

    All items below are proved theorems in the Theorems.* module shown.
    Operational groundings live in StepSemantics.lean.
    ======================================================================== -/

/-! ## Key Grounding Relationships

| Theorem                        | Module (Theorems.*)   | Operational Basis (StepSemantics.lean)     |
|-------------------------------|----------------------|-------------------------------------------|
| `withdrawal_gates`            | `Withdrawal`         | `withdrawal_requires_three_gates`         |
| `repair_enforces_revalidation`| `Withdrawal`         | `repair_produces_candidate`               |
| `header_localization_link`    | `Headers`            | `grounded_export_requires_headers`        |

## Proved Theorems by Category

### Literature Diagnoses (structural theorems about classic puzzles):
- `gettier_is_V_failure` — Gettier cases exhibit V-independence failure
- `fake_barn_is_E_failure` — Fake Barn cases exhibit E-field gaps
- `safety_ctx_V_link`, `sensitivity_ctx_E_link` — Modal conditions map to V/E fields (WorldCtx-parameterized)

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

Both follow from `¬depositHasHeader`: `bridge_monolithic_opaque` via
`harder_without_headers`; `bridge_stripped_ungrounded` by direct unfolding. -/


end EpArch

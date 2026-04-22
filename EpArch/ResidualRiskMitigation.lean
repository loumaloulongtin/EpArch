/-
EpArch.ResidualRiskMitigation — Residual Risk Mitigation Coverage

Classification theorem: every residual-risk mode induced by bounded autonomous
novelty handling is covered by a prescribed EpArch mechanism.

Grounded coverage layer: companion proof-grounded relation where each constructor
carries upstream theorem evidence or structural field/projection evidence.

Grounded mode layer: structural forcing evidence showing each mode is unavoidable,
not an arbitrary taxonomy choice.

Key exports:
- `ResidualRiskMode`: nine structural failure modes induced by the operating regime
- `EpArchMechanism`: eleven prescribed architectural mechanisms
- `Mitigates`: declared coverage relation; each constructor is definitional evidence for a pairing
- `eparch_surface_covers_residual_risk_modes`: capstone coverage theorem
- `GroundedMitigates`: proof-backed companion; each constructor carries upstream theorem or
  structural projection evidence
- `grounded_mitigation_implies_mitigation`: every grounded pairing implies a declared pairing
- `eparch_surface_groundedly_covers_residual_risk_modes`: grounded coverage theorem
- `GroundedRiskMode`: grounding evidence for each mode; each constructor carries the upstream
  structural theorem that backs the mode's presence in the taxonomy
- `all_modes_structurally_grounded`: every mode is backed by an upstream structural theorem
- `all_modes_grounded_and_groundedly_covered`: bilateral capstone; every mode is both
  structurally grounded (GroundedRiskMode) and proof-backed addressed (GroundedMitigates)
-/

import EpArch.Health
import EpArch.Minimality
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments
import EpArch.Adversarial.Obligations

namespace EpArch

/-! ## ResidualRiskMode — Structural Failure Mode Taxonomy

The nine distinct failure modes that remain once risk-free autonomous novelty
handling is unavailable.  Each constructor names a mode, not an implementation
defect.  The modes exist because the operating regime (bounded verification +
PRP + novel inputs) generates them structurally; see
`residual_risk_forced_when_no_scratch_no_escalation` in `EpArch.Health`. -/

/-- The distinct structural failure modes that remain once risk-free autonomous
    novelty handling is unavailable.  Each constructor names a mode, not an
    implementation defect: the mode exists because the operating regime (bounded
    verification + PRP + novel inputs) generates it structurally.

    - `scopeLeak`:         a claim valid in one bubble is silently imported and
                           relied on outside the scope where it was verified.
    - `standardMismatch`:  no explicit acceptance threshold; the wrong standard
                           is applied at reliance time.
    - `unmodeledError`:    known failure modes or uncertainty are not recorded;
                           they propagate silently through bridge reliance.
    - `provenanceGap`:     source / chain dependency is invisible at reliance time;
                           bridge origin cannot be audited or challenged.
    - `staleness`:         a time-sensitive claim is relied on past its freshness
                           window; no mechanism enforces temporal validity.
    - `adversarialImport`: an untrusted actor submits or promotes a deposit;
                           no authorization gate is enforced.
    - `unrevokedDefect`:   a defective deposit is not revoked; the challenge and
                           correction path is absent or blocked.
    - `overbudgetReliance`: bridge reliance hides the verification gap and is
                           treated operationally as if it were scratch
                           verification; the gap is unlabelled rather than
                           structurally absent.
    - `unsafeAutonomy`:    autonomous action is taken without a sound non-action
                           branch; the escalation path is structurally absent. -/
inductive ResidualRiskMode where
  | scopeLeak
  | standardMismatch
  | unmodeledError
  | provenanceGap
  | staleness
  | adversarialImport
  | unrevokedDefect
  | overbudgetReliance
  | unsafeAutonomy
  deriving DecidableEq, Repr

/-! ## EpArchMechanism — Prescribed Architectural Surface

The eleven mechanisms that compose the EpArch mitigation surface.  Each is
present because it mitigates at least one `ResidualRiskMode` that the operating
regime forces.  The surface is prescribed by the architecture;
`eparch_surface_covers_residual_risk_modes` establishes coverage; irredundancy
is proved in a companion theorem. -/

/-- The EpArch mechanisms that compose the mitigation surface.
    Each constructor names a structural mechanism; each is present because it
    mitigates at least one `ResidualRiskMode` that the operating regime forces.
    The surface is prescribed by the architecture, not proved irredundant here:
    `eparch_surface_covers_residual_risk_modes` establishes coverage, not
    minimality in the strict sense.
    The `Mitigates` inductive below contains one or more constructors
    for every mechanism. -/
inductive EpArchMechanism where
  | bubbles           -- scope isolation: claims are localised to bubbles
  | standardsHeader   -- S-field: explicit acceptance threshold
  | errorHeader       -- E-field: uncertainty / failure-mode record
  | provenanceHeader  -- V-field: source / chain dependency
  | tau               -- τ-field: temporal validity window
  | trustBridge       -- analogical import with explicit verification gap
  | authorization     -- ACL: submit / promote / update permissions
  | bankLifecycle     -- Candidate → Deposited → Quarantined → Revoked / Forgotten
  | redeemability     -- challenge + required correction path
  | boundedRecall     -- recall-admissibility filtering; see recall_only_withdrawal_incomplete
  | escalation        -- principled non-action / referral branch; see no_escalation_forces_bridge
  deriving DecidableEq, Repr

/-! ## Mitigates — Coverage Relation

`Mitigates m r` holds when mechanism `m` converts residual-risk mode `r` from
an unstructured failure possibility into an auditable operational obligation.
Each constructor is definitional evidence; the doc-comment names the grounding
(upstream theorem or structural invariant). -/

/-- `Mitigates m r` holds when mechanism `m` converts residual-risk mode `r`
    from an unstructured failure possibility into an auditable operational
    obligation.  The inductive constructors are the evidence: each names the
    specific structural reason why the pairing holds. -/
inductive Mitigates : EpArchMechanism → ResidualRiskMode → Prop where
  /-- Bubbles localise validity: every deposit carries a `bubble` field
      (`Deposit.bubble`) that records the scope in which it was verified;
      bank-side predicates such as `deposited B d` enforce locality.
      (`Header` carries S/E/V/τ/acl/redeem; the bubble is on `Deposit`, not `Header`.)
      Scope-leak is converted into a structural locality obligation. -/
  | bubbles_scope_leak      : Mitigates .bubbles .scopeLeak
  /-- The S-header makes the acceptance standard explicit in the deposit record.
      `Deposit.Header.S : Standard` is a required field; the acceptance threshold
      is never implicit.
      Standard-mismatch is converted into a field-level audit obligation. -/
  | standards_mismatch      : Mitigates .standardsHeader .standardMismatch
  /-- The E-header records known error modes and uncertainty at deposit time.
      `Deposit.Header.E : ErrorModel` is a required field; known failure modes
      are declared at deposit time or the field is absent and visible.
      Unmodeled-error risk is converted into a declared-uncertainty obligation. -/
  | error_unmodeled         : Mitigates .errorHeader .unmodeledError
  /-- The V-header exposes the source and chain dependency of every deposit.
      `Deposit.Header.V : Provenance` is a required field; `PathExists.ttl_valid`
      and `status_live` make the path auditable.
      Provenance-gap risk is converted into a traceable-origin obligation. -/
  | provenance_gap          : Mitigates .provenanceHeader .provenanceGap
  /-- τ makes temporal validity part of the deposit record; `τ = 0` blocks
      path existence (`PathExists`).  Staleness risk is converted into a
      freshness-enforcement obligation. -/
  | tau_staleness           : Mitigates .tau .staleness
  /-- `Header.acl` records the authorization surface for every deposit;
      `Action` constructors carry agent attribution.  Authorization forcing
      is modeled at the agent/configuration layer (`AuthorizedWithdrawalGoal`,
      `TwoTierAccess`, and granular ACL results), while the abstract bank LTS
      deliberately does not enforce ACL as a Step precondition.
      Adversarial-import risk is converted into a declared authorization obligation. -/
  | auth_adversarial        : Mitigates .authorization .adversarialImport
  /-- The bank lifecycle provides Challenge/Repair/Revoke transitions:
      `challenge_produces_quarantined`, `Repair_B_produces_candidate`,
      and `revoke_produces_revoked` in `Bank.lean` witness the abstract
      lifecycle; `Step.challenge`, `Step.repair`, and `Step.revoke` in
      `StepSemantics.lean` operationalize the same correction surface.
      Unrevoked-defect risk is converted into a revocation/repair obligation. -/
  | lifecycle_defect        : Mitigates .bankLifecycle .unrevokedDefect
  /-- A trust bridge carries an explicit verification gap (`residualRiskVia`);
      overbudget reliance is labelled, not hidden.
      `risk_not_eliminable_by_budgeted_bridge` shows why the gap is irreducible;
      the bridge mechanism makes it explicit rather than hidden.
      Overbudget-reliance risk is converted into an explicit gap-labelling obligation. -/
  | bridge_overbudget       : Mitigates .trustBridge .overbudgetReliance
  /-- The escalation branch (`canEscalate`) is the sound non-action path.
      `no_escalation_forces_bridge` shows that without it the system is forced
      to bridge-or-nothing; with it, unsafe autonomous action is not the only
      remaining option.
      Unsafe-autonomy risk is converted into a principled-referral obligation. -/
  | escalation_unsafe       : Mitigates .escalation .unsafeAutonomy
  /-- Redeemability makes the challenge-and-correction path explicit and
      required: `redeemable d` (`Commitments.lean`) requires a `VerificationPath`
      aligned to `d.h.redeem`; `challenge_produces_quarantined` (`Bank.lean`)
      shows the first step of the correction pipeline is closed.
      (`PathExists.status_live` separately carries the non-revoked precondition
      for adversarial path obligations — a distinct proof surface.)
      An unrevoked defect without a redeemability structure has no correction
      obligation; with it, the obligation is explicit and auditable. -/
  | redeemability_defect    : Mitigates .redeemability .unrevokedDefect
  /-- `recall_only_withdrawal_incomplete` shows that provenance chains exceeding
      the recall budget make recall-only verification structurally incomplete.
      The `boundedRecall` mechanism prevents silent over-reliance: old deposits
      that exhaust the recall budget are filtered, converting silent overbudget
      reliance into an explicit scope failure. -/
  | bounded_recall_overbudget : Mitigates .boundedRecall .overbudgetReliance

/-! ## Coverage Theorem

`eparch_surface_covers_residual_risk_modes` is the capstone classification
theorem: every declared residual-risk mode is answered by some EpArch
mechanism.  The proof is zero-cost — each `cases r` branch supplies the
matching `Mitigates` constructor. -/

/-- EPARCH SURFACE COVERS FORCED RESIDUAL RISK MODES

    Every residual-risk mode induced by bounded autonomous novelty handling
    is covered by an EpArch mechanism that makes that mode an auditable
    operational obligation rather than an unstructured failure possibility.

    **Theorem shape:** `∀ r : ResidualRiskMode, ∃ m : EpArchMechanism, Mitigates m r`
    **Proof strategy:** `cases r`; supply the matching `Mitigates` constructor.

    This theorem is a classification theorem, not an impossibility theorem.
    The structural depth lives in `residual_risk_forced_when_no_scratch_no_escalation`
    and related theorems in `EpArch.Health`: those results explain why the
    nine risk modes are not arbitrary.  This theorem shows that EpArch's
    surface is *complete* with respect to those modes — no mode is left
    unaddressed.

    Does not say: the mechanisms eliminate the underlying risk.  `Mitigates m r`
    states that mechanism `m` converts risk mode `r` into an auditable obligation;
    whether that obligation is correctly discharged is a system-level property,
    not an architectural guarantee.

    Does not say: each mechanism addresses exactly one mode.  The existence
    theorem requires only coverage; multiple mechanisms may address the same
    mode, and a single mechanism may address multiple modes.

    Exhaustiveness: this theorem is exhaustive over the declared
    `ResidualRiskMode` inductive.  Adding a new constructor to
    `ResidualRiskMode` breaks the proof until a new `Mitigates` constructor
    and a new case branch are supplied — the coverage guarantee is
    machine-checked, not informal. -/
theorem eparch_surface_covers_residual_risk_modes :
    ∀ r : ResidualRiskMode, ∃ m : EpArchMechanism, Mitigates m r := by
  intro r; cases r with
  | scopeLeak         => exact ⟨.bubbles,         .bubbles_scope_leak⟩
  | standardMismatch  => exact ⟨.standardsHeader, .standards_mismatch⟩
  | unmodeledError    => exact ⟨.errorHeader,      .error_unmodeled⟩
  | provenanceGap     => exact ⟨.provenanceHeader, .provenance_gap⟩
  | staleness         => exact ⟨.tau,              .tau_staleness⟩
  | adversarialImport => exact ⟨.authorization,   .auth_adversarial⟩
  | unrevokedDefect   => exact ⟨.bankLifecycle,    .lifecycle_defect⟩
  | overbudgetReliance => exact ⟨.trustBridge,    .bridge_overbudget⟩
  | unsafeAutonomy    => exact ⟨.escalation,       .escalation_unsafe⟩

/-! ========================================================================
    GROUNDED COVERAGE LAYER — Proof-Backed Mitigation Evidence
    ========================================================================

    `eparch_surface_covers_residual_risk_modes` establishes declared coverage:
    every `ResidualRiskMode` has some `Mitigates` pairing — constructors are
    definitional evidence backed by doc-comment reasoning.

    `GroundedMitigates` is a companion inductive where each constructor carries
    *actual proof evidence* — either an upstream theorem (applied to its real
    inputs) or a structural projection from an existing field.  This makes
    coverage machine-verifiable in depth, not just in classification.

    Does not prove strict minimality or irredundancy of the surface; irredundancy
    is proved in a companion theorem over the same surface.
    Each upstream-theorem case carries the theorem as a function value.
    Structural cases carry either field-projection evidence (proved by `rfl`) or
    a small proof from an existing structural field, such as `PathExists.ttl_valid`. -/

/-! ## GroundedMitigates — Proof-Backed Coverage Relation -/

/-- `GroundedMitigates m r` is the proof-backed companion to `Mitigates m r`.

    Each constructor carries an actual evidence argument: either an upstream
    theorem (as a function applied to its proper hypotheses) or a structural
    projection from a required field.  The evidence is not a bare constructor
    tag but a proof obligation whose content can be inspected.

    - Upstream-theorem constructors carry a universally-quantified function
      whose body is an application of the named theorem.
    - Structural constructors carry either a field-projection proposition
      proved by `rfl` (confirming the required field exists and is accessible)
      or a small proof obligation over an existing structural field
      (for example, `tau_staleness` derives `False` from `τ = 0 ∧ PathExists.ttl_valid`
      via `simp` rather than a plain field projection).

    `grounded_mitigation_implies_mitigation` shows this relation implies
    `Mitigates`; `eparch_surface_groundedly_covers_residual_risk_modes`
    proves grounded coverage exhaustively. -/
inductive GroundedMitigates : EpArchMechanism → ResidualRiskMode → Prop where

  /-- Scope isolation grounded by structural projection.
      Every `Deposit` carries a `bubble : Bubble` field.  The scope of a
      deposit is not implicit or inferred — it is a required record component.
      Grounding: `fun _ _ _ _ d => ⟨d.bubble, rfl⟩` — field projection from
      the `Deposit` structure definition in `EpArch.Header`. -/
  | bubbles_scope_leak :
      (∀ (PL S E P : Type) (d : Deposit PL S E P), ∃ b : Bubble, d.bubble = b) →
      GroundedMitigates .bubbles .scopeLeak

  /-- Standard enforcement grounded by structural projection.
      Every `Header` carries an `S : Standard` field.  The acceptance threshold
      is a required record component, never implicit.
      Grounding: `fun _ _ _ h => ⟨h.S, rfl⟩` — `Header.S` field projection. -/
  | standards_mismatch :
      (∀ (S E P : Type) (h : Header S E P), ∃ s : S, h.S = s) →
      GroundedMitigates .standardsHeader .standardMismatch

  /-- Error disclosure grounded by structural projection.
      Every `Header` carries an `E : ErrorModel` field.  Known failure modes
      are a required record component, not optional metadata.
      Grounding: `fun _ _ _ h => ⟨h.E, rfl⟩` — `Header.E` field projection. -/
  | error_unmodeled :
      (∀ (S E P : Type) (h : Header S E P), ∃ e : E, h.E = e) →
      GroundedMitigates .errorHeader .unmodeledError

  /-- Provenance traceability grounded by structural projection.
      Every `Header` carries a `V : Provenance` field.  Source and chain
      dependency are required record components.
      Grounding: `fun _ _ _ h => ⟨h.V, rfl⟩` — `Header.V` field projection. -/
  | provenance_gap :
      (∀ (S E P : Type) (h : Header S E P), ∃ v : P, h.V = v) →
      GroundedMitigates .provenanceHeader .provenanceGap

  /-- Temporal window enforcement grounded by `PathExists.ttl_valid`.
      `AdversarialObligations.PathExists d` requires `d.h.τ > 0` (`ttl_valid` field).
      A deposit with `τ = 0` structurally cannot carry a valid path witness.
      Proof: `simp [h_zero]` rewrites `ttl_valid : τ > 0` to `0 > 0` given
      `h_zero : τ = 0`, closing the contradiction. -/
  | tau_staleness :
      (∀ (PL S E P : Type) (d : Deposit PL S E P),
          d.h.τ = 0 → ¬AdversarialObligations.PathExists d) →
      GroundedMitigates .tau .staleness

  /-- Authorization forcing grounded by `flat_authorization_impossible`.
      `flat_authorization_impossible (M : TwoTierAccess)` proves that no flat
      authorization predicate can represent both the submission tier and the
      commit tier — granular ACL is structurally forced.
      Grounding: `flat_authorization_impossible` from `EpArch.Minimality`. -/
  | auth_adversarial :
      (∀ (M : TwoTierAccess),
          ¬∃ (f : M.Agent → M.Claim → Prop),
            (∀ a c, f a c ↔ M.can_propose a c) ∧
            (∀ a c, f a c ↔ M.can_commit a c)) →
      GroundedMitigates .authorization .adversarialImport

  /-- Lifecycle correction grounded by `challenge_produces_quarantined`.
      A deposited record subjected to `Challenge_B` moves to `Quarantined`
      status — the first step of the correction pipeline is structurally
      closed.
      Grounding: `challenge_produces_quarantined` from `EpArch.Bank`. -/
  | lifecycle_defect :
      (∀ (PL S E P : Type) (B : Bubble) (d : Deposit PL S E P) (f : Field),
          d.status = .Deposited → (Challenge_B B d f).status = .Quarantined) →
      GroundedMitigates .bankLifecycle .unrevokedDefect

  /-- Overbudget-reliance grounded by `risk_not_eliminable_by_budgeted_bridge`.
      Any similar bridge that fits within the verification budget carries
      residual risk — the gap cannot be closed by cost-constrained bridging.
      Grounding: `risk_not_eliminable_by_budgeted_bridge` from `EpArch.Minimality`. -/
  | bridge_overbudget :
      (∀ (R : ResidualRiskBridge) (b : R.Bridge),
          R.sim b R.novel_claim →
          R.bridge_cost b R.novel_claim ≤ R.budget →
          ¬R.risk_free b R.novel_claim) →
      GroundedMitigates .trustBridge .overbudgetReliance

  /-- Escalation path grounded by `no_escalation_forces_bridge`.
      When an autonomy model satisfies `AutonomyUnderPRPGoal` and
      escalation is unavailable, a bridge is the only sound response.
      The escalation mechanism supplies the principled non-action branch
      that makes unsafe autonomous action structurally avoidable.
      Grounding: `no_escalation_forces_bridge` from `EpArch.Health`. -/
  | escalation_unsafe :
      (∀ (M : AutonomyModel) (_ : AutonomyUnderPRPGoal M)
          (B : M.sig.Bubble) (d : M.sig.Deposit)
          (_ : M.ops.mustHandle B d)
          (_ : ¬M.ops.verifyWithin B d (M.ops.effectiveTime B))
          (_ : ¬M.ops.canEscalate B d),
          ∃ b : M.sig.Deposit,
            M.ops.bridgeAvailable B b ∧
            M.ops.analogSim b d ∧
            M.ops.verifyVia B b d (M.ops.effectiveTime B)) →
      GroundedMitigates .escalation .unsafeAutonomy

  /-- Redeemability obligation grounded by `redeemable_implies_surface_aligned`.
      A redeemable deposit has a `VerificationPath` aligned to `d.h.redeem`.
      The challenge-and-correction path is not merely declared — it is
      structurally required by the `redeemable` predicate.
      Grounding: `redeemable_implies_surface_aligned` from `EpArch.Commitments`. -/
  | redeemability_defect :
      (∀ (PL S E P : Type) (d : Deposit PL S E P),
          redeemable d →
          ∃ vp : VerificationPath (PropLike := PL) (Standard := S)
              (ErrorModel := E) (Provenance := P),
            vp.deposit = d ∧ vp.surface = d.h.redeem) →
      GroundedMitigates .redeemability .unrevokedDefect

  /-- Bounded-recall grounded by `recall_only_withdrawal_incomplete`.
      A fixed recall budget cannot re-verify all provenance chains:
      `¬∀ v : M.Provenance, M.recall_cost v ≤ M.budget`.
      This proves that silent recall-only withdrawal is incomplete,
      which is precisely the residual that `boundedRecall` makes explicit.
      Grounding: `recall_only_withdrawal_incomplete` from `EpArch.Minimality`. -/
  | bounded_recall_overbudget :
      (∀ (M : RecallBudget), ¬∀ v : M.Provenance, M.recall_cost v ≤ M.budget) →
      GroundedMitigates .boundedRecall .overbudgetReliance

/-! ## Grounded Coverage Theorems -/



/-- GROUNDED MITIGATION IMPLIES DECLARED MITIGATION.

    Every proof-backed pairing in `GroundedMitigates` is also a declared pairing
    in `Mitigates`.  The implication is one-way: `Mitigates` constructors carry
    no proof payload, so the reverse does not hold without additional evidence.

    **Theorem shape:** `GroundedMitigates m r → Mitigates m r`
    **Proof strategy:** `cases` on the `GroundedMitigates` constructor; supply the
    matching `Mitigates` constructor directly. -/
theorem grounded_mitigation_implies_mitigation {m : EpArchMechanism} {r : ResidualRiskMode} :
    GroundedMitigates m r → Mitigates m r := by
  intro h
  cases h with
  | bubbles_scope_leak _          => exact .bubbles_scope_leak
  | standards_mismatch _          => exact .standards_mismatch
  | error_unmodeled _             => exact .error_unmodeled
  | provenance_gap _              => exact .provenance_gap
  | tau_staleness _               => exact .tau_staleness
  | auth_adversarial _            => exact .auth_adversarial
  | lifecycle_defect _            => exact .lifecycle_defect
  | bridge_overbudget _           => exact .bridge_overbudget
  | escalation_unsafe _           => exact .escalation_unsafe
  | redeemability_defect _        => exact .redeemability_defect
  | bounded_recall_overbudget _   => exact .bounded_recall_overbudget

/-- EPARCH SURFACE GROUNDEDLY COVERS RESIDUAL RISK MODES.

    Every residual-risk mode has a mitigation pairing backed by upstream theorem
    evidence or structural field-projection evidence.  This strengthens
    `eparch_surface_covers_residual_risk_modes`: the grounding confirms that each
    pairing is not merely a taxonomy claim but reflects structural or proof-level
    constraints in the formalization.

    **Theorem shape:** `∀ r : ResidualRiskMode, ∃ m : EpArchMechanism, GroundedMitigates m r`
    **Proof strategy:** `cases r`; supply the matching `GroundedMitigates` constructor
    with the actual proof witness for each mode.

    `GroundedMitigates` has eleven constructors but this proof uses nine — one per
    `ResidualRiskMode` constructor.  `redeemability_defect` and
    `bounded_recall_overbudget` are not used here because `unrevokedDefect` and
    `overbudgetReliance` are already covered by `lifecycle_defect` and
    `bridge_overbudget` respectively.  Both constructors remain available for the
    per-mechanism obligation in the irredundancy companion theorem.

    Does not say: the mechanisms are irredundant or the surface is minimal.
    Does not say: the upstream theorems eliminate the underlying risk.
    Irredundancy is proved in a companion theorem over the same surface. -/
theorem eparch_surface_groundedly_covers_residual_risk_modes :
    ∀ r : ResidualRiskMode, ∃ m : EpArchMechanism, GroundedMitigates m r := by
  intro r; cases r with
  | scopeLeak =>
    exact ⟨.bubbles,
      .bubbles_scope_leak (fun PL S E P d => ⟨d.bubble, rfl⟩)⟩
  | standardMismatch =>
    exact ⟨.standardsHeader,
      .standards_mismatch (fun S E P h => ⟨h.S, rfl⟩)⟩
  | unmodeledError =>
    exact ⟨.errorHeader,
      .error_unmodeled (fun S E P h => ⟨h.E, rfl⟩)⟩
  | provenanceGap =>
    exact ⟨.provenanceHeader,
      .provenance_gap (fun S E P h => ⟨h.V, rfl⟩)⟩
  | staleness =>
    -- PathExists.ttl_valid requires d.h.τ > 0; h_zero : τ = 0 contradicts this via simp.
    exact ⟨.tau,
      .tau_staleness (fun PL S E P d h_zero pe =>
        absurd pe.ttl_valid (by simp [h_zero]))⟩
  | adversarialImport =>
    -- flat_authorization_impossible: no flat predicate represents both access tiers.
    exact ⟨.authorization,
      .auth_adversarial (fun M h => flat_authorization_impossible M h)⟩
  | unrevokedDefect =>
    -- challenge_produces_quarantined: deposited deposit is quarantined by Challenge_B.
    exact ⟨.bankLifecycle,
      .lifecycle_defect (fun PL S E P B d f h =>
        challenge_produces_quarantined B d f h)⟩
  | overbudgetReliance =>
    -- risk_not_eliminable_by_budgeted_bridge: budget-feasible bridge carries residual risk.
    exact ⟨.trustBridge,
      .bridge_overbudget (fun R b h_sim h_bud =>
        risk_not_eliminable_by_budgeted_bridge R b h_sim h_bud)⟩
  | unsafeAutonomy =>
    -- no_escalation_forces_bridge: without escalation, bridge is the only sound response.
    exact ⟨.escalation,
      .escalation_unsafe (fun M h_auto B d h_req h_fail h_no_esc =>
        no_escalation_forces_bridge M h_auto B d h_req h_fail h_no_esc)⟩

/-! ========================================================================
    GROUNDED MODE LAYER — Structural Evidence for the Mode Taxonomy
    ========================================================================

    `GroundedRiskMode r` witnesses that residual-risk mode `r` is backed by
    upstream structural evidence — not merely introduced as a label.  Each
    constructor carries the relevant theorem (from `EpArch.Minimality` or
    `EpArch.Health`) that establishes the structural ground for the mode.

    `all_modes_structurally_grounded` shows every mode in the taxonomy has such
    backing.  `all_modes_grounded_and_groundedly_covered` is the bilateral
    capstone: every mode is both structurally grounded and proof-backed addressed.
    The two grounded sides are:
    - `GroundedRiskMode r`     — mode is backed by upstream structural evidence
    - `GroundedMitigates m r`  — mode is addressed with machine-checked evidence -/

/-! ## GroundedMode — Forcing Evidence for Each Mode -/

/-- `GroundedRiskMode r` carries upstream structural evidence that mode `r` is
    backed by a real structural constraint — not merely introduced as a label.
    Each constructor holds the relevant upstream theorem as a universally-quantified
    function applied to its proper model-structure type.

    This is the mode-taxonomy companion to `GroundedMitigates`: where
    `GroundedMitigates m r` proves mechanism `m` addresses mode `r`,
    `GroundedRiskMode r` provides the upstream structural grounding for mode `r`.

    `all_modes_structurally_grounded` instantiates every constructor from the
    named theorems in `EpArch.Minimality` and `EpArch.Health`. -/
inductive GroundedRiskMode : ResidualRiskMode → Prop where

  /-- Scope leak forced by `scope_leak_forced`.
      A flat predicate aligned to one scope leaks claims a disagreeing scope
      would reject — bubble isolation is structurally necessary. -/
  | scope_leak :
      (∀ (D : AgentDisagreement) (f : D.Claim → Prop),
          (∀ c, f c ↔ D.accept₁ c) →
          ∃ c : D.Claim, f c ∧ ¬D.accept₂ c) →
      GroundedRiskMode .scopeLeak

  /-- Standard mismatch forced by `implicit_standard_forces_mismatch`.
      No uniform standard serves claims verified under heterogeneous standards;
      a per-claim S field is structurally necessary. -/
  | standard_mismatch :
      (∀ (M : HeterogeneousStandards),
          ¬∃ (s : M.Standard), s = M.required₁ ∧ s = M.required₂) →
      GroundedRiskMode .standardMismatch

  /-- Unmodeled error forced by `implicit_error_model_forces_gap`.
      No uniform error model represents claims verified under different failure
      models; a per-claim E field is structurally necessary. -/
  | unmodeled_error :
      (∀ (M : HeterogeneousErrors),
          ¬∃ (e : M.ErrorModel), e = M.model₁ ∧ e = M.model₂) →
      GroundedRiskMode .unmodeledError

  /-- Provenance gap forced by `implicit_provenance_forces_gap`.
      No uniform source identity represents claims with different origins;
      a per-claim V field is structurally necessary. -/
  | provenance_gap :
      (∀ (M : HeterogeneousProvenance),
          ¬∃ (v : M.Provenance), v = M.source₁ ∧ v = M.source₂) →
      GroundedRiskMode .provenanceGap

  /-- Staleness grounded by `PathExists.ttl_valid`.
      A deposit with τ = 0 structurally cannot carry a valid path witness —
      the τ field is the structural ground for the staleness mode. -/
  | staleness :
      (∀ (PL S E P : Type) (d : Deposit PL S E P),
          d.h.τ = 0 → ¬AdversarialObligations.PathExists d) →
      GroundedRiskMode .staleness

  /-- Adversarial import forced by `flat_authorization_impossible`.
      No flat predicate represents both submission and commit ACL tiers;
      granular per-tier authorization is structurally forced. -/
  | adversarial_import :
      (∀ (M : TwoTierAccess),
          ¬∃ (f : M.Agent → M.Claim → Prop),
            (∀ a c, f a c ↔ M.can_propose a c) ∧
            (∀ a c, f a c ↔ M.can_commit a c)) →
      GroundedRiskMode .adversarialImport

  /-- Unrevoked defect forced by `no_lifecycle_cannot_ensure_nondefective`.
      A lifecycle-free bank cannot guarantee all admitted claims are
      non-defective; a correction lifecycle is structurally necessary. -/
  | unrevoked_defect :
      (∀ (M : DefectiveBank), ¬∀ c : M.Claim, M.admit c → ¬M.defective c) →
      GroundedRiskMode .unrevokedDefect

  /-- Overbudget reliance forced by `risk_not_eliminable_by_budgeted_bridge`.
      Any budget-feasible similar bridge for a novel over-budget claim carries
      residual risk; the verification gap cannot be closed by cheaper bridging. -/
  | overbudget_reliance :
      (∀ (R : ResidualRiskBridge) (b : R.Bridge),
          R.sim b R.novel_claim →
          R.bridge_cost b R.novel_claim ≤ R.budget →
          ¬R.risk_free b R.novel_claim) →
      GroundedRiskMode .overbudgetReliance

  /-- Unsafe autonomy grounded by `no_escalation_forces_bridge`.
      When escalation is absent, bridge reliance is the only sound response
      under PRP — the no-escalation condition is the structural ground for
      the unsafe-autonomy mode. -/
  | unsafe_autonomy :
      (∀ (M : AutonomyModel) (_ : AutonomyUnderPRPGoal M)
          (B : M.sig.Bubble) (d : M.sig.Deposit)
          (_ : M.ops.mustHandle B d)
          (_ : ¬M.ops.verifyWithin B d (M.ops.effectiveTime B))
          (_ : ¬M.ops.canEscalate B d),
          ∃ b : M.sig.Deposit,
            M.ops.bridgeAvailable B b ∧
            M.ops.analogSim b d ∧
            M.ops.verifyVia B b d (M.ops.effectiveTime B)) →
      GroundedRiskMode .unsafeAutonomy

/-! ## Mode Forcing and Bilateral Capstone -/

/-- ALL MODES ARE STRUCTURALLY GROUNDED.

    Every `ResidualRiskMode` constructor names a mode backed by an upstream
    structural theorem.  The nine modes are not a taxonomy choice — each has
    structural evidence in `EpArch.Minimality` or `EpArch.Health`.

    **Theorem shape:** `∀ r : ResidualRiskMode, GroundedRiskMode r`
    **Proof strategy:** `cases r`; supply the matching `GroundedRiskMode` constructor
    with the upstream theorem as its direct function argument. -/
theorem all_modes_structurally_grounded : ∀ r : ResidualRiskMode, GroundedRiskMode r := by
  intro r; cases r with
  | scopeLeak =>
    exact .scope_leak (fun D f hf => scope_leak_forced D f hf)
  | standardMismatch =>
    exact .standard_mismatch (fun M => implicit_standard_forces_mismatch M)
  | unmodeledError =>
    exact .unmodeled_error (fun M => implicit_error_model_forces_gap M)
  | provenanceGap =>
    exact .provenance_gap (fun M => implicit_provenance_forces_gap M)
  | staleness =>
    -- PathExists.ttl_valid requires d.h.τ > 0; h_zero : τ = 0 contradicts this via simp.
    exact .staleness (fun PL S E P d h_zero pe => absurd pe.ttl_valid (by simp [h_zero]))
  | adversarialImport =>
    exact .adversarial_import (fun M => flat_authorization_impossible M)
  | unrevokedDefect =>
    exact .unrevoked_defect (fun M => no_lifecycle_cannot_ensure_nondefective M)
  | overbudgetReliance =>
    exact .overbudget_reliance (fun R b h_sim h_bud =>
      risk_not_eliminable_by_budgeted_bridge R b h_sim h_bud)
  | unsafeAutonomy =>
    exact .unsafe_autonomy (fun M h_auto B d h_req h_fail h_no_esc =>
      no_escalation_forces_bridge M h_auto B d h_req h_fail h_no_esc)

/-- ALL MODES ARE STRUCTURALLY GROUNDED AND GROUNDEDLY COVERED (bilateral capstone).

    Every residual-risk mode is:
    (1) structurally grounded — backed by an upstream structural theorem, not
        merely introduced as a label, and
    (2) proof-backed addressed — some EpArch mechanism converts it into an
        auditable operational obligation, with machine-checked evidence.

    Together these answer two distinct challenges:
    - "the modes are an arbitrary taxonomy" — answered by `GroundedRiskMode r`
    - "the coverage is mere classification" — answered by `GroundedMitigates m r`

    **Theorem shape:**
    `∀ r, GroundedRiskMode r ∧ ∃ m : EpArchMechanism, GroundedMitigates m r`
    **Proof strategy:** pair `all_modes_structurally_grounded` with
    `eparch_surface_groundedly_covers_residual_risk_modes`. -/
theorem all_modes_grounded_and_groundedly_covered :
    ∀ r : ResidualRiskMode,
        GroundedRiskMode r ∧ ∃ m : EpArchMechanism, GroundedMitigates m r :=
  fun r => ⟨all_modes_structurally_grounded r,
             eparch_surface_groundedly_covers_residual_risk_modes r⟩

end EpArch

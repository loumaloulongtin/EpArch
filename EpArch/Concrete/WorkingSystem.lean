/-
EpArch.Concrete.WorkingSystem — Behavioral Equivalence, Grounding, and Working System

Concrete model behavioral equivalence, abstract-theorem grounding,
ConcreteWorkingSystem, Has* proofs, structural forcing, ForcingEmbedding,
and grounded-consequence derivation.

Part of the EpArch.Concrete module family.
-/

import EpArch.Concrete.Commitments
import EpArch.SystemSpec
import EpArch.Minimality
import EpArch.Convergence

namespace EpArch.ConcreteModel

/-! ## Sharp Behavioral Equivalence -/

/-- Input events that a system can receive. -/
inductive CInputEvent
  | WithdrawRequest (agent : CAgent) (bubble : CBubble) (claim : CProp)
  | ExportRequest (req : CExportRequest)
  | Challenge (ch : CChallenge)
  | TimeAdvance (ticks : CTime)

/-- Observable outcomes from processing events. -/
inductive COutcome
  | WithdrawSuccess (claim : CProp)
  | WithdrawDenied (reason : String)
  | ExportSuccess (claim : CProp) (target : String)
  | ExportDenied (reason : String)
  | ChallengeResolved (response : CRepairResponse)
  | TimeAdvanced
  deriving Repr

/-- An observation trace: sequence of (input, outcome) pairs. -/
abbrev CObservationTrace := List (CInputEvent × COutcome)

/-- Process a withdraw request in the concrete model. -/
def process_withdraw (acl : CACL) (agent : CAgent) (bubble : CBubble)
    (claim : CProp) (current_time : CTime) : COutcome :=
  match bubble.deposits.find? (fun d => d.claim = claim) with
  | none => .WithdrawDenied "no deposit found"
  | some d =>
    if compute_status d current_time ≠ .Deposited then
      .WithdrawDenied "deposit not current"
    else if ¬(acl.entries.any fun e =>
        (e.agent_id = agent.id ∨ e.agent_id = "*") ∧
        (e.bubble_id = bubble.id ∨ e.bubble_id = "*") ∧
        e.permission = "withdraw") then
      .WithdrawDenied "ACL denied"
    else
      .WithdrawSuccess claim

/-- Process an export request in the concrete model.
    Delegates the gate check to `c_valid_export` — the single authoritative
    definition. Only the outcome string is determined here. -/
def process_export (req : CExportRequest) : COutcome :=
  if c_valid_export req then
    .ExportSuccess req.deposit.claim req.target.id
  else
    .ExportDenied "no revalidation or trust bridge"

/-- Process a challenge in the concrete model. -/
def process_challenge (ch : CChallenge) : COutcome :=
  if ch.field ∈ ["S", "E", "V", "τ"] then
    -- Field-local challenge: can be diagnosed and repaired
    .ChallengeResolved .Pending
  else
    -- No field specified: cannot localize → immediately revoked
    .ChallengeResolved .Revoked

/-- Two concrete systems are behaviorally equivalent if they produce
    the same outcomes on all inputs.

    This is a SHARP definition: equivalence is observable agreement. -/
def CBehaviorallyEquivalent (acl1 acl2 : CACL) (bubble1 bubble2 : CBubble) : Prop :=
  ∀ (agent : CAgent) (claim : CProp) (t : CTime),
    process_withdraw acl1 agent bubble1 claim t = process_withdraw acl2 agent bubble2 claim t

/-- Theorem: Systems with the same deposits and ACL behave identically.

    The primitives (deposits, ACL, lifecycle) determine the behavior. -/
theorem concrete_bank_determines_behavior (acl : CACL) (B1 B2 : CBubble) :
    B1.deposits = B2.deposits → B1.id = B2.id → CBehaviorallyEquivalent acl acl B1 B2 := by
  intro h_eq h_id
  unfold CBehaviorallyEquivalent process_withdraw
  intro agent claim t
  rw [h_eq, h_id]


/-! ## Grounding Abstract Theorems in Concrete Model -/

/-- Theorem: Valid export requires revalidation or a trust bridge.

    In the concrete model, `c_valid_export` implies the request carries
    either `revalidated = true` (explicit re-run of lifecycle under target
    bubble's standards) or `via_trust_bridge = some _` (trust-bridge auth
    path). Unauthenticated cross-bubble export is impossible. -/
theorem concrete_export_requires_auth (req : CExportRequest) :
    c_valid_export req → (req.revalidated ∨ req.via_trust_bridge.isSome) := by
  -- c_valid_export is Bool, so we need to handle it as a boolean
  unfold c_valid_export
  intro h
  cases h_rev : req.revalidated with
  | true => exact Or.inl rfl
  | false =>
    simp only [h_rev, Bool.false_or] at h
    cases h_tb : req.via_trust_bridge with
    | none =>
      simp only [h_tb, Option.any] at h
    | some _ => exact Or.inr rfl

/-- Theorem: Withdrawal requires deposit-found and status-liveness (concrete model).

    In the concrete model, successful withdrawal (via `process_withdraw`) requires:
    1. Deposit found in bubble (list membership)
    2. Deposit has `compute_status d t = .Deposited` (liveness at time t)

    Note: `process_withdraw` also checks ACL permission, but this theorem only extracts
    the found deposit and status/liveness facts. The ACL branch is not witnessed in the
    conclusion. This is a concrete-model theorem about `process_withdraw`, not about
    the abstract `StepSemantics.Step.withdraw`. The abstract model enforces only `Deposited`
    status; the concrete model's `compute_status` incorporates time-based liveness as a
    domain-level policy decision separate from the abstract gate.
    The deposit returned is the one found in the bubble. -/
-- Helper lemma for find? properties (not available in all Mathlib versions)
theorem list_find?_implies {α : Type _} {p : α → Bool} {l : List α} {x : α}
    (h : l.find? p = some x) : x ∈ l ∧ p x = true := by
  induction l with
  | nil => simp only [List.find?] at h
  | cons head tail ih =>
    simp only [List.find?] at h
    split at h
    · -- p head = true
      injection h with h_eq
      subst h_eq
      constructor
      · exact List.Mem.head _
      · assumption
    · -- p head = false
      have ⟨h_mem, h_pred⟩ := ih h
      constructor
      · exact List.Mem.tail _ h_mem
      · exact h_pred

theorem concrete_withdrawal_requires_gates (acl : CACL) (agent : CAgent)
    (bubble : CBubble) (claim : CProp) (t : CTime) :
    (∃ d, process_withdraw acl agent bubble claim t = .WithdrawSuccess d) →
    ∃ d, d ∈ bubble.deposits ∧ d.claim = claim ∧ compute_status d t = .Deposited := by
  -- Withdraw success implies deposit found with correct status
  intro ⟨_, h_success⟩
  simp only [process_withdraw] at h_success
  -- Case on find?
  split at h_success
  next =>
    -- none case - contradiction
    simp at h_success
  next d heq =>
    -- heq : bubble.deposits.find? (fun d => d.claim = claim) = some d
    split at h_success
    next h_ne =>
      -- status ≠ Deposited - contradiction
      simp at h_success
    next h_status =>
      -- h_status is: ¬compute_status d current_time ≠ .Deposited
      split at h_success
      next =>
        -- ACL denied - contradiction
        simp at h_success
      next h_acl =>
        -- Success case - extract from heq using our helper
        have h_mem_pred := list_find?_implies heq
        refine ⟨d, ?_, ?_, ?_⟩
        -- d ∈ bubble.deposits
        · exact h_mem_pred.1
        -- d.claim = claim: from the predicate
        · simp at h_mem_pred
          exact h_mem_pred.2
        -- compute_status d t = .Deposited: from ¬(status ≠ Deposited)
        · simp only [ne_eq] at h_status
          cases hd : compute_status d t
          case Deposited => rfl
          all_goals exact absurd hd (fun h => h_status (by simp [h]))

/-- Theorem: Header-stripped deposits cannot be diagnosed (grounded version).

    When E and V are empty, challenges cannot localize to a field. -/
theorem concrete_headerless_undiagnosable (d : CDeposit) :
    c_header_stripped d → (d.E.length = 0 ∨ d.V.length = 0 ∨ d.S = 0) := by
  intro h_stripped
  simp only [c_header_stripped] at h_stripped
  -- Direct case analysis on disjunction - just reorder
  cases h_stripped with
  | inl h_s => exact Or.inr (Or.inr h_s)
  | inr h_rest =>
    cases h_rest with
    | inl h_e => exact Or.inl h_e
    | inr h_v => exact Or.inr (Or.inl h_v)

end EpArch.ConcreteModel


/-! ========================================================================
    Concrete Working System as Satisfying Instance

    This section proves the concrete model satisfies all Has* predicates,
    demonstrating that the SystemSpec is not vacuously true.
    ======================================================================== -/

namespace EpArch.ConcreteInstance

open EpArch

/-! ## Concrete System Specification

The concrete model has ALL Bank features:
- Bubble separation: CBubble provides scoped trust zones
- Trust bridges: CTrustBridge.auth is a sum — byAgent checks presenter identity;
  byToken applies an arbitrary credential check (email domain, badge, JWT, crypto
  key — anything ByteArray can carry). Both paths require an accountable party.
- Headers: CDeposit has S/E/V/τ structure
- Revocation: CDepositStatus.Revoked exists
- Shared ledger: CGlobalLedger provides bank functionality
- Redeemability: CConstraintSurface provides constraint-surface contact -/

/-- The concrete model's SystemSpec: all features enabled.

    This is the interpretation function: ConcreteModel → SystemSpec.
    Each feature maps to a concrete implementation. -/
def concreteSystemSpec : SystemSpec where
  has_bubble_separation := true   -- CBubble provides scoped zones
  has_trust_bridges := true       -- CTrustBridge in export protocol
  preserves_headers := true       -- CDeposit.{S,E,V,τ} preserved
  has_revocation := true          -- CDepositStatus.Revoked
  has_shared_ledger := true       -- CGlobalLedger
  has_redeemability := true       -- CConstraintSurface
  has_granular_acl := true        -- CACL provides agent-specific access control

/-! ## Concrete GroundedX Witnesses

Each `GroundedX` instance below uses a fresh private inductive type as the
domain so that the witness is self-contained within this namespace and does
not depend on `EpArch.ConcreteModel` details.

These witnesses are **minimal by design**: their purpose is to prove that the
`SystemSpec` is satisfiable (non-vacuous) — that there exists *some* system
instantiating all seven dimensions. A non-vacuity proof requires one instance,
not a realistic one. The tiny private inductives (`ConcScopeLabel`, etc.) and
trivial predicates are the smallest possible constructions that discharge each
`GroundedXStrict` obligation. For a realistic instantiation, see
`EpArch.ConcreteModel.ConcreteWorkingSystem` in `WorkingSystem.lean`. -/

private inductive ConcScopeLabel where | s1 | s2 deriving DecidableEq
private inductive ConcDeclKind  where | trusted | untrusted deriving DecidableEq
private inductive ConcStatus    where | live | revoked deriving DecidableEq
private inductive ConcEntry     where | entry deriving DecidableEq
private inductive ConcClaim     where | constrained | free deriving DecidableEq

/-- Concrete bubble evidence: two scopes disagree on `.s1`. -/
private def concBubbles : GroundedBubbles where
  Claim          := ConcScopeLabel
  scope₁         := fun c => c = .s1
  scope₂         := fun c => c = .s2
  witness        := .s1
  scope₁_accepts := rfl
  scope₂_rejects := by decide

/-- Concrete trust-bridge evidence: a trusted declaration is accepted upstream
    and downstream. -/
private def concTrustBridges : GroundedTrustBridges where
  Declaration           := ConcDeclKind
  upstream_accepts      := fun d => d = .trusted
  downstream_accepts    := fun d => d = .trusted
  witness               := .trusted
  upstream_holds        := rfl
  downstream_via_bridge := rfl

/-- Concrete header-preservation evidence: identity export preserves the datum. -/
private def concHeaders : GroundedHeaders where
  Datum            := ConcEntry
  Header           := ConcEntry
  extract          := id
  export_datum     := id
  witness          := .entry
  header_preserved := rfl

/-- Concrete revocation evidence: `.revoked` is invalid and revocable. -/
private def concRevocation : GroundedRevocation where
  Claim              := ConcStatus
  valid              := fun s => s = .live
  revocable          := fun s => s = .revoked
  witness            := .revoked
  witness_is_invalid := by decide
  can_revoke         := rfl

/-- Concrete bank evidence: a single entry produced AND consumed. -/
private def concBank : GroundedBank where
  Entry           := ConcEntry
  agent₁_produces := fun _ => True
  agent₂_consumes := fun _ => True
  witness         := .entry
  produced        := True.intro
  consumed        := True.intro

/-- Concrete redeemability evidence: constrained claims always have an audit path. -/
private def concRedeemability : GroundedRedeemability where
  Claim          := ConcClaim
  constrained    := fun c => c = .constrained
  redeemable     := fun _ => True
  witness        := .constrained
  is_constrained := rfl
  has_path       := True.intro

/-- Concrete authorization evidence: two-tier access model.

    Two agent kinds: `.authorized` (commit tier) and `.restricted` (submission tier only).
    The `.restricted` agent may propose (`can_propose = True`) but cannot commit.
    Proven by `decide` on the `ConcAuthKind` inductive with `DecidableEq`. -/
private inductive ConcAuthKind where | authorized | restricted deriving DecidableEq

private def concAuthorization : GroundedAuthorization where
  Agent         := ConcAuthKind
  Claim         := ConcAuthKind
  can_propose   := fun _ _ => True
  can_commit    := fun a _ => a = .authorized
  submitter     := .restricted
  committer     := .authorized
  tier_claim    := .authorized
  may_propose   := trivial
  cannot_commit := by decide
  may_commit    := rfl

/-- The concrete working system: all seven proof-carrying option fields set
    from concrete domain evidence. -/
def ConcreteWorkingSystem : WorkingSystem where
  spec             := concreteSystemSpec
  bubbles_ev       := some concBubbles.toStrict
  bridges_ev       := some concTrustBridges.toStrict
  headers_ev       := some concHeaders.toStrict
  revocation_ev    := some concRevocation.toStrict
  bank_ev          := some concBank.toStrict
  redeemability_ev := some concRedeemability.toStrict
  authorization_ev := some concAuthorization.toStrict


/-! ## Has* Predicates Hold for Concrete Model

Each proof is trivial by definition — the spec has the feature. -/

theorem concrete_has_bubbles : HasBubbles ConcreteWorkingSystem := by
  unfold HasBubbles ConcreteWorkingSystem concreteSystemSpec
  rfl

theorem concrete_has_trust_bridges : HasTrustBridges ConcreteWorkingSystem := by
  unfold HasTrustBridges ConcreteWorkingSystem concreteSystemSpec
  rfl

theorem concrete_has_headers : HasHeaders ConcreteWorkingSystem := by
  unfold HasHeaders ConcreteWorkingSystem concreteSystemSpec
  rfl

theorem concrete_has_revocation : HasRevocation ConcreteWorkingSystem := by
  unfold HasRevocation ConcreteWorkingSystem concreteSystemSpec
  rfl

theorem concrete_has_bank : HasBank ConcreteWorkingSystem := by
  unfold HasBank ConcreteWorkingSystem concreteSystemSpec
  rfl

theorem concrete_has_redeemability : HasRedeemability ConcreteWorkingSystem := by
  unfold HasRedeemability ConcreteWorkingSystem concreteSystemSpec
  rfl

theorem concrete_has_granular_acl : HasGranularACL ConcreteWorkingSystem := by
  unfold HasGranularACL ConcreteWorkingSystem concreteSystemSpec
  rfl

/-- Concrete model contains all Bank primitives.
    This is the consistency proof: the spec is satisfiable. -/
theorem concrete_contains_bank_primitives :
    containsBankPrimitives ConcreteWorkingSystem := by
  intro P
  cases P
  · exact concrete_has_bubbles
  · exact concrete_has_trust_bridges
  · exact concrete_has_headers
  · exact concrete_has_revocation
  · exact concrete_has_bank
  · exact concrete_has_redeemability
  · exact concrete_has_granular_acl


/-! ## Operational Properties Hold

The concrete model also satisfies the handles_* predicates. -/

/-- Concrete model satisfies ALL seven operational properties. -/
theorem concrete_satisfies_all_properties :
    SatisfiesAllProperties ConcreteWorkingSystem := by
  intro P; cases P <;>
  simp [handles_pressure, handles_distributed_agents, handles_bounded_audit,
        handles_export, handles_adversarial, handles_coordination,
        handles_truth_pressure, handles_multi_agent,
        ConcreteWorkingSystem, Option.isSome]


/-! ## ForcingEmbedding Instance

The concrete model instantiates `ForcingEmbedding`: since all features
are present, each embedding returns `Or.inl` (the feature itself).
The right disjunct (the impossible scenario) is never reached.

The derivation chain for the concrete model is now:
    concrete_forcing_embedding → embedding_to_structurally_forced →
    convergence_structural → containsBankPrimitives -/

/-- The concrete model's forcing embedding.  Every field is `Or.inl`
    because all features are present. -/
def concrete_forcing_embedding : ForcingEmbedding ConcreteWorkingSystem where
  embed P _ := match P with
    | .scope         => Or.inl concrete_has_bubbles
    | .trust         => Or.inl concrete_has_trust_bridges
    | .headers       => Or.inl concrete_has_headers
    | .revocation    => Or.inl concrete_has_revocation
    | .bank          => Or.inl concrete_has_bank
    | .redeemability => Or.inl concrete_has_redeemability
    | .authorization => Or.inl concrete_has_granular_acl

/-- The concrete model is structurally forced.
    Reads the stored `GroundedXStrict` witnesses from `ConcreteWorkingSystem`
    directly.  Each `evidence` field uses `injection` to bind the
    `some X = some G` hypothesis to the concrete witness, then applies that
    witness’s impossibility field. -/
theorem concrete_structurally_forced : StructurallyForced ConcreteWorkingSystem where
  forcing P _ := match P with
    | .scope         => concrete_has_bubbles
    | .trust         => concrete_has_trust_bridges
    | .headers       => concrete_has_headers
    | .revocation    => concrete_has_revocation
    | .bank          => concrete_has_bank
    | .redeemability => concrete_has_redeemability
    | .authorization => concrete_has_granular_acl
  evidence := {
    scope_consequence := fun G heq => by
      have hrfl : ConcreteWorkingSystem.bubbles_ev = some concBubbles.toStrict := rfl
      rw [hrfl] at heq; injection heq with hG; subst hG
      exact concBubbles.toStrict.no_flat_resolver
    trust_consequence := fun G heq => by
      have hrfl : ConcreteWorkingSystem.bridges_ev = some concTrustBridges.toStrict := rfl
      rw [hrfl] at heq; injection heq with hG; subst hG
      exact concTrustBridges.toStrict.bridge_forces_acceptance
    headers_consequence := fun G heq => by
      have hrfl : ConcreteWorkingSystem.headers_ev = some concHeaders.toStrict := rfl
      rw [hrfl] at heq; injection heq with hG; subst hG
      exact concHeaders.toStrict.routing_invariant
    revocation_consequence := fun G heq => by
      have hrfl : ConcreteWorkingSystem.revocation_ev = some concRevocation.toStrict := rfl
      rw [hrfl] at heq; injection heq with hG; subst hG
      exact concRevocation.toStrict.has_invalid_revocable_witness
    bank_consequence := fun G heq => by
      have hrfl : ConcreteWorkingSystem.bank_ev = some concBank.toStrict := rfl
      rw [hrfl] at heq; injection heq with hG; subst hG
      exact concBank.toStrict.has_shared_entry
    redeemability_consequence := fun G heq => by
      have hrfl : ConcreteWorkingSystem.redeemability_ev = some concRedeemability.toStrict := rfl
      rw [hrfl] at heq; injection heq with hG; subst hG
      exact concRedeemability.toStrict.has_constrained_redeemable_witness
    authorization_consequence := fun G heq => by
      have hrfl : ConcreteWorkingSystem.authorization_ev = some concAuthorization.toStrict := rfl
      rw [hrfl] at heq; injection heq with hG; subst hG
      exact concAuthorization.toStrict.no_flat_tier }

/-- Structural convergence applies to the concrete model.
    Full chain: ForcingEmbedding → StructurallyForced → convergence. -/
theorem concrete_structural_convergence :
    containsBankPrimitives ConcreteWorkingSystem :=
  convergence_structural ConcreteWorkingSystem concrete_structurally_forced
    concrete_satisfies_all_properties

/-- Each stored GroundedXStrict witness in ConcreteWorkingSystem satisfies its
    dimension's structural consequence obligation. -/
def concrete_grounded_consequences :=
  grounded_evidence_consequences ConcreteWorkingSystem
    concrete_structurally_forced concrete_satisfies_all_properties



end EpArch.ConcreteInstance

/-
EpArch/Meta/LeanKernelModel.lean — Lean Kernel as EpArch Instantiation

Proves that Lean's own type-checking kernel is a valid EpArch WorldCtx
instantiation satisfying all three core world-assumption bundles.

## Model

    LeanKernelCtx : WorldCtx where
      World  := Bool   -- kernel environment: clean (true) / sorry-tainted (false)
      Agent  := Unit   -- the elaborator (single kernel agent)
      Claim  := Bool   -- proposition status: provable (true) / unprovable (false)
      Obs    := Unit   -- proof irrelevance: proof-term identity is unobservable
      Truth  := fun w P => w = P   -- clean env authenticates exactly clean claims
      Utter  := fun _ _ => True    -- `sorry` = unrestricted utterance gate
      obs    := fun _ => ()        -- all worlds look the same (proof irrelevance)
      VerifyWithin := fun _ _ t => t ≥ 1  -- heartbeat-bounded elaboration

## Bundle Witnesses

- `holds_W_lies_possible`       : `sorry` is an unconditional utterance gate;
                                   unprovable claims exist (e.g., `False`).
- `holds_W_bounded_verification`: every term requires ≥ 1 heartbeat to elaborate;
                                   the heartbeat budget is the VerifyWithin bound.
- `holds_W_partial_observability`: proof irrelevance makes `obs` constant;
                                   two environments can differ on truth while
                                   looking identical to an external observer.

## Self-Referential Note

This file is type-checked by the same kernel it models.  The Lean kernel
that verifies `holds_W_lies_possible` is the entity described by
`LeanKernelCtx.World`.  The heartbeat consumed elaborating
`holds_W_bounded_verification` is bounded by `LeanKernelCtx.VerifyWithin`.

## Limitation

`LeanKernelCtx` is a proxy model matching kernel behavior by construction.
It is not a formal introspection of the Lean 4 kernel source code (which
would require importing the kernel's own implementation as a Lean library).

-/

import EpArch.WorldCtx
import EpArch.ConcreteLedgerModel
import EpArch.Meta.FalsifiableNotAuthorizable

namespace EpArch.LeanKernelModel

open EpArch


/-! ## Lean Kernel Context -/

/-- LeanKernelCtx: Lean's type-checking kernel modeled as an EpArch WorldCtx.

    Each field maps a kernel concept to an EpArch semantic primitive:

    | EpArch field       | Lean kernel concept                                    |
    |--------------------|--------------------------------------------------------|
    | World := Bool      | Kernel environment: clean (true) / sorry-tainted (false) |
    | Agent := Unit      | The elaborator (single kernel agent)                   |
    | Claim := Bool      | Proposition: provable (true) / unprovable (false)      |
    | Obs   := Unit      | Proof irrelevance: proof-term identity is not observable |
    | Truth w P = (w=P)  | Clean env authenticates exactly clean claims           |
    | Utter _ _ = True   | `sorry` makes every utterance syntactically available  |
    | obs _ = ()         | All worlds look the same externally (proof irrelevance) |
    | VerifyWithin t ≥ 1 | Elaboration costs ≥ 1 heartbeat; budget is finite      |

    Proxy-model note: this matches kernel behavior by construction.
    It is not a formal theorem obtained by introspecting kernel source code. -/
def LeanKernelCtx : EpArch.WorldCtx where
  World := Bool
  Agent := Unit
  Claim := Bool
  Obs   := Unit

  -- Truth: claim is true iff world matches claim value.
  -- Kernel reading: in a clean (true) environment, only provable (true) claims hold.
  Truth := fun w P => w = P

  -- Utter: always True — `sorry` makes every syntactic utterance available
  -- regardless of whether the claimed type is actually inhabited.
  Utter := fun _ _ => True

  -- obs: constant — proof irrelevance means proof-term identity is not observable.
  -- Two kernel environments (clean vs sorry-tainted) look identical externally.
  obs := fun _ => ()

  -- VerifyWithin: requires at least 1 heartbeat.
  -- Kernel reading: every elaboration step consumes heartbeats from the budget.
  VerifyWithin := fun _ _ t => t ≥ 1

  effectiveTime := fun _ => 10

  world_inhabited := ⟨true⟩
  agent_inhabited := ⟨()⟩
  claim_inhabited := ⟨true⟩


/-! ## W_lies_possible: `sorry` as Unrestricted Utterance -/

/-- W_lies_possible holds in LeanKernelCtx.

    In Lean, `sorry` is a kernel-level term that closes any open goal
    regardless of whether the claimed type is actually inhabited.  This is
    exactly the `unrestricted_utterance` field: the agent (elaborator) can
    utter any claim independent of its truth value.

    The false proposition is `False` in the empty environment — formalized
    here as `Truth false true = (false = true) = False`. -/
theorem holds_W_lies_possible : LeanKernelCtx.W_lies_possible where
  some_false          := ⟨false, true, fun h => Bool.noConfusion h⟩
  unrestricted_utterance := fun _ _ => trivial


/-! ## W_bounded_verification: Heartbeat Limit -/

/-- W_bounded_verification holds in LeanKernelCtx.

    Lean's elaborator operates under a heartbeat budget (set via
    `set_option maxHeartbeats`).  Every elaboration step consumes
    heartbeats; elaboration terminates (with an error) when the budget
    is exhausted.  This is formalized as `VerifyWithin w P t = (t ≥ 1)`:
    any non-trivial claim requires at least 1 heartbeat to verify.

    The witness claim is `true`, requiring step budget `k = 1`.  For any
    `t < 1` (i.e., `t = 0`), verification cannot succeed: 0 heartbeats
    are not enough to elaborate even the simplest non-trivial term. -/
theorem holds_W_bounded_verification : LeanKernelCtx.W_bounded_verification where
  verification_has_cost := ⟨true, 1, by decide, fun _ => by
    simp only [EpArch.WorldCtx.RequiresSteps, LeanKernelCtx]
    intro t h_lt h_ge
    cases t with
    | zero  => exact Nat.not_succ_le_zero 0 h_ge
    | succ n => exact Nat.not_lt_zero n (Nat.lt_of_succ_lt_succ h_lt)⟩


/-! ## W_partial_observability: Proof Irrelevance -/

/-- W_partial_observability holds in LeanKernelCtx.

    In Lean, proof irrelevance means two proofs of the same proposition are
    definitionally equal.  More broadly, the external observer sees only
    whether a term type-checks — not the kernel environment (clean vs
    sorry-tainted) that produced it.

    This is formalized as `obs w = ()` for all `w`: observationally
    equivalent worlds (both mapping to `()`) can have different truth
    values for the same claim.  Here worlds `true` and `false` are
    obs-equivalent yet `Truth true true` and `Truth false true` differ. -/
theorem holds_W_partial_observability : LeanKernelCtx.W_partial_observability where
  obs_underdetermines := ⟨true, true, false, rfl, by
    simp only [LeanKernelCtx]
    constructor
    · intro _; exact fun h => nomatch h
    · intro _; trivial⟩


/-! ## Bundle Satisfiability -/

/-- All three core world-assumption bundles hold jointly in LeanKernelCtx. -/
theorem lean_kernel_satisfies_bundles :
    Nonempty LeanKernelCtx.W_lies_possible ∧
    Nonempty LeanKernelCtx.W_bounded_verification ∧
    Nonempty LeanKernelCtx.W_partial_observability :=
  ⟨⟨holds_W_lies_possible⟩,
   ⟨holds_W_bounded_verification⟩,
   ⟨holds_W_partial_observability⟩⟩


/-! ## Theory Floor -/

/-- The Lean kernel satisfies the EpArch theory floor.

    `EpArch.Meta.TheoryFloor C` (from `Meta.FalsifiableNotAuthorizable`) is the
    named conjunction of the three W_* bundle inhabitations.  This theorem
    places `LeanKernelCtx` alongside `WitnessCtx` from `WorldWitness.lean` as
    a concrete witness, but with kernel-specific bundle interpretations:
    sorry / heartbeat / proof-irrelevance. -/
theorem lean_kernel_theory_floor : EpArch.Meta.TheoryFloor LeanKernelCtx :=
  lean_kernel_satisfies_bundles


/-! ## CAP Theorem on the Lean Kernel -/

/-- No obs-based ledger over the Lean kernel supports both innovation and
    coordination simultaneously.

    Instantiation of `WorldCtx.no_ledger_tradeoff` at `LeanKernelCtx`:
    the `obs` function is constant (`fun _ => ()`), so any obs-based Lean
    ledger gives the same verdict for the clean and the sorry-tainted
    environment.  It cannot simultaneously accept all locally valid claims
    (innovation / availability) and reject all non-globally-valid claims
    (coordination / consistency).

    Kernel reading: Lean's proof environment faces the same inherent tension
    between permissive elaboration (`sorry` closes any goal — innovation) and
    strict global coherence (only consistent theorems count — coordination).
    EpArch's Bank architecture is the structural response to this tension. -/
theorem lean_kernel_no_tradeoff :
    ∀ L : LeanKernelCtx.Ledger,
      LeanKernelCtx.obs_based L →
      ¬(LeanKernelCtx.supports_innovation L ∧ LeanKernelCtx.supports_coordination L) :=
  fun L hObs => WorldCtx.no_ledger_tradeoff LeanKernelCtx L hObs holds_W_partial_observability


/-! ## Self-Referential Meta-Theorem -/

/-- The Lean kernel is a valid EpArch WorldCtx witnessing all three bundles.

    Self-referential claim: `LeanKernelCtx` models the same kernel that
    type-checks this theorem.  Unlike the generic `WitnessCtx` from
    `WorldWitness.lean`, this existential witness carries kernel-specific
    interpretations:

    - `W_lies_possible`        ↔ `sorry` mechanism
    - `W_bounded_verification` ↔ heartbeat budget
    - `W_partial_observability`↔ proof irrelevance

    The architecture-layer requirements follow from `LeanWorkingSystem`;
    see `lean_structural_convergence` and `lean_kernel_existence`. -/
theorem lean_is_eparch_world :
    ∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability :=
  ⟨LeanKernelCtx, lean_kernel_satisfies_bundles⟩


/-! ## Architecture Layer: Lean as a Working System -/

/-- `LeanKernelSystemSpec`: the Lean kernel's architectural features as `SystemSpec`.
    | SystemSpec field          | Lean kernel feature                                        |
    |---------------------------|-----------------------------------------------------------|
    | `has_bubble_separation`   | Namespaces + module scoping = scoped trust zones          |
    | `has_trust_bridges`       | `import` declarations = cross-module trust bridges        |
    | `preserves_headers`       | Type signatures = headers preserved across elaboration    |
    | `has_revocation`          | Kernel rejects ill-typed terms; sorry taints tracked      |
    | `has_shared_ledger`       | Shared `Environment` accumulates all declarations         |
    | `has_redeemability`       | `#print axioms` verifies zero-sorry (redeemability)       | -/
def LeanKernelSystemSpec : SystemSpec where
  has_bubble_separation := true   -- Lean namespaces / module system = scoped trust zones
  has_trust_bridges     := true   -- `import` declarations = cross-module trust bridges
  preserves_headers     := true   -- type signatures = headers preserved across elaboration
  has_revocation        := true   -- kernel rejects ill-typed terms; sorry taints tracked
  has_shared_ledger     := true   -- shared `Environment` = bank (shared ledger)
  has_redeemability     := true   -- `#print axioms` = zero-sorry redeemability check


/-! ## Architecture Evidence: Domain Types and Grounded Feature Witnesses

All grounding material is defined here, before `LeanWorkingSystem`, so that
`LeanGroundedSystemSpec.toSystemSpec` can serve as `LeanWorkingSystem.spec`.
Structural impossibility theorems built on this data appear after `lean_partial_wellformed`. -/

/-! ### Bubbles: Lean Namespaces Disagree on Name Resolution -/

/-- A minimal model of Lean's namespace-qualified names.

    `LeanName.natAdd` represents `Nat.add` (in the `Nat` namespace).
    `LeanName.intAdd` represents `Int.add` (in the `Int` namespace).

    These two names share the same short form `add` but live in different
    namespaces — the essential property that forces scope separation. -/
inductive LeanName where
  | natAdd   -- Nat.add: `add` resolved under `open Nat`
  | intAdd   -- Int.add: `add` resolved under `open Int`

/-- Agent 1 (a compilation unit with `open Nat`) accepts `natAdd`. -/
def openNatAccepts : LeanName → Prop
  | .natAdd => True
  | .intAdd => False

/-- Agent 2 (a compilation unit with `open Int`) accepts `intAdd`. -/
def openIntAccepts : LeanName → Prop
  | .natAdd => False
  | .intAdd => True

/-- Bubble evidence: two Lean scopes disagree on `.natAdd`. -/
def LeanGroundedBubbles : GroundedBubbles where
  Claim          := LeanName
  scope₁         := openNatAccepts
  scope₂         := openIntAccepts
  witness        := .natAdd
  scope₁_accepts := True.intro
  scope₂_rejects := fun h => nomatch h

/-- `LeanGroundedBubbles` with impossibility consequence: no flat resolver can represent
    both the Nat-namespace and Int-namespace scopes simultaneously.
    Constructed via `GroundedBubbles.toStrict`; `no_flat_resolver` is derived
    directly from `LeanGroundedBubbles`'s scope fields. -/
def LeanGroundedBubblesStrict : GroundedBubblesStrict :=
  GroundedBubblesStrict.mk' LeanGroundedBubbles


/-! ### Trust Bridges: Lean's `import` Mechanism -/

/-- Two-constructor model of Lean modules for the trust bridge evidence.

    `init` = the Init standard library (trusted upstream).
    `userFile` = a downstream compilation unit that `import Init`. -/
inductive LeanLibrary where
  | init      -- the Init standard library
  | userFile  -- a downstream file that imports Init

/-- Init provides its own declarations. -/
def initDeclarations : LeanLibrary → Prop
  | .init     => True
  | .userFile => False

/-- After `import Init`, the user file can access Init's declarations via the bridge. -/
def userImportsInit : LeanLibrary → Prop
  | .init     => True
  | .userFile => True

/-- Trust bridge evidence: Init's `.init` entry is vouched upstream and
    accepted downstream via `import`. -/
def LeanGroundedTrustBridges : GroundedTrustBridges where
  Declaration           := LeanLibrary
  upstream_accepts      := initDeclarations
  downstream_accepts    := userImportsInit
  witness               := .init
  upstream_holds        := True.intro
  downstream_via_bridge := True.intro

/-- `LeanGroundedTrustBridges` with bridge-forcing consequence: any downstream-sound
    policy must accept Init declarations — a re-verify-only policy cannot exclude them. -/
def LeanGroundedTrustBridgesStrict : GroundedTrustBridgesStrict :=
  GroundedTrustBridgesStrict.mk' LeanGroundedTrustBridges


/-! ### Headers: Type Signatures Preserved Across Elaboration -/

/-- A Lean declaration paired with its type signature (the S/E/V header). -/
structure LeanDeclaration where
  name    : String
  typeSig : String

/-- Extract the type signature (header). -/
def leanExtractHeader : LeanDeclaration → String := fun d => d.typeSig

/-- Export step: elaboration is modelled as `id` — type signature unchanged. -/
def leanExportStep : LeanDeclaration → LeanDeclaration := id

/-- Header evidence: `Nat.succ`'s type sig survives the identity export step. -/
def LeanGroundedHeaders : GroundedHeaders where
  Datum            := LeanDeclaration
  Header           := String
  extract          := leanExtractHeader
  export_datum     := leanExportStep
  witness          := { name := "Nat.succ", typeSig := "Nat → Nat" }
  header_preserved := rfl

/-- `LeanGroundedHeaders` with routing invariance: a type-signature router agrees on
    `Nat.succ` before and after the identity export step. -/
def LeanGroundedHeadersStrict : GroundedHeadersStrict :=
  GroundedHeadersStrict.mk' LeanGroundedHeaders


/-! ### Revocation: sorry-Tainted Terms Can Be Quarantined -/

/-- A Lean term is either sorry-free (kernel-valid) or sorry-tainted. -/
inductive LeanTermKind where
  | sorryFree    -- elaborated without any `sorry`
  | sorryTainted -- closes a goal via `sorry`

/-- A term is valid iff it contains no sorry. -/
def leanTermValid : LeanTermKind → Prop
  | .sorryFree    => True
  | .sorryTainted => False

/-- A term is revocable iff it is sorry-tainted. -/
def leanTermRevocable : LeanTermKind → Prop
  | .sorryFree    => False
  | .sorryTainted => True

/-- Revocation evidence: `.sorryTainted` is invalid and revocable. -/
def LeanGroundedRevocation : GroundedRevocation where
  Claim              := LeanTermKind
  valid              := leanTermValid
  revocable          := leanTermRevocable
  witness            := .sorryTainted
  witness_is_invalid := fun h => nomatch h
  can_revoke         := True.intro

/-- `LeanGroundedRevocation` with invalid-revocable existential: `.sorryTainted` is
    demonstrably invalid and revocable, refuting any no-revocation policy. -/
def LeanGroundedRevocationStrict : GroundedRevocationStrict :=
  GroundedRevocationStrict.mk' LeanGroundedRevocation


/-! ### Shared Ledger: Cross-Module Reliance via the Environment -/

/-- Two entries in Lean's shared `Environment`. -/
inductive LeanEnvEntry where
  | initDef  -- a definition contributed by Init
  | userDef  -- a definition contributed by the user's module

/-- The Init module produces its own definitions. -/
def initProduces : LeanEnvEntry → Prop
  | .initDef => True
  | .userDef => False

/-- The user module reads Init's definitions from the shared `Environment`. -/
def userConsumes : LeanEnvEntry → Prop
  | .initDef => True
  | .userDef => True

/-- Bank evidence: `.initDef` produced by Init, consumed by user via shared Env. -/
def LeanGroundedBank : GroundedBank where
  Entry           := LeanEnvEntry
  agent₁_produces := initProduces
  agent₂_consumes := userConsumes
  witness         := .initDef
  produced        := True.intro
  consumed        := True.intro

/-- `LeanGroundedBank` with shared-entry existential: `.initDef` is produced by Init
    and consumed by the user module, refuting any isolation assumption. -/
def LeanGroundedBankStrict : GroundedBankStrict :=
  GroundedBankStrict.mk' LeanGroundedBank


/-! ### Redeemability: `#print axioms` as the Audit Path -/

/-- A Lean claim is either under constraint or verified axiom-free. -/
inductive LeanClaimStatus where
  | underReview  -- axiom dependencies not yet audited
  | axiomFree    -- passed `#print axioms`

/-- A claim is constrained iff it is under review. -/
def leanIsConstrained : LeanClaimStatus → Prop
  | .underReview => True
  | .axiomFree   => False

/-- `#print axioms` always terminates and reveals the full axiom footprint. -/
def leanHasAuditPath : LeanClaimStatus → Prop
  | .underReview => True
  | .axiomFree   => True

/-- Redeemability evidence: `.underReview` has the `#print axioms` audit path. -/
def LeanGroundedRedeemability : GroundedRedeemability where
  Claim          := LeanClaimStatus
  constrained    := leanIsConstrained
  redeemable     := leanHasAuditPath
  witness        := .underReview
  is_constrained := True.intro
  has_path       := True.intro

/-- `LeanGroundedRedeemability` with constrained-and-redeemable existential:
    `.underReview` is constrained and has the `#print axioms` audit path,
    refuting any closure assumption. -/
def LeanGroundedRedeemabilityStrict : GroundedRedeemabilityStrict :=
  GroundedRedeemabilityStrict.mk' LeanGroundedRedeemability


/-! ### Full Grounded Spec -/

/-- All-false base: every `true` in `toSystemSpec` comes from evidence. -/
private def leanZeroSpec : SystemSpec where
  has_bubble_separation := false
  has_trust_bridges     := false
  preserves_headers     := false
  has_revocation        := false
  has_shared_ledger     := false
  has_redeemability     := false

/-- The Lean kernel's `GroundedSystemSpec`: all six Bank features backed by evidence.
    | Feature        | Evidence                                                     |
    |----------------|--------------------------------------------------------------|
    | `bubbles`      | Nat vs Int namespaces disagree on `add` (LeanName data)      |
    | `trust_bridges`| Init declarations available downstream via `import`          |
    | `headers`      | `Nat.succ` type sig preserved through identity export        |
    | `revocation`   | sorry-tainted terms quarantined by the kernel TCB            |
    | `bank`         | Shared `Environment`: Init produces, user consumes           |
    | `redeemability`| `#print axioms` provides the audit path for any claim        | -/
def LeanGroundedSystemSpec : GroundedSystemSpec where
  bubbles       := LeanGroundedBubbles
  trust_bridges := LeanGroundedTrustBridges
  headers       := LeanGroundedHeaders
  revocation    := LeanGroundedRevocation
  bank          := LeanGroundedBank
  redeemability := LeanGroundedRedeemability
  base          := leanZeroSpec


/-- `LeanGroundedBehavior`: evidence for all six behavioral capabilities,
    one per architectural forcing dimension.

    | WorkingSystem field  | Evidence                  | Kernel basis                              |
    |----------------------|---------------------------|-------------------------------------------|
    | `bubbles_ev`         | `LeanGroundedBubbles`     | Nat vs Int namespaces disagree on `add`   |
    | `bridges_ev`         | `LeanGroundedTrustBridges`| Init declarations relied on via import    |
    | `headers_ev`         | `LeanGroundedHeaders`     | Type sig preserved through identity export|
    | `revocation_ev`      | `LeanGroundedRevocation`  | sorry-tainted terms can be quarantined    |
    | `bank_ev`            | `LeanGroundedBank`        | InitDef accumulated in Env, consumed      |
    | `redeemability_ev`   | `LeanGroundedRedeemability`| `#print axioms` provides the audit path  | -/
def LeanGroundedBehavior : GroundedBehavior where
  bubbles       := LeanGroundedBubbles
  trust_bridges := LeanGroundedTrustBridges
  headers       := LeanGroundedHeaders
  revocation    := LeanGroundedRevocation
  bank          := LeanGroundedBank
  redeemability := LeanGroundedRedeemability

/-- `LeanWorkingSystem`: the Lean kernel modeled as an EpArch `WorkingSystem`.

    Built from `LeanGroundedBehavior` and `LeanGroundedSystemSpec.toSystemSpec` via
    `WorkingSystem.withGroundedBehavior`.  The base arg passes `none` for all `_ev`
    fields; `withGroundedBehavior` immediately replaces each with `some G.toStrict`.

    | `WorkingSystem` evidence field | Stored value (set by `withGroundedBehavior`)            |
    |--------------------------------|---------------------------------------------------------|
    | `bubbles_ev`                   | `some (LeanGroundedBubbles.toStrict)`                   |
    | `bridges_ev`                   | `some (LeanGroundedTrustBridges.toStrict)`              |
    | `headers_ev`                   | `some (LeanGroundedHeaders.toStrict)`                   |
    | `revocation_ev`                | `some (LeanGroundedRevocation.toStrict)`                |
    | `bank_ev`                      | `some (LeanGroundedBank.toStrict)`                      |
    | `redeemability_ev`             | `some (LeanGroundedRedeemability.toStrict)`             |

    Because each `_ev` field is `some`, `Option.isSome = true` and all six
    `handles_*` predicates hold (`SatisfiesAllProperties`).

    All six `HasX` predicates are satisfied via `grounded_spec_contains_all
    LeanGroundedSystemSpec`, which reads the corresponding `SystemSpec` fields
    (`has_bubble_separation`, `has_trust_bridges`, `preserves_headers`,
    `has_revocation`, `has_shared_ledger`, `has_redeemability`) set to `true`
    by `LeanGroundedSystemSpec.toSystemSpec`. -/
def LeanWorkingSystem : WorkingSystem :=
  WorkingSystem.withGroundedBehavior LeanGroundedBehavior
    { spec               := LeanGroundedSystemSpec.toSystemSpec
      bubbles_ev         := none
      bridges_ev         := none
      headers_ev         := none
      revocation_ev      := none
      bank_ev            := none
      redeemability_ev   := none }


/-! ## Has* Predicates for LeanWorkingSystem -/

-- `grounded_spec_contains_all LeanGroundedSystemSpec` proves all six features
-- simultaneously.  After `unfold HasX LeanWorkingSystem`, the goal becomes
-- `spec_has_X LeanGroundedSystemSpec.toSystemSpec`, which is the corresponding
-- component of the conjunction — no manually-set flag is consulted.
theorem lean_has_bubbles : HasBubbles LeanWorkingSystem := by
  unfold HasBubbles LeanWorkingSystem
  exact (grounded_spec_contains_all LeanGroundedSystemSpec).1

theorem lean_has_trust_bridges : HasTrustBridges LeanWorkingSystem := by
  unfold HasTrustBridges LeanWorkingSystem
  exact (grounded_spec_contains_all LeanGroundedSystemSpec).2.1

theorem lean_has_headers : HasHeaders LeanWorkingSystem := by
  unfold HasHeaders LeanWorkingSystem
  exact (grounded_spec_contains_all LeanGroundedSystemSpec).2.2.1

theorem lean_has_revocation : HasRevocation LeanWorkingSystem := by
  unfold HasRevocation LeanWorkingSystem
  exact (grounded_spec_contains_all LeanGroundedSystemSpec).2.2.2.1

theorem lean_has_bank : HasBank LeanWorkingSystem := by
  unfold HasBank LeanWorkingSystem
  exact (grounded_spec_contains_all LeanGroundedSystemSpec).2.2.2.2.1

theorem lean_has_redeemability : HasRedeemability LeanWorkingSystem := by
  unfold HasRedeemability LeanWorkingSystem
  exact (grounded_spec_contains_all LeanGroundedSystemSpec).2.2.2.2.2


/-! ## Direct Implementation: Bank Primitives by Construction -/

/-- `LeanWorkingSystem` directly implements all six Bank primitives.

    This is the *direct* route — independent of the convergence theorem.
    It does not say "any system handling X must have Y, and this system
    handles X"; it says "this system has Y, constructed from evidence."

    Each `HasX` proof extracts the corresponding component from
    `grounded_spec_contains_all LeanGroundedSystemSpec`; no Boolean flag
    is inspected directly.  The `Bool = true` values in `LeanWorkingSystem`'s
    spec are set by `GroundedSystemSpec.toSystemSpec`, which requires each
    `GroundedX` witness to have been supplied.

    | HasX primitive      | Evidence basis                                        |
    |---------------------|-------------------------------------------------------|
    | `HasBubbles`        | `LeanGroundedBubbles` (Nat vs Int namespace disagreement) |
    | `HasTrustBridges`   | `LeanGroundedTrustBridges` (`import Init` trust bridge) |
    | `HasHeaders`        | `LeanGroundedHeaders` (`Nat.succ` type sig preserved)  |
    | `HasRevocation`     | `LeanGroundedRevocation` (sorry-tainted → quarantine)  |
    | `HasBank`           | `LeanGroundedBank` (InitDef produced and consumed)     |
    | `HasRedeemability`  | `LeanGroundedRedeemability` (`#print axioms` audit path)| -/
theorem lean_implements_bank_primitives : containsBankPrimitives LeanWorkingSystem := by
  intro P
  cases P
  · exact lean_has_bubbles
  · exact lean_has_trust_bridges
  · exact lean_has_headers
  · exact lean_has_revocation
  · exact lean_has_bank
  · exact lean_has_redeemability

/-- `LeanWorkingSystem` is partially well-formed at all constraints: stored
    evidence fields ↔ architectural features.

    Applies `grounded_partial_wellformed`: any system built via
    `withGroundedBehavior`/`toSystemSpec` satisfies `PartialWellFormed W allConstraints`. -/
theorem lean_partial_wellformed : PartialWellFormed LeanWorkingSystem allConstraints :=
  grounded_partial_wellformed LeanGroundedBehavior LeanGroundedSystemSpec

/-- The Lean kernel satisfies all six operational properties.

    Follows directly from `grounded_behavior_satisfies_all`: any system
    built via `WorkingSystem.withGroundedBehavior` satisfies all six
    `handles_*` predicates, because each `Option *_ev.isSome = true`
    witness is set from the evidence in `LeanGroundedBehavior`. -/
theorem lean_satisfies_all_properties : SatisfiesAllProperties LeanWorkingSystem :=
  grounded_behavior_satisfies_all LeanGroundedBehavior _


/-! ## Structural Grounding for HasBubbles

A concrete `AgentDisagreement` built from Lean's namespace model makes
`flat_scope_impossible` fire, proving that scope separation is structurally
required by the Lean kernel's own name-resolution structure.

### Model

In Lean, a name like `add` lives in a namespace.  `Nat.add` and `Int.add`
are both "add", but resolved in different namespaces.  When two compilation
units open different namespaces:

    -- Module A: `open Nat`  → "add" means `Nat.add`
    -- Module B: `open Int`  → "add" means `Int.add`

Each module has a different acceptance criterion for the unqualified name
"add".  No single flat resolver can simultaneously agree with both.

### Claims

We model Lean names as a two-constructor inductive reflecting a minimal
namespace hierarchy: a qualified name belongs to one of two namespaces. -/

/-- The namespace disagreement: two Lean compilation units disagree on
    which `add` is canonical.  `natAdd` is the witness — accepted by the
    `open Nat` module, rejected by the `open Int` module. -/
def leanNamespaceDisagreement : AgentDisagreement where
  Claim           := LeanName
  accept₁         := openNatAccepts
  accept₂         := openIntAccepts
  witness         := .natAdd
  agent1_accepts  := trivial         -- openNatAccepts .natAdd = True
  agent2_rejects  := id              -- openIntAccepts .natAdd = False; ¬False = True

/-- **`flat_scope_impossible` fires on Lean's namespace structure.**

    No single name-resolution function can simultaneously:
    - agree with `open Nat` (accepting `natAdd`, rejecting `intAdd`), AND
    - agree with `open Int` (accepting `intAdd`, rejecting `natAdd`).

    Derived from `flat_scope_impossible` applied to `leanNamespaceDisagreement`:
    a flat (single-namespace) resolver is provably inadequate. -/
theorem lean_namespace_requires_scope_separation :
    ¬∃ (f : LeanName → Prop),
      (∀ n, f n ↔ openNatAccepts n) ∧
      (∀ n, f n ↔ openIntAccepts n) :=
  flat_scope_impossible leanNamespaceDisagreement

/-- `LeanWorkingSystem` carries the namespace disagreement data.

    This instances `RepresentsDisagreement` for `LeanWorkingSystem`,
    connecting the abstract structural model to the concrete kernel
    evidence.  When combined with the bridge impossibility machinery,
    it shows that a bubbleless `LeanWorkingSystem` would be self-contradictory. -/
def lean_represents_disagreement : RepresentsDisagreement LeanWorkingSystem where
  Claim          := LeanName
  accept₁        := openNatAccepts
  accept₂        := openIntAccepts
  witness        := .natAdd
  agent1_accepts := trivial
  agent2_rejects := id

/-- If `LeanWorkingSystem` lacked bubbles but committed to a flat resolver
    faithful to both namespace agents, the contradiction is immediate.

    This is the bridge impossibility applied to kernel data: `bridge_bubbles_impossible`
    fires regardless of which system we consider — the flat-resolver commitment
    is universally absurd, and `leanNamespaceDisagreement` supplies the
    concrete witness that makes it absurd for the Lean kernel specifically. -/
theorem lean_no_flat_namespace_resolver
    (f : LeanName → Prop)
    (h₁ : ∀ n, f n ↔ openNatAccepts n)
    (h₂ : ∀ n, f n ↔ openIntAccepts n) :
    False :=
  lean_namespace_requires_scope_separation ⟨f, h₁, h₂⟩


/-! ## Single-Feature Grounded Spec (Stepping Stone)

`LeanGroundedBubbles` and the full `LeanGroundedSystemSpec` are defined above
in the Architecture Evidence section.  `LeanKernelSystemSpecGrounded` below
grounds only `has_bubble_separation` and is the intermediate artifact from
before the full six-feature grounding was available. -/

/-- A `SystemSpec` for the Lean kernel grounded in `LeanGroundedBubbles`.

    This is `LeanKernelSystemSpec` with `has_bubble_separation` set
    *because* `LeanGroundedBubbles` was provided — not asserted manually.
    The other five fields are copied from `LeanKernelSystemSpec`. -/
def LeanKernelSystemSpecGrounded : SystemSpec :=
  SystemSpec.withGroundedBubbles LeanGroundedBubbles LeanKernelSystemSpec

/-- `HasBubbles` holds for a `WorkingSystem` whose spec is
    `LeanKernelSystemSpecGrounded`, derived from evidence.

    Traces back to `LeanGroundedBubbles`, `openNatAccepts`, and
    `leanNamespaceDisagreement`. -/
theorem lean_has_bubbles_grounded :
    spec_has_bubbles LeanKernelSystemSpecGrounded :=
  grounded_bubbles_justified LeanGroundedBubbles LeanKernelSystemSpec


/-! ## Structural Forcing -/

/-- Forcing embedding for `LeanWorkingSystem`.

    All six arms return `Or.inl` (the feature itself) because every
    architectural feature is present in the Lean kernel.  The right
    disjunct (the impossible bridge scenario) is never reached. -/
def lean_forcing_embedding : ForcingEmbedding LeanWorkingSystem where
  embed P _ := match P with
    | .scope         => Or.inl lean_has_bubbles
    | .trust         => Or.inl lean_has_trust_bridges
    | .headers       => Or.inl lean_has_headers
    | .revocation    => Or.inl lean_has_revocation
    | .bank          => Or.inl lean_has_bank
    | .redeemability => Or.inl lean_has_redeemability

/-- `LeanWorkingSystem` is structurally forced — derived from the
    forcing embedding via the generic translation layer. -/
theorem lean_structurally_forced : StructurallyForced LeanWorkingSystem :=
  embedding_to_structurally_forced LeanWorkingSystem lean_forcing_embedding

/-- `LeanWorkingSystem` contains Bank primitives.

    Full chain: ForcingEmbedding → StructurallyForced → convergence.
    Self-referential: type-checked by the same kernel whose features populate
    `LeanKernelSystemSpec`. -/
theorem lean_structural_convergence : containsBankPrimitives LeanWorkingSystem :=
  convergence_structural LeanWorkingSystem lean_structurally_forced lean_satisfies_all_properties

/-- Each stored GroundedXStrict witness in LeanWorkingSystem satisfies its
    dimension's structural consequence obligation. -/
def lean_grounded_consequences :=
  grounded_evidence_consequences LeanWorkingSystem
    lean_structurally_forced lean_satisfies_all_properties


/-! ## Combined Two-Layer Summary -/

/-- The Lean kernel, as `LeanWorkingSystem`, contains Bank primitives.

    Citability anchor.  Two independent proofs are available in this file:

    - **Direct** (`lean_implements_bank_primitives`): via
      `grounded_spec_contains_all LeanGroundedSystemSpec` — each `HasX`
      proof extracts the matching component of the conjunction; no Boolean
      flag is inspected directly.  Does not depend on the convergence theorem.

    - **Structural** (`lean_structural_convergence`): by necessity — any
      system handling these six operational pressures must have the features.
      Routes through `ForcingEmbedding → StructurallyForced →
      convergence_structural`.

    This alias uses the direct route (`lean_implements_bank_primitives`). -/
theorem lean_kernel_forces_bank_primitives : containsBankPrimitives LeanWorkingSystem :=
  lean_implements_bank_primitives

/-- The Lean kernel satisfies all EpArch requirements — both layers.

    **World layer** (`LeanKernelCtx`):
    - `W_lies_possible`        ↔ `sorry` mechanism
    - `W_bounded_verification` ↔ heartbeat budget
    - `W_partial_observability`↔ proof irrelevance
    - No obs-based ledger serves both innovation and coordination
      (`lean_kernel_no_tradeoff`)

    **Architecture layer** (`LeanWorkingSystem`):
    - `PartialWellFormed W allConstraints` — all six behavioral ↔ architectural biconditionals hold
    - `containsBankPrimitives` — directly: all six `HasX` fields hold by construction;
                                  separately: forced by `lean_structural_convergence`
    - `StructurallyForced`     — six embedding arms all return `Or.inl`
    - `SatisfiesAllProperties` — all six `handles_*` predicates hold via `Option *_ev.isSome = true`

    The proof is discharged by the kernel it models. -/
theorem lean_kernel_existence :
    (∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability) ∧
    (∃ W : WorkingSystem,
      PartialWellFormed W allConstraints ∧ StructurallyForced W ∧ SatisfiesAllProperties W ∧
      containsBankPrimitives W) :=
  ⟨lean_is_eparch_world,
   ⟨LeanWorkingSystem,
    lean_partial_wellformed,
    lean_structurally_forced,
    lean_satisfies_all_properties,
    lean_implements_bank_primitives⟩⟩

/-! ## Gettier / Safety / Sensitivity Witnesses (Phase 0B)

`LeanKernelCtx` exhibits a concrete Gettier case.  With `World = Bool`:

- `world := false` — sorry-tainted environment (P is not true here)
- `P    := true`  — a claim that is true only in the clean environment

S and E both pass, but the truth-maker (`world = true`) and the actual world
(`world = false`) are observationally identical (`obs _ = ()`), yet distinct.
The `provenance_disconnected` field requires `Bool.noConfusion` — not trivial.

**Safety / Sensitivity witnesses require `v_independent` / `e_covers` fields**
of type `∀ w' : Bool, (w' = P) ↔ (deposit_world = P)` (or the negation form).
With a 2-element `Bool` universe, no choice of `P` and `deposit_world` satisfies
this universally: if `deposit_world = P` the RHS is `True`, forcing `w' = P` for
all `w'`; if `deposit_world ≠ P` the RHS is `False`, forcing `¬(w' = P)` for all
`w'`.  Both are false in a 2-element type.  A richer world type (e.g. a single-
world `Unit` context or a multi-valued propositions lattice) is needed to witness
these structures non-trivially.  Their theorems (`safety_ctx_V_link`,
`sensitivity_ctx_E_link`) are therefore demonstrated generically in `Theorems.lean`
rather than at this concrete instantiation. -/

/-- Concrete Gettier case at `LeanKernelCtx`.

    `world = false` (sorry-tainted environment); `P = true` (a claim that is
    provable — i.e., `Truth true true` — only in the clean environment).
    `Truth false true = (false = true) = False`, so the claim is not true in
    this world.  The clean environment (`true`) witnesses `P` and is
    observationally indistinguishable (`obs _ = ()`).

    `provenance_disconnected`: any `w'` with `C.Truth w' true = (w' = true)` is
    distinct from `world = false`.  Proved by `subst; decide` after the kernel
    reduces `LeanKernelCtx.Truth`. -/
def leanKernelGettierCase : GettierCaseCtx LeanKernelCtx where
  world    := false   -- sorry-tainted environment
  P        := true    -- claim that is false in this world
  S_passes := true    -- syntactically accepted
  E_passes := true    -- error model locally adequate
  provenance_disconnected := by
    intro w' h_truth _ h_eq
    -- h_truth : LeanKernelCtx.Truth w' true;  h_eq : w' = false
    -- Rewrite w' → false in h_truth; then Bool.noConfusion closes the goal
    rw [h_eq] at h_truth
    exact Bool.noConfusion h_truth

/-- The Gettier profile holds at `leanKernelGettierCase`:
    S and E pass, the claim is false in `world = false`,
    and the clean environment `true` witnesses `P` while being obs-equivalent. -/
theorem leanKernel_is_gettier : IsGettierCtx LeanKernelCtx leanKernelGettierCase :=
  ⟨rfl, rfl, Bool.noConfusion, ⟨true, rfl, rfl⟩⟩

/-- The Gettier provenance gap at `LeanKernelCtx`.

    There exists a world (the clean environment `true`) that
    (1) witnesses `P`,
    (2) is observationally equivalent to `world = false`,
    (3) is distinct from `world`.
    Proved by applying the generic `gettier_ctx_exhibits_provenance_gap` to the
    concrete witness — the non-trivial path through `provenance_disconnected`. -/
theorem leanKernel_gettier_gap :
    ∃ w' : LeanKernelCtx.World,
      LeanKernelCtx.Truth w' leanKernelGettierCase.P ∧
      LeanKernelCtx.obs w' = LeanKernelCtx.obs leanKernelGettierCase.world ∧
      w' ≠ leanKernelGettierCase.world :=
  gettier_ctx_exhibits_provenance_gap LeanKernelCtx leanKernelGettierCase leanKernel_is_gettier

/-! ## Kernel-Level S-Field: Axiom Footprint as Standard

    The axiom footprint of a proof is its S field in the EpArch sense.
    `#print axioms some_theorem` is the kernel's S-field readout — a
    truthful record of what standard was applied at elaboration time.
    It is stamped on the claim, fixed, and not changeable per reader.

    S/E/V independence at the meta level:

    - V: the kernel genuinely elaborated this term (provenance is sound).
    - E: proof components are present; no detection gap.
    - S: the axiom level actually used — `allows_sorry`, `classical_only`,
         or `axiom_free`.

    Two distinct kinds of S-failure arise, mirroring Theorems.lean:

    1. **Relational** (axiom threshold mismatch): the same sorry-containing
       proof is acceptable to a development consumer and a S-failure for a
       publication consumer. Both V and E are sound. Only the consuming
       agent's required threshold differs.

    2. **Absolute/void** (`sorry ⊢ False`): when E already documents
       `sorryTainted` as revocable (`LeanGroundedRevocation`) and S is
       solely "sorry closed it", both structural conditions are present in
       the fields — `lean_S_is_void` is witnessed. This is a demonstration
       of field independence, not a prescription for agent acceptance policy.
       Mirrors the known-liar-cook case in Theorems.lean.
-/

/-- Lean axiom levels: the S-field vocabulary for Lean proofs.
    Stamped by the kernel at elaboration time. Property of the claim. -/
inductive LeanAxiomLevel where
  | allows_sorry    -- sorryAx in the axiom closure (dev standard)
  | classical_only  -- Classical.choice / propext only; no sorryAx
  | axiom_free      -- kernel primitives only; `#print axioms` empty
  deriving DecidableEq, Repr

/-- Does a proof at `deposit_level` satisfy the `required_level` threshold
    for a specific consuming agent?

    Mirrors `StandardClearance` in Theorems.lean (bucket 1 upgrade):
    `threshold_met : Prop` is the real semantic content; `clears : Bool` is an
    executable mirror; `clears_sound` bridges them.  EpArch records that the
    threshold relationship holds or fails; the ordering on `LeanAxiomLevel`
    (allows_sorry < classical_only < axiom_free) lives in the consuming agent's
    acceptance policy, outside EpArch's scope. -/
structure LeanStandardClearance where
  /-- The S value stamped on the proof: axiom level actually used. -/
  deposit_level  : LeanAxiomLevel
  /-- The minimum axiom level this consuming agent requires. -/
  required_level : LeanAxiomLevel
  /-- The real semantic content: does deposit_level satisfy required_level?
      EpArch records that this relation holds or fails; the ordering on
      LeanAxiomLevel lives in the consuming agent's policy. -/
  threshold_met  : Prop
  /-- Executable mirror of threshold_met for computable contexts. -/
  clears         : Bool
  /-- Sound bridge: the Bool is honest about the Prop. -/
  clears_sound   : clears = true ↔ threshold_met

/-- V-witness for a Lean Standard case: the kernel genuinely elaborated the term.

    Mirrors `VProvenance` in Theorems.lean.  V is sound when the kernel used
    its normal elaboration path (no definitional shortcuts bypassing type-checking). -/
structure LeanVWitness where
  /-- The declaration name whose provenance is being witnessed -/
  decl_name         : String
  /-- Kernel genuinely elaborated this term (normal elaboration, not bypassed) -/
  kernel_elaborated : Bool
  /-- V passes: certified at construction time -/
  kernel_cert       : kernel_elaborated = true

/-- E-witness for a Lean Standard case: known failure modes are documented.

    Mirrors `EAdequacy` in Theorems.lean.  E is sound when all relevant
    known failure modes (e.g., sorryAx, inconsistent axioms) are explicitly
    documented in the LeanGroundedRevocation surface. -/
structure LeanEWitness where
  /-- Known failure modes documented in the error model (e.g., "sorryAx") -/
  documented_failures : List String
  /-- E adequate: no relevant undocumented failure mode for this proof -/
  e_adequate          : Bool
  /-- E passes: certified at construction time -/
  adequate_cert       : e_adequate = true

/-- Lean Standard Case: the proof's S field doesn't clear a strict consumer.
    V and E remain sound — the only issue is S.

    Mirrors `StandardCase` in Theorems.lean (bucket 2 upgrade): replaces Bool
    `e_passes`/`v_passes` with `LeanEWitness`/`LeanVWitness` carrying explicit
    documented-failures and kernel-elaboration evidence. -/
structure LeanStandardCase where
  decl_name   : String
  /-- V-field witness: kernel genuinely elaborated this term -/
  v_witness   : LeanVWitness
  /-- E-field witness: known failure modes are documented -/
  e_witness   : LeanEWitness
  s_clearance : LeanStandardClearance
  /-- S fails: the threshold relation is not met (Prop-level, not Bool = false) -/
  clearance_fails_cert : ¬s_clearance.threshold_met

def lean_S_fails (lsc : LeanStandardCase) : Bool := !lsc.s_clearance.clears

/-- A LeanStandardCase routes to S-failure.
    Proof: extracts `¬threshold_met` from `clearance_fails_cert` via Bool
    case-split on `clears` + `clears_sound` bridge — a genuine Prop negation. -/
theorem lean_standard_case_is_S_failure (lsc : LeanStandardCase) :
    lean_S_fails lsc = true := by
  simp only [lean_S_fails]
  cases h_eq : lsc.s_clearance.clears with
  | false => rfl
  | true => exact absurd (lsc.s_clearance.clears_sound.mp h_eq) lsc.clearance_fails_cert

/-- Canonical publication-mode failure: `allows_sorry` proof, `axiom_free` required.

    - `v_witness`: kernel genuinely elaborated the term (normal path)
    - `e_witness`: "sorryAx" is documented in `LeanGroundedRevocation`
    - `threshold_met = False`: allows_sorry does not satisfy axiom_free
    - `clearance_fails_cert = False.elim`: witnesses `¬False` -/
def canonical_sorry_publication_case (name : String) : LeanStandardCase :=
  { decl_name   := name,
    v_witness   := { decl_name         := name,
                     kernel_elaborated  := true,
                     kernel_cert        := rfl },
    e_witness   := { documented_failures := ["sorryAx"],
                     e_adequate          := true,
                     adequate_cert       := rfl },
    s_clearance := { deposit_level  := .allows_sorry,
                     required_level := .axiom_free,
                     threshold_met  := False,
                     clears         := false,
                     clears_sound   := ⟨Bool.noConfusion, False.elim⟩ },
    clearance_fails_cert := False.elim }

/-- Same proof, development-mode consumer: `allows_sorry` clears `allows_sorry`.
    `threshold_met = True` (trivially met); `clears_sound` bridges them. -/
def canonical_sorry_dev_clearance : LeanStandardClearance :=
  { deposit_level  := .allows_sorry,
    required_level := .allows_sorry,
    threshold_met  := True,
    clears         := true,
    clears_sound   := ⟨fun _ => trivial, fun _ => rfl⟩ }

/-- Relational S-failure at the kernel level.

    Same declaration. Same V (kernel_elaborated). Same E (sorryAx documented).
    Same axiom footprint.  Publication consumer: `¬threshold_met` (S-failure).
    Development consumer: `threshold_met = True` (clears).  What differs is the
    consuming agent's required threshold — outside EpArch's scope. -/
theorem lean_axiom_failure_is_relational (name : String) :
    lean_S_fails (canonical_sorry_publication_case name) = true ∧
    canonical_sorry_dev_clearance.threshold_met := by
  constructor
  · exact lean_standard_case_is_S_failure _
  · exact trivial

/-- Absolute (void) S at the kernel level: `sorry ⊢ False`.

    E already documents `sorryTainted` as revocable in `LeanGroundedRevocation`
    (`witness_is_invalid`, `can_revoke`).  When S is solely "sorry closed it",
    both structural conditions (`e_documents_sorry` and `s_is_sorry_only`) are
    present in the fields — `lean_S_is_void` is witnessed structurally.

    This is the known-liar-cook case instantiated in the kernel:
    - V: the kernel genuinely elaborated this (V is accurate).
    - E: `LeanGroundedRevocation` documents sorry as a known failure mode.
    - S: "sorry closed the goal" — the structural pattern is recorded.

    EpArch records the field pattern. What consuming agents do with
    `lean_S_is_void` is outside the model's scope. -/
structure LeanVacuousStandard where
  decl_name              : String
  /-- E documents sorry as a known failure mode (cf. LeanGroundedRevocation.witness_is_invalid). -/
  e_documents_sorry      : Bool
  e_documents_sorry_cert : e_documents_sorry = true
  /-- S is solely "it elaborated via sorry" — no independent verification. -/
  s_is_sorry_only        : Bool
  s_is_sorry_only_cert   : s_is_sorry_only = true

def lean_S_is_void (lvs : LeanVacuousStandard) : Prop :=
  lvs.s_is_sorry_only = true ∧ lvs.e_documents_sorry = true

/-- Void S is witnessed by the two structural fields — no case analysis. -/
theorem lean_vacuous_standard_is_void (lvs : LeanVacuousStandard) :
    lean_S_is_void lvs :=
  ⟨lvs.s_is_sorry_only_cert, lvs.e_documents_sorry_cert⟩

/-- Canonical void instance: a `sorry`-closed proof of `False`.
    `e_documents_sorry = true` is grounded in `LeanGroundedRevocation`:
    the same `.sorryTainted` constructor that makes `witness_is_invalid` fire
    is what S = "sorry closed it" refers to. -/
def canonical_sorry_false_case : LeanVacuousStandard :=
  { decl_name              := "sorry_closes_False",
    e_documents_sorry      := true,
    e_documents_sorry_cert := rfl,
    s_is_sorry_only        := true,
    s_is_sorry_only_cert   := rfl }

/-- Both kinds of S-failure, at the kernel level.

    Relational: same sorry-containing proof; one consuming agent's clearance
    fails, another's passes. S is a property of the claim; the threshold
    is a property of the consuming agent — outside EpArch's scope.

    Absolute/void: E + V together structurally witness `lean_S_is_void`.
    EpArch records both conditions in the fields; agent acceptance decisions
    are not modeled here. -/
theorem lean_S_failure_taxonomy (name : String) :
    lean_S_fails (canonical_sorry_publication_case name) = true ∧
    canonical_sorry_dev_clearance.threshold_met ∧
    lean_S_is_void canonical_sorry_false_case := by
  exact ⟨lean_standard_case_is_S_failure _, trivial,
        lean_vacuous_standard_is_void _⟩

end EpArch.LeanKernelModel

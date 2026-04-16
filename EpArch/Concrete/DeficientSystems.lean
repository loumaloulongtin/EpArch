/-
EpArch.Concrete.DeficientSystems — Deficient System Witnesses and Bridge Impossibility

Concrete systems each lacking one feature, with scenario-data structures,
structural model firing theorems, and bridge-impossibility theorems.

Part of the EpArch.Concrete module family.
-/

import EpArch.Concrete.WorkingSystem
import EpArch.Scenarios

namespace EpArch.ConcreteInstance

open EpArch

/-! ## Deficient Systems: Structural Models Fire on Real Data

The concrete model above uses `Or.inl` everywhere — it has all features,
so the abstract impossibility models in `ForcingEmbedding` are not exercised.

Below, we construct **deficient** working systems: systems that lack a feature
but carry rich scenario predicates (`RepresentsDisagreement`,
`RepresentsPrivateCoordination`).  The structural models
`flat_scope_impossible` and `private_storage_no_sharing` fire on these
systems' scenario data — producing genuine impossibility results.

The forcing argument then becomes:

> "A system that handles constraint X and carries this scenario data
>  CANNOT lack feature Y, because the structural model catches the
>  contradiction."

The scenario data is fully constructible; the impossibility is genuine;
the abstract model does real work. -/


/-! ### Deficient System 1: No Bubble Separation -/

/-- A claim type for the disagreement scenario. -/
inductive DisagreementClaim where
  | witness   -- the claim where agents disagree
  | neutral   -- a claim both agents accept

/-- System spec with all features except bubbles. -/
def noBubblesSpec : SystemSpec where
  has_bubble_separation := false
  has_trust_bridges := true
  preserves_headers := true
  has_revocation := true
  has_shared_ledger := true
  has_redeemability := true

/-- Working system whose spec lacks bubble separation (`has_bubble_separation = false`).
    All evidence fields are `none`, so no `handles_*` predicate holds.
    Used solely as a "no-bubbles spec" witness for `no_bubbles_lacks_bubbles`. -/
def NoBubblesSystem : WorkingSystem where
  spec             := noBubblesSpec
  bubbles_ev       := none
  bridges_ev       := none
  headers_ev       := none
  revocation_ev    := none
  bank_ev          := none
  redeemability_ev := none

/-- The no-bubbles system genuinely lacks bubbles. -/
theorem no_bubbles_lacks_bubbles : ¬HasBubbles NoBubblesSystem := by
  unfold HasBubbles NoBubblesSystem noBubblesSpec; decide

/-- Agent 1's acceptance: accepts everything. -/
def agent1_accept : DisagreementClaim → Prop
  | _ => True

/-- Agent 2's acceptance: accepts `neutral`, rejects `witness`. -/
def agent2_accept : DisagreementClaim → Prop
  | .neutral => True
  | .witness => False

/-- The disagreement scenario: two agents with conflicting acceptance
    criteria on the `witness` claim.  This is constructible — genuine
    scenario data, not hypothetical. -/
def noBubblesDisagreement : RepresentsDisagreement NoBubblesSystem where
  Claim := DisagreementClaim
  accept₁ := agent1_accept
  accept₂ := agent2_accept
  witness := .witness
  agent1_accepts := True.intro
  agent2_rejects := fun h => nomatch h

/-- **Structural model fires: no flat scope exists for this system's data.**

    The `AgentDisagreement` extracted from `noBubblesDisagreement` carries
    genuine disagreement (agent 1 accepts `.witness`, agent 2 rejects it).
    `flat_scope_impossible` proves: no single acceptance function can
    faithfully represent both agents.

    The scenario data is constructible and the result is a genuine negation. -/
theorem noBubbles_no_flat_scope :
    ¬∃ f : DisagreementClaim → Prop,
      (∀ c, f c ↔ agent1_accept c) ∧ (∀ c, f c ↔ agent2_accept c) :=
  flat_scope_impossible noBubblesDisagreement.toDisagreement

/-- The structural model's impossibility applied to a specific function.
    If someone claims `f` faithfully represents both agents,
    `flat_scope_impossible` derives False.  The structural model
    catches the contradiction between
    `f witness ↔ True` and `f witness ↔ False`. -/
theorem noBubbles_flat_scope_fires
    (f : DisagreementClaim → Prop)
    (h₁ : ∀ c, f c ↔ agent1_accept c)
    (h₂ : ∀ c, f c ↔ agent2_accept c) :
    False :=
  noBubbles_no_flat_scope ⟨f, h₁, h₂⟩

/-- **Bridge impossibility for the no-bubbles system.**

    If the system commits to a flat acceptance function faithful to both
    agents, `bridge_bubbles_impossible` derives the contradiction — and
    `no_bubbles_lacks_bubbles` supplies the refutation. -/
theorem noBubbles_bridge_impossible
    (f : DisagreementClaim → Prop)
    (hf₁ : ∀ c, f c ↔ agent1_accept c)
    (hf₂ : ∀ c, f c ↔ agent2_accept c) :
    False :=
  bridge_bubbles_impossible NoBubblesSystem
    ⟨noBubblesDisagreement.toDisagreement, f, hf₁, hf₂⟩


/-! ### Deficient System 2: No Shared Ledger (Bank) -/

/-- An agent type for the coordination scenario. -/
inductive CoordinationAgent where
  | alice
  | bob
  deriving DecidableEq

/-- A deposit type. -/
inductive CoordinationDeposit where
  | the_deposit

/-- System spec with all features except shared ledger. -/
def noBankSpec : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := true
  preserves_headers := true
  has_revocation := true
  has_shared_ledger := false
  has_redeemability := true

/-- Working system whose spec lacks a shared ledger (`has_shared_ledger = false`).
    All evidence fields are `none`, so no `handles_*` predicate holds.
    Used solely as a "no-bank spec" witness for `no_bank_lacks_bank`. -/
def NoBankSystem : WorkingSystem where
  spec             := noBankSpec
  bubbles_ev       := none
  bridges_ev       := none
  headers_ev       := none
  revocation_ev    := none
  bank_ev          := none
  redeemability_ev := none

/-- The no-bank system genuinely lacks a bank. -/
theorem no_bank_lacks_bank : ¬HasBank NoBankSystem := by
  unfold HasBank NoBankSystem noBankSpec; decide

/-- Private access: alice can access the deposit, bob cannot.
    This models storage that is genuinely isolated per-agent. -/
def private_access : CoordinationAgent → CoordinationDeposit → Prop
  | .alice, _ => True
  | .bob, _ => False

/-- The private coordination scenario for the no-bank system.

    Without a shared ledger, storage is isolated: alice's deposits
    are inaccessible to bob.  The `isolation_without_bank` field
    captures this directly from the access relation. -/
def noBankCoordination : RepresentsPrivateCoordination NoBankSystem where
  Agent := CoordinationAgent
  Deposit := CoordinationDeposit
  has_access := private_access
  a₁ := .alice
  a₂ := .bob
  distinct := by decide
  isolation_without_bank := fun _ _ _ h_bob => h_bob

/-- **Structural model fires: no shared deposit exists for this system's data.**

    The `PrivateOnlyStorage` extracted from `noBankCoordination` carries
    genuine isolation (alice accesses, bob can't).  `private_storage_no_sharing`
    proves: no deposit can be simultaneously accessed by both agents.

    The structural model fires on this system's scenario data and produces
    a genuine impossibility result. -/
theorem noBank_no_shared_deposit :
    ¬∃ d : CoordinationDeposit,
      private_access .alice d ∧ private_access .bob d :=
  private_storage_no_sharing (noBankCoordination.toPrivateStorage no_bank_lacks_bank)

/-- The structural model's impossibility applied to a specific deposit.
    If someone claims agents share deposit `d`, `private_storage_no_sharing`
    derives False. -/
theorem noBank_shared_deposit_fires
    (d : CoordinationDeposit)
    (h₁ : private_access .alice d)
    (h₂ : private_access .bob d) :
    False :=
  noBank_no_shared_deposit ⟨d, h₁, h₂⟩

/-- **Bridge impossibility for the no-bank system.**

    If a shared deposit `d` is accessible to both alice and bob,
    `bridge_bank_impossible` derives the contradiction — and `no_bank_lacks_bank`
    supplies the refutation. -/
theorem noBank_bridge_impossible
    (d : CoordinationDeposit)
    (h₁ : private_access .alice d)
    (h₂ : private_access .bob d) :
    False :=
  bridge_bank_impossible NoBankSystem
    ⟨noBankCoordination.toPrivateStorage no_bank_lacks_bank, d, h₁, h₂⟩


/-! ### Deficient System 3: No Revocation (Adversarial → Revocation)

A system with all features except `has_revocation`.  It carries
`RepresentsMonotonicLifecycle`: a concrete 2-state lifecycle where
the accepted state is absorbing. -/

/-- A simple 2-state lifecycle: pending or accepted. -/
inductive LifecycleState where
  | pending
  | accepted

/-- System spec with all features except revocation. -/
def noRevocationSpec : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := true
  preserves_headers := true
  has_revocation := false
  has_shared_ledger := true
  has_redeemability := true

/-- Working system whose spec lacks revocation (`has_revocation = false`).
    All evidence fields are `none`, so no `handles_*` predicate holds.
    Used solely as a "no-revocation spec" witness for `no_revocation_lacks_revocation`. -/
def NoRevocationSystem : WorkingSystem where
  spec             := noRevocationSpec
  bubbles_ev       := none
  bridges_ev       := none
  headers_ev       := none
  revocation_ev    := none
  bank_ev          := none
  redeemability_ev := none

/-- The no-revocation system genuinely lacks revocation. -/
theorem no_revocation_lacks_revocation : ¬HasRevocation NoRevocationSystem := by
  unfold HasRevocation NoRevocationSystem noRevocationSpec; decide

/-- The lifecycle transition: accepted stays accepted (absorbing),
    pending moves to accepted.  Without revocation, there is no
    transition out of the accepted state. -/
def lifecycle_step : LifecycleState → LifecycleState
  | .pending => .accepted
  | .accepted => .accepted

/-- The monotonic lifecycle scenario for the no-revocation system.

    The transition `lifecycle_step` makes `accepted` absorbing: once a
    deposit is accepted, no number of steps can change that.  The
    `absorbing_without_revocation` field captures this with `rfl`. -/
def noRevocationLifecycle : RepresentsMonotonicLifecycle NoRevocationSystem where
  State := LifecycleState
  accepted := .accepted
  step := lifecycle_step
  absorbing_without_revocation := fun _ => rfl

/-- **Structural model fires: accepted state cannot be escaped.**

    `monotonic_no_exit` fires by INDUCTION on step count `n`:
    - Base: `iter step 0 accepted = accepted` by definition.
    - Step: `step (iter step n accepted) = step accepted = accepted`
      by the absorbing property.

    Uses genuine mathematical
    induction, not just hypothesis contradiction.  The lifecycle data
    is fully constructible. -/
theorem noRevocation_accepted_permanent (n : Nat) :
    iter lifecycle_step n LifecycleState.accepted = LifecycleState.accepted :=
  monotonic_no_exit (noRevocationLifecycle.toLifecycle no_revocation_lacks_revocation) n

/-- Even after 100 steps, an accepted deposit is still accepted.
    A concrete demonstration of the inductive result. -/
theorem noRevocation_accepted_after_100 :
    iter lifecycle_step 100 LifecycleState.accepted = LifecycleState.accepted :=
  noRevocation_accepted_permanent 100

/-- An adversarial deposit that reaches `accepted` through `pending`
    also stays accepted permanently.  The bad deposit passes acceptance
    and can never be removed. -/
theorem noRevocation_bad_deposit_stuck (n : Nat) :
    iter lifecycle_step n (lifecycle_step LifecycleState.pending)
      = LifecycleState.accepted :=
  noRevocation_accepted_permanent n

/-- **Bridge impossibility for the no-revocation system.**

    If some `n` steps escape the accepted state, `bridge_revocation_impossible`
    derives the contradiction via induction — and `no_revocation_lacks_revocation`
    supplies the refutation.  The inductive force of `monotonic_no_exit` is
    fully preserved in the `bridge_revocation_impossible` theorem in EpArch.Minimality. -/
theorem noRevocation_bridge_impossible
    (n : Nat)
    (h : iter lifecycle_step n LifecycleState.accepted ≠ LifecycleState.accepted) :
    False :=
  bridge_revocation_impossible NoRevocationSystem
    ⟨noRevocationLifecycle.toLifecycle no_revocation_lacks_revocation, n, h⟩


/-! ### Deficient System 4: No Headers (Export → Headers)

A system with all features except `preserves_headers`.  It carries
`RepresentsDiscriminatingImport`: two concrete claims (good and bad)
that must be distinguished on import.  Without headers, the import
function is uniform — and `no_sound_complete_uniform_import` fires
via `Bool.noConfusion` to prove no sound-and-complete import exists. -/

/-- Two claims that must be distinguished on cross-scope import. -/
inductive ImportClaim where
  | good_data    -- a legitimate deposit to accept
  | bad_data     -- a problematic deposit to reject
  deriving DecidableEq

/-- System spec with all features except headers. -/
def noHeadersSpec : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := true
  preserves_headers := false
  has_revocation := true
  has_shared_ledger := true
  has_redeemability := true

/-- Working system whose spec lacks header preservation (`preserves_headers = false`).
    All evidence fields are `none`, so no `handles_*` predicate holds.
    Used solely as a "no-headers spec" witness for `no_headers_lacks_headers`. -/
def NoHeadersSystem : WorkingSystem where
  spec             := noHeadersSpec
  bubbles_ev       := none
  bridges_ev       := none
  headers_ev       := none
  revocation_ev    := none
  bank_ev          := none
  redeemability_ev := none

/-- The no-headers system genuinely lacks headers. -/
theorem no_headers_lacks_headers : ¬HasHeaders NoHeadersSystem := by
  unfold HasHeaders NoHeadersSystem noHeadersSpec; decide

/-- The discriminating import scenario for the no-headers system.

    Without headers, there is no metadata to distinguish good from bad
    imports.  The bridge hypothesis (provided as a theorem argument)
    says that without metadata, import functions
    are uniform: `f x = f y` for all x y. -/
def noHeadersImport : RepresentsDiscriminatingImport NoHeadersSystem where
  Claim := ImportClaim
  good := .good_data
  bad := .bad_data
  good_ne_bad := by decide

/-- **Structural model fires: no sound-and-complete uniform import exists.**

    Any import function `f : ImportClaim → Bool` that is uniform
    produces `f good_data = f bad_data`.  But sound-and-complete import
    requires `f bad_data = false` AND `f good_data = true`.
    `Bool.noConfusion` catches the contradiction: `true = false` is absurd.

    The uniformity hypothesis is the bridge predicate: it says that
    without headers, the system cannot distinguish good from bad claims,
    so any import decision function is forced to treat them identically.

    The structural model fires via `no_sound_complete_uniform_import`
    on this system's concrete claim data. -/
theorem noHeaders_no_sound_complete_import
    (f : ImportClaim → Bool)
    (h_uniform : ∀ x y : ImportClaim, f x = f y)
    (h_sound : f .bad_data = false)
    (h_complete : f .good_data = true) :
    False :=
  discriminating_import_without_headers_embeds
    NoHeadersSystem noHeadersImport no_headers_lacks_headers f
    h_uniform h_sound h_complete

/-- The uniformity result instantiated directly: any UNIFORM import function
    on this system's claims produces identical results for good and bad. -/
theorem noHeaders_uniform_import
    (f : ImportClaim → Bool)
    (h_uniform : ∀ x y : ImportClaim, f x = f y) :
    f ImportClaim.good_data = f ImportClaim.bad_data :=
  uniform_import_nondiscriminating noHeadersImport.toImport f h_uniform

/-- **Bridge impossibility for the no-headers system.**

    If a uniform import function is both sound and complete,
    `bridge_headers_impossible` derives the contradiction via `Bool.noConfusion`
    — and `no_headers_lacks_headers` supplies the refutation. -/
theorem noHeaders_bridge_impossible
    (f : ImportClaim → Bool)
    (h_uniform : ∀ x y : ImportClaim, f x = f y)
    (h_sound : f .bad_data = false)
    (h_complete : f .good_data = true) :
    False :=
  bridge_headers_impossible NoHeadersSystem
    ⟨noHeadersImport.toImport, f, h_uniform, h_sound, h_complete⟩


/-! ### Deficient System 5: No Trust Bridges (Bounded Audit → Trust)

A system with all features except `has_trust_bridges`.  It carries
`RepresentsBoundedVerification`: a claim universe with a hard claim
whose verification cost exceeds the budget.  Without trust bridges,
`verification_only_import_incomplete` fires via Nat arithmetic. -/

/-- System spec with all features except trust bridges. -/
def noTrustSpec : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := false
  preserves_headers := true
  has_revocation := true
  has_shared_ledger := true
  has_redeemability := true

/-- Working system whose spec lacks trust bridges (`has_trust_bridges = false`).
    All evidence fields are `none`, so no `handles_*` predicate holds.
    Used solely as a "no-trust spec" witness for `no_trust_lacks_trust`. -/
def NoTrustSystem : WorkingSystem where
  spec             := noTrustSpec
  bubbles_ev       := none
  bridges_ev       := none
  headers_ev       := none
  revocation_ev    := none
  bank_ev          := none
  redeemability_ev := none

/-- The no-trust system genuinely lacks trust bridges. -/
theorem no_trust_lacks_trust : ¬HasTrustBridges NoTrustSystem := by
  unfold HasTrustBridges NoTrustSystem noTrustSpec; decide

/-- Concrete claim type with a hard claim. -/
inductive AuditClaim where
  | easy_claim   -- verification cost 5, within budget
  | hard_claim   -- verification cost 200, exceeds budget of 100

/-- Verification cost: easy costs 5, hard costs 200. -/
def audit_verify_cost : AuditClaim → Nat
  | .easy_claim => 5
  | .hard_claim => 200

/-- The bounded verification scenario for the no-trust system.

    The verification budget is 100.  `hard_claim` costs 200 to verify,
    genuinely exceeding the budget.  The `exceeds_budget` proof
    reduces to `200 > 100` which holds by `Nat.lt.step` chain. -/
def noTrustVerification : RepresentsBoundedVerification NoTrustSystem where
  Claim := AuditClaim
  verify_cost := audit_verify_cost
  budget := 100
  hard_claim := .hard_claim
  exceeds_budget := by decide

/-- **Structural model fires: not all claims fit within the budget.**

    `verification_only_import_incomplete` fires via Nat arithmetic:
    the hard claim costs 200, the budget is 100, and
    `200 > 100` makes `verify_cost hard_claim ≤ budget` absurd.

    The structural model proves that verification-only import CANNOT
    handle this system's claim universe — a trust-based mechanism
    (trust bridges) is forced. -/
theorem noTrust_verification_incomplete :
    ¬∀ c : AuditClaim, audit_verify_cost c ≤ 100 :=
  verification_only_import_incomplete noTrustVerification.toVerification

/-- The hard claim specifically cannot be verified within budget. -/
theorem noTrust_hard_claim_exceeds :
    ¬(audit_verify_cost AuditClaim.hard_claim ≤ 100) := by decide

/-- **Bridge impossibility for the no-trust system.**

    If all verification costs fit within budget, `bridge_trust_impossible`
    derives the contradiction via Nat arithmetic — and `no_trust_lacks_trust`
    supplies the refutation. -/
theorem noTrust_bridge_impossible
    (h : ∀ c : AuditClaim, audit_verify_cost c ≤ 100) :
    False :=
  bridge_trust_impossible NoTrustSystem
    ⟨noTrustVerification.toVerification, h⟩


/-! ### Deficient System 6: No Redeemability (Truth Pressure → Redeemability)

A system with all features except `has_redeemability`.  It carries
`RepresentsClosedEndorsement`: a claim that is both endorsed and
externally falsifiable, but closure (without redeemability) prevents
this combination.  `closed_system_unfalsifiable` fires to catch
the contradiction. -/

/-- A claim type for the truth pressure scenario. -/
inductive TruthClaim where
  | the_claim   -- an endorsed claim that should be falsifiable

/-- System spec with all features except redeemability. -/
def noRedeemabilitySpec : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := true
  preserves_headers := true
  has_revocation := true
  has_shared_ledger := true
  has_redeemability := false

/-- Working system whose spec lacks redeemability (`has_redeemability = false`).
    All evidence fields are `none`, so no `handles_*` predicate holds.
    Used solely as a "no-redeemability spec" witness for `no_redeemability_lacks_redeemability`. -/
def NoRedeemabilitySystem : WorkingSystem where
  spec             := noRedeemabilitySpec
  bubbles_ev       := none
  bridges_ev       := none
  headers_ev       := none
  revocation_ev    := none
  bank_ev          := none
  redeemability_ev := none

/-- The no-redeemability system genuinely lacks redeemability. -/
theorem no_redeemability_lacks_redeemability : ¬HasRedeemability NoRedeemabilitySystem := by
  unfold HasRedeemability NoRedeemabilitySystem noRedeemabilitySpec; decide

/-- Endorsement: the_claim is endorsed (passed consensus). -/
def truth_endorsed : TruthClaim → Prop
  | .the_claim => True

/-- Falsifiability: without redeemability, nothing is externally falsifiable.
    The closed system has no external constraint surface to test against.
    This IS the bridge predicate: "closed" means "no external falsification." -/
def truth_falsifiable_closed : TruthClaim → Prop
  | .the_claim => False

/-- The closed endorsement scenario for the no-redeemability system.

    Without redeemability (no external constraint surface), endorsed
    claims cannot be externally falsified.  The closure hypothesis holds
    trivially because `truth_falsifiable_closed` maps everything to False.

    The structural model then fires: `closed_system_unfalsifiable` proves
    that no claim can be both endorsed AND falsifiable under closure.
    Truth pressure (which REQUIRES such a claim) is therefore impossible
    in this system.  Redeemability is forced to make endorsed claims
    falsifiable. -/
def noRedeemabilityClosed : RepresentsClosedEndorsement NoRedeemabilitySystem where
  Claim := TruthClaim
  endorsed := truth_endorsed
  externally_falsifiable := truth_falsifiable_closed
  closed_without_redeemability := fun _ _ _ h_fals => h_fals

/-- **Structural model fires: no endorsed-and-falsifiable claim exists.**

    `closed_system_unfalsifiable` fires to prove that under closure,
    no claim can be both endorsed and externally falsifiable.

    For this system, `truth_falsifiable_closed` maps everything to False,
    so the result is straightforward — but that IS the point: the closure
    predicate captures that a system without redeemability has no external
    falsification mechanism.  The structural model is what PROVES that
    truth pressure (∃ endorsed ∧ falsifiable) is impossible under this
    condition. -/
theorem noRedeemability_no_truth_pressure :
    ¬∃ c : TruthClaim, truth_endorsed c ∧ truth_falsifiable_closed c :=
  closed_system_unfalsifiable (noRedeemabilityClosed.toClosed
    no_redeemability_lacks_redeemability)

/-- **Bridge impossibility for the no-redeemability system.**

    If a claim is both endorsed and externally falsifiable under closure,
    `bridge_redeemability_impossible` derives the contradiction — and
    `no_redeemability_lacks_redeemability` supplies the refutation. -/
theorem noRedeemability_bridge_impossible
    (c : TruthClaim)
    (h_end : truth_endorsed c)
    (h_fals : truth_falsifiable_closed c) :
    False :=
  bridge_redeemability_impossible NoRedeemabilitySystem
    ⟨noRedeemabilityClosed.toClosed no_redeemability_lacks_redeemability, c, h_end, h_fals⟩


/-! ## Concrete Instance Summary

The concrete model demonstrates:
1. SystemSpec is satisfiable (concreteSystemSpec exists)
2. WorkingSystem can be instantiated (ConcreteWorkingSystem)
3. All Has* predicates hold (trivially, by construction)
4. SatisfiesAllProperties holds (all seven operational properties)
5. Convergence theorem applies via ForcingEmbedding (all Or.inl)

The deficient systems demonstrate six bridge-impossibility theorems:
6. Scope: `noBubbles_bridge_impossible` — flat scope bridge hypothesis
   → `bridge_bubbles_impossible` → contradiction.
   Structural model: `flat_scope_impossible`.
7. Bank: `noBank_bridge_impossible` — shared deposit bridge hypothesis
   → `bridge_bank_impossible` → contradiction.
   Structural model: `private_storage_no_sharing`.
8. Revocation: `noRevocation_bridge_impossible` — escape bridge hypothesis
   → `bridge_revocation_impossible` (induction) → contradiction.
   Structural model: `monotonic_no_exit`.
9. Headers: `noHeaders_bridge_impossible` — uniform+sound+complete import predicate
   → `bridge_headers_impossible` (Bool.noConfusion) → contradiction.
   Structural model: `no_sound_complete_uniform_import`.
10. Trust: `noTrust_bridge_impossible` — within-budget bridge hypothesis
    → `bridge_trust_impossible` (Nat arithmetic) → contradiction.
    Structural model: `verification_only_import_incomplete`.
11. Redeemability: `noRedeemability_bridge_impossible` — endorsed+falsifiable predicate
    → `bridge_redeemability_impossible` → contradiction.
    Structural model: `closed_system_unfalsifiable`.

**Separation of concerns:**
The concrete system uses ForcingEmbedding → StructurallyForced → convergence_structural.
Deficient systems apply `bridge_*_impossible` directly, without the convergence pipeline.

The commitments are consistent: they do not rule out all possible systems.
The Bank architecture is realizable, and the structural models catch genuine
contradictions in systems that lack required features. -/



end EpArch.ConcreteInstance

/-
EpArch.Meta.Reconfiguration — Safe Reconfiguration Theorems

Proves that capability additions preserve PartialWellFormed certificates;
the addX functions are bank-inert by type, since they transform WorkingSystem
configuration rather than SystemState. Also proves that the Bank cannot
self-heal without an explicit agent action.

Key exports:
- WorkingSystem.addBubbles / addTrustBridges / addHeaders / addRevocation /
  addBank / addRedeemability / addAuthorization / addStorageManagement — additive capability defs
- pwf_add_bubbles .. pwf_add_storage_management — PartialWellFormed extension theorems
- StatusImproves — deposit status improvement order
- no_self_healing_bank — every status improvement is driven by an explicit action
-/

import EpArch.Minimality
import EpArch.Semantics.StepSemantics

/-! ========================================================================
    PART B — Capability Addition: WorkingSystem.addX × 8
    Defined in namespace EpArch so dot notation W.addX works.
    ======================================================================== -/

/-! ## Additive WorkingSystem Extensions

Each WorkingSystem.addX sets the corresponding evidence field and spec flag,
leaving all other fields unchanged. Bank-inertness is type-level: no addX
function has type WorkingSystem -> SystemState -> SystemState. -/

namespace EpArch

/-- Extend a WorkingSystem with scope-separation evidence.
    Sets bubbles_ev and spec.has_bubble_separation; all other fields unchanged. -/
def WorkingSystem.addBubbles (W : WorkingSystem)
    (ev : GroundedBubblesStrict) : WorkingSystem :=
  { W with bubbles_ev := some ev,
           spec := { W.spec with has_bubble_separation := true } }

/-- Extend a WorkingSystem with trust-bridge evidence.
    Sets bridges_ev and spec.has_trust_bridges; all other fields unchanged. -/
def WorkingSystem.addTrustBridges (W : WorkingSystem)
    (ev : GroundedTrustBridgesStrict) : WorkingSystem :=
  { W with bridges_ev := some ev,
           spec := { W.spec with has_trust_bridges := true } }

/-- Extend a WorkingSystem with header-preservation evidence.
    Sets headers_ev and spec.preserves_headers; all other fields unchanged. -/
def WorkingSystem.addHeaders (W : WorkingSystem)
    (ev : GroundedHeadersStrict) : WorkingSystem :=
  { W with headers_ev := some ev,
           spec := { W.spec with preserves_headers := true } }

/-- Extend a WorkingSystem with revocation evidence.
    Sets revocation_ev and spec.has_revocation; all other fields unchanged. -/
def WorkingSystem.addRevocation (W : WorkingSystem)
    (ev : GroundedRevocationStrict) : WorkingSystem :=
  { W with revocation_ev := some ev,
           spec := { W.spec with has_revocation := true } }

/-- Extend a WorkingSystem with shared-ledger evidence.
    Sets bank_ev and spec.has_shared_ledger; all other fields unchanged. -/
def WorkingSystem.addBank (W : WorkingSystem)
    (ev : GroundedBankStrict) : WorkingSystem :=
  { W with bank_ev := some ev,
           spec := { W.spec with has_shared_ledger := true } }

/-- Extend a WorkingSystem with redeemability evidence.
    Sets redeemability_ev and spec.has_redeemability; all other fields unchanged. -/
def WorkingSystem.addRedeemability (W : WorkingSystem)
    (ev : GroundedRedeemabilityStrict) : WorkingSystem :=
  { W with redeemability_ev := some ev,
           spec := { W.spec with has_redeemability := true } }

/-- Extend a WorkingSystem with authorization evidence.
    Sets authorization_ev and spec.has_granular_acl; all other fields unchanged. -/
def WorkingSystem.addAuthorization (W : WorkingSystem)
    (ev : GroundedAuthorizationStrict) : WorkingSystem :=
  { W with authorization_ev := some ev,
           spec := { W.spec with has_granular_acl := true } }

/-- Extend a WorkingSystem with storage-management evidence.
    Sets storage_ev and spec.has_storage_management; all other fields unchanged. -/
def WorkingSystem.addStorageManagement (W : WorkingSystem)
    (ev : GroundedStorageStrict) : WorkingSystem :=
  { W with storage_ev := some ev,
           spec := { W.spec with has_storage_management := true } }

end EpArch

namespace EpArch.Meta.Reconfiguration

open EpArch
open EpArch.StepSemantics

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type _}

/-! ## PartialWellFormed Extension Theorems

Each `pwf_add_X` theorem extends an existing `PartialWellFormed W S` certificate to
cover one additional constraint dimension, producing `PartialWellFormed (W.addX ev) { S with X_flag := true }`.

Uniform proof pattern across all eight theorems:

- **Activated dimension** (`X_flag`): the goal `handles_X (W.addX ev) ↔ HasX (W.addX ev)`
  reduces to `True ↔ True` after unfolding. `addX` sets `X_ev := some ev` (so `isSome = true`)
  and `spec.X_flag := true`; both sides become `true = true`. Closed by `simp [Option.isSome]`.

- **Seven preserved dimensions** (`Y_flag ≠ X_flag`): `addX` does not touch `Y_ev` or
  `spec.Y_flag`. After `simp [handles_Y, HasY, WorkingSystem.addX]` reduces via struct-update
  transparency to `handles_Y W ↔ HasY W`, `exact h.wf_Y hY` supplies the biconditional
  already established in `h`. -/

/-- Adding bubbles evidence activates the `distributed` biconditional.

    **Theorem shape:** `PartialWellFormed (W.addBubbles ev) { S with distributed := true }`.
    **Proof strategy:** see section banner above. -/
theorem pwf_add_bubbles (W : WorkingSystem) (S : ConstraintSubset)
    (h : PartialWellFormed W S) (ev : GroundedBubblesStrict) :
    PartialWellFormed (W.addBubbles ev) { S with distributed := true } :=
  { wf_distributed    := fun _ => by
        simp [handles_distributed_agents, HasBubbles, WorkingSystem.addBubbles, Option.isSome]
    wf_bounded_audit  := fun hb => by
        simp [handles_bounded_audit, HasTrustBridges, WorkingSystem.addBubbles]
        exact h.wf_bounded_audit hb
    wf_export         := fun he => by
        simp [handles_export, HasHeaders, WorkingSystem.addBubbles]
        exact h.wf_export he
    wf_adversarial    := fun ha => by
        simp [handles_adversarial, HasRevocation, WorkingSystem.addBubbles]
        exact h.wf_adversarial ha
    wf_coordination   := fun hc => by
        simp [handles_coordination, HasBank, WorkingSystem.addBubbles]
        exact h.wf_coordination hc
    wf_truth_pressure := fun ht => by
        simp [handles_truth_pressure, HasRedeemability, WorkingSystem.addBubbles]
        exact h.wf_truth_pressure ht
    wf_multi_agent    := fun hm => by
        simp [handles_multi_agent, HasGranularACL, WorkingSystem.addBubbles]
        exact h.wf_multi_agent hm
    wf_storage        := fun hs => by
        simp [handles_storage, HasStorageManagement, WorkingSystem.addBubbles]
        exact h.wf_storage hs }

/-- Adding trust-bridge evidence activates the `bounded_audit` biconditional.

    **Theorem shape:** `PartialWellFormed (W.addTrustBridges ev) { S with bounded_audit := true }`.
    **Proof strategy:** see section banner above. -/
theorem pwf_add_trust_bridges (W : WorkingSystem) (S : ConstraintSubset)
    (h : PartialWellFormed W S) (ev : GroundedTrustBridgesStrict) :
    PartialWellFormed (W.addTrustBridges ev) { S with bounded_audit := true } :=
  { wf_distributed    := fun hd => by
        simp [handles_distributed_agents, HasBubbles, WorkingSystem.addTrustBridges]
        exact h.wf_distributed hd
    wf_bounded_audit  := fun _ => by
        simp [handles_bounded_audit, HasTrustBridges, WorkingSystem.addTrustBridges, Option.isSome]
    wf_export         := fun he => by
        simp [handles_export, HasHeaders, WorkingSystem.addTrustBridges]
        exact h.wf_export he
    wf_adversarial    := fun ha => by
        simp [handles_adversarial, HasRevocation, WorkingSystem.addTrustBridges]
        exact h.wf_adversarial ha
    wf_coordination   := fun hc => by
        simp [handles_coordination, HasBank, WorkingSystem.addTrustBridges]
        exact h.wf_coordination hc
    wf_truth_pressure := fun ht => by
        simp [handles_truth_pressure, HasRedeemability, WorkingSystem.addTrustBridges]
        exact h.wf_truth_pressure ht
    wf_multi_agent    := fun hm => by
        simp [handles_multi_agent, HasGranularACL, WorkingSystem.addTrustBridges]
        exact h.wf_multi_agent hm
    wf_storage        := fun hs => by
        simp [handles_storage, HasStorageManagement, WorkingSystem.addTrustBridges]
        exact h.wf_storage hs }

/-- Adding header evidence activates the `export_across` biconditional.

    **Theorem shape:** `PartialWellFormed (W.addHeaders ev) { S with export_across := true }`.
    **Proof strategy:** see section banner above. -/
theorem pwf_add_headers (W : WorkingSystem) (S : ConstraintSubset)
    (h : PartialWellFormed W S) (ev : GroundedHeadersStrict) :
    PartialWellFormed (W.addHeaders ev) { S with export_across := true } :=
  { wf_distributed    := fun hd => by
        simp [handles_distributed_agents, HasBubbles, WorkingSystem.addHeaders]
        exact h.wf_distributed hd
    wf_bounded_audit  := fun hb => by
        simp [handles_bounded_audit, HasTrustBridges, WorkingSystem.addHeaders]
        exact h.wf_bounded_audit hb
    wf_export         := fun _ => by
        simp [handles_export, HasHeaders, WorkingSystem.addHeaders, Option.isSome]
    wf_adversarial    := fun ha => by
        simp [handles_adversarial, HasRevocation, WorkingSystem.addHeaders]
        exact h.wf_adversarial ha
    wf_coordination   := fun hc => by
        simp [handles_coordination, HasBank, WorkingSystem.addHeaders]
        exact h.wf_coordination hc
    wf_truth_pressure := fun ht => by
        simp [handles_truth_pressure, HasRedeemability, WorkingSystem.addHeaders]
        exact h.wf_truth_pressure ht
    wf_multi_agent    := fun hm => by
        simp [handles_multi_agent, HasGranularACL, WorkingSystem.addHeaders]
        exact h.wf_multi_agent hm
    wf_storage        := fun hs => by
        simp [handles_storage, HasStorageManagement, WorkingSystem.addHeaders]
        exact h.wf_storage hs }

/-- Adding revocation evidence activates the `adversarial` biconditional.

    **Theorem shape:** `PartialWellFormed (W.addRevocation ev) { S with adversarial := true }`.
    **Proof strategy:** see section banner above. -/
theorem pwf_add_revocation (W : WorkingSystem) (S : ConstraintSubset)
    (h : PartialWellFormed W S) (ev : GroundedRevocationStrict) :
    PartialWellFormed (W.addRevocation ev) { S with adversarial := true } :=
  { wf_distributed    := fun hd => by
        simp [handles_distributed_agents, HasBubbles, WorkingSystem.addRevocation]
        exact h.wf_distributed hd
    wf_bounded_audit  := fun hb => by
        simp [handles_bounded_audit, HasTrustBridges, WorkingSystem.addRevocation]
        exact h.wf_bounded_audit hb
    wf_export         := fun he => by
        simp [handles_export, HasHeaders, WorkingSystem.addRevocation]
        exact h.wf_export he
    wf_adversarial    := fun _ => by
        simp [handles_adversarial, HasRevocation, WorkingSystem.addRevocation, Option.isSome]
    wf_coordination   := fun hc => by
        simp [handles_coordination, HasBank, WorkingSystem.addRevocation]
        exact h.wf_coordination hc
    wf_truth_pressure := fun ht => by
        simp [handles_truth_pressure, HasRedeemability, WorkingSystem.addRevocation]
        exact h.wf_truth_pressure ht
    wf_multi_agent    := fun hm => by
        simp [handles_multi_agent, HasGranularACL, WorkingSystem.addRevocation]
        exact h.wf_multi_agent hm
    wf_storage        := fun hs => by
        simp [handles_storage, HasStorageManagement, WorkingSystem.addRevocation]
        exact h.wf_storage hs }

/-- Adding bank evidence activates the `coordination` biconditional.

    **Theorem shape:** `PartialWellFormed (W.addBank ev) { S with coordination := true }`.
    **Proof strategy:** see section banner above. -/
theorem pwf_add_bank (W : WorkingSystem) (S : ConstraintSubset)
    (h : PartialWellFormed W S) (ev : GroundedBankStrict) :
    PartialWellFormed (W.addBank ev) { S with coordination := true } :=
  { wf_distributed    := fun hd => by
        simp [handles_distributed_agents, HasBubbles, WorkingSystem.addBank]
        exact h.wf_distributed hd
    wf_bounded_audit  := fun hb => by
        simp [handles_bounded_audit, HasTrustBridges, WorkingSystem.addBank]
        exact h.wf_bounded_audit hb
    wf_export         := fun he => by
        simp [handles_export, HasHeaders, WorkingSystem.addBank]
        exact h.wf_export he
    wf_adversarial    := fun ha => by
        simp [handles_adversarial, HasRevocation, WorkingSystem.addBank]
        exact h.wf_adversarial ha
    wf_coordination   := fun _ => by
        simp [handles_coordination, HasBank, WorkingSystem.addBank, Option.isSome]
    wf_truth_pressure := fun ht => by
        simp [handles_truth_pressure, HasRedeemability, WorkingSystem.addBank]
        exact h.wf_truth_pressure ht
    wf_multi_agent    := fun hm => by
        simp [handles_multi_agent, HasGranularACL, WorkingSystem.addBank]
        exact h.wf_multi_agent hm
    wf_storage        := fun hs => by
        simp [handles_storage, HasStorageManagement, WorkingSystem.addBank]
        exact h.wf_storage hs }

/-- Adding redeemability evidence activates the `truth_pressure` biconditional.

    **Theorem shape:** `PartialWellFormed (W.addRedeemability ev) { S with truth_pressure := true }`.
    **Proof strategy:** see section banner above. -/
theorem pwf_add_redeemability (W : WorkingSystem) (S : ConstraintSubset)
    (h : PartialWellFormed W S) (ev : GroundedRedeemabilityStrict) :
    PartialWellFormed (W.addRedeemability ev) { S with truth_pressure := true } :=
  { wf_distributed    := fun hd => by
        simp [handles_distributed_agents, HasBubbles, WorkingSystem.addRedeemability]
        exact h.wf_distributed hd
    wf_bounded_audit  := fun hb => by
        simp [handles_bounded_audit, HasTrustBridges, WorkingSystem.addRedeemability]
        exact h.wf_bounded_audit hb
    wf_export         := fun he => by
        simp [handles_export, HasHeaders, WorkingSystem.addRedeemability]
        exact h.wf_export he
    wf_adversarial    := fun ha => by
        simp [handles_adversarial, HasRevocation, WorkingSystem.addRedeemability]
        exact h.wf_adversarial ha
    wf_coordination   := fun hc => by
        simp [handles_coordination, HasBank, WorkingSystem.addRedeemability]
        exact h.wf_coordination hc
    wf_truth_pressure := fun _ => by
        simp [handles_truth_pressure, HasRedeemability, WorkingSystem.addRedeemability, Option.isSome]
    wf_multi_agent    := fun hm => by
        simp [handles_multi_agent, HasGranularACL, WorkingSystem.addRedeemability]
        exact h.wf_multi_agent hm
    wf_storage        := fun hs => by
        simp [handles_storage, HasStorageManagement, WorkingSystem.addRedeemability]
        exact h.wf_storage hs }

/-- Adding authorization evidence activates the `multi_agent` biconditional.

    **Theorem shape:** `PartialWellFormed (W.addAuthorization ev) { S with multi_agent := true }`.
    **Proof strategy:** see section banner above. -/
theorem pwf_add_authorization (W : WorkingSystem) (S : ConstraintSubset)
    (h : PartialWellFormed W S) (ev : GroundedAuthorizationStrict) :
    PartialWellFormed (W.addAuthorization ev) { S with multi_agent := true } :=
  { wf_distributed    := fun hd => by
        simp [handles_distributed_agents, HasBubbles, WorkingSystem.addAuthorization]
        exact h.wf_distributed hd
    wf_bounded_audit  := fun hb => by
        simp [handles_bounded_audit, HasTrustBridges, WorkingSystem.addAuthorization]
        exact h.wf_bounded_audit hb
    wf_export         := fun he => by
        simp [handles_export, HasHeaders, WorkingSystem.addAuthorization]
        exact h.wf_export he
    wf_adversarial    := fun ha => by
        simp [handles_adversarial, HasRevocation, WorkingSystem.addAuthorization]
        exact h.wf_adversarial ha
    wf_coordination   := fun hc => by
        simp [handles_coordination, HasBank, WorkingSystem.addAuthorization]
        exact h.wf_coordination hc
    wf_truth_pressure := fun ht => by
        simp [handles_truth_pressure, HasRedeemability, WorkingSystem.addAuthorization]
        exact h.wf_truth_pressure ht
    wf_multi_agent    := fun _ => by
        simp [handles_multi_agent, HasGranularACL, WorkingSystem.addAuthorization, Option.isSome]
    wf_storage        := fun hs => by
        simp [handles_storage, HasStorageManagement, WorkingSystem.addAuthorization]
        exact h.wf_storage hs }

/-- Adding storage-management evidence activates the `bounded_storage` biconditional.

    **Theorem shape:** `PartialWellFormed (W.addStorageManagement ev) { S with bounded_storage := true }`.
    **Proof strategy:** see section banner above. -/
theorem pwf_add_storage_management (W : WorkingSystem) (S : ConstraintSubset)
    (h : PartialWellFormed W S) (ev : GroundedStorageStrict) :
    PartialWellFormed (W.addStorageManagement ev) { S with bounded_storage := true } :=
  { wf_distributed    := fun hd => by
        simp [handles_distributed_agents, HasBubbles, WorkingSystem.addStorageManagement]
        exact h.wf_distributed hd
    wf_bounded_audit  := fun hb => by
        simp [handles_bounded_audit, HasTrustBridges, WorkingSystem.addStorageManagement]
        exact h.wf_bounded_audit hb
    wf_export         := fun he => by
        simp [handles_export, HasHeaders, WorkingSystem.addStorageManagement]
        exact h.wf_export he
    wf_adversarial    := fun ha => by
        simp [handles_adversarial, HasRevocation, WorkingSystem.addStorageManagement]
        exact h.wf_adversarial ha
    wf_coordination   := fun hc => by
        simp [handles_coordination, HasBank, WorkingSystem.addStorageManagement]
        exact h.wf_coordination hc
    wf_truth_pressure := fun ht => by
        simp [handles_truth_pressure, HasRedeemability, WorkingSystem.addStorageManagement]
        exact h.wf_truth_pressure ht
    wf_multi_agent    := fun hm => by
        simp [handles_multi_agent, HasGranularACL, WorkingSystem.addStorageManagement]
        exact h.wf_multi_agent hm
    wf_storage        := fun _ => by
        simp [handles_storage, HasStorageManagement, WorkingSystem.addStorageManagement, Option.isSome] }



/-! ========================================================================
    PART C — No Self-Healing Bank Without Magic
    ======================================================================== -/

/-- Deposit status improvement order.
    A status “improves” when it moves toward the live Deposited state.
    - .Quarantined → .Candidate  : repaired and re-queued
    - .Quarantined → .Deposited  : direct reinstatement
    - .Candidate   → .Deposited  : bank operator promotes
    All reflexive and downward cases are False (not improvements). -/
def StatusImproves : DepositStatus → DepositStatus → Prop
  | .Quarantined, .Candidate  => True
  | .Quarantined, .Deposited  => True
  | .Candidate,   .Deposited  => True
  | _,            _           => False

/-- NO SELF-HEALING BANK WITHOUT MAGIC.

    Every deposit status improvement is caused by an explicit agent-bearing
    action. Action.Tick is the only agentless step and never touches the
    ledger. Every status improvement therefore requires an actor.

    Automated repair daemons are EpArch agents: anything that fires a Step
    action is an agent by definition. The theorem prohibits anonymous action,
    not automation.

    Proof: tick is the only agentless Step constructor; its ledger is unchanged
    so d = d’ at the index, making StatusImproves d.status d.status = False,
    contradicting h_impr. All other constructors carry an agent identifier
    and are trivially ≠ .Tick by discriminator. -/
theorem no_self_healing_bank
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s a s')
    (d_idx : Nat) (d d' : Deposit PropLike Standard ErrorModel Provenance)
    (h_prev : s.ledger.get? d_idx = some d)
    (h_next : s'.ledger.get? d_idx = some d')
    (h_impr : StatusImproves d.status d'.status) :
    a ≠ .Tick := by
  cases h_step with
  | tick _ _ =>
    -- Tick only advances clock; ledger is definitionally unchanged.
    -- d = d’ at the index, making StatusImproves d.status d.status = False.
    intro _
    rw [h_prev] at h_next
    have h_dd' : d = d' := by injection h_next
    subst h_dd'
    exact absurd h_impr (by cases d.status <;> simp [StatusImproves])
  | submit _ _ => intro h; cases h
  | register _ _ => intro h; cases h
  | withdraw _ _ _ _ => intro h; cases h
  | challenge _ _ _ _ _ => intro h; cases h
  | revoke _ _ _ _ => intro h; cases h
  | repair _ _ _ _ _ => intro h; cases h
  | promote _ _ _ _ => intro h; cases h
  | forget _ _ _ _ _ _ => intro h; cases h
  | update _ _ _ _ _ _ _ => intro h; cases h

end EpArch.Meta.Reconfiguration

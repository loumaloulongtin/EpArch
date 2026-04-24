# Axioms and the Import Surface

The `Main.lean` import surface contains **zero `axiom` declarations**. One
named axiom exists in the repository (`lean_kernel_verification_path`), but it
lives in a file that `Main.lean` does not import and is therefore outside the
core architectural claim.

---

## The `Main.lean` import surface

`lake build` (driven by `Main.lean`) is the single build target for the core
formalization. Every file imported transitively from `Main.lean` introduces ordinary Lean
declarations such as `theorem`, `def`, `abbrev`, `structure`, `inductive`,
and `opaque`; no `axiom` declarations occur in this surface.

This is the trusted-base boundary for the core formalization. If a result is
cited as "proved", its proof sits inside this import surface.

---

## Named axiom inventory

There is one named `axiom` declaration in the repository:

| Name | File | Imported by `Main.lean`? |
|---|---|---|
| `lean_kernel_verification_path` | `EpArch/Meta/LeanKernel/VerificationPath.lean` | **No** |

`VerificationPath.lean` is a worked domain-instantiation example for the Lean
kernel. It exhibits how a concrete domain can supply a `vindication_evidence`
witness for `redeemable`. Other domains (RLHF, peer challenge, institutional
assessment, observation over time) would each name their own analogous axiom
or build a non-axiomatic witness.

`VerificationPath.lean` is not in the `Main.lean` transitive import closure;
downstream clients may import it explicitly as an optional worked instance.

---

## Opaques vs defs vs theorems

`opaque` constants are uninterpreted domain primitives. They are not `axiom`
declarations: they introduce a name with a type but no body, and any concrete
inhabitant must be supplied by an instantiation. Theorems that use them state
the dependence in their hypotheses.

Complete opaque inventory (26 declarations, 6 files):

**`Basic.lean`**

| Name | Type | Role |
|---|---|---|
| `agentTraction` | `Agent → (Claim → LadderStage)` | Agent's private traction function; different agent types implement it differently without affecting any revision-gate theorem |
| `ignores_bank_signal` | `Agent → Claim → Prop` | Agent's review channel is closed for a claim; separate from `certainty_L` — reaching Certainty does not close the channel |

**`Bank.lean`**

| Name | Type | Role |
|---|---|---|
| `exportDep` | `Bubble → Bubble → Deposit … → Prop` | Deposit crosses from bubble B1 to B2 (testimony / trust-boundary transfer) |
| `TrustBridge` | `Bubble → Bubble → Prop` | B1 and B2 have an established trust relationship permitting export without full revalidation |
| `Revalidate` | `Bubble → Bubble → Deposit … → Prop` | B2 re-runs its acceptance protocol on a deposit received from B1 |
| `RepairAction` | `Type u` | An action that modifies a specific field of a deposit; `repair` applies it and sets status to `Candidate` |

**`Header.lean`**

| Name | Type | Role |
|---|---|---|
| `header_preserved` | `Deposit P S E V → Prop` | Deposit header is intact; `header_stripped` is defined as `¬header_preserved`, making mutual exclusion a theorem |

**`Commitments.lean`**

| Name | Type | Role |
|---|---|---|
| `vindication_evidence` | `Deposit … → ConstraintSurface → Prop` | Surface-relative vindication witness; domain instantiators discharge it by axiom or by building a concrete non-opaque witness (see `VerificationPath.lean`) |
| `pushback` | `Deposit … → Prop` | Agent-level contestation primitive; used in the repair-loop (Commitment 6) family |

**`ConditionalPredictions.lean`**

| Name | Type | Role |
|---|---|---|
| `import_gated` | `Agent → Bubble → Claim → Prop` | Bubble's admission policy blocks disconfirming deposits from outside approved provenance chains; the import-side trust boundary |

**`Adversarial/Base.lean`** (16 opaques)

*Attack primitives — deposit/agent level*

| Name | Type | Role |
|---|---|---|
| `V_spoof` | `Deposit … → Prop` | Attacker injects fake provenance header |
| `amplify_cues` | `Deposit … → Prop` | Attacker amplifies cheap-to-process cues as substitutes for expensive checks |
| `consultation_suppressed` | `Agent → Prop` | Attacker blocks victim's access to validators |
| `expertise_gap` | `Agent → Prop` | Victim cannot distinguish surface checks from deep checks |

*Audit-channel / DDoS primitives*

| Name | Type | Role |
|---|---|---|
| `AuditChannel` | `Type` | The verification pathway type; `channel_capacity` and `attack_volume` are defined over it |
| `channel_capacity` | `AuditChannel → Nat` | How much verification can be processed on a channel |
| `attack_volume` | `AuditChannel → Nat` | How much the attacker is pushing through a channel |
| `ladder_overloaded` | `Agent → Prop` | Traction commits before V can be checked (high-salience flooding) |
| `V_channel_exhausted` | `Agent → Prop` | Provenance checking too costly or slow to keep pace with incoming claims |
| `E_field_poisoned` | `Agent → Prop` | Noise injected so error signals become ubiquitous |
| `denial_triggered` | `Agent → Prop` | Generalized distrust induced, blocking all external import |

*Boundary / countermeasure primitives*

| Name | Type | Role |
|---|---|---|
| `trust_centralized` | `Agent → Prop` | Agent delegates to a single "trusted" authority (single-point-of-failure structure) |
| `trust_bridge_on_hand` | `Agent → Prop` | Victim has pre-established expertise access (attack-failure condition) |
| `E_includes_threat` | `Agent → Prop` | Victim models this attack pattern in its error field (attack-failure condition) |

*Cost scalars*

| Name | Type | Role |
|---|---|---|
| `export_cost` | `Nat` | Attacker's per-deposit export cost; used in cost-asymmetry theorems |
| `import_defense_cost` | `Nat` | Defender's per-deposit import-defense cost; paired with `export_cost` |

The following names are **`def`s, not opaques** — they are computed from other
data and have inspectable bodies:

- `certainty_L a P := ladder_stage a P = .Certainty`
- `deposited B d := d.status = .Deposited ∧ d.bubble = B`
- `hasDeposit B P := ∃ S E V d, d.status = .Deposited ∧ d.bubble = B ∧ d.P = P`
- `knowledge_B := hasDeposit` (with `KnowledgeIffDeposited : Iff.rfl`)
- `cheap_validator_reachable`, `transaction_reversible`,
  `constraint_cheaply_testable` (all grounded as `τ > 0` predicates)

`structure`, `inductive`, and `theorem` declarations carry full proofs or
constructive content; none of them widen the trusted base.

---

## Optional / stretch exception surface

`VerificationPath.lean` belongs to the `EpArch/Meta/LeanKernel/*` family —
the worked Lean-kernel self-application. The other modules in that family
(`World.lean`, `RepairLoop.lean`, `SFailure.lean`, `OdometerModel.lean`)
are imported by `Main.lean` and contain no `axiom` declarations;
`VerificationPath.lean` is the one in that family that does, and is the one
that is held out of the core import surface.

Anything proved only by importing `VerificationPath.lean` is a worked domain
instance, not a core architectural claim. [optional/LEAN-KERNEL.md](../optional/LEAN-KERNEL.md)
documents the self-application in detail.

---

## What this file does not claim

This file is the boundary doc for axioms and the trusted base. It is not the
theorem registry (see [THEOREMS.md](THEOREMS.md)) and it is not a defence of
any particular use of `opaque`. It does not classify which opaques are
"essential" vs "convenient" — every opaque is named and every theorem that
uses one carries the dependence in its hypotheses.

---

## Go next

- [optional/LEAN-KERNEL.md](../optional/LEAN-KERNEL.md) — the
  `VerificationPath.lean` worked example in detail.
- [THEOREMS.md](THEOREMS.md) — what gets proved against this trusted base.

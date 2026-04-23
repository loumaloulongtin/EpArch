# Axioms and the Import Surface

The `Main.lean` import surface contains **zero `axiom` declarations**. One
named axiom exists in the repository (`lean_kernel_verification_path`), but it
lives in a file that `Main.lean` does not import and is therefore outside the
core architectural claim.

---

## The `Main.lean` import surface

`lake build` (driven by `Main.lean`) is the single build target for the core
formalization. Every file imported transitively from `Main.lean` introduces
only `theorem`, `def`, `structure`, `inductive`, and `opaque` declarations.
There are **no `axiom` declarations** in this surface.

This is the boundary that every other claim in the docs implicitly relies on.
If a result is cited as "proved", its proof (and every lemma it depends on)
sits inside this import-surface.

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

No file in the `Main.lean` transitive import closure imports
`VerificationPath.lean`. Importing it explicitly in a downstream client
widens that client's trusted base; the core build does not.

---

## Opaques vs defs vs theorems

`opaque` constants are uninterpreted domain primitives. They are not `axiom`
declarations: they introduce a name with a type but no body, and any concrete
inhabitant must be supplied by an instantiation. Theorems that use them state
the dependence in their hypotheses.

The opaque primitives in the core surface (representative, not exhaustive):

| Primitive | File | Role |
|---|---|---|
| `agentTraction` | `Basic.lean` | Agent's private traction assignment (Claim → LadderStage) |
| `ignores_bank_signal` | `Basic.lean` | Whether the agent's review channel is closed |
| `header_preserved` | `Header.lean` | Deposit header intact (vs stripped) |
| `vindication_evidence` | `Commitments.lean` | Surface-relative vindication witness for redeemability |
| `pushback` | `Commitments.lean` | Agent-level contestation primitive |
| `exportDep` / `TrustBridge` / `Revalidate` / `RepairAction` | `Bank.lean` | Cross-bubble and lifecycle hooks |
| Adversarial primitives | `Adversarial/Base.lean` | Attack-channel, DDoS, countermeasure, and cost primitives |

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

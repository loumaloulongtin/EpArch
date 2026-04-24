# Lean kernel as an EpArch instance (optional)

This file is an optional worked example. It documents the
`EpArch/Meta/LeanKernel/` subtree, in which Lean's own type-checking
kernel is exhibited as a concrete EpArch instantiation. The subtree is
not part of the core architectural claim. The headline forcing,
commitments, and witness results in [../reference/THEOREMS.md](../reference/THEOREMS.md)
and [../PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md) do not depend on any
file documented here, and the one named axiom in the repository lives
inside this subtree, outside `Main.lean`'s import surface.

---

## What lives in `EpArch/Meta/LeanKernel/`

The subtree contains five files. The first four are imported by
`Main.lean`; the fifth is not.

| File | Role |
|---|---|
| [Meta/LeanKernel/World.lean](../../EpArch/Meta/LeanKernel/World.lean) | Defines `LeanKernelCtx : WorldCtx` and proves it satisfies the three world-assumption bundles (lies-possible, bounded-verification, partial-observability). Hosts the entry theorems for the subtree. |
| [Meta/LeanKernel/SFailure.lean](../../EpArch/Meta/LeanKernel/SFailure.lean) | Lean-specific S-field failure taxonomy: vacuous and void witnesses, canonical failure cases, and the master `lean_S_failure_taxonomy` theorem. |
| [Meta/LeanKernel/RepairLoop.lean](../../EpArch/Meta/LeanKernel/RepairLoop.lean) | Lean elaboration as a worked deposit lifecycle: declared signature as `S`, elaborator challenge report as `E`, import list as `V`. Proves the repair loop on this concrete instance. |
| [Meta/LeanKernel/OdometerModel.lean](../../EpArch/Meta/LeanKernel/OdometerModel.lean) | A stylized minimal sub-bundle witness in which only `SoundDepositsGoal` is substantively satisfied. Used to exhibit the no-self-correction floor and the staleness distinction (true-but-superseded vs false). |
| [Meta/LeanKernel/VerificationPath.lean](../../EpArch/Meta/LeanKernel/VerificationPath.lean) | Worked C4b domain instantiation. Part A discharges the surface as a closed theorem with zero axioms; Part B bridges to the core opaque `vindication_evidence` via the one named axiom in the repository (`lean_kernel_verification_path`). **Not imported by `Main.lean`.** |

`Main.lean` imports `OdometerModel`, `World`, `SFailure`, and
`RepairLoop`. It does not import `VerificationPath`. The file is
mentioned in `Main.lean`'s prose comments as a worked
domain-instantiation example, not as a dependency.

---

## What this subtree is showing

Three things, all of them illustrative rather than load-bearing.

**Lean as an EpArch-like worked instance.** `LeanKernelCtx` fixes
`World := Bool` (clean vs `sorry`-tainted environment), `Agent := Unit`,
`Claim := Bool` (provable vs unprovable), `Obs := Unit` (proof
irrelevance), `Truth := fun w P => w = P`, `Utter := fun _ _ => True`
(`sorry` as unrestricted utterance gate), and a heartbeat-bounded
`VerifyWithin`. Under that fixing, the three world-assumption bundles
hold and the bundled-existence is concrete, not just abstract.

**Repair / lifecycle / S-failure interpretation.** `RepairLoop.lean`
gives the elaboration cycle as a concrete deposit lifecycle: declared
signature is `S`, the elaborator's challenge report (file, line,
expected, actual) is `E`, and the import list is `V`. `SFailure.lean`
catalogues how the `S` field can be satisfied vacuously or void-ably
inside this instance.

**Odometer contrast model.** `OdometerModel.lean` exhibits a sub-bundle
in which only `SoundDepositsGoal` substantively holds. Revision,
adversarial, and reliable-export goals fail or hold only vacuously.
This makes the no-self-correction floor concrete — a system where the
ledger is append-only, readings become stale rather than false, and
`RevisionGate` holds vacuously because there is no revision capability
to gate.

---

## Main theorem route

| Theorem | Location | What it gives |
|---|---|---|
| `lean_kernel_satisfies_bundles` | [Meta/LeanKernel/World.lean#L176](../../EpArch/Meta/LeanKernel/World.lean#L176) | `LeanKernelCtx` satisfies all three world-assumption bundles. Entry theorem for the subtree. |
| `lean_kernel_no_tradeoff` | [Meta/LeanKernel/World.lean#L213](../../EpArch/Meta/LeanKernel/World.lean#L213) | Lifts the no-tradeoff result to the Lean-kernel instance. |
| `lean_kernel_existence` | [Meta/LeanKernel/World.lean#L850](../../EpArch/Meta/LeanKernel/World.lean#L850) | Concrete bundled-existence witness for the Lean-kernel instance. |
| `lean_kernel_path_is_redeemable` | [Meta/LeanKernel/VerificationPath.lean#L129](../../EpArch/Meta/LeanKernel/VerificationPath.lean#L129) | Any proved Prop deposit is `redeemable` in the core theory's sense. **Sits behind the named axiom** (Part B). |

Secondary support, in [Meta/LeanKernel/OdometerModel.lean](../../EpArch/Meta/LeanKernel/OdometerModel.lean):
`odometer_no_self_correction`, `odometer_revision_gate`,
`odometer_sound_deposits`, `odometer_not_corrigible`,
`odometer_not_safe_withdrawal`, `odometer_not_reliable_export`,
`odometer_self_correction_vacuous`, plus
`odometer_is_minimal_goal_witness` (typed bundle for the goal-stance
profile) and `odometer_extension_safe`.

In [Meta/LeanKernel/World.lean](../../EpArch/Meta/LeanKernel/World.lean):
`leanKernel_is_gettier` and `leanKernel_gettier_gap` exhibit a
canonical Gettier instance inside `LeanKernelCtx`.

`lean_redeemable_deposits_exist` in
[Meta/LeanKernel/VerificationPath.lean](../../EpArch/Meta/LeanKernel/VerificationPath.lean)
is Part A: a closed, axiom-free theorem in the parallel
Lean-domain interface (`LeanPathExists` / `LeanVerificationPath`). It
does not use the named axiom.

---

## The axiom boundary

The repository contains exactly one named axiom:

```lean
axiom lean_kernel_verification_path
    {Standard ErrorModel Provenance : Type}
    (d : Deposit Prop Standard ErrorModel Provenance)
    (h_prop : d.P) :
    vindication_evidence d d.h.redeem
```

It is declared in
[Meta/LeanKernel/VerificationPath.lean#L116](../../EpArch/Meta/LeanKernel/VerificationPath.lean#L116).
`VerificationPath.lean` is not imported by `Main.lean` and is not in
`Main.lean`'s transitive import closure. The core import surface is
axiom-free; the axiom is reachable only by a downstream client that
explicitly imports `VerificationPath.lean`.

The axiom names a domain-specific trust boundary: in the Lean domain,
elaboration produces `vindication_evidence` for a proved `Prop`
deposit. The opaque `vindication_evidence` in
[Commitments.lean](../../EpArch/Commitments.lean) is sealed by design
because its realization varies across domains, across subsystems within
a domain, and across deposits within the same system. Other domains
supply their own analogous statement; this is the Lean domain's.

`lean_kernel_path_is_redeemable` is the only theorem in this subtree
that sits behind the axiom. Everything else listed above — including
`lean_kernel_satisfies_bundles`, `lean_kernel_no_tradeoff`,
`lean_kernel_existence`, the odometer family, and Part A's
`lean_redeemable_deposits_exist` — is axiom-free.

The exact boundary is documented in [../reference/AXIOMS.md](../reference/AXIOMS.md).

---

## What this file is not claiming

- Not that EpArch originates from, or is motivated by, the Lean kernel.
  The subtree is a worked instance, not a foundation.
- Not that this self-application is required for any headline result.
  Removing the entire `Meta/LeanKernel/` subtree leaves the core
  architectural claim intact.
- Not that the named axiom is part of the core build surface. It is
  reachable only when `VerificationPath.lean` is explicitly imported.
- Not that `LeanKernelCtx` is the unique or canonical realization. It
  is one concrete instantiation; other domains supply their own.
- Not that the odometer model is a literal model of any physical
  device. It is a stylized minimal witness for the goal-stance
  profile.

---

## Where to go next

- [../reference/AXIOMS.md](../reference/AXIOMS.md) — the exact
  named-axiom and import-surface boundary.
- [../PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md) — the core proof route
  this subtree sits outside of.
- [../START-HERE.md](../START-HERE.md) — orientation and glossary.

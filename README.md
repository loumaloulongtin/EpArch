# EpArch — Machine-Checked Epistemic Architecture

> **Work in progress.** This formalization has not undergone peer review. Proofs and documentation are subject to change.

EpArch is a Lean 4 formalization of an epistemic architecture: machine-checked
theorems showing that certain operational primitives — lifecycle gates,
header-preserving export, a revision loop, scoped authorization, temporal
validity, storage management — are *forced* by the combination of agent
constraints and system health goals, not chosen.

[![CI](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml/badge.svg)](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml)

`lake build` — **0 axiom declarations** in the core import surface, **0 sorries**.
The exact boundary lives in [DOCS/reference/AXIOMS.md](DOCS/reference/AXIOMS.md).

---

## What this repo proves

- **Structural forcing.** Eight pressure dimensions, each backed by a
  per-dimension impossibility witness, force any working system meeting
  the corresponding operational and bridge properties to contain the
  bank-primitive cluster. Headline theorem:
  `bundled_structure_forces_bank_primitives` in
  [`EpArch/WorldBridges.lean`](EpArch/WorldBridges.lean).
- **Commitments.** All eight structural commitments (C1–C8) are proved as
  standalone theorems; `commitments_pack` bundles the unconditional ones
  ([`EpArch/Commitments.lean`](EpArch/Commitments.lean)).
- **Operational semantics.** Lifecycle, withdrawal, export, challenge, and
  repair gates are typed transitions whose constructors carry their
  preconditions ([`EpArch/Semantics/StepSemantics.lean`](EpArch/Semantics/StepSemantics.lean)).
- **Witnesses.** Concrete inhabitants discharge the existence side
  ([`EpArch/Concrete/`](EpArch/Concrete/), [`EpArch/WorldWitness.lean`](EpArch/WorldWitness.lean));
  conservative-extension lemmas establish what the witnesses do and do not
  buy ([DOCS/reference/WITNESS-SCOPE.md](DOCS/reference/WITNESS-SCOPE.md)).
- **Modularity.** Constraint subsetting, theorem transport, and a 32-cluster
  certification surface live under [`EpArch/Meta/`](EpArch/Meta/).

---

## Repository shape

```
EpArch/
  Main.lean              build entry point — defines the core import surface
  EpArch/                kernel, theorem library, witnesses, meta layer
    Basic, Header, Bank, Commitments, ...
    Semantics/           LTS and step semantics
    Theorems/            withdrawal, headers, dissolutions, case bindings
    Concrete/            zero-axiom constructive witnesses
    Adversarial/         attack/defense obligations
    Agent/               agent constraints, imposition, corroboration
    Meta/                modularity, transport, cluster registry, optional kernel
  DOCS/                  reader-facing documentation
  lakefile.lean          build manifest (Lean 4.3.0, no Mathlib)
```

The full file-by-file map is in [DOCS/reference/FILE-INVENTORY.md](DOCS/reference/FILE-INVENTORY.md).

---

## Build and check

```bash
lake build
```

Requires Lean 4.3.0; no Mathlib dependency. The build target is `Main.lean`.
The core import surface (everything `Main.lean` transitively imports) contains
**zero `axiom` declarations** and **zero `sorry`**. One named axiom
(`lean_kernel_verification_path`) exists in the optional Lean-kernel subtree
and is *not* in `Main.lean`'s import closure — see
[DOCS/reference/AXIOMS.md](DOCS/reference/AXIOMS.md) for the exact boundary
and [DOCS/optional/LEAN-KERNEL.md](DOCS/optional/LEAN-KERNEL.md) for the
worked example.

---

## Where to start

| If you are…                                | Read first                                                          |
|--------------------------------------------|---------------------------------------------------------------------|
| New to the repo                            | [DOCS/START-HERE.md](DOCS/START-HERE.md)                            |
| Reviewing the proof                        | [DOCS/PROOF-STRUCTURE.md](DOCS/PROOF-STRUCTURE.md)                  |
| Looking up a theorem                       | [DOCS/reference/THEOREMS.md](DOCS/reference/THEOREMS.md)            |
| Browsing the docs index                    | [DOCS/README.md](DOCS/README.md)                                    |

---

## Scope and boundaries

- The forcing claim is conditional on the stated constraint, goal, and
  bridge data. EpArch does *not* assert that the real world satisfies the
  W-bundles; W-bundles are explicit assumptions/witnessed contexts used by
  the relevant theorems.
- The bundled-existence theorems witness inhabitation. They do *not* assert
  that the concrete realization is unique or canonical — other realizations
  satisfying the same signatures are admissible.
- The optional Lean-kernel subtree (`EpArch/Meta/LeanKernel/`) is a worked
  domain instantiation, not part of the core architectural claim. The one
  named axiom in the repository lives there and is outside `Main.lean`'s
  import surface.

---

## References

> Longtin, L.-M. (2026). *Epistemic Architecture: A Constraints-and-Objectives Framework for Bounded Agents Under Adversarial Pressure.* PhilArchive: <https://philarchive.org/rec/LONEAA-7>
>
> *Working draft. The repository has evolved significantly since the version
> reflected in the paper (see pinned commit). Some terminology and structure
> may differ; the repository is the authoritative source for the current
> formalization.*
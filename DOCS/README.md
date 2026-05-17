# EpArch Lean Formalization — Documentation Index

This folder documents the Lean formalization. It does not teach the proof, it
routes you to the file that does.

## Reader routes

| If you are…                                          | Read first                                                          |
|------------------------------------------------------|---------------------------------------------------------------------|
| New to the repo                                      | [START-HERE.md](START-HERE.md)                                      |
| Reviewing the proof                                  | [PROOF-STRUCTURE.md](PROOF-STRUCTURE.md)                            |
| Looking up a theorem                                 | [reference/THEOREMS.md](reference/THEOREMS.md)                      |
| Auditing axioms / import surface                     | [reference/AXIOMS.md](reference/AXIOMS.md)                          |
| Reading the optional Lean-kernel worked example      | [optional/LEAN-KERNEL.md](optional/LEAN-KERNEL.md)                  |
| Wanting the architectural intuition (prose walk)     | [../theory/README.md](../theory/README.md)                          |

## Tree

```
DOCS/
  README.md                   you are here
  START-HERE.md               onboarding + glossary
  PROOF-STRUCTURE.md          reviewer proof-route

  architecture/               layer descriptions (what each layer is, claims, boundaries)
    SEMANTICS.md              operational substrate (Bank, LTS, gates)
    WORLD.md                  W-bundles, WorldCtx, obligation theorems
    FEASIBILITY.md            non-vacuity, concrete inhabitation
    CORROBORATION.md          multi-source acceptance, common-mode failure
    MODULARITY.md             projection, transport, certification

  reference/                  lookup / boundary docs
    THEOREMS.md               theorem registry by family
    AXIOMS.md                 import-surface and axiom boundary
    WITNESS-SCOPE.md          what witnesses establish and what they don't
    FILE-INVENTORY.md         file-role map of the Lean source

  cases/
    CASE-STUDIES.md           cross-domain corroboration / stress-test

  optional/
    LEAN-KERNEL.md            Lean kernel as worked EpArch instance (outside core claim)
```

## Core vs optional

Everything under `architecture/`, `reference/`, and the three top-level files is
core: it documents the headline forcing claim and its supporting machinery.

`cases/` is corroboration only — not a proof appendix.

`optional/` is outside the core architectural claim. The worked Lean-kernel
example is the only place a named axiom appears, and it is not in
`Main.lean`'s import surface (see [reference/AXIOMS.md](reference/AXIOMS.md)).

## Companion prose layer

The sibling [`../theory/`](../theory/) folder is a separate, optional but
recommended path. It walks the architecture as a narrative (world → bubble →
agent → forcing → goals → autonomy → concrete → meta) and explains
what the kernel cannot say in its own register — why each structural piece
is forced, what credit is being carried, which silences are deliberate. It
is not a tutorial for DOCS and DOCS is not a summary of it; the two layers
are complementary. Read them alongside, before, or after one another.

## Build

`lake build` (via `Main.lean`) is the single build target. Zero sorries, zero
core axiom declarations — see [reference/AXIOMS.md](reference/AXIOMS.md) for
the exact statement.

## See also

- [../README.md](../README.md) — repository landing page

/-
MainPaper.lean — Paper-Facing Build Surface

This is the minimal import for paper-facing claims.
It imports ONLY the paper-facing surface.

## Build Surfaces

| Surface | Import | Description |
|---------|--------|-------------|
| **Paper-Facing** | `MainPaper.lean` | Core-facing theorems only |
| **Full** | `Main.lean` | Full build (same axioms, more modules) |

## What This Surface Includes

- **PaperFacing.lean** — Canonical exports for core-facing claims
  - Derived theorems (RevisionSafety, ScopeIrrelevance, Gates)
  - Conditional obligation theorems (World, AdversarialObligations)
  - Specification axioms (Health, Invariants, Commitments)

## Axiom Declarations (Paper-Facing Surface)

The paper-facing surface contains **zero `axiom` declarations**.
All structural commitments are exposed as fields of `CommitmentsCtx`.
Opaque domain primitives remain as uninterpreted constants.

Health goals are definitional, not axioms.
Agent design-forcing and WorldCtx transport are proved theorems.
-/

import EpArch.PaperFacing

def main : IO Unit :=
  IO.println s!"EpArch: Paper-Facing Surface (0 axiom declarations, 0 sorry)"

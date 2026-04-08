/-
MainPaper.lean — Paper-Facing Build Surface

This is the minimal import for paper-facing claims.
It imports ONLY the paper-facing surface.

## Build Surfaces

| Surface | Import | Description |
|---------|--------|-------------|
| **Paper-Facing** | `MainPaper.lean` | Core-facing theorems only |
| **Full** | `Main.lean` | Full build |

## What This Surface Includes

- **PaperFacing.lean** — Canonical exports for core-facing claims
  - Derived theorems (RevisionSafety, ScopeIrrelevance, Gates)
  - Conditional obligation theorems (World, AdversarialObligations)
  - Health goals, structural invariants, and architectural commitments

## Axiom Declarations (Paper-Facing Surface)

The paper-facing surface contains **zero `axiom` declarations**.
All 8 structural commitments are proved standalone theorems; `commitments_pack` bundles
the unconditional ones (C3/C7b/C8).
Opaque domain primitives remain as uninterpreted constants.

Health goals are definitional, not axioms.
Agent design-forcing and WorldCtx transport are proved theorems.
-/

import EpArch.PaperFacing

def main : IO Unit :=
  IO.println s!"EpArch: Paper-Facing Surface (0 axiom declarations, 0 sorry)"

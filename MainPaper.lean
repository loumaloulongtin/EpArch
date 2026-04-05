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

## Axiom Count (Paper-Facing Surface)

| File | Count | Category |
|------|-------|----------|
| Bank.lean | 18 | Spec: operator postconditions |
| Commitments.lean | 13 | Spec: architecture commitments |
| Invariants.lean | 5 | Spec: protocol requirements |
| **Total** | **36** | All specification axioms |

Health goals are definitional, not axioms.
Agent design-forcing and WorldCtx transport are now proved theorems.
-/

import EpArch.PaperFacing

def main : IO Unit :=
  IO.println s!"EpArch: Paper-Facing Surface (36 axioms, 0 sorry)"

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
| Bank.lean | 3 | Remaining: KnowledgeIffDeposited, success_driven_bypass, blast_radius_scales_with_reliance |
| Commitments.lean | 9 | Design commitments over opaque external predicates |
| Invariants.lean | 5 | Protocol requirements (design requirements, not derivable) |
| **Total** | **17** | Remaining specification axioms |

Discharged in `discharge-axioms` branch: 11 operator defs + 4 status-transition
theorems + 3 Commitments theorems = **18 discharged** (35 → 17 axioms).

Health goals are definitional, not axioms.
Agent design-forcing and WorldCtx transport are now proved theorems.
-/

import EpArch.PaperFacing

def main : IO Unit :=
  IO.println s!"EpArch: Paper-Facing Surface (17 axioms, 0 sorry)"

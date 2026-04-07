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
| Bank.lean | 0 | All discharged |
| Commitments.lean | 5 | Permanently architectural: TractionAuthorizationSplit, NoGlobalLedgerTradeoff, RedeemabilityExternal, by_consensus_creates_redeemability, ConsensusNotSufficient |
| Invariants.lean | 4 | Gating invariants + no_deposit_without_redeemability |
| **Total** | **9** | Permanently architectural axioms |

Total discharged: 35 → 9 axioms (26 discharged).

Health goals are definitional, not axioms.
Agent design-forcing and WorldCtx transport are now proved theorems.
-/

import EpArch.PaperFacing

def main : IO Unit :=
  IO.println s!"EpArch: Paper-Facing Surface (9 axioms, 0 sorry)"

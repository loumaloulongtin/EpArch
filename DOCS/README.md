# EpArch Lean Formalization — Documentation Index

This folder contains detailed documentation for the Lean formalization of the Epistemic Architecture (EpArch) framework.

**The problem:** When independent agents — scientists, courts, open-source communities — assess and authorize knowledge claims, what structural requirements must any functioning system share? **The answer this formalization gives:** lifecycle gates, header-preserving export, a revision loop, and temporal validity are not design choices. They are *forced* by the combination of agent constraints (imperfect agents face permanent challenge pressure) and system health goals (safe withdrawal, reliable export, self-correction). The 435 theorem declarations below are the machine-checked evidence.

## Build Surfaces

| Surface | Entry Point | Axioms | Description |
|---------|-------------|--------|-------------|
| **Paper-Facing** | `MainPaper.lean` | 35 | Only theorems cited by the paper |
| **Full** | `Main.lean` | 35 | Full build (same axioms) |

## Documents

| File | Description |
|------|-------------|
| [THEOREMS.md](THEOREMS.md) | Complete theorem inventory organized by paper role |
| [AXIOMS.md](AXIOMS.md) | Axiom inventory with categories and justifications |
| [WORLD.md](WORLD.md) | World layer for obligation theorems |

| [FEASIBILITY.md](FEASIBILITY.md) | Non-vacuity / joint feasibility theorems |
| [CORROBORATION.md](CORROBORATION.md) | Multi-agent corroboration and common-mode failure |
| [SEMANTICS.md](SEMANTICS.md) | Step semantics and LTS overview |
| [WITNESS-SCOPE.md](WITNESS-SCOPE.md) | What the concrete model witnesses (and doesn't) |

For the full paper-section-to-Lean-artifact mapping (with math notation, A.# labels, and claim-budget notes), see **Appendix A** of the paper.

## Core Concepts (Glossary)

| Term | Meaning |
|------|---------|
| **Deposit** | An epistemic claim with a governance lifecycle (Candidate → Validated → Deposited → Quarantined → Revoked). The unit of knowledge in the architecture. |
| **Bubble** | A bounded authorization domain. Authority is scoped to a bubble; cross-bubble transfer requires explicit export. |
| **S / E / V** | The three header fields: **S**ource (who asserted it), **E**ntailment (why it is supported), **V**erification (how it was checked). Stripping these loses diagnosability. |
| **Traction** | A claim has *traction* if it influences epistemic behavior (belief, action) — strictly broader than formal authorization. |
| **Redeemability** | Whether a claim can be cashed out against external reality. External, not conferred by consensus. |
| **Competition gate** | A theorem showing that a rival epistemic architecture *must* address some specific structural requirement to function — you cannot simply skip it. |
| **PRP** | Permanent Redeemability Pressure — agents face a continuous challenge stream that cannot be fully discharged, preventing terminal epistemic closure. |
| **W-bundle** | An explicit assumption package (e.g. `W_lies_possible`). Obligation theorems have shape `W_* → Conclusion`, making premises auditable. |
| **Tier A / B / C** | Proved theorem / Conditional on W-bundle / Design axiom (intentionally postulated). |

---

## Quick Navigation

### Core Theorem Buckets

| Bucket | Topic |
|--------|-------|
| 1 | Lifecycle & Type-Separation — Candidate/Validated/Deposited/Quarantine/Revoked gates |
| 2 | Competition Gate Cluster — Revision ⇔ Self-correction equivalence |
| 3 | Export/Strip Asymmetry — No left inverse, reconstruction impossible |
| 4 | Diagnosability — Observability monotonicity, repair granularity |
| 5 | τ (Temporal Validity) — Staleness, blocking, hygiene pressure |
| 6 | Case Bindings — Gettier, Fake Barn, Lottery (illustrative diagnoses) |
| 7 | Invariant Preservation — Truth and gate invariants under trace induction |
| 8 | Modal Properties — Safety/Sensitivity ↔ S/E/V header preservation |
| 9 | Grounded Minimality — Each feature necessary for specific capabilities |
| 10 | Adversarial Model — Attack structures, DDoS vectors, obligation theorems |
| 11 | Repair Loop Semantics — Challenge-repair-revalidation cycle |
| 12 | Withdrawal Gates — Three-gate model (Status ∧ ACL ∧ τ) |
| 13 | Obligation Theorems — World ⇒ Mechanism (W_* bundles) |
| 14 | Health → Necessity — Health goals force capability requirements |
| 15 | Scope/Irrelevance — Substrate independence, extra-state erasure |
| 16 | Discharged Linking Axioms — 20 philosophical axioms now proved theorems |
| 17 | Revision Safety — Compatible extensions, premise strengthening, transport |
| 18 | Agent Constraints & PRP — Imperfect agents force mechanisms |
| 19 | Feasibility — Existence under constraints, forced Bank primitives |
| 20 | Meta-Status — Floor falsifiable, not fully authorizable from obs |
| 21 | Multi-Agent Corroboration — Conditional minimality, bubble infection |
| 22 | Entrenchment — Pathological Certainty state breaks safe withdrawal |
| 23 | Observational Completeness — No hidden deposit fields |

### Key Files

| Lean File | Role | Axioms |
|-----------|------|--------|
| `Basic.lean` | Core types (Claim, Agent, Bubble, Field, etc.) | 0 |
| `Header.lean` | S/E/V header structure + Deposit records | 0 |
| `StepSemantics.lean` | Labeled transition system (Step, Trace, Action) | 0 |
| `Theorems.lean` | Derived theorems, corner gates, case diagnoses | 0 |
| `World.lean` | World layer for obligation theorems | 0 |
| `AdversarialObligations.lean` | Adversarial axioms → obligation theorems | 0 |
| `RevisionSafety.lean` | Premise strengthening + compatible extensions | 0 |
| `ScopeIrrelevance.lean` | Scope irrelevance theorems | 0 |
| `Bank.lean` | Bank substrate, lifecycle operators | 18 |
| `Commitments.lean` | Paper's 8 commitments | 13 |
| `Health.lean` | Health predicates + necessity theorems | 0 |
| `Invariants.lean` | Protocol requirements | 5 |
| `ConcreteLedgerModel.lean` | Non-vacuity witness (constructive) | 0 |

## Build & Verification

```bash
cd lean-formalization
lake build
```

**Current Status:** Zero errors, zero sorries, 35 axioms (paper-facing surface).

## See Also

- [../README.md](../README.md) — Main project README

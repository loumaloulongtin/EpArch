# EpArch Lean Formalization — Documentation Index

This folder documents the Lean formalization of the Epistemic Architecture (EpArch) framework — 712 proved theorems, 0 axiom declarations, zero sorries.

**The core claim:** lifecycle gates, header-preserving export, a revision loop, and temporal validity are not design choices. They are *forced* by the combination of agent constraints (imperfect agents face permanent challenge pressure) and system health goals (safe withdrawal, reliable export, self-correction). The files below are the machine-checked record of that forcing argument.

## Build Surface

`lake build` (via `Main.lean`) is the single build target. **0 axiom declarations.**

## Documents

| File | Description |
|------|-------------|
| [THEOREMS.md](THEOREMS.md) | Complete theorem inventory organized by architectural role |
| [AXIOMS.md](AXIOMS.md) | Axiom inventory with categories and justifications |
| [WORLD.md](WORLD.md) | Explicit world assumptions (W-bundles) and obligation theorem structure |
| [FEASIBILITY.md](FEASIBILITY.md) | Non-vacuity / joint feasibility theorems |
| [CORROBORATION.md](CORROBORATION.md) | Multi-agent corroboration and common-mode failure |
| [SEMANTICS.md](SEMANTICS.md) | Step semantics and LTS overview |
| [WITNESS-SCOPE.md](WITNESS-SCOPE.md) | What the concrete model witnesses (and doesn't) |
| [MODULARITY.md](MODULARITY.md) | Modularity tiers: what survives disabling a constraint, health goal, or world bundle, and by what mechanism |

## Core Concepts (Glossary)

| Term | Meaning |
|------|---------|
| **Deposit** | An epistemic claim with a governance lifecycle (Candidate → Deposited → Quarantined → Revoked). The unit of knowledge in the architecture. |
| **Bubble** | A bounded authorization domain. Authority is scoped to a bubble; cross-bubble transfer requires explicit export. |
| **S / E / V** | The three header fields: **S**tandard (the validation threshold applied), **E**rror model (known failure modes the validation accounts for), **V**-provenance (the chain of evidence and checks). Stripping these loses diagnosability. |
| **Traction** | A claim has *traction* if it influences epistemic behavior (belief, action) — strictly broader than formal authorization. |
| **Redeemability** | Whether a claim can be cashed out against external reality. External, not conferred by consensus. |
| **Competition gate** | A theorem showing that a rival epistemic architecture *must* address some specific structural requirement to function — you cannot simply skip it. |
| **PRP** | Permanent Redeemability Pressure — agents face a continuous challenge stream that cannot be fully discharged, preventing terminal epistemic closure. |
| **W-bundle** | An explicit assumption package (e.g. `W_lies_possible`). Obligation theorems have shape `W_* → Conclusion`, making premises auditable. |
| **Tier A / B / C** | Proved theorem / Conditional on W-bundle / Design commitment (context-bundled structural assumption). |

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
| 9b | Abstract Structural Forcing — Six per-dimension `*_forces_*` theorems (no `WellFormed`, no biconditionals) + `SystemOperationalBundle` / `WorldBridgeBundle`; headline `bundled_structure_forces_bank_primitives`; six structural impossibility models + `StructurallyForced` / `convergence_structural` (`Minimality.lean` + `Convergence.lean`) |
| 9c | Observation-Boundary Equivalence — Any two `GroundedBehavior` witnesses produce identical observations; step-bridge grounds withdraw/challenge/tick via `ReadyState` + `behavior_from_step` (`Theorems/BehavioralEquivalence.lean`) |
| 9d | Kernel Verification Depth — `DepthClaim` constructive witness; `bounded_verify` budget decision procedure; `DepthWorldCtx` closes `W_bounded_verification` by construction (`VerificationDepth.lean`) |
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
| 24 | Lattice-Stability — Graceful degradation, sub-level revision safety, modularity pack |
| 25 | Theorem Transport — Health Goal Layer (Tier 3 closure) |
| 26 | Theorem Transport — Main Library Layer (Tier 4 closure: standalone commitments + structural + LTS + health goals) |
| 27 | Modularity Meta-Theorem — ∀ S ⊆ Constraints, projection_valid S |
| 28 | Certification Engine — `EpArchConfig → ClusterTag → certified proof` (29 clusters) |
| 29 | Lean Kernel Instantiation — Lean's type-checking kernel modeled as EpArch-compliant (`LeanKernelCtx`, `LeanWorkingSystem`, 30 theorems) |

### Key Files

| Lean File | Role | Axiom decls |
|-----------|------|--------|
| `Basic.lean` | Core types (Claim, Agent, Bubble, Field, etc.) | 0 |
| `Header.lean` | S/E/V header structure + Deposit records | 0 |
| `StepSemantics.lean` | Labeled transition system (Step, Trace, Action) | 0 |
| `Theorems/` | Primary theorem library split into 8 focused sub-modules (Withdrawal, Cases, Headers, Modal, Strip, Corners, Dissolutions, Pathologies) | 0 |
| `World.lean` | World layer for obligation theorems | 0 |
| `Adversarial/Obligations.lean` | Adversarial axioms → obligation theorems | 0 |
| `RevisionSafety.lean` | Premise strengthening + compatible extensions | 0 |
| `ScopeIrrelevance.lean` | Scope irrelevance theorems | 0 |
| `Bank.lean` | Bank substrate, lifecycle operators | 0 |
| `Commitments.lean` | 8 structural commitments; all proved as standalone theorems; `commitments_pack` bundles the unconditional ones (C3/C4b/C7b/C8) | 0 |
| `Meta/ClusterRegistry.lean` | 29-cluster tag registry, routing, per-family canonical lists | 0 |
| `Meta/Config.lean` | Certification engine: `certify`, proof witnesses, completeness theorems | 0 |
| `Health.lean` | Health predicates + necessity theorems | 0 |
| `Invariants.lean` | Protocol requirements | 0 |
| `Minimality.lean` | Structural impossibility models + alternative-architecture dismissals | 0 |
| `Convergence.lean` | `StructurallyForced`, `ForcingEmbedding`, `convergence_structural`, bridge predicates | 0 |
| `Theorems/BehavioralEquivalence.lean` | Observation-boundary equivalence; `Behavior` takes `GroundedBehavior`, step-grounded for withdraw/challenge/tick | 0 |
| `ConcreteLedgerModel.lean` | Non-vacuity witness (constructive) | 0 |
| `Meta/LeanKernel/World.lean` | Lean kernel self-application: `LeanKernelCtx`, `LeanWorkingSystem`, world-layer witnesses, architecture-layer proofs, convergence chain, OleanStaleness | 0 |
| `Meta/LeanKernel/SFailure.lean` | Lean kernel S-field failure taxonomy: axiom levels, standard/vacuous cases, relational vs. absolute failure | 0 |

## Build & Verification

```bash
lake build
```

**Current Status:** Zero errors, zero sorries, zero axiom declarations.

## See Also

- [../README.md](../README.md) — Main project README

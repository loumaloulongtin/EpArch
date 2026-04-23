# Start Here

EpArch is a Lean formalization of an epistemic architecture: a set of
machine-checked theorems showing that certain operational primitives —
lifecycle gates, header-preserving export, a revision loop, temporal
validity — are *forced* by the combination of agent constraints and
system health goals, not chosen.

## Glossary

The canonical home for project vocabulary. Other docs use these terms
without redefining them.

| Term            | Meaning                                                                                                  |
|-----------------|----------------------------------------------------------------------------------------------------------|
| **PRP**         | Permanent Redeemability Pressure — agents face a continuous challenge stream that cannot be discharged.  |
| **Deposit**     | An epistemic claim with a governance lifecycle (Candidate → Deposited → Quarantined → Revoked).          |
| **Header**      | The S/E/V triple attached to a deposit; routing depends on it.                                           |
| **Gate**        | A typed lifecycle transition whose constructor encodes its preconditions (ACL, currency, status).        |
| **W-bundle**    | An explicit world-assumption package (e.g. `W_lies_possible`); obligation theorems have shape `W_* → C`. |
| **S / E / V**   | Header fields: **S**tandard applied, **E**rror model, **V**-provenance chain.                            |
| **Scope**       | A bounded authorization domain (bubble); cross-scope transfer requires explicit export.                  |
| **Lifecycle**   | The typed state machine a deposit traverses; gate theorems show the transitions are not optional.        |

## What the repo proves

Eight architectural pressure dimensions, backed by structural impossibility
witnesses, force any working system satisfying the corresponding operational
and bridge properties to contain the bank-primitive cluster — gates,
header-preserving export, revision, scoping, storage management. The headline
theorem is `bundled_structure_forces_bank_primitives` in
[`WorldBridges.lean`](../EpArch/WorldBridges.lean). Its signature is
world-agnostic: it takes `SystemOperationalBundle`, `WorldBridgeBundle`, and
`SatisfiesAllProperties` — not `W_*` bundles directly. World bundles are the
natural source for the bridge data, but they are not formal preconditions.

## What the repo is made of

- **Substrate** — `Basic.lean`, `Header.lean`, `Bank.lean`, `WorldCtx.lean`,
  `Commitments.lean`, `Semantics/LTS.lean`, `Semantics/StepSemantics.lean`.
- **Forcing chain** — `Minimality.lean`, `Scenarios.lean`,
  `GroundedEvidence.lean`, `Convergence.lean`, `WorldBridges.lean`.
- **Witnesses** — `Concrete/*.lean`, `WorldWitness.lean`, `Feasibility.lean`.
- **Derived theorems** — `Theorems/*.lean` (withdrawal, headers, dissolutions,
  pathologies, diagnosability, behavioral equivalence, case bindings).
- **Meta** — `Meta/Modular.lean`, `Meta/TheoremTransport.lean`,
  `Meta/Tier4Transport.lean`, `Meta/Config.lean`, `Meta/ClusterRegistry.lean`,
  `Meta/Reconfiguration.lean`, `Meta/FalsifiableNotAuthorizable.lean`.
- **Optional** — `Meta/LeanKernel/*.lean` (Lean as a worked EpArch instance),
  `Meta/TheoryCoreClaim.lean` (theory-core token).

## Main proof route

The chain runs `Minimality.lean` (per-dimension semantic obstructions) →
`Scenarios.lean` (`Represents*` embeddings) → `GroundedEvidence.lean`
(`GroundedXStrict` consequences) → `Convergence.lean` (`StructurallyForced`,
`convergence_structural`) → `WorldBridges.lean`
(`bundled_structure_forces_bank_primitives`).

Read it from the top down, not the bottom up. Start at the capstone in
[`WorldBridges.lean`](../EpArch/WorldBridges.lean), then `convergence_structural`
in [`Convergence.lean`](../EpArch/Convergence.lean), and only then descend into
`Scenarios.lean`, `GroundedEvidence.lean`, and the per-dimension obstructions
in `Minimality.lean`. The lower layers carry the mathematical content but
front-load definitional scaffolding that is hard to read in isolation.

The walkthrough lives in [PROOF-STRUCTURE.md](PROOF-STRUCTURE.md).

## Three reading paths

- **"I want the headline claim."** Read `bundled_structure_forces_bank_primitives`
  in [`WorldBridges.lean`](../EpArch/WorldBridges.lean), then this file's
  *Main proof route* section.
- **"I want the operational model."** Read [architecture/SEMANTICS.md](architecture/SEMANTICS.md),
  then `Theorems/Withdrawal.lean`.
- **"I want the meta / modularity side."** Read [architecture/MODULARITY.md](architecture/MODULARITY.md),
  then [reference/THEOREMS.md](reference/THEOREMS.md).

## Boundaries

This file's boundary disclaimer is intentionally short; each architecture and
reference doc carries its own canonical scope statement.

- The architectural claim is not a uniqueness claim. Many systems can satisfy
  the bundles.
- World bundles are explicit assumptions, not assertions about reality. See
  [architecture/WORLD.md](architecture/WORLD.md).
- Concrete witnesses establish non-vacuity, not empirical correspondence. See
  [reference/WITNESS-SCOPE.md](reference/WITNESS-SCOPE.md).
- The optional Lean-kernel subtree is outside the core claim and carries the
  one named axiom. See [reference/AXIOMS.md](reference/AXIOMS.md) and
  [optional/LEAN-KERNEL.md](optional/LEAN-KERNEL.md).

## Go next

- [PROOF-STRUCTURE.md](PROOF-STRUCTURE.md) — reviewer proof-route walkthrough.
- [reference/THEOREMS.md](reference/THEOREMS.md) — theorem registry by family.

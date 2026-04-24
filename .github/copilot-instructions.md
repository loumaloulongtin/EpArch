# EpArch — Project Map

This file is a map. It tells an assistant where things are, so questions about the project can be answered without grepping blind.

## What this repo is

Lean 4 formalization of an epistemic architecture framework. No Mathlib dependency. Zero `axiom` declarations and zero `sorry`s on the `Main.lean` import surface. Build entrypoint is `Main.lean`; build command is `lake build`. The headline claim is structural: eight world-level constraint bundles are argued to be unavoidable features of any system coordinating knowledge under bounded verification, adversarial pressure, and multi-agent authorization; any working system satisfying them necessarily contains the bank-primitive cluster. The W_* bundles are explicit antecedents, not assumptions about any particular world — they are the constraints whose unavoidability is the domain-level argument.

## The capstone and the route to it

The capstone theorem is `bundled_structure_forces_bank_primitives` in [`EpArch/WorldBridges.lean`](../EpArch/WorldBridges.lean). The full route is documented in [`DOCS/PROOF-STRUCTURE.md`](../DOCS/PROOF-STRUCTURE.md).

The route is a five-layer chain:

| Layer    | File                                                                        | What it owns                                                                                            |
|----------|-----------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------|
| Layer 1  | [`EpArch/Minimality.lean`](../EpArch/Minimality.lean)                       | Abstract impossibility models and the eight per-dimension impossibility theorems                        |
| Layer 2  | [`EpArch/Scenarios.lean`](../EpArch/Scenarios.lean)                         | `Represents*` structures and the `_without_*_embeds` / `_forces_*` pairs                                |
| Layer 3a | [`EpArch/GroundedEvidence.lean`](../EpArch/GroundedEvidence.lean)           | `GroundedX` / `GroundedXStrict` evidence structures                                                     |
| Layer 3b | [`EpArch/Convergence.lean`](../EpArch/Convergence.lean)                     | `StructurallyForced`, `ForcingEmbedding`, `convergence_structural`                                      |
| Capstone | [`EpArch/WorldBridges.lean`](../EpArch/WorldBridges.lean)                   | `bundled_structure_forces_bank_primitives` — the world-assumption-free path                             |

The pragmatic reviewer entry is the other end: start with `StructurallyForced` in [`Convergence.lean`](../EpArch/Convergence.lean), then trace back.

## Where the rest of the proof surface lives

Eight families orbit the capstone. Each line names the canonical file(s); deeper references live in the docs.

- **Operational LTS / lifecycle gates.** [`EpArch/Semantics/StepSemantics.lean`](../EpArch/Semantics/StepSemantics.lean), [`EpArch/Semantics/LTS.lean`](../EpArch/Semantics/LTS.lean), [`EpArch/Theorems/Withdrawal.lean`](../EpArch/Theorems/Withdrawal.lean).
- **Eight architectural commitments (C1–C8).** [`EpArch/Commitments.lean`](../EpArch/Commitments.lean); concrete satisfiability in [`EpArch/Concrete/Commitments.lean`](../EpArch/Concrete/Commitments.lean).
- **World-bundle obligations.** [`EpArch/WorldCtx.lean`](../EpArch/WorldCtx.lean), [`EpArch/WorldBridges.lean`](../EpArch/WorldBridges.lean), [`EpArch/WorldWitness.lean`](../EpArch/WorldWitness.lean), [`EpArch/Adversarial/Obligations.lean`](../EpArch/Adversarial/Obligations.lean).
- **Health goals and autonomy / residual risk.** [`EpArch/Health.lean`](../EpArch/Health.lean), [`EpArch/ResidualRiskMitigation.lean`](../EpArch/ResidualRiskMitigation.lean), [`EpArch/Agent/Imposition.lean`](../EpArch/Agent/Imposition.lean).
- **Corroboration and independence.** [`EpArch/Agent/Corroboration.lean`](../EpArch/Agent/Corroboration.lean); architectural prose in [`DOCS/architecture/CORROBORATION.md`](../DOCS/architecture/CORROBORATION.md).
- **Adversarial mitigation.** [`EpArch/Adversarial/Base.lean`](../EpArch/Adversarial/Base.lean), [`EpArch/Adversarial/Concrete.lean`](../EpArch/Adversarial/Concrete.lean), [`EpArch/Adversarial/Obligations.lean`](../EpArch/Adversarial/Obligations.lean).
- **Diagnosability and behavioural equivalence.** [`EpArch/Theorems/Diagnosability.lean`](../EpArch/Theorems/Diagnosability.lean), [`EpArch/Theorems/Headers.lean`](../EpArch/Theorems/Headers.lean), [`EpArch/Theorems/BehavioralEquivalence.lean`](../EpArch/Theorems/BehavioralEquivalence.lean).
- **Pathology dissolutions (Gettier, Fake Barn, lottery, Moorean, …).** [`EpArch/Theorems/Cases/`](../EpArch/Theorems/Cases/), [`EpArch/Theorems/Dissolutions.lean`](../EpArch/Theorems/Dissolutions.lean), [`EpArch/Theorems/Pathologies.lean`](../EpArch/Theorems/Pathologies.lean).

Two cross-cutting surfaces:

- **Concrete witnesses (non-vacuity).** [`EpArch/Concrete/`](../EpArch/Concrete/), [`EpArch/WorldWitness.lean`](../EpArch/WorldWitness.lean), [`EpArch/Feasibility.lean`](../EpArch/Feasibility.lean). These discharge "the model has at least one inhabitant" obligations.
- **Meta / cluster / transport.** [`EpArch/Meta/ClusterRegistry.lean`](../EpArch/Meta/ClusterRegistry.lean), [`EpArch/Meta/Config.lean`](../EpArch/Meta/Config.lean), [`EpArch/Meta/TheoremTransport.lean`](../EpArch/Meta/TheoremTransport.lean), [`EpArch/Meta/Tier4Transport.lean`](../EpArch/Meta/Tier4Transport.lean), [`EpArch/Meta/Modular.lean`](../EpArch/Meta/Modular.lean). These reason about EpArch rather than inside it.

## Where core types and substrate live

- **Core types** (`Deposit`, `Bubble`, `Header`, `Agent`, S/E/V triples): [`EpArch/Basic.lean`](../EpArch/Basic.lean), [`EpArch/Header.lean`](../EpArch/Header.lean), [`EpArch/Bank.lean`](../EpArch/Bank.lean).
- **System spec and invariants:** [`EpArch/SystemSpec.lean`](../EpArch/SystemSpec.lean), [`EpArch/Invariants.lean`](../EpArch/Invariants.lean).
- **Agent constraints:** [`EpArch/Agent/Constraints.lean`](../EpArch/Agent/Constraints.lean).
- **Mechanisms:** [`EpArch/Mechanisms.lean`](../EpArch/Mechanisms.lean).

## The named axiom

The repository contains exactly one named axiom, `lean_kernel_verification_path`, in [`EpArch/Meta/LeanKernel/VerificationPath.lean`](../EpArch/Meta/LeanKernel/VerificationPath.lean). It is part of an optional self-application worked example and is not on `Main.lean`'s import surface. The full account is in [`DOCS/reference/AXIOMS.md`](../DOCS/reference/AXIOMS.md).

## Documentation map

The DOCS tree is the canonical destination for prose. Use this table to route a question to the right file before reading source.

| Question                                      | Doc                                                                                       |
|-----------------------------------------------|-------------------------------------------------------------------------------------------|
| Where do I start?                             | [`DOCS/START-HERE.md`](../DOCS/START-HERE.md)                                             |
| What's the proof route?                       | [`DOCS/PROOF-STRUCTURE.md`](../DOCS/PROOF-STRUCTURE.md)                                   |
| What does the operational semantics look like?| [`DOCS/architecture/SEMANTICS.md`](../DOCS/architecture/SEMANTICS.md)                     |
| What does `W_*` mean? What do bundles buy?    | [`DOCS/architecture/WORLD.md`](../DOCS/architecture/WORLD.md)                             |
| Are the constraints satisfiable?              | [`DOCS/architecture/FEASIBILITY.md`](../DOCS/architecture/FEASIBILITY.md)                 |
| Multi-source corroboration / independence?    | [`DOCS/architecture/CORROBORATION.md`](../DOCS/architecture/CORROBORATION.md)             |
| Cluster families, projection, modularity?     | [`DOCS/architecture/MODULARITY.md`](../DOCS/architecture/MODULARITY.md)                   |
| Where is theorem T proved?                    | [`DOCS/reference/THEOREMS.md`](../DOCS/reference/THEOREMS.md)                             |
| What is the axiom story?                      | [`DOCS/reference/AXIOMS.md`](../DOCS/reference/AXIOMS.md)                                 |
| What do the concrete witnesses buy?           | [`DOCS/reference/WITNESS-SCOPE.md`](../DOCS/reference/WITNESS-SCOPE.md)                   |
| Which file owns module M?                     | [`DOCS/reference/FILE-INVENTORY.md`](../DOCS/reference/FILE-INVENTORY.md)                 |
| Worked corroboration / cross-domain cases?    | [`DOCS/cases/CASE-STUDIES.md`](../DOCS/cases/CASE-STUDIES.md)                             |
| Lean kernel as an EpArch instance?            | [`DOCS/optional/LEAN-KERNEL.md`](../DOCS/optional/LEAN-KERNEL.md)                         |
| The DOCS index itself                         | [`DOCS/README.md`](../DOCS/README.md)                                                     |
| What does the framework *not* claim?          | [`DOCS/architecture/WORLD.md`](../DOCS/architecture/WORLD.md), [`DOCS/reference/WITNESS-SCOPE.md`](../DOCS/reference/WITNESS-SCOPE.md) |
| Are the constraints opt-in / avoidable?       | [`DOCS/architecture/WORLD.md`](../DOCS/architecture/WORLD.md)                             |
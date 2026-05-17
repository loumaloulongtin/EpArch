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
| Want the architectural intuition (prose walk) | [`theory/README.md`](../theory/README.md)                                                 |

## The `theory/` companion — a third register

The repository carries a third prose layer alongside the Lean source and DOCS:
the [`theory/`](../theory/) tree. It is **optional but recommended**, and it
does a job neither the kernel nor DOCS does.

| Layer       | Job                                                                                              |
|-------------|--------------------------------------------------------------------------------------------------|
| Lean source | Authoritative — what is forced, machine-checked, and what each constructor commits to.           |
| `DOCS/`     | The kernel's own map of itself — reader routes, theorem registry, layer descriptions, scope.     |
| `theory/`   | The architecture's running commentary on itself — narrative walk in a register the proof avoids. |

The three layers are **complementary, not redundant**. The kernel proves more
than `theory/` translates back; `theory/` explains more than the kernel needs
to say in its own register; `DOCS/` indexes both. A reader may take them in
any order or alongside each other.

### Conventions for `theory/`

`theory/` operates under a deliberately **different discipline** from
`DOCS/`. The DOCS anti-patterns about "process narration", "scope
disclaimers", and "what you won't find here" sections **do not transfer**
to `theory/` — that register is built on exactly those moves and uses them
as load-bearing. Specifically, in `theory/`:

- Files are **narrative**, with named opening stories ("the friends and the
  window", "the night-nurse story", "the scale model story"). This voice is
  intentional and should be preserved.
- Each cluster has a **hub file** (`theory/<cluster>/<cluster>.md`) plus
  spokes. The hub opens with a cluster list; spokes carry `← prev`, `↑ hub`,
  `next →` navigation.
- Files end with a **forward link** to the next file in the walk. The chain
  is: `world → bubble → agent → forcing → goals → autonomy → concrete → meta`.
- Each cluster hub ends with a single **`*Proof-side companion: …*`** line
  pointing into `DOCS/` or to a named Lean entry theorem. Add one when
  creating a new hub; do not bloat it into a full cross-reference table.

The discipline that **does** transfer from DOCS to `theory/`:

- No task or sprint references (`T25`, `§T26a`) — reference named items.
- No version history or authorship lines.
- No theorem-count quotations that will go stale (use "current count is in
  `lake build`" if the count is needed at all).
- Scope notes (the "does not buy" / "what this leaves open" sections) are
  **load-bearing** and must be preserved, exactly as in DOCS. They close
  overclaiming and underspecifying attacks on the prose.

### Cross-register rules

- `theory/` may cite Lean files for what is forced and DOCS files for what is
  registered, but should not duplicate either's job. Do not paste theorem
  registries into `theory/`; do not paste `theory/` narrative into DOCS.
- DOCS architecture files may carry a single `*Companion in theory: …*`
  bullet in their `## Go next` section pointing to the matching theory hub.
  This is the only DOCS-side mention of `theory/` that belongs in the
  architecture files; the README and START-HERE carry the broader framing.
- `theory/` is read as Markdown. Do not add a build target, PDF artefact,
  or any reference to one inside this repository.
/-
Main.lean — Full Build Surface for EpArch

## What This Project Is

EpArch formalizes the paper "Epistemic Architecture: A Constraints-and-
Objectives Framework for Bounded Agents Under Adversarial Pressure."
The paper argues that knowledge
management in the real world (science, law, journalism, etc.) converges on
a common architecture — not because anyone designed it, but because the
constraints of imperfect agents under permanent challenge pressure force
a specific set of structural features.

The formalization proves these claims:
1. Six constraints (distributed agents, bounded audit, export across boundaries,
   adversarial pressure, coordination need, truth pressure) each force a specific
   architectural feature (bubbles, trust bridges, headers, revocation, shared
   ledger, redeemability).
2. Removing any feature breaks a necessary property (impossibility theorems).
3. All knowledge-managing systems satisfying the constraints converge on the
   same primitive cluster (convergence theorem).

## Core Domain Concepts (Glossary)

- **Deposit**: A claim bundled with its validation metadata (header). Analogous
  to a bank deposit: you "deposit" a knowledge claim into a shared ledger,
  and others can "withdraw" (rely on) it.

- **Header (S/E/V/τ/acl/redeem)**: The metadata attached to every deposit.
  S = Standard (acceptance threshold), E = Error Model (known failure modes),
  V = Provenance (evidence chain), τ = temporal validity, acl = access control,
  redeem = redeemability path.

- **Bubble**: A scoped validation domain — a community with its own acceptance
  standards. Think: a scientific field, a legal jurisdiction, a newsroom.
  Claims validated in one bubble may need revalidation when exported to another.

- **Bank**: The shared ledger of deposits within a bubble. This is what
  distinguishes knowledge (publicly recorded, challengeable) from mere certainty
  (private conviction).

- **Ladder**: An agent's internal certainty progression
  (Denial → Doubt → Ignorance → Belief → Certainty). This is private
  mental state, NOT the Bank. The paper's key claim: "traction" (feeling
  sure, Ladder) is distinct from "authorization" (having a valid deposit,
  Bank).

- **PRP (Permanent Redeemability Pressure)**: The constraint that challenges
  never stop. There is always another challenge coming, and sometimes it
  exceeds the agent's verification budget. This forces ongoing revision.

- **Competition Gate**: The key impossibility result — domains that structurally
  prohibit revision (Challenge/Revoke actions) cannot self-correct.

- **Export Gate**: Deposits carry headers when crossing bubble boundaries
  (export requires header preservation). On the receiving side, import
  requires either a trust bridge (pre-established permission) or
  full revalidation against the target bubble's standards.

## Recommended Reading Order

1. **Basic.lean** — Core types: Agent, Claim, Bubble, Deposit, Header, Field, etc.
2. **Header.lean** — The S/E/V/τ/acl/redeem header structure and observational
   completeness theorems.
3. **Bank.lean** — Bank substrate: lifecycle operators (Validate, Challenge,
   Repair, Revoke, etc.) as concrete guarded definitions.
4. **LTS.lean** — Generic labeled transition systems, traces, invariants,
   refinement, and safety preservation.
5. **StepSemantics.lean** — The constructive operational semantics: SystemState,
   Action, Step relation, competition gate theorem.
6. **Commitments.lean** — Eight architectural commitments (structural requirements
   for conforming epistemic systems, expressed as fields of `CommitmentsCtx`).
7. **Minimality.lean** — The convergence/impossibility theorems: constraints force
   features, removal breaks properties.
8. **WorldCtx.lean** — Parametric world semantics: the interface through which
   world-level assumptions (lies possible, bounded verification, partial
   observability) enter the formalization.
9. **RevisionSafety.lean** — Safe extensions: adding constraints doesn't break
   existing theorems (the Compatible/transport_core machinery).
10. **Theorems.lean** — Derived theorems: withdrawal gates, epistemology diagnoses
    (Gettier, Fake Barn, Lottery, etc.), competition gate corners.
11. **ConcreteLedgerModel.lean** — A constructive zero-axiom concrete model that
    witnesses satisfiability of all commitments. This proves non-vacuity.
12. **PaperFacing.lean** — The stable public API: re-exports all paper-facing
    theorems in one place.

## Architecture (Dependency Layers)

Layers group files by semantic role, not minimal import depth.
No file imports from a layer above its own.

```
Layer 0 (Types):      Basic, Header
Layer 1 (Substrate):  Bank, LTS, WorldCtx
Layer 2 (Semantics):  StepSemantics, RevisionSafety, Predictions, WorkedTraces, World (deprecated)
Layer 3 (Theory):     Commitments, SystemSpec, Invariants, Minimality
Layer 4 (Derived):    Theorems, Diagnosability, Health, ScopeIrrelevance
Layer 5 (Agent):      Mechanisms, Agent/{Constraints, Imposition, Resilience, Corroboration}
Layer 6 (Witness):    WorldWitness, ConcreteLedgerModel, Realizer, Feasibility
Layer 7 (Adversarial): AdversarialBase, AdversarialObligations
Layer 8 (Meta):       Meta/*
Layer 9 (Surface):    PaperFacing
Layer 10 (Modularity): Modularity
```

## Build Surfaces

| Surface | Import | Description |
|---------|--------|-------------|
| **Paper-Facing** | `MainPaper.lean` | Core-facing theorems only |
| **Full** | `Main.lean` | Full build |

## Axiom Declarations

The formalization contains **zero `axiom` declarations**. The four structural
commitments are expressed as fields of `CommitmentsCtx` (a hypothesis bundle
modelled on `WorldCtx`); forward theorems are stated as:

    theorem T (C : CommitmentsCtx ...) ...

and hold for any conforming architecture. Opaque domain primitives
(`certainty_L`, `knowledge_B`, `sticky`, etc.) are uninterpreted constants,
not `axiom` declarations.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments
import EpArch.SystemSpec
import EpArch.Theorems
import EpArch.Minimality
import EpArch.AdversarialBase  -- Base types/structures (no axioms)
import EpArch.Invariants
import EpArch.WorkedTraces
import EpArch.Predictions
import EpArch.StepSemantics
import EpArch.Diagnosability  -- principled observability
import EpArch.ConcreteLedgerModel  -- Full model now compiles
import EpArch.World  -- World layer for obligation theorems
import EpArch.WorldWitness  -- Non-vacuity witness for world bundles
import EpArch.AdversarialObligations  -- Adversarial axioms → obligation theorems
import EpArch.LTS  -- Generic LTS for revision safety
import EpArch.RevisionSafety  -- Revision safety meta-theorems
import EpArch.Health  -- Health predicates and necessity theorems
import EpArch.Mechanisms  -- Canonical mechanism predicates
import EpArch.ScopeIrrelevance  -- Scope/irrelevance theorems
import EpArch.PaperFacing  -- Paper-facing surface exports
import EpArch.Agent  -- Agent constraints interface (PRP, design-imposition)
import EpArch.Realizer  -- Feasibility: System realizer interface
import EpArch.Feasibility  -- Feasibility: Joint non-vacuity theorem
import EpArch.Meta.FalsifiableNotAuthorizable  -- Meta-status proof pack
import EpArch.Meta.TheoryCoreClaim  -- Optional stretch: theory_core claim token
import EpArch.Meta.TheoremTransport  -- Generic theorem transport schema (Tier 3 closure)
import EpArch.Meta.Tier4Transport    -- Main theorem library transport (Tier 4 closure)
import EpArch.Modularity  -- Lattice-stability: graceful scale-down + sub-level RevisionSafety
import EpArch.Meta.Modular     -- Modularity meta-theorem: ∀ S ⊆ constraints, projection_valid S
import EpArch.Meta.Config      -- Configurable certification engine: EpArchConfig → ClusterTag → certified proof

def main : IO Unit :=
  IO.println s!"EpArch: Epistemic Architecture Formalization"

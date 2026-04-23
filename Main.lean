/-
Main.lean — Full Build Surface for EpArch

## What This Project Is

EpArch is a machine-checked constraints-and-objectives framework for
bounded epistemic systems under adversarial pressure.
Knowledge management in the real world (science, law, journalism, etc.) converges on
a common architecture — not because anyone designed it, but because the
constraints of imperfect agents under permanent challenge pressure force
a specific set of structural features.

The formalization proves these claims:
1. Eight constraints (distributed agents, bounded audit, export across boundaries,
   adversarial pressure, coordination need, truth pressure, multi-agent authorization,
   bounded storage management)
   each force a specific architectural feature (bubbles, trust bridges, headers,
   revocation, shared ledger, redeemability, granular ACL, storage management).
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
  mental state, NOT the Bank. Key claim: "traction" (feeling
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

1. **EpArch.Basic** — Core types: Agent, Claim, Bubble, Deposit, Header, Field, etc.
2. **EpArch.Header** — The S/E/V/τ/acl/redeem header structure and observational
   completeness theorems.
3. **EpArch.Bank** — Bank substrate: lifecycle operators (Promote, Challenge,
   Repair, Revoke, etc.) as concrete guarded definitions.
4. **EpArch.Semantics.LTS** — Generic labeled transition systems, traces, invariants,
   refinement, and safety preservation.
5. **EpArch.Semantics.StepSemantics** — The constructive operational semantics: SystemState,
   Action, Step relation, competition gate theorem.
6. **EpArch.Commitments** — Eight architectural commitments (all proved as standalone
   theorems; `commitments_pack` bundles the unconditional ones).
7. **EpArch.Minimality** — The convergence/impossibility theorems: constraints force
   features, removal breaks properties.
8. **EpArch.WorldCtx** — Parametric world semantics: the interface through which
   world-level assumptions (lies possible, bounded verification, partial
   observability) enter the formalization.
9. **EpArch.Semantics.RevisionSafety** — Safe extensions: adding constraints doesn't break
   existing theorems (the Compatible/transport_core machinery).
10. **Theorems/** — Derived theorems, split into ten focused modules:
    - **Withdrawal** — Withdrawal gates, repair lifecycle, diagnosis infrastructure
    - **Cases/** — Classic epistemology case types, one file per case (open for contributions):
      `Gettier`, `FakeBarn`, `Standard`, `VacuousStandard`, `TypeErrors` (Lottery, Confabulation)
    - **Headers** — Diagnosability metrics, field checkability, header-dispute link
    - **Modal** — WorldCtx-parameterized modal cases (Safety↔V, Sensitivity↔E)
    - **Dissolutions** — Type-separation dissolutions (closure, luminosity, Moorean,
      preface, trace-level), progress metrics, dissolution criteria
    - **Pathologies** — Literature pathology diagnoses (testimony through extended
      cognition), bridge theorems, pathology summary table
    - **Strip** — All stripping results: provenance loss (`stripV`/`Payload`) and
      header loss (`strip`/`PayloadStripped`); competition gate corners 3, 4, 10
    - **Corners** — Corner theorems 1, 2, 6, 7, 8, 9; entrenchment;
      lottery *gate* (operational: `lottery_no_deposit_blocks_withdraw`, `lottery_paradox_dissolved_architecturally`);
      cf. `EpArch.Theorems.Cases.TypeErrors` for the type-error *diagnosis* side
    - **Diagnosability** — Observability-based diagnosability ordering
    - **BehavioralEquivalence** — Observation-boundary equivalence; `working_systems_equivalent`
11. **EpArch/Concrete/** — Zero-axiom constructive witnesses split into seven focused
    modules (Types, Commitments, WorkingSystem, DeficientSystems, NonVacuity,
    Realizer, VerificationDepth).
    Together they prove non-vacuity for all commitments.

## Architecture (Dependency Layers)

Layers group files by semantic role, not minimal import depth.
No file imports from a layer above its own.

```
Layer 0 (Types):      Basic, Header
Layer 1 (Substrate):  Bank, Semantics/LTS, WorldCtx
Layer 2 (Semantics):  Semantics/StepSemantics, Semantics/RevisionSafety
Layer 3 (Theory):     Commitments, SystemSpec, Invariants, Minimality, Convergence, Scenarios
Layer 4 (Derived):    Theorems/{Withdrawal,Cases,Headers,Modal,Dissolutions,Pathologies,Strip,Corners,Diagnosability,BehavioralEquivalence}, Health, Semantics/ScopeIrrelevance
Layer 5 (Agent):      ConditionalPredictions, Mechanisms, Agent/{Constraints, Imposition, Resilience, Corroboration}
Layer 6 (Witness):    WorldWitness, WorldBridges, Concrete/{Types,Commitments,WorkingSystem,DeficientSystems,NonVacuity}, Concrete/Realizer, Feasibility
Layer 7 (Adversarial): Adversarial/{Base, Obligations, Concrete}
Layer 8 (Meta):       Meta/* (incl. Meta/Modular, Meta/Config, Meta/TheoremTransport, Meta/LeanKernel/*)
```

## Build Surface

`lake build` (via Main) is the single build target.

## Axiom Declarations

The formalization contains **zero `axiom` declarations**. All 8 structural commitments
are proved standalone theorems.  C1 (Traction/Authorization Split) is proved by
`innovation_allows_traction_without_authorization` and
`caveated_authorization_does_not_force_certainty`.  Some domain primitives are
`opaque` constants (e.g., `agentTraction`, `ignores_bank_signal`, `pushback`,
`τ_compress`, `V_spoof`, and the performance/adversarial-pressure opaques in
`Theorems.Dissolutions` / `Theorems.Pathologies` / `Adversarial.Base`); others, including `certainty_L` and
`knowledge_B`, are ordinary `def`s grounded in their respective types.
None are `axiom` declarations.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments
import EpArch.SystemSpec
import EpArch.Theorems.Withdrawal
import EpArch.Theorems.Cases.Gettier
import EpArch.Theorems.Cases.FakeBarn
import EpArch.Theorems.Cases.Standard
import EpArch.Theorems.Cases.VacuousStandard
import EpArch.Theorems.Cases.TypeErrors
import EpArch.Theorems.Headers
import EpArch.Theorems.Modal
import EpArch.Theorems.Dissolutions
import EpArch.Theorems.Pathologies
import EpArch.Theorems.Strip
import EpArch.Theorems.Corners
import EpArch.Minimality
import EpArch.Theorems.BehavioralEquivalence
import EpArch.Convergence
import EpArch.Adversarial.Base  -- Base types/structures (no axioms)
import EpArch.Adversarial.Concrete  -- Concrete attack mitigation proofs
import EpArch.Invariants
import EpArch.ConditionalPredictions
import EpArch.Semantics.StepSemantics
import EpArch.Theorems.Diagnosability  -- principled observability
import EpArch.Concrete.Types
import EpArch.Concrete.Commitments
import EpArch.Concrete.WorkingSystem
import EpArch.Concrete.DeficientSystems
import EpArch.Concrete.NonVacuity
import EpArch.WorldWitness  -- Non-vacuity witness for world bundles
import EpArch.Adversarial.Obligations  -- Adversarial axioms → obligation theorems
import EpArch.Semantics.LTS  -- Generic LTS for revision safety
import EpArch.Semantics.RevisionSafety  -- Revision safety meta-theorems
import EpArch.Health  -- Health predicates and necessity theorems
import EpArch.ResidualRiskMitigation  -- Residual-risk mitigation coverage and relative minimality
import EpArch.Mechanisms  -- Canonical mechanism predicates
import EpArch.Semantics.ScopeIrrelevance  -- Scope/irrelevance theorems
import EpArch.Agent.Constraints   -- AgentConstraints, PRP, PRP theorems
import EpArch.Agent.Imposition    -- Design-forcing theorems
import EpArch.Agent.PatternExamples -- Pedagogical annex: concrete pattern instantiations
import EpArch.Agent.Resilience    -- Fault events, LTS, containment proofs
import EpArch.Agent.Corroboration -- Multi-agent corroboration theorems
import EpArch.Concrete.Realizer  -- Feasibility: System realizer interface
import EpArch.Feasibility  -- Feasibility: Joint non-vacuity theorem
import EpArch.WorldBridges  -- World-to-structural bridges + headline convergence
import EpArch.Meta.FalsifiableNotAuthorizable  -- Meta-status proof pack
import EpArch.Meta.TheoryCoreClaim  -- Optional stretch: theory_core claim token
import EpArch.Meta.TheoremTransport  -- Generic theorem transport schema (Tier 3 closure)
import EpArch.Meta.Tier4Transport    -- Main theorem library transport (Tier 4 closure)
import EpArch.Meta.LeanKernel.OdometerModel  -- Odometer sub-model: concrete minimal EpArch instance
import EpArch.Meta.Modular     -- Modularity meta-theorem: ∀ S ⊆ constraints, projection_valid S
import EpArch.Meta.Reconfiguration  -- Safe reconfiguration: addX × 8, quarantine gate, no-self-heal
import EpArch.Meta.Config      -- Configurable certification engine: EpArchConfig → ClusterTag → certified proof
import EpArch.Meta.LeanKernel.World     -- Self-referential: Lean kernel world + architecture + OleanStaleness
import EpArch.Meta.LeanKernel.SFailure     -- Lean kernel S-field failure taxonomy
import EpArch.Meta.LeanKernel.RepairLoop   -- Full S/E/V lifecycle witness: repair loop proved and self-instantiated
import EpArch.Theorems.NotationBridge      -- Notation bridge authorization (Layers 2, 3, Gettier)

/-- Entry point: confirms the formalization compiles and prints a banner. -/
def main : IO Unit :=
  IO.println s!"EpArch: Epistemic Architecture Formalization"

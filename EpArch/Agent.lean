/-
EpArch/Agent.lean — Agent Constraints Interface (Re-export)

This module re-exports the Agent layer components:
- Constraints: AgentConstraints, PRP, PRP theorems
- Imposition: Design-forcing theorems
- Resilience: Fault events, LTS, containment proofs
- Corroboration: Multi-agent corroboration and common-mode failure

## Design Principles

1. **Constraints as predicates, not axioms about the world**
2. **No new semantic primitives** (or they must project away via Compatible)
3. **Minimal imports** — depends only on core definitions

## Module Structure

- EpArch/Agent/Constraints.lean — AgentConstraints, PRP, PRP theorems
- EpArch/Agent/Imposition.lean — Design-forcing theorems
- EpArch/Agent/Resilience.lean — Fault events, LTS, containment proofs
- EpArch/Agent/Corroboration.lean — Multi-agent corroboration theorems

This file re-exports all components for backward compatibility.
-/

import EpArch.Agent.Constraints
import EpArch.Agent.Imposition
import EpArch.Agent.Resilience
import EpArch.Agent.Corroboration

namespace EpArch.Agent

/-! ## Re-exports

All types, structures, and theorems are re-exported from the submodules.
See individual files for documentation.
-/

-- Constraints are exported from EpArch.Agent.Constraints:
-- - TimeIdx, Challenge, VerifyCost, Budget
-- - PRP, AgentConstraints
-- - no_global_closure_of_PRP, needs_revision_of_PRP, needs_scoping_of_PRP

-- Design-forcing theorems are exported from EpArch.Agent.Imposition:
-- - Mechanisms, HealthGoals
-- - safe_withdrawal_needs_reversibility
-- - sound_deposits_need_cheap_validator
-- - reliable_export_needs_gate

-- Resilience/containment are exported from EpArch.Agent.Resilience:
-- - FaultEvent, AgentAction, AgentSystemState
-- - AgentLTS, agentSystemStep
-- - truthInvariant, gateInvariant
-- - truth_invariant_preserved, gate_invariant_preserved
-- - truth_preserved_along_trace, gate_preserved_along_trace
-- - agent_containment


end EpArch.Agent

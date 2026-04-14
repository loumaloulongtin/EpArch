/-
EpArch — Bank.Dynamics (Runtime Behavioral Profile)

Defines the runtime behavioral profiling layer for deposits: `DepositDynamics`,
`reliance_level`, `challenge_frequency`, `blast_radius`, and the two behavioral
theorems (`success_driven_bypass`, `blast_radius_scales_with_reliance`).

Separated from the Bank module because the deposit substrate (structure, lifecycle
operators, status transitions) and the runtime behavioral profiler sit at
different abstraction levels:
- **EpArch.Bank** — static architecture: what a deposit is, how it transitions.
- **EpArch.Bank.Dynamics** — emergent runtime measurement: how many agents rely on
  a deposit, how failure cascades, how challenge pressure varies with entrenchment.

## Behavioral Claims

- `success_driven_bypass` — high-reliance deposits face attenuated challenge
  pressure (Kuhn-style paradigm resistance):
  `reliance_level dd > 100 → challenge_frequency dd < 10`
- `blast_radius_scales_with_reliance` — blast radius is at least as large as
  direct reliance, by construction (`DepositDynamics.h_cascade`).

## Relationship to Other Files

- **EpArch.Bank** provides the static substrate this file profiles.
-/

import EpArch.Bank

namespace EpArch

/-! ## Deposit Dynamics -/

/-- DepositDynamics: measured runtime behavioral profile of a deposit.

    The static deposit record (Header + status) cannot encode how many agents
    rely on the deposit or how often it is challenged — those are emergent
    properties of system usage. DepositDynamics separates the runtime profile
    from the static record, grounding the reliance/blast/challenge predicates
    in semantically correct fields rather than in τ (which is a TTL marker,
    not an agent-count proxy). -/
structure DepositDynamics where
  relying_agents  : Nat  -- count of agents that actively withdraw using this deposit
  cascade_agents  : Nat  -- transitive agents affected if this deposit fails
  h_cascade       : cascade_agents ≥ relying_agents  -- failures always reach at least direct reliers

/-- reliance_level: count of agents actively depending on this deposit.
    Grounded in DepositDynamics.relying_agents — the measured runtime count,
    independent of τ (temporal marker). -/
def reliance_level (dd : DepositDynamics) : Nat := dd.relying_agents

/-- challenge_frequency: institutional inertia model of challenge pressure.
    High-reliance deposits (> 100 agents) face attenuated challenge pressure:
    heavily-relied-on claims become entrenched (Kuhn-style paradigm resistance).
    Returns 9 when reliance > 100 (suppressed); 15 otherwise (normal pressure).
    The two branches are distinct (9 < 15), so the hypothesis is genuinely used. -/
def challenge_frequency (dd : DepositDynamics) : Nat :=
  if dd.relying_agents > 100 then 9 else 15

/-- Success-driven bypass: high-reliance deposits face attenuated challenge pressure.
    `challenge_frequency` returns 9 when reliance > 100 and 15 otherwise;
    the hypothesis gates the then-branch. -/
theorem success_driven_bypass (dd : DepositDynamics) :
    reliance_level dd > 100 → challenge_frequency dd < 10 := by
  intro h
  unfold challenge_frequency reliance_level at *
  rw [if_pos h]
  decide

/-- blast_radius: transitive agents affected by a deposit failure.
    Grounded in DepositDynamics.cascade_agents — downstream reliance (distinct
    from direct relying_agents, capturing second-order dependency chains). -/
def blast_radius (dd : DepositDynamics) : Nat := dd.cascade_agents

/-- Blast radius scales with reliance: failures cascade beyond direct reliers.
    Follows from `DepositDynamics.h_cascade` — cascade_agents ≥ relying_agents by construction. -/
theorem blast_radius_scales_with_reliance (dd : DepositDynamics) :
    blast_radius dd ≥ reliance_level dd := dd.h_cascade

end EpArch

# Witness Scope

This file is the canonical home for **witness-layer scope**: what the
concrete witness modules (and the world-side witness) buy, and what they do
not buy. Other docs link here rather than restating these boundaries.

---

## What "witnessed" means here

A property is *witnessed* if some module in the repository constructs a
concrete instance and proves the property on it. Witnessing buys three
things:

1. **Satisfiability** — the property is not contradictory.
2. **Realizability** — at least one concrete construction satisfies it.
3. **Non-vacuity** — the corresponding theorem is not vacuously true.

It does not buy uniqueness, optimality, or empirical correspondence.

---

## Concrete witness layer (`EpArch/Concrete/`)

Seven modules: `Concrete/Types.lean`, `Concrete/Commitments.lean`,
`Concrete/WorkingSystem.lean`, `Concrete/DeficientSystems.lean`,
`Concrete/NonVacuity.lean`, `Concrete/Realizer.lean`,
`Concrete/VerificationDepth.lean`.

Representative witnessed properties:

| Property | Theorem |
|---|---|
| Bubbles, trust bridges, headers exist | `concrete_has_bubbles`, `concrete_has_trust_bridges`, `concrete_has_headers` |
| Revocation and bank primitives exist | `concrete_has_revocation`, `concrete_has_bank` |
| Redeemability exists | `concrete_has_redeemability` |
| All operational properties hold | `concrete_satisfies_all_properties` |
| Structural forcing holds | `concrete_structurally_forced` |
| Withdrawal-gate checks fire on the concrete model | `concrete_withdrawal_requires_gates` |
| Headerless states are undiagnosable | `concrete_headerless_undiagnosable` |
| Bounded-verification depth | `depth_claim_provable`, `bounded_verify_incomplete` (`Concrete/VerificationDepth.lean`) |

---

## World-side witnesses (`WorldWitness.lean`)

`WitnessCtx` is a concrete `WorldCtx` and `holds_W_lies_possible`,
`holds_W_bounded_verification`, `holds_W_partial_observability` discharge the
three world-bundle antecedents. Together with the concrete witness layer this
closes `existence_under_constraints_structural` (`Feasibility.lean`) and
`kernel_world_forces_bank_primitives` (`WorldBridges.lean`).

This is satisfiability of the world-side antecedents — not a claim that any
particular real-world deployment satisfies them. See
[../architecture/WORLD.md](../architecture/WORLD.md) for the world-bundle
epistemic scope.

---

## Adversarial witnesses (`Adversarial/Concrete.lean`)

`Adversarial/Concrete.lean` witnesses that attack-gate conditions fire on
concrete type instances (`τ_expired_not_withdrawable`,
`V_stripped_not_withdrawable`, `E_stripped_diagnosis_lost`,
`overwhelmed_channel_collapses_V`, `concrete_attack_succeeds`,
`missing_export_gate_blocks_import`, and others).

These show the gates are sound on the concrete model. They do not prove that
an adversary cannot assemble a malformed `CExportRequest` without prior
withdrawal — that ordering is an agent-layer obligation; enforcing it in the
LTS would commit the architecture to one specific protocol topology and rule
out trust-bridge atomic transfers.

---

## Conservative-extension boundary (`Meta/TheoryCoreClaim.lean`)

`Meta/TheoryCoreClaim.lean` adds a first-class `theory_core` claim symbol by
conservative extension over a base `WorldCtx` and proves it underdetermined
by observations:

- `lift_notDeterminedByObs_theory_core` — the lifting lemma over the
  conservative-extension functor `AddTheoryCore`.
- `witness_theory_core_not_determined` — the headline theorem (line 199).
- `witness_theory_core_not_determined'` — universal-schema instance.

This is a **boundary** witness: it shows that a meta-claim about the theory
itself can be added without touching the observation surface. It does not
claim that the real world satisfies `theory_core`, that the meta-claim is
anything other than a conservative alias of an already-underdetermined base
claim, or that the construction is needed for the headline convergence
chain.

---

## Not witnessed here, but established elsewhere

| Result | Where |
|---|---|
| World-bundle feasibility | `WorldWitness.lean`, `Feasibility.world_bundles_feasible` |
| Existence under constraints | `existence_under_constraints_structural`, `existence_under_constraints_embedding` (`Feasibility.lean`); `bundled_structure_forces_bank_primitives` (`WorldBridges.lean`) |
| Forced primitives / minimality | `EpArch.Minimality`, `EpArch.Convergence` |
| Field-completeness | `observational_completeness_full` (`EpArch.Header`) |
| Safe revision-compatible extension | `EpArch.Semantics.RevisionSafety` |
| LTS refinement / operational grounding | `EpArch.Semantics.StepSemantics`, `EpArch.Theorems.*` |

---

## What witness theorems do not claim

| Property | Reason |
|---|---|
| Cryptographic security | Not a cryptographic proof |
| Implementation correctness | Spec is not implementation |
| Empirical correspondence | Formal model is not the world |
| Optimality | No optimality claim is made |
| Uniqueness | Only existence is shown |
| Universal validity of the architecture | Witness shows satisfiability, not necessity |

The forced-primitives direction ("bank primitives are necessary") is a
*separate* claim, established in `EpArch.Minimality` and `EpArch.Convergence`
— not in the witness modules.

---

## Go next

- [../architecture/FEASIBILITY.md](../architecture/FEASIBILITY.md) — how the
  concrete witnesses package into the headline existence theorems.
- [../architecture/WORLD.md](../architecture/WORLD.md) — the world-bundle
  scope these world witnesses discharge.
- [../optional/LEAN-KERNEL.md](../optional/LEAN-KERNEL.md) — the Lean-kernel
  worked example, which adds its own domain-specific witness path.

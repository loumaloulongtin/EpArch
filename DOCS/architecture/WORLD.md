# World Layer

The world layer is a parametric semantic interface (`WorldCtx`), not a
concrete model of reality. Its job is to convert world-side assumptions into
named bundles `W_*` so that each architectural obligation can be stated as a
conditional theorem `W_* → obligation` instead of an unconditional axiom.

This is the canonical home for the **world-bundle epistemic scope** — what
the `W_*` antecedents do and do not commit the framework to. Other files
(WITNESS-SCOPE, FEASIBILITY) link here rather than restating it.

---

## What `WorldCtx` is

`WorldCtx` is a record with parametric fields `World`, `Agent`, `Claim`,
`Obs`, `Truth`, `Utter`, `obs`, `VerifyWithin`, `effectiveTime`, plus
three inhabitedness witnesses (`world_inhabited`, `agent_inhabited`,
`claim_inhabited`). Theorems are stated over `(C : WorldCtx)` and access
primitives as `C.Truth`, `C.obs`, `C.Agent`, etc.

A few derived notions are defined directly from the interface:

| Notion | Definition |
|---|---|
| `Lie w a P` | `Utter a P ∧ ¬Truth w P` |
| `PartialObs w0 w1` | `obs w0 = obs w1` |
| `NotDeterminedByObs P` | `∃ w0 w1, PartialObs w0 w1 ∧ (Truth w0 P ↔ ¬Truth w1 P)` |
| `RequiresSteps w P k` | `∀ t < k, ¬VerifyWithin w P t` |

These are the minimum derived notions the obligation theorems use.

---

## The three core world-to-structural bundles

Three `W_*` structures in `WorldCtx.lean` package conditions on a
`WorldCtx` and each independently forces one structural feature of the
convergence chain. They are *conditions* — some instantiations satisfy
them, others (like a degenerate `TrivialCtx` with `Truth w P = True`
always) provably do not. `W_asymmetric_costs` is also in `WorldCtx.lean`.
Additional adversarial `W_*` bundles (`W_spoofedV`, `W_lies_scale`,
`W_ddos`, and others) live in `Adversarial/Obligations.lean` and enable
the adversarial obligation theorems; they do not drive the structural
convergence chain.

### `W_lies_possible`
```
some_false             : ∃ w P, ¬C.Truth w P
unrestricted_utterance : ∀ a P, C.Utter a P
```
False propositions exist; agents can utter arbitrary claims. Grounds the
revocation-primitive forcing argument via `w_lies_forces_revocation_need`.

### `W_bounded_verification`
```
verification_has_cost : ∃ P k, k > 0 ∧ ∀ w, C.RequiresSteps w P k
```
Some verification has non-trivial cost. Grounds the trust-bridge forcing
argument via `w_bounded_forces_incompleteness`.

### `W_partial_observability`
```
obs_underdetermines : ∃ P, C.NotDeterminedByObs P
```
Observation does not settle every claim. Grounds the redeemability forcing
argument via `w_partial_obs_forces_redeemability`.

Each bundle independently forces its own architectural conclusion — none
needs the others to do its work. The "all three" requirement appears only in
the top-level convergence theorem `world_assumptions_force_bank_primitives`,
where each bundle discharges exactly one of the three world-conditioned
features inside `containsBankPrimitives`.

---

## Obligation-theorem shape

The standard pattern for world-conditioned obligation theorems is:

| Pattern | Meaning |
|---|---|
| `W_X` | The minimal assumption bundle on a `WorldCtx`. |
| `X_of_W` | The conditional theorem whose antecedent is a `W_X`. |

A representative example:

```
theorem WorldCtx.lie_possible_of_W
    (C : WorldCtx) (W : WorldCtx.W_lies_possible C) :
    ∃ w a P, C.Lie w a P
```

Adversarial obligations follow the same pattern in
`Adversarial/Obligations.lean`: `spoofed_V_blocks_path_of_W`,
`ddos_causes_verification_collapse_of_W`,
`collapse_causes_centralization_of_W`, and so on, each with its own `W_*`
antecedent.

---

## World-bundle vs world-assumption-free path

The W_* bundles are not the only — and not the strongest — way to drive the
forcing chain. The headline convergence theorem
`bundled_structure_forces_bank_primitives` (in `WorldBridges.lean`) takes
`SystemOperationalBundle W`, `WorldBridgeBundle W`, and `SatisfiesAllProperties
W`, and concludes `containsBankPrimitives W` with **no `WorldCtx` at all**.
The W_* bundles are the natural *source* of the bridge witnesses, but they
are not formal preconditions of the headline theorem.

The universe boundary is real: W_* bundles are `Prop`-valued and cannot
auto-manufacture the `Type`-valued fields (`State : Type`, `Claim : Type`)
that `Represents*` structures carry. Callers that already have concrete
structural witnesses get a strictly stronger result. The
`WorldSystemCompat` adapter (`WorldBridges.lean`) closes the gap explicitly:
given a per-dimension certificate that the system genuinely operates under
the W_* conditions, `world_deriving_bridge` assembles a `WorldBridgeBundle W`
without spelling out the bundle fields by hand.

---

## What this layer does not claim

The W_* bundles are explicit antecedents; they are not assertions about the
real world. `WorldWitness.lean` exhibits a concrete `WitnessCtx` satisfying
all three, which closes the non-vacuity question — but a witness model is a
proof of *satisfiability*, not of *empirical correspondence*. The framework
makes inference load visible and auditable; it does not certify that any
deployed system inhabits the bundle.

The contrapositive `kernel_redundant_without_lies` makes the same point in
the other direction: in a world where every claim is universally true, the
discriminator never fires, so the architecture's accept/reject machinery is a
no-op. This is *why* the W_* bundles are foregrounded — they record the
exact world conditions under which the architecture is non-trivial.

Existence/capability obligations (`lie_possible_of_W`,
`all_agents_can_lie_of_W`) establish *that* a property is structurally
possible, not *how often* it occurs or *how effectively* it is exercised.
Prevalence and scaling claims are separate.

---

## Go next

- [FEASIBILITY.md](FEASIBILITY.md) — concrete satisfiability of the W_*
  bundles and the closed-form convergence corollary.
- [PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md) — how each bundle plugs into
  its corresponding pressure dimension.

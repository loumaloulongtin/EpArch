# Modularity

Modularity in EpArch is *controlled projection*: the theorem corpus is sliced
into named clusters certified against an explicit constraint/goal/world
profile, so a sub-system that adopts only a subset of the operational
pressures still receives a sound, machine-checked subset of the theorems.

This is the canonical home for **modularity scope** — what the cluster
surface buys, where its limits are, and why "every subset" is not the right
mental model. The certified-projection layer also subsumes the older
trust-bridge design notes; both auth modes are referenced below.

---

## High-level claim

EpArch's theorem corpus is partitioned into **32 certified clusters** across
six families. Constraint, goal, and world clusters are *config-driven* —
activated by the `EpArchConfig` the user supplies. Meta-modularity,
lattice-stability, and all Tier 4 clusters are *always-on*: they hold
unconditionally and require no configuration.

| Family | Count | Role |
|---|---|---|
| Forcing clusters (Tier 2) | 8 | one per pressure dimension |
| Goal transport (Tier 3) | 6 | health goals preserved under compatible extension |
| Tier 4 library | 5 | commitments, structural, LTS-universal, bank-goal transport |
| World obligations (Tier 1) | 8 | one per `W_*` bundle |
| Meta-modularity | 1 | constraint-subset independence (`PartialWellFormed → projection_valid`) |
| Lattice-stability | 3 | `graceful_degradation`, `sub_revision_safety`, `modularity_pack` |

The 32 `ClusterTag` values in `Meta/ClusterRegistry.lean` are the canonical
names. The full per-cluster registry — tag, statement, witness — is in
[reference/THEOREMS.md](../reference/THEOREMS.md).

---

## Why modularity is a kernel design constraint

EpArch must remain applicable across agents that do not share the same
internal epistemology, including minimal agents (e.g. an odometer-like
system) that face only a sub-bundle of the full eight pressures. The
cluster architecture ensures the kernel scales down gracefully: a system
that does not face, say, `Pressure.revocation` (adversarial pressure)
simply does not receive the clusters that depend on it, and the remaining
claims stay sound.

This is why the kernel boundary stops at coordination-relevant
architectural requirements rather than agent-internal dynamics models.

---

## Three transport layers

A caller interacts with three layers between an `EpArchConfig` and the
proof content. Each layer has a single owner; mismatches between them are
build-time bugs.

### User-facing surface

| API | Lives in | Role |
|---|---|---|
| `EpArchConfig` | `Meta/Config.lean` | user-supplied `constraints`/`goals`/`worlds` lists |
| `ClusterTag` | `Meta/ClusterRegistry.lean` | the 32 cluster identifiers |
| `certify` | `Meta/Config.lean` | `EpArchConfig → CertifiedProjection cfg` |
| `showConfig` / `#eval` output | `Meta/Config.lean` | human-readable display |

`certify myConfig` returns a record with one indexed witness per family
(`.goalWitnesses`, `.tier4Witnesses`, `.worldWitnesses`, ...).

### Routing/metadata layer (`Meta/ClusterRegistry.lean`)

Owns `ClusterTag`, every `EnabledXxxCluster` enumeration, `clusterEnabled`,
and every `toClusterTag` mapping. **No EpArch-specific imports** — pure
metadata. Changing a cluster's description, family, or enabled status is an
edit here only.

### Proof-carrying layer (`Meta/Config.lean`)

Owns the indexed witness inductives (`GoalWitness`, `Tier4Witness`,
`WorldWitness`, `MetaModularWitness`, `LatticeWitness`) and the Tier 2 proof
carriers (`ConstraintProof`, `ConstraintClusterSpec`). Each constructor
holds the actual Lean type of the theorem being certified; each match arm
wires a tag to its proof term.

The witness inductives use *indexed* constructors (rather than plain
function types) for universe management: model-parameter universes
(`Type 1`) cause issues if bundled into a flat function type. Tier 2 is the
exception — it uses direct `ConstraintProof` because its theorems are
universe-flat.

---

## Certification surface

### `EpArchConfig → CertifiedProjection`

```
def MyConfig : EpArchConfig := { constraints := [.distributed_agents, ...],
                                 goals := [...], worlds := [...] }

#check (certify MyConfig)
```

The result is a record of indexed witnesses; if it type-checks, every
selected cluster is machine-certified against the config.

### `PartialGroundedSpec` for product compliance

The `EpArch.Meta.Modular.partial_modular` entry point (in `Meta/Modular.lean`)
produces a stronger claim: not just that the selected clusters hold, but
that the user's *concrete domain evidence* satisfies them. The workflow:

1. declare a `ConstraintSubset` of active pressures;
2. supply a `PartialGroundedSpec` with domain-typed `GroundedX` evidence
   for each active constraint, and a vacuous inhabitant for each
   inactive one;
3. compile.

If `partial_modular MyConstraints MySpec` type-checks, the Lean kernel has
verified that the design satisfies every active EpArch constraint. The
guarantee covers structural well-formedness and the constraint→feature
forcing implications; it explicitly does not cover the model-gap
(whether the `GroundedX` records faithfully describe a physical system) or
the compiler-trust gap (Lean's compiler is not CompCert).

### Trust-bridge auth modes

Trust-bridge primitives (`CTrustBridgeAuth` in `Concrete/Types.lean`)
support two auth modes — `.byAgent` (named presenter) and `.byToken`
(credential-checked presenter) — both of which satisfy the same
architectural invariant: **bubbles never communicate directly; an agent is
always in the middle**. The two modes are two answers to the same gate
question: "is this agent authorised to make this cross-bubble assertion?"

Multi-hop chains (`A ↔ Agent₁ ↔ Agent₂ ↔ B`) are handled naturally — each
boundary is a separate `CExportRequest` with its own gate check, and no hop
is gate-free. Neither mode certifies that the underlying withdrawal was
valid at the source; that is a separate agent-layer obligation, which is
why `revalidated = true` exists as a first-class export path alongside the
two bridge modes.

---

## Cluster registry and routing

The cluster registry is intentionally *not* a complete index of every
forcing surface in the repo. Two further forcing surfaces are intentionally
outside `ClusterTag`:

- **`AuthorizedWithdrawalGoal`** (`Health.lean`) — a structural implication
  for multi-agent differentiated certification, not a config-selectable
  goal. The config-facing authorization story is carried by the
  `multi_agent_access` pressure dimension.
- **Residual-risk / autonomy forcing surface** (`Health.lean`,
  `ResidualRiskMitigation.lean`) — closed autonomy-regime consequences over
  `AutonomyModel` and `PRPObligationStream`, not over the eight
  `WorkingSystem` pressure dimensions.

"Not in `certify`" means *not user-configurable*, not *forgotten*. Both
surfaces remain documented in
[reference/THEOREMS.md](../reference/THEOREMS.md).

---

## Adding, removing, refactoring clusters

The full add-cluster recipe (Tier 2 vs indexed-witness families,
copy-paste templates) lives in `Meta/ClusterRegistry.lean` and
`Meta/Config.lean` source comments. The discipline is:

- **Touch layers in order**: source theorem → `Config.lean` witness
  constructor → `ClusterRegistry.lean` tag/description → docs.
- **No empty compatibility shells.** If a theorem family becomes
  standalone, its cluster reflects that — do not leave a transport wrapper
  with vacuous proofs. The `CommitmentsCtx` removal (commit `5a1cdea`) is
  the canonical example.
- **Routing, witnesses, and descriptions update together.** A mismatch
  between the registry description and what the witness carries is a
  documentation bug; the three layers must always agree.

The registry's invariants (I1–I6) live in `Meta/ClusterRegistry.lean`'s
file comment.

---

## What modularity does not claim

Modularity does not mean "any subset of constraints yields a useful
system." Some sub-bundles are degenerate (the empty subset trivially
satisfies `PartialWellFormed`). The cluster surface certifies that *if*
the user selects a profile, the corresponding clusters hold; it does not
certify that the selected profile is non-trivial, well-motivated, or
sufficient for any given application.

Cluster surface ≠ unique decomposition. The 32 clusters are the current
machine-certified projection grouping; alternative groupings exist (e.g.
the eight per-dimension `*_forces_*` theorems can be cited individually
without going through the cluster registry). The registry is a stable
citation surface, not a uniqueness theorem.

The exhaustiveness of the eight pressures is *architectural discipline*
within the theory (every `cases P` over `Pressure` is checked by the
kernel), not a metaphysical claim about reality. A proposed ninth
dimension that lives at the agent-agnostic architectural level, that is
not a sub-case of an existing one, and that admits the same forcing
treatment (`Represents*`, `handles_*`/`Has*`, impossibility model) extends
the theory cleanly — adding it is a typed extension, not a refutation.

---

## Go next

- [reference/THEOREMS.md](../reference/THEOREMS.md) — full per-cluster
  registry of statements and witnesses.
- [../START-HERE.md](../START-HERE.md) — terminology and reading routes.

# EpArch — Copilot Instructions

Lean 4 formalization of an epistemic architecture framework. No Mathlib. Zero
axiom declarations, zero sorries. Build: `lake build`.

---

## How to Find Things

**Do not guess file paths or theorem names. Search the repo.**

### Directory structure

- `EpArch/` — all Lean source. One file per module.
- `EpArch/Agent/` — agent-level constraints, corroboration, imposition, resilience.
- `EpArch/Meta/` — certification engine, cluster registry, transport, modularity meta-theorems.
- `DOCS/` — documentation. Each `.md` describes one area. Read `DOCS/README.md` for the index.
- `Main.lean` — full build entry point.

### Naming conventions (stable patterns, not exhaustive lists)

- Core types live in `Basic.lean`. If you need `Deposit`, `Bubble`, `Header`, `Agent`, start there.
- Operational semantics (step transitions) live in `StepSemantics.lean`.
- Forcing / necessity theorems ("constraint X forces feature Y") live in `Minimality.lean`.
- Health goal definitions live in `Health.lean`.
- Commitments (C1–C8) live in `Commitments.lean`.
- World assumption bundles (`W_*`) live in `WorldCtx.lean`.
- Adversarial obligation theorems (`*_of_W`) live in `Adversarial/Obligations.lean`.
- The cluster tag registry lives in `Meta/ClusterRegistry.lean`.
- The certification engine (`certify`, `CertifiedProjection`) lives in `Meta/Config.lean`.
- Transport theorems live in `Meta/TheoremTransport.lean` (Tier 3) and `Meta/Tier4Transport.lean` (Tier 4).

When in doubt, `grep` for the name. The doc headers at the top of every `.lean`
file describe what that module owns.

### Documentation

`DOCS/README.md` is the maintained index. Consult it rather than guessing which
doc covers a topic. Key docs for common questions:

- Cluster families, how to add/remove clusters → `DOCS/MODULARITY.md`
- Axiom boundary → `DOCS/AXIOMS.md`

---

## Layer Split — Read Before Editing

The `Meta/` directory has a rigid two-file split. Do not merge the layers.

**`Meta/ClusterRegistry.lean`** — routing and metadata only. Owns `ClusterTag`,
`EnabledXxxCluster` inductives, `clusterEnabled`, `clusterDescription`. No
EpArch-specific imports. Edit here to change what a cluster is *called*, *when*
it's enabled, or *how it's described*.

**`Meta/Config.lean`** — proof-carrying layer. Owns witness inductives
(`GoalWitness`, `Tier4Witness`, etc.), `CertifiedProjection`, `certify`. Edit
here to change what a cluster *certifies* (its type or proof term).

**Theorem modules** (everything else in `EpArch/`) — source of actual proofs.
Editing a theorem module does **not** change the cluster surface unless
`Config.lean` is also updated.

---

## Key Distinctions

These are architectural invariants, not version-specific facts.

- **Always-on vs. config-driven clusters.** Some clusters (Tier 4, meta-modularity,
  lattice-stability) are always enabled. Forcing, goal, and world clusters are
  gated by `EpArchConfig`. Inspect `clusterEnabled` in `ClusterRegistry.lean` for
  the authoritative routing.

- **Traction ≠ authorization.** Core architectural split. Search `Theorems.lean`
  for `traction_broader_than_authorization`.

- **RevisionGate = SelfCorrectionGoal.** Definitionally equal. See
  `self_correction_is_revision_gate` in `Health.lean`.

- **Tier 4 has distinct sub-clusters** (commitments, structural, LTS-universal,
  bank-goal transport). Do not conflate them. Inspect the `EnabledTier4Cluster`
  inductive in `ClusterRegistry.lean`.

---

## Rules

1. **Read the relevant `.lean` file before proposing edits.** The Lean source is
   the source of truth. README and DOCS prose are secondary.

2. **Use current theorem names.** Do not invent or guess. Search the repo.

3. **Do not add `axiom` declarations.** Use `opaque` for domain primitives.

4. **Do not add `sorry`.** Every theorem is fully proved.

5. **Preserve the routing/proof split.** No proof terms in the registry, no
   routing logic in the config.

6. **Update layers together.** Changing a cluster means updating
   `ClusterRegistry.lean`, `Config.lean`, and `DOCS/MODULARITY.md` in one pass.
   See `DOCS/MODULARITY.md` for the exact recipe.

7. **Do not modify theorem code unless explicitly asked.**

8. **If the cluster count changes**, update `DOCS/MODULARITY.md` and `README.md`.

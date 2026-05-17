# Theory

This is the prose layer of EpArch. The Lean kernel says, in its own register, what is forced and what is not; the DOCS folder records the architectural argument for a reader who wants the formalisation's own map of itself. This folder does neither. It walks the architecture as a sequence of stories — substrate, private state, forcing, goals, autonomy, concrete inhabitants, meta — and tries to leave a reader who has clicked through it with the same sense of *what is load-bearing and why* that a reader of the kernel would arrive at by other means.

The walk is one file at a time. Each cluster opens with a hub file that sets out what the cluster is for, then takes the reader through the pieces in an order that tries to earn each commitment before it is invoked. Every file ends with a forward link to the next. The walk terminates at [meta/falsifiability.md](meta/falsifiability.md), which is the last thing the architecture has to say in this register.

---

## Start here

Open [world/world.md](world/world.md) and click the *Next* link at the bottom of each file. The chain runs:

> world → bubble → agent → forcing → goals → autonomy → concrete → meta

Each cluster's hub file is the natural pause-point if you want to stop and reorient. Backlinks (*←*) at the top of each hub take you to the previous cluster's terminal file; the parent-link (*↑*) on cluster-internal files takes you back to that cluster's hub.

If you have read the kernel and want the prose only where it covers something the kernel cannot say in its own register, [meta/](meta/) is the cluster to start with — it is the one whose subject matter is the architecture's own scope rather than the architecture's content.

---

## Why this folder exists

The kernel proves what it proves and is silent about everything else. That silence is correct in the kernel and unhelpful for a reader who wants to know which of the architecture's commitments are doing real work, which are scaffolding, which are deliberate refusals, and which are honest non-results. This folder is where those distinctions are spoken aloud. It is not a tutorial for the kernel and it is not a paper; it is the running commentary the architecture would make about itself if it were the kind of object that talked.

---

## Index

### [world/](world/) — what the architecture commits to about the world

- [world.md](world/world.md) — the friends-and-the-window opener; what the architecture fixes about the world and what it leaves to whoever is using it
- [bridges.md](world/bridges.md) — how facts in the world become problems in the kernel
- [witnessing.md](world/witnessing.md) — what the architecture is willing to certify, and what it leaves open

### [bubble/](bubble/) — the shared substrate

- [bubble.md](bubble/bubble.md) — what a bubble is and why it is the unit the architecture works over
- [bank/](bubble/bank/) — the substrate's internals: deposits, claims, headers, lifecycle, safety, and the under-attack story that closes the cluster

### [agent/](agent/) — private state inside the substrate

- [agent.md](agent/agent.md) — the night-nurse story; what an agent is, set against what a bubble is
- [ladder/](agent/ladder/) — the five-stage stance vocabulary (Ignorance, Doubt, Belief, Certainty, Denial) and the extremes that close the cluster

### [forcing/](forcing/) — why the architecture has the shape it does

- [forcing.md](forcing/forcing.md) — the eight-pressure argument that the architecture's structural pieces are not arbitrary
- [corners/](forcing/corners/) — the worked corner cases, one per piece
- [pathologies.md](forcing/pathologies.md) — what dissolves when a piece is missing

### [goals/](goals/) — what a working architecture buys

- [goals.md](goals/goals.md) — the six goals the architecture commits to
- [profiles.md](goals/profiles.md) — substantive / vacuous / explicit-no, the goal-stance vocabulary
- [convergence.md](goals/convergence.md) — what convergence does and does not mean here

### [autonomy/](autonomy/) — the goal that needs its own cluster

- [autonomy.md](autonomy/autonomy.md) — why autonomy is treated separately from the other goals
- [goal.md](autonomy/goal.md) — what the autonomy goal claims
- [corners.md](autonomy/corners.md) — the autonomy-specific corners
- [risk.md](autonomy/risk.md) — the bridge-use layer of residual risk

### [concrete/](concrete/) — the architecture's inhabitants

- [concrete.md](concrete/concrete.md) — why exhibiting inhabitants matters
- [realizers.md](concrete/realizers.md) — the working-system witness and the OdometerModel
- [deficient.md](concrete/deficient.md) — honest non-inhabitants the forcing theorems predict

### [meta/](meta/) — the architecture as a configurable kernel

- [meta.md](meta/meta.md) — the modularity meta-theorem and what it licenses
- [configurations.md](meta/configurations.md) — typed deployment surfaces
- [transport.md](meta/transport.md) — what survives a configuration change
- [grounded-evidence.md](meta/grounded-evidence.md) — the deployment-facing certificate and residual risk
- [falsifiability.md](meta/falsifiability.md) — claims you cannot make true by saying so

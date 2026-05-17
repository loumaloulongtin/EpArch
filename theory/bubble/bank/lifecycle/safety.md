# What the Lifecycle Cannot Do by Accident

*[← The Bakery](lifecycle.md) · [Under Attack →](under-attack.md)*

---

## In this series

- [The Bakery Story](lifecycle.md) — the lifecycle as the operational engine
- *steps/* — one file per recordable event, walked through one developing case
- [What the Lifecycle Cannot Do by Accident](safety.md) — the safety guarantees the engine ships *(you are here)*
- [When the Engine Comes Under Coordinated Pressure](under-attack.md) — the engine under coordinated pressure

---

## What "safety" means here

The lifecycle's ten constructors are not just a catalogue of recordable events. They are a catalogue of events whose *shapes* — preconditions, successor formulas, action labels — rule out entire classes of unintended outcome. The safety story of the lifecycle is the story of those structural preclusions: claims of the form *no trace, no matter what its constructors did, can do X*, proved by induction on traces from per-step lemmas about the constructors themselves.

This is not a claim about deployment discipline, agent vigilance, or the quality of the surrounding policy layer. None of those are in scope. The safety guarantees are properties of the kernel's relation between states — they hold by virtue of how the constructors are *defined*, regardless of which agent invoked them, in what order, with what intent, against what history.

The kernel splits these guarantees into two layers, and makes the distinction syntactically checkable on the trace.

---

## Two layers of guarantee

The lifecycle's safety guarantees come in two layers, and the kernel makes the distinction explicit on the trace.

The first layer holds over *every* trace, no matter what the constructors did. The agents' ladder map — who is at what stage on which claim — is preserved through every step and therefore through every trace. The clock advances only on `Tick`. A `.Forgotten` slot stays `.Forgotten` forever. A move on slot 7 does not modify slot 8. A move in one bubble does not modify another bubble's view of the same content. These hold across all ten constructors used in any combination, including any number of `Update`s, `Challenge`s, `Revoke`s, and `Forget`s.

The second layer holds only over *revision-free* traces — traces that contain no `Challenge`, no `Revoke`, and no `Update`. The kernel marks each of those as `Action.isRevision = true`, and `Trace.hasRevision` lifts that to whole traces. A trace that contains any of them is a *revision trace*, and the revision-free guarantees do not apply to it by hypothesis. The architecture's role is not to forbid revision — revision is built into the lifecycle on purpose — but to make the cost visible: a deployment cannot use revision and keep the revision-free guarantees too. Whether a guarantee holds over a given trace becomes a syntactic question the architecture lets a reader answer.

The rest of this file walks the major guarantees in each layer.

---

## The any-trace layer

### The ladder map is untouched

Every step in the lifecycle either returns the system state unchanged (`Withdraw`) or modifies one specific field of it — the ledger, the clock — using Lean 4's struct-update syntax that copies every other field forward. The agents' ladder map is one of those copied-forward fields, and the kernel proves it: `step_preserves_ladder_map` says `s'.ladder_map = s.ladder_map` for any step, and `trace_preserves_ladder_map` lifts the same to any trace.

The architectural meaning is the bank/ladder independence the agent cluster argued for, made operational. No promotion of a candidate, no quarantine of a deposit, no revoke of a quarantined entry, no submission of a new candidate, no overwrite via `Update`, no deletion via `Forget` can move an agent's ladder position. Any change to where a particular agent sits on a particular claim is a ladder-internal move; the bank's events do not produce it. A trace reader who wants to know whether some agent's ladder position changed during a stretch of bank activity has the answer immediately: it did not.

The corollary the kernel ships is that bank traces *cannot discharge closure*: an agent at the Certainty stage on `P` at the start of a trace is at the Certainty stage on `P` at the end. The bank can do whatever it likes to the deposits underlying that closure — quarantine them, revoke them, forget them, overwrite them — and the agent's ladder closure remains where it was. The agent's epistemic position is the agent's; the bank's ledger is the bank's; the lifecycle keeps them apart.

### The clock is modified only by `Tick`, and `Tick` is monotone

Every constructor that is not `Tick` carries the clock forward unchanged: `Submit`, `Register`, `Challenge`, `Repair`, `Revoke`, `Promote`, `Forget`, and `Update` all use struct-update syntax that copies the clock from the predecessor state to the successor state. `Withdraw` returns the predecessor state outright. Only `Tick` writes the clock field, and `Tick` only writes the clock field — its precondition `s.clock ≤ t'` enforces monotonicity from below (including `t' = s.clock`), and the constructor body installs the new clock without touching anything else.

The architectural payoff is that any temporal-validity check the deployment writes against the bank's clock can be phrased in terms of *the moment some other event was recorded* without worrying that an unrelated quarantine or repair could have nudged the clock between the two. Time has its own move; the rest of the engine cannot touch it. (What the kernel proves is the clock discipline; what counts as *expired* or *stale* is the deployment's validity-policy layer, as the parent file noted.)

### `.Forgotten` is absorbing

Once a slot has been forgotten, no constructor can move it back to anything else. The kernel proves this with `forgotten_status_stable_step`: every constructor that touches a status either leaves a `.Forgotten` slot strictly alone (by acting at a different index) or carries a precondition that contradicts `.Forgotten` at the affected index — `Challenge` requires `Deposited`, `Revoke` and `Repair` require `Quarantined`, `Promote` requires `Candidate`, `Forget` and `Update` carry `h_not_forgotten`. There is no constructor whose precondition is satisfied by a `.Forgotten` slot. The trace-level lift, `forgotten_status_stable_trace`, says the same about any trace: a slot that is `.Forgotten` at the start of the trace is `.Forgotten` at the end, regardless of which actions the trace contains.

This is what makes `Forget` mean what the parent file said it meant. The agent's commitment that the slot is gone from the bank's operational memory is enforced not by procedure but by *the impossibility of any other event firing on that slot*. There is no way to revive a forgotten slot through the lifecycle. A deployment that needs the slot back has to write to a *different* index — `Submit` or `Register`, which only ever append.

### Locality across slots, with bubble scope supplied by the model

A move on slot 7 edits slot 7 and leaves other ledger indices untouched. That is the kernel-level locality guarantee: `updateDepositStatus s.ledger 7 …` and `modifyAt s.ledger 7 …` leave every other index unchanged by construction. A move at slot 7 cannot modify slot 8, slot 17, or slot 4711.

The `bubbles` field of the system state is also not edited by the lifecycle constructors. A step does not create, destroy, or mutate bubbles as a side effect of editing the ledger.

The stronger operational reading — that an operation in one bubble cannot target another bubble's deposit — depends on the deployment maintaining the intended bubble/index discipline. The kernel records bubble labels in the action, and deposits carry bubble fields, but the step relation itself edits the selected ledger index. The kernel's contribution is per-index locality; the bubble-scope guarantee is the deployment's to enforce.

---

## The revision-free layer

### Revision-free traces prevent revocation and overwrite, not every loss of liveness

The kernel's headline revision-free theorem is `trace_no_revision_preserves_non_revoked_slot`: if a slot is `Deposited` at the start of a trace, and the trace contains no `Challenge`, no `Revoke`, and no `Update`, then the slot cannot end as `Revoked` through that trace.

This is not the same as saying the slot remains live. `Forget` is not a revision action, and a deployment may forget a deposited slot for capacity management or operational deletion without that trace being classified as a revision trace. What the revision-free layer rules out is the revision path: challenge/quarantine, revocation, or wholesale overwrite. It does not rule out every non-revision lifecycle event.

The cost of the revision-free guarantee is exactly what the kernel makes visible: the moment a `Challenge`, `Revoke`, or `Update` enters the trace, the guarantee no longer applies, and the trace reader sees the revision action on the trace where it happened.

### Self-correction requires revision

The dual of the preservation theorem is the *competition gate* — the architecture's commitment that a domain which structurally prohibits revision cannot self-correct. If a deposit's status is to move from `Deposited` to `Revoked`, some action on the trace must have installed `.Revoked` at the slot, and only `Revoke` and `Update` can do that. A trace that contains neither cannot exhibit a `Deposited → Revoked` transition.

`prohibits_revision`, in the kernel, is the predicate on system states saying *every reachable trace from here is revision-free*. The competition-gate theorem reads it forward: in a `prohibits_revision` state, no trace ever demonstrates self-correction. The architecture does not assert that any particular real-world domain prohibits revision; it asserts the structural fact that *if* a domain does, *then* self-correction is foreclosed. Whether a domain does or does not is a separate empirical question, the answer to which the architecture refuses to legislate.

This is the gate around which the broader epistemic-architecture argument is built. The lifecycle ships the gate as a theorem about its own traces; the larger architecture wires that theorem into the cross-domain analysis it then runs.

### The structured route is the transparent revision route

When revision is needed, the lifecycle offers two routes through the engine. The structured route is `Challenge → Repair` if the deposit is recoverable, or `Challenge → Revoke` if it is not. Each move is a separate event on the trace with its own attribution; a reader can walk the slot's history move by move, and the architecture's per-step gate theorems (Withdrawal Gates, Revoke Gates, etc.) apply to each transition. The route is a revision route — `Challenge` is `isRevision = true` — so a trace that uses it cannot also be revision-free. But it is *transparent*: every step is on the trace, every status change carries its own justification, and every gate the kernel proves about the structured constructors applies.

The other route is `Update`: a single wholesale overwrite that installs whatever deposit `d_new` the agent supplies, with no kernel check on `d_new` beyond the slot-existence and tombstone-boundary preconditions. `Update` is also `isRevision = true`, so it costs the revision-free guarantees. What it does *not* offer is the structured route's transparency: the new deposit's status is whatever the agent put there, the kernel does not adjudicate the change, and a trace reader who wants to know what the slot used to be has to consult the pre-state or earlier trace events.

The architecture's stance is not that one route is right and the other wrong. It is that the structured route is the *default*, that the structured route's transparency is what the structured-revision invariants depend on, and that `Update` is available when a deployment genuinely needs it — at the cost the architecture insists on naming.

---

## What the safety layer does not buy

The lifecycle does not guarantee that the deployment will *use* the safety properties well. A deployment that signs every trace with `Update` events foregoes the revision-free layer entirely; the kernel will continue to prove its theorems, but those theorems will not apply to the deployment's traces. A deployment that uses `Forget` indiscriminately will lose information the architecture would have preserved had `Revoke` been used first; the kernel's `Forget` semantics are exactly what the parent file said they were, and a deployment that wanted *content survives revocation, then gets voided* needs the `Challenge → Revoke → Forget` ordering.

The lifecycle also does not guarantee correspondence with any external world. The clock advances only on `Tick`, but whether the new clock value reflects real wall-clock time is the deployment's problem; the kernel proves clock discipline, not clock truth. The ladder map is preserved across bank steps, but whether an agent's ladder position is *epistemically correct* is the agent's problem and the ladder layer's problem; the bank simply does not perturb it. Locality across slots and bubbles is provable, but whether the deployment's bubble decomposition matches anything in the analyst's domain is a modelling question the architecture does not adjudicate.

The lifecycle also does not, at the kernel level, enforce the deployment-policy gates the parent file mentioned. Temporal validity (is this deposit still within its TTL?), ACL admission (is this agent allowed to withdraw this deposit?), and similar reliance-policy checks are real architectural fields and a deployment is free to enforce them in the surrounding policy that wraps the kernel steps. The kernel's safety theorems are about the kernel's transitions; the deployment's policy theorems are the deployment's to prove.

---

## Takeaway

The lifecycle's safety guarantees are properties of how the constructors are *shaped*, lifted from individual steps to whole traces. The any-trace layer holds across every combination of moves: the ladder map is preserved, the clock is modified only by `Tick` and monotonically, `.Forgotten` is absorbing, and per-step index locality prevents cross-slot interference. The revision-free layer holds across traces that avoid `Challenge`, `Revoke`, and `Update`: revision-free traces cannot revoke or wholesale-overwrite live deposits, and self-correction is structurally foreclosed in any domain whose traces are revision-free.

The architectural payoff is that a deployment can read its safety properties off the syntactic shape of its traces. *Did the trace contain any revision action?* is a check on the trace itself, decidable by `Trace.hasRevision`. *Did the trace touch the ladder map?* is answered by the any-trace lift: no. *Could a forgotten slot have been revived?* is answered by `forgotten_status_stable_trace`: no. The lifecycle gives the architecture provable safety, and the kernel gives the deployment the trace-level predicates that make those guarantees readable from the outside.

The next file in the cluster, *under-attack*, picks up what happens when the engine is exposed to coordinated pressure rather than a single move at a time — the saturation regimes the per-step gates are not, on their own, designed to defeat.

---

*[← The Bakery](lifecycle.md) · [Under Attack →](under-attack.md)*

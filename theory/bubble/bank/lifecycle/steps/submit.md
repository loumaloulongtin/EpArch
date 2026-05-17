# The Cooling Rack Story

*[← The Bakery](../lifecycle.md) · [Register →](register.md)*

---

## In this series

- [The Cooling Rack Story](submit.md) — `Submit`, the standard entry path: a deposit enters the system as a `Candidate` *(you are here)*
- [The Central Kitchen Delivery Story](register.md) — `Register`, the vouched-for entry path: a deposit enters straight as `Deposited`
- *(more step files follow: withdraw, challenge, quarantine, repair, revoke, promote, forget, update)*

---

## A loaf in the back

Just past five in the morning. The first batch of sourdough is out of the oven. It is too hot to slice, too hot to put on the front shelves, and there is no question of selling it yet. Someone takes it off the trays and onto the cooling rack against the back wall. A small card goes with it: *sourdough, batch S-04-26, baked 05:12*. The card stays with the loaf until someone signs it onto the front.

A customer who walks in at five-thirty and points at the cooling rack does not get sold a loaf. The staff member glances at the rack and shakes her head: *that one's not ready yet.* The loaf is in the bakery, has a label, has a place on the shelf system, and is not for sale.

That is what `Submit` does to a deposit. The deposit comes into the bank's ledger, with all of its headers attached, in `Candidate` status. No agent can withdraw it as a bank-authorized reliance target yet. The bank holds it; it is on a shelf, but not the front shelf. Promotion is a separate move, with its own preconditions, and that one is what would put the loaf on the front. Submit does not pre-empt that decision; it just gets the loaf into the building with its label intact.

---

## What the move actually does

`Step.submit` in the kernel takes a system state, an agent (the submitter), and a deposit, and produces the same system state with one change: the deposit has been appended to the ledger with its status forced to `Candidate`. That is the entire effect. The clock does not move. The bubble structure does not change. The ladder map does not change. Other deposits' statuses do not change. A new entry, in `Candidate` status, at a new slot number at the end of the ledger.

There is no bank-side precondition. The submitter does not need to prove anything to the bank to be allowed to submit. This is deliberate, and the kernel's comment says so: *authorization is an agent-level concern; the bank records the structural deposit event*. The architectural division of labour between agent and bank is sharp here. Whether *this agent* is permitted to put *this kind of deposit* into *this bubble* is a question for whatever access-control overlay the deployment installs on the agent side. The bank's job, on receiving a submit, is to write the entry down with the candidate marker on it. That is everything the bank is asked to do at this step.

The agent's identity and the deposit are recorded in the action label `Action.Submit a d`. A trace observer reading the day's log can see *who submitted what*. They can also see, from the constructor name, *which entry path was used* — submit, not register, not anything else. The `Submit` and `Register` constructors are trace-distinguishable, and the difference matters: it tells a downstream reader whether the deposit went through the candidate queue or skipped it, which is the difference between *this agent put the loaf in the cooling rack* and *this agent told us the loaf was already cleared*.

---

## Why Candidate

The deposit's status is forced to `Candidate` regardless of whatever status field was on the deposit value the submitter handed in. This is the kernel insisting on a property of the entry path: anything that comes in through `Submit` lands in the candidate queue. There is no way to use `Submit` as a back door to put a deposit straight into `Deposited` status. If the submitter wants the deposit to enter as `Deposited`, the kernel offers a different constructor — `Register` — and the trace will record which choice was made.

The `Candidate` status is the bank's *I have this entry, but no agent should rely on it yet* marker. A withdrawal cannot fire against a candidate; the withdrawal-gate theorem requires `isDeposited`, and a candidate is not deposited. A challenge cannot fire against a candidate either; challenge requires deposited status. A candidate sits in the ledger, fully present, until something else happens to it: most commonly a `Promote` move flips it from `Candidate` to `Deposited`. Until then, the candidate is the bakery's cooling rack — bread the bakery has, bread with a label on it, bread no customer will be sold.

This is the architecturally important bit. A bank that let new entries land directly as withdrawable would have no separation between *recorded* and *available for reliance*. The candidate stage is what makes that separation operational. Submit is the move that puts something into the bank without yet making it available; promote is the move that makes the available-call. They are different moves on purpose, and the trace records which step did which.

---

## What submit does not do

`Submit` does not check the deposit's headers. The kernel does not look at the temporal validity window, the standard, the error model, or the provenance bundle when the submit fires. Whatever the submitter handed over goes onto the ledger as it was, with `status` overridden to `Candidate`. If the headers are nonsense — a τ in the past, a standard the deployment does not recognize — the deposit lands as a candidate anyway. Those problems belong to the surrounding validation and reliance workflow: a reviewer can refuse to promote it, revise or resubmit it, or a later reliance policy can reject it. The kernel-level `Submit` still records the entry; only `status` is forced to `Candidate`.

`Submit` does not authorize the submitter. As above: there is no agent-side check on whether *this agent* may submit *this deposit*. That check, if a deployment wants one, lives in whichever overlay the deployment ships on top of the agent layer. The kernel's `Submit` is the structural recording of *something has been put forward*; the rest is policy.

`Submit` does not move the ladder. No agent's stance on any claim changes by virtue of a submit happening. This is the bank/ladder separation in its operational form: every step in the kernel carries the proof `step_preserves_ladder_map`, and `Submit` is the easy case. A submitter who submits a deposit that, if held, would support a particular claim has not thereby moved themselves up the ladder for that claim. The agent-side dynamics that would move the ladder are a separate matter, downstream of and independent from the structural fact of the submission.

`Submit` does not advance the clock. The clock advances only on `Tick`. A deposit submitted while the system clock is at `t` enters during that state, but `Submit` does not automatically rewrite the deposit's τ field to `t`. The deposit carries whatever τ was already present in its header; only `status` is forced to `Candidate`. Time only moves when the bakery says *that's the next hour now*.

---

## How the trace reads later

Two days later, a reviewer reads the day's log. They see, at some position in the trace, the action `.Submit a d`. They can read off four things directly from that record:

The submitting agent — `a`. The deposit, with its full headers — `d`. The path of entry — submit, not register, not anything else (the constructor is the path). The fact that the deposit landed as a candidate — true by construction; the kernel's effect rule forces it.

What they cannot read off directly is whether the deposit was eventually promoted, whether it was challenged, whether it was repaired, whether it was forgotten. Those are later moves in the same trace, recorded under their own action labels. The architecture does not collapse a deposit's lifecycle into a single record; it leaves a trail of moves, each with its own constructor and its own preconditions, and the reviewer reconstructs the lifecycle by reading the moves in order.

This is what makes the lifecycle legible the way the parent file said it was. Each step is a small, named, fully-recorded event. A submit is a submit; a promote is a promote; a withdrawal is a withdrawal with its bank-side precondition — deposited status — readable back out. The cooling-rack moment is its own moment, separate from the front-shelf moment, separate from the customer-takes-the-loaf moment, and the trace says so.

---

## Takeaway

Submit is the standard entry path: a deposit enters the bank's ledger as a `Candidate`, with no bank-side precondition, with the submitter recorded in the action label and the deposit's bubble recorded inside the deposit itself, with no other state changed. The candidate stage exists so that *being recorded by the bank* and *being available for reliance by an agent* are two separate facts the architecture can track and a trace can distinguish. The bakery's cooling rack does the same job for the same reason: not every loaf the bakery has is a loaf the bakery is selling.

The vouched-for alternative — *I am bringing this in already cleared* — is the next step file, `Register`. The two are deliberately distinct constructors so that the trace records which path the deposit took. Submission is the cautious path; registration is the asserted-ready path. Both are honest; the architecture's only insistence is that the choice be visible.

---

*[← The Bakery](../lifecycle.md) · [Register →](register.md)*

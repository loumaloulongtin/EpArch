# The Central Kitchen Delivery Story

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [Withdraw →](withdraw.md)*

---

## In this series

- [The Cooling Rack Story](submit.md) — `Submit`, the standard entry path: a deposit enters the system as a `Candidate`
- [The Central Kitchen Delivery Story](register.md) — `Register`, the vouched-for entry path: a deposit enters straight as `Deposited` *(you are here)*
- *(more step files follow: withdraw, challenge, quarantine, repair, revoke, promote, forget, update)*

---

## The morning delivery

Five-fifty in the morning. A van pulls up at the back of the bakery. Trays come off the back of the van, each one tagged: *baguettes, central kitchen run K-04-26, baked 04:45, QC cleared 05:20, driver J. Arnaud*. The manager signs the delivery slip without slicing into a baguette to taste it. The trays go straight from the van to the front shelves. By six, when the doors open, the baguettes are out front, ready to sell.

Nothing about that is a shortcut. The bakery has a standing arrangement with the central kitchen. The central kitchen runs its own QC; the manager has, on hundreds of prior mornings, opened bags and confirmed the QC is good; the delivery slip carries the kitchen's stamp; the driver is known. The bread does not need to go through this bakery's own cooling-rack-and-front-check sequence because the cooling-rack-and-front-check sequence is about *bread we baked here this morning* and *did our process actually clear it*, and these baguettes were not baked here. They came in vouched for. The only thing the manager is doing at the back door is recording the delivery: *we received K-04-26, here it is on the shelf, here is the slip*.

That is what `Register` does to a deposit. The deposit comes into the bank's ledger, with all of its headers attached, in `Deposited` status. No candidate stage. The agent presenting the register *is* the assertion that the deposit is already grounded — direct experience, or carrying from another bubble where the deposit was already established, or the standing arrangement of a trusted source. Provenance lives in the deposit's `h.V` field, and the bank does not verify the agent's grounds. The bank records the structural fact: *this agent registered this deposit, here, now*.

---

## What the move actually does

`Step.register` in the kernel is structurally identical to `Step.submit` with one change: the status the kernel forces on the new entry is `Deposited`, not `Candidate`. A new deposit is appended to the ledger at a new slot, the clock does not move, the bubble structure does not change, the ladder map does not change, other deposits' statuses do not change. There is no bank-side precondition: the kernel does not inspect the deposit's headers and does not certify the agent's grounds. Whatever standing the agent has to make the assertion lives outside the bank, in the deployment's overlay or in the deposit's own provenance bundle `h.V`. The bank's job is to write the structural event down.

The registering agent and the deposit are recorded in the action label `Action.Register a d`, and the constructor name itself records which entry path was used. The constructors `Submit` and `Register` are trace-distinguishable, and that distinguishability is load-bearing in what comes next.

---

## Why the path is recorded, not just the deposit

A naive design might have collapsed `Submit` and `Register` into a single entry move with a *status* parameter: *here is a deposit, please record it as candidate* or *here is a deposit, please record it as deposited*. The kernel does not do this. It ships two distinct constructors. The reason is in what the trace lets a downstream reader reconstruct.

When a reviewer reads the day's log and sees `.Register a d`, they know without further investigation: *this agent vouched for this deposit's grounding, and the bank did not run its own candidate-then-promote check on it*. The trail of responsibility is in the constructor itself. If the deposit later turns out to be defective, the trace shows precisely where the warrant came from: not from the bank's clearance procedure (because there was none — register skips it), but from the agent's own assertion at the moment of registration. The provenance bundle in `d.h.V` is what that assertion points to: a bubble, a source, a chain of standing the agent is willing to stake their registration on.

Conversely, `.Submit a d` tells the reviewer that the deposit went through the candidate path; whatever justified its later promotion belongs to the surrounding workflow and shows up as a separate `.Promote` move further on. Both paths are honest, and the architecture does not prefer one over the other. What it insists on is that the choice of path be visible in the record. The bakery does not pretend the central-kitchen baguettes were tested on its own cooling rack, and the bank does not pretend the registered deposit went through the candidate queue. The constructor name is the truth-in-labelling, and it is what gives a downstream reader a clean answer to *whose call was this* if the deposit later fails: the entry constructor names the responsible party.

The deployment is free to legislate what *grounded enough to register* means — only certain agents, only certain provenance bundles, whatever the standing arrangement is. That gating lives in the agent-side overlay; the kernel's `Step.register` carries no precondition of its own.

---

## Two things register is not

Two confusions are worth heading off explicitly because the bakery metaphor does not make them obvious.

`Register` is not `Promote`. `Promote` is the candidate-to-deposited *transition* and has its own precondition (the deposit must already be a candidate). `Register` creates a *new* deposit directly at `Deposited`. A deposit that came in via `Submit` becomes deposited only via `Promote`; a deposit that enters at `Deposited` does so only via `Register`. The two constructors do not substitute for each other.

`Register` does not certify across bubbles. If the deposit's provenance points to another bubble, registration does not establish that the source bubble's verdict carries over here. Cross-bubble certification, where it exists at all, is the work of bridges and witnessing in other parts of the architecture. Registration only records *this agent presented this deposit, with this provenance attached, in this bubble*.

---

## Takeaway

Register is the vouched-for entry path: a deposit enters the bank's ledger as `Deposited` directly, with no bank-side precondition, with the registering agent and the full provenance bundle recorded, and with the trace marking the entry path as register rather than submit. The cautious path is `Submit` followed by `Promote`; the asserted-ready path is `Register`. Both are honest; the architecture's insistence is that the choice be readable. The bakery's cooling rack and the bakery's back-door delivery are two different intake procedures, and the day's log records which one this loaf came through.

---

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [Withdraw →](withdraw.md)*

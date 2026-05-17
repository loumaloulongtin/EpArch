# Doubt

The ladder names five stages an agent's traction on a claim can occupy: Ignorance, Doubt, Belief, Certainty, Denial. Doubt sits on the negative-valence side of the engaged stages — the stage where the agent is *engaged with* a claim and is *actively pressing the traction down*.

The everyday word *doubt* carries Cartesian baggage: global suspension, methodological scepticism, the doubt-everything posture. The kernel's Doubt is none of that. It is per-claim, positive, and on the engagement side of the ladder. The misreading the file exists to disarm is the natural one: that Doubt is the *absence* of belief. The kernel says no. Absence of engagement is Ignorance. Doubt is positive engagement with negative valence — it is its own active stance, and the work it represents is often among the most labour-intensive an agent does.

This file is about what the work actually is, why Doubt and Denial are kept architecturally apart, and what the file does not buy.

---

## What Doubt is

The kernel constructor and its docstring:

> `Doubt — claim on radar but traction actively demoted`

Two operational claims compressed into one line. *On radar* means engaged: the agent is actively monitoring the claim, treating it as a live question rather than a settled background or an ignored one. *Actively demoted* means the traction is being pressed against, weighed down, held below the threshold at which the agent would act on the claim as a working premise.

Doubt is the conjunction: the agent is engaging *and* pushing back. Neither half alone is Doubt. An agent who is no longer engaging with the claim is no longer at Doubt — engagement is constitutive of the stage. Where such an agent ends up instead is an overlay-level question the kernel does not adjudicate; the architecture only requires that whatever stage they are at, it is one of the five and they are at exactly one of them. An agent who is engaging without pressing back is somewhere on the positive side — Belief or Certainty. Doubt is the stage of *engaged-with-negative-valence*.

That is the entire kernel commitment. Like Belief, Doubt is one of the three stages the `LadderStage` docstring marks as *reserved vocabulary for agent-specific overlays*: its internal dynamics, transition rules, and gradations are intentionally left to applications. The architecture supplies the slot and stops. (The full development of why this room exists is in [belief.md](belief.md); this file does not redo it.)

---

## Doubt is active work

Doubt's distinctive flavour, set against the rest of the ladder:

- **Ignorance does no work.** No engagement; nothing to do.
- **Certainty has put the work down.** The claim is in background; active monitoring has been released.
- **Belief is running on work that has reached the action threshold.** The agent is engaged and willing to act; the labour now is to keep watching.
- **Denial has refused the work.** The channel is closed; incoming signals are not being processed as revision candidates.
- **Doubt is often the stage where the work is most labour-intensive.** Active monitoring *and* active demotion, simultaneously. The agent has to keep engaging with a claim while also keeping the traction pressed down.

A referee on a paper they would like to be true. They have read it three times. There is a place where the argument doesn't quite hold up — they have circled it, written marginal notes, tried to construct the missing step themselves and failed. They will write a careful report. They will recommend revision rather than rejection. They will read the revised version with the same attention. If the author closes the gap, they will accept the paper.

What stage is the referee at, on the claim *the paper's central result is correct*?

Not Ignorance — they are deeply engaged. Not Belief — they cannot recommend acceptance; they are not willing to act on the claim as a settled premise. Not Certainty — definitely not settled. Not Denial — they would absolutely accept the paper if the gap were closed. Doubt is the only slot that fits, and the slot is doing real work: holding the question open, keeping the channel wired for revision, while pressing the traction down because the argument as it stands does not warrant the higher stage.

That picture — engaged, demoted, channel open — is what the kernel constructor compresses into nine words.

---

## Doubt versus Denial — the contrast that matters

This is the architectural payoff of keeping Doubt as a separate stage. From outside, an agent at Doubt and an agent at Denial can look similar on a particular claim: neither is accepting P, neither will act on P. From inside the architecture, they are at different positions on what [extremes.md](extremes.md) develops as the channel axis.

- **Doubt holds the question open.** The agent is engaged with the claim and weighing it down, but has not closed any channel against the direction the claim comes from. New input on that direction reaches them as input on a live question.
- **Denial is a targeted closure.** The agent has taken a stance against further input from a particular source or direction. The closure is part of the stage — the agent has done it, can usually identify what they have closed and on what grounds, and is not in the process of weighing the claim against incoming evidence on that line because that line is the one they have closed.

Neither of those is the entrenchment failure [extremes.md](extremes.md) develops at the other end of the ladder. Denial is a position the agent occupies, with the closure encoded in the position; entrenchment is Certainty with a separately-held closure of the review channel, where the agent processes signals but the processing no longer revises the core. Doubt is opposite to Denial on the channel question — channel-against-this-direction not closed — and opposite to entrenchment on the engagement question — actively pressing the traction down rather than holding it fixed at the top.

In the kernel, the stage is indexed by agent and claim. When this file speaks of a source or direction, that is application-level structure: the direction must be represented in the claim, in the deposit or header context, or in an agent-side overlay. The kernel records the stage value; what counts as the *direction* against which a Denial is targeted, or which a Doubt holds open, is downstream.

The architectural significance of keeping Doubt and Denial as separate stages turns on this. Both are negative-valence positions on a claim. They differ on whether the agent has closed the channel against the direction the claim comes from. If they were collapsed into a single "negative" stage, the kernel would lose its ability to mark, in the stage value itself, the difference between an agent who is engaging-and-weighing-against and an agent who has closed a particular line of input. That difference is what the five-stage partition is doing on the negative side, and Doubt is the stage that occupies the still-open position.

The architecture does not adjudicate either side. Whether a particular Denial tracks something the agent later endorses or later regrets, and whether a particular Doubt should have been resolved upward or downward, are questions the kernel does not address. The structural job is to keep the two positions distinguishable; the rest is downstream.

---

## Doubt is not the absence of belief

The most common collapse, worth disarming directly. An agent at Doubt is not "not-believing"; they are *actively engaging with negative valence*. An agent who is not engaging at all is at Ignorance.

Two different boundaries are at play, and conflating them produces most of the everyday confusion about what doubt is:

- **The engagement axis.** Ignorance versus the four engaged stages (Doubt, Belief, Certainty, Denial). Whether the agent is engaging at all.
- **The valence axis, within engagement.** Doubt versus Belief. Whether the engagement presses against acting on the claim or for it.

"Not believing P" is ambiguous between "not engaged with P" (Ignorance) and "engaged with P with negative valence" (Doubt). The kernel keeps them apart deliberately, and most everyday muddles about doubt — *is doubt the failure to commit, or the active stance against?* — dissolve once the two axes are pulled apart.

Doubt is the engaged-and-against stance. The unengaged stance is Ignorance, and the architecture has its own file for that.

---

## What Doubt is not

A few neighbouring confusions worth pulling apart:

- **Not Ignorance.** There is engagement. The claim is on the radar; the agent is actively monitoring it, even though their traction is demoted.
- **Not Belief.** Negative valence; the agent will not act on the claim as a settled premise. (This is the action-guiding boundary [belief.md](belief.md) develops.)
- **Not Denial.** The agent has not closed a channel against the direction the claim comes from. They are weighing the claim against incoming input, not refusing input from a particular source. (This is the channel boundary [extremes.md](extremes.md) develops, and Denial there is a *targeted* closure, not a general refusal-to-update.)
- **Not Certainty.** Active monitoring is on; the claim is figure, not ground.
- **Not global Cartesian doubt.** Per-claim demotion of traction, not a methodological global suspension. The kernel's Doubt has no thesis about other claims the agent might hold.
- **Not the absence of belief.** Active negative engagement, not non-engagement. An agent who has not even encountered the claim is at Ignorance, not Doubt.

---

## What this file does not buy

A few things to head off explicitly:

- **The architecture does not say when an agent should reach or release Doubt.** `agentTraction` is opaque. Whether a particular agent's overlay enters Doubt on counter-evidence, on cost-of-error grounds, on virtue-driven scepticism, or by some other rule is application-level.
- **The architecture does not adjudicate which doubts are warranted.** Same boundary [certainty.md](certainty.md) draws on the warrant question for Certainty: the kernel records the stage value and supplies the structural slots; whether any particular path into Doubt was epistemically sound is left to overlays the kernel does not legislate.
- **"Actively demoted" is the only operational commitment in the constructor.** There is no `actively_demotes a P` predicate, no theorem the kernel reasons about Doubt with. The constructor docstring marks the slot's intended role; the architecture does not formalize it further.
- **Doubt is not closure-with-a-different-name.** Denial is a targeted closure against a particular direction, encoded in the stage; Doubt is the still-open position. Applications that wish to refine Doubt internally must keep the boundary against Denial — no internal substage of Doubt should encode the targeted closure that defines Denial.

---

## Takeaway

Doubt is the architecture's slot for *engaged negative valence with the channel open*. It is the stage where the agent is on a claim's radar and actively pressing the traction down, and it is often the stage where epistemic work is most labour-intensive: holding a question open while not yielding to it, while remaining movable by a sufficient signal.

It is not the absence of belief. The absence of engagement is Ignorance; Doubt is the positive stance of weighing-against.

Its closest neighbour on the negative side is Denial, and the architectural significance of keeping the two as separate stages turns on whether the agent has closed a channel against the direction the claim comes from. Doubt has not; Denial has. The five-stage partition is doing real work at exactly that boundary, and Doubt is the stage that occupies the still-open position. The referee who keeps reading, the juror still listening to closing arguments, the engineer who has not signed off on the design — all of them are in Doubt's slot, and what they have in common is the part of the architecture this stage exists to mark: they are still in the conversation.

---

*[← Ignorance](ignorance.md) · [Belief →](belief.md)*

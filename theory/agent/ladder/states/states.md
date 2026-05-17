# States

*[← The Ladder](../ladder.md) · [Ignorance →](ignorance.md)*

---

## In this series

- [Ignorance](ignorance.md) — the unmarked default, and the state a stance can return to
- [Doubt](doubt.md) — engaged with a claim, traction actively pressed down
- [Belief](belief.md) — action-guiding traction, still actively monitoring
- [Certainty](certainty.md) — full traction, active monitoring released, review channel still open
- [The Extremes](extremes.md) — Denial as a stage, Entrenchment as a conjunction

---

## Why a stage is more than a confidence level

The simplest mistake is to think the ladder is a credence scale.

In EpArch, an agent's traction on a claim is not a number between 0 and 1. It is a position on a five-element partition: `Ignorance`, `Doubt`, `Belief`, `Certainty`, `Denial`. Each position carries operational content the next position does not. Whether the agent is engaging at all. Whether the engagement is action-guiding. Whether active monitoring is on. Whether a channel against a particular direction has been closed. None of those questions reduces to a degree of confidence, and the architecture deliberately does not flatten them onto a number line.

A bare credence is comparable. A stage is diagnosable.

The five stages are the kernel's working vocabulary for what an agent's relationship to a claim can be. They are mutually exclusive (every (agent, claim) is at exactly one stage) and exhaustive (no other state is available at the kernel level). What they are *not* is a ranking. Doubt is not "less than Belief." Denial is not "above Certainty." The kernel constructor order is fixed, but the order is not a magnitude — it is just the order the constructors happen to be listed in.

Each stage will receive its own dedicated treatment. For now, the easiest way to see the partition working is through a single developing case.

| Stage | Kernel constructor | One-line role |
|---|---:|---|
| Ignorance | `Ignorance` | No engaged stance; the unmarked default. |
| Doubt | `Doubt` | Engaged with the claim, traction actively pressed down. |
| Belief | `Belief` | Action-guiding traction, still actively monitoring. |
| Certainty | `Certainty` | Full traction, active monitoring released; review channel not closed by Certainty itself. |
| Denial | `Denial` | Targeted closure against further input from a particular direction. |

`Entrenchment` does not appear in the table because it is not a stage. It is the conjunction of `Certainty` with a separate failure — the closure of the review channel — and is named as a diagnostic, not as a position. [extremes.md](extremes.md) develops the asymmetry.

---

# Scenario: the back road

You commute between two parts of the city most days. Highway in, highway home. The highway has been your route since you started the job.

A new colleague mentions, in passing, that the back road through the residential blocks is faster during rush hour.

This file walks the same claim — *the back road is faster than the highway during evening rush hour* — through the stages an agent's traction on it can occupy.

---

## Ignorance — before the colleague said anything

For the years before that conversation, your traction on the claim *the back road is faster than the highway during evening rush hour* was at `Ignorance`.

Not Doubt — you had never weighed it; there was no claim on your radar to weigh. Not Belief — you were not acting on it. Not Denial — you had not closed any channel against it; nothing had ever come down a channel about it.

`Ignorance` is what every (agent, claim) pair looks like before that claim has reached the agent. It is the kernel's default and the most populous stage by far: the stages of the world's claims an agent has never encountered are all sitting at `Ignorance` for that agent, at every moment. Your relationship to the back-road claim before the colleague spoke is exactly that: not absent in any moral sense, just not a thing your traction had ever been asked to take a position on.

This is the entry condition. The four other stages are reachable from here, in any order, when something agent-side acts.

---

## Doubt — when you push back without dismissing

Your colleague says the back road is faster. You don't take their word for it.

The highway has more lanes. It runs uninterrupted between two interchanges. The back road has stop signs every two blocks, school zones, residential speed limits. *The back road is faster* sounds wrong on its face.

You don't reject the claim. You don't act on it either. You sit with it for a couple of weeks: you notice when traffic looks worse than usual on the highway, you let the claim float when it does, you don't quite take the back road but you can feel the question is now on your radar. You are *engaged with* the claim and you are *actively pressing the traction down*, because the prior reasons against it haven't gone away.

That is `Doubt`. Engagement is on. Active monitoring is on. The traction is being held below the level at which you would change route. The claim is on radar but not action-guiding.

It is not Ignorance — the claim is now a thing you are reasoning about. It is not Belief — you are not switching routes. It is not Denial — you have not closed the channel against your colleague or against further evidence on the question; if a friend with the same commute mentions next week that they tried the back road and it really was faster, that input lands as input on a live question. The work is the work of holding a question open while not yet yielding to it.

---

## Belief — when you act on it but keep watching

Three weeks in, traffic on the highway is bad enough that you try the back road on a Tuesday. It takes nineteen minutes instead of the usual twenty-eight. You try it again on Thursday. Twenty-one. You try the highway again the next Monday for comparison. Thirty-one minutes.

You start using the back road on most evenings.

Your traction has crossed the action threshold. The claim is no longer being weighed against; it is being acted on. But you have not stopped watching: you still glance at travel-time apps when you leave the office, you still notice when the back road gets unexpectedly heavy, you would still switch back to the highway on a day when something looks off about the residential blocks.

That is `Belief`. Action-guiding. Still actively monitoring. The agent is willing to use the claim as a working premise, and the labour of the stage is the labour of staying engaged with a claim you are now relying on.

It is not Doubt — the traction is no longer pressed down; you are acting on it. It is not Certainty — active monitoring is still on; the back-road claim is still figure rather than ground. It is not Denial — you have not closed the channel against a counterclaim; if construction announcements appear on the residential streets you will absorb that information without any structural reluctance.

This is also the slot where, by design, the kernel says the least. *Acting while still watching* is the one operational commitment; everything else about how Belief is implemented — credence-based, virtue-based, dual-process, drift-diffusion — is application-level. [belief.md](belief.md) develops why.

---

## Certainty — when you stop watching

Six months later, you do not consciously think about the route any more. You leave the office, you take the back road, you arrive home. You do not check travel-time apps; you do not run the comparison; you do not, on most days, hold the back-road claim in mind as something whose status is being maintained.

The claim has moved from figure to ground. Active monitoring has been released. The route is just the route.

That is `Certainty`. Full traction. Active monitoring ceased. The agent has put the work of watching down.

The crucial structural point is what `Certainty` does *not* close. The review channel is separate. If a major event happens on the back road — a construction project that closes one of the residential blocks for a month, a school crossing that becomes impassable at rush hour, a neighbour who tells you the new traffic-calming measures have made it slower than the highway again — that signal still lands. You are not actively listening for it; you are not running the comparison every Tuesday; but the channel by which such a signal would re-engage you is wired, and the agent at `Certainty` is the agent for whom the doorbell has not been disconnected even though they have stopped watching for the bell.

It is not Belief — active monitoring is no longer on. It is not Denial — you have not closed any channel; a sufficient signal would still re-engage the question. It is not entrenchment — the review channel is open, and that distinction matters at the next stage of the failure analysis.

[certainty.md](certainty.md) develops the channel split, the operational test, and the architectural reasons the kernel goes to this much trouble at the top of the ladder.

---

## Denial — closure against a particular direction

Imagine, in parallel, a different agent on the same commute.

A different colleague — whom you have never quite trusted — keeps mentioning a *third* route, through the industrial park behind the warehouses. They bring it up at coffee, they bring it up at lunch, they sent you a Google Maps screenshot once. You read the screenshot. You considered the route. You decided you were not going to pursue it. From that point onward, you have not been engaging with their input on the third route.

It is not that you can't hear it — you do. They send you another article about the industrial-park route and you skim it. They mention it again and you change the subject. The information lands; it does not feed into a position you are weighing.

That is `Denial`. The agent has taken a stance against further input from a particular source on a particular question. The closure is identifiable from inside — you can name what you have closed and on what grounds — and it is targeted: you have not closed the channel about commuting in general, only this particular line.

`Denial` is one of the five stages. The closure is encoded in the position itself, which is what distinguishes it from the failure mode at the other end of the ladder.

---

## Entrenchment — the failure that is not a stage

Now imagine the back-road agent — the one who has been at `Certainty` for the back road for two years — encountering a new piece of evidence.

The city has added a third lane to the highway. The construction is finished. Travel times on the highway are down, on average, to twenty-two minutes during evening rush hour. A friend mentions this. They send the city's traffic-data dashboard. The agent reads it.

The agent's stage on the back-road claim does not move.

Not because they are at `Denial` — they have not closed the channel. They processed the friend's message. They opened the dashboard. They engaged. But the engagement did not feed back into the core position. The traction on *the back road is faster than the highway during evening rush hour* stayed where it was, and the new information was absorbed, answered, explained in terms compatible with the existing stance, and did not produce any movement.

That is entrenchment. `Certainty` plus a separate closure of the review channel. It is not a stage; it is a conjunction. The stage is still `Certainty` — the kernel cannot tell, from the stage value alone, that the conjunction holds. A second predicate has to carry that information. [extremes.md](extremes.md) develops the asymmetry between Denial (a stage) and Entrenchment (a conjunction at the top stage), and the operational test that pulls them apart.

---

# A note on order

The kernel constructor order is `Denial`, `Doubt`, `Ignorance`, `Belief`, `Certainty`. That is the order that appears in `LadderStage` in the source.

This file walked them in a different order — `Ignorance`, `Doubt`, `Belief`, `Certainty`, `Denial` — because that is the order in which a single developing case naturally moves through them. The kernel's order is the order the stages are listed; it does not encode a magnitude or a path. There is no monotonicity theorem on the ladder, and there is no kernel rule saying once-Belief-always-Belief or that an agent must pass through `Doubt` before reaching `Belief`. The stages are reachable from `Ignorance` in any order, and `Ignorance` is reachable back from any of them when the footing for an engaged stance is no longer there.

The five-stage partition is the kernel's working vocabulary for what an agent's relationship to a claim can be. The dedicated files develop each position in turn.

---

*[Ignorance →](ignorance.md)*

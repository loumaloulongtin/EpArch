# Ignorance

The ladder names five stages an agent's traction on a claim can occupy: Ignorance, Doubt, Belief, Certainty, Denial. Four of them name a relationship the agent has to a claim — a stance taken, a position occupied, a channel closed. Ignorance does not. It names the absence of any such relationship.

The everyday word *ignorance* carries a moral charge: ignorant of, willful ignorance, an absence the agent should have closed. The kernel's `Ignorance` is a different object. It is the unmarked state, the one the architecture installs by default, and the one an agent's traction can return to when the footing for an engaged stance is no longer there.

This file is about that state — what it is, how an agent gets there, how an agent gets back to it, and what it is not.

---

## The default

The kernel installs Ignorance everywhere. Every (agent, claim) pair starts at Ignorance, by construction: the default `ladder_map` is the constant function returning `LadderStage.Ignorance`. The bank/ladder separation does the rest of the work: bank traces preserve the ladder map for every stage, not just for Ignorance, so once an agent is at Ignorance for a claim, no submission, challenge, revocation, or repair on that claim moves them off it. The kernel records this directly for the entry condition as `trace_cannot_elevate_ladder`: any trace which begins with the agent at Ignorance for a claim ends with the agent still at Ignorance for that claim.

What this means architecturally: the ladder is silent on a claim until something agent-side acts. The bank can fill up with deposits about a topic, get challenged, get revoked, get restored, and through all of it the agent's ladder for those claims stays at Ignorance unless the agent's own internal dynamics produce a stance.

So Ignorance is not just one stage among five. It is the stage every (agent, claim) pair occupies until something moves it. That gives it a structural role the other four stages do not have: every other stage is a place an agent has reached *from* Ignorance, and the agent had to do the reaching.

---

## Two routes in

There are two ways an agent ends up at Ignorance for a claim. Both are honest occupations of the state, and the architecture does not distinguish them at the level of the stage value — Ignorance is Ignorance — but the routes are different stories about how the no-engagement got there.

### Never engaged

Pick any specialist claim from a field you do not work in. The mass-loss profile of a particular pulsar. The morphology of a beetle described in a 1973 monograph. The standard reference voltage for a thermocouple junction at 400°C.

You are at Ignorance for it. Not Doubt — Doubt is a stance against a claim that has reached you and that you have engaged with. Not Denial — Denial is a closed channel against a known direction. Ignorance is what every (agent, claim) pair looks like before that claim has ever been encountered, weighed, or rejected.

This is the population case. Most claims, for most agents, are at Ignorance because no contact has happened. The kernel's default is honest about the world: an agent's actual epistemic surface area is tiny relative to the space of claims, and Ignorance is what the rest of the space looks like from inside.

### Returned via staleness

The other route. An agent had a stance — a Doubt, a Belief, a Certainty — and the deposits supporting that stance have aged past their τ. Nothing current has come in to replace them. The footing on which the stance rested is no longer warrantable.

The agent's traction can revise back to Ignorance. Not because the claim has been refuted; nothing has come in to refute it. Not because the agent has chosen to close the channel; that would be Denial. Because the basis on which the agent was holding an engaged stance is no longer current, and the agent is not in the business of holding engaged stances on stale footing.

The kernel does not legislate this transition. `agentTraction` is opaque, and the architecture deliberately leaves agent-side ladder dynamics open. What it provides is the room: there is no monotonicity theorem on the ladder, no kernel rule that says once-engaged-always-engaged. An agent's overlay is free to demote on τ-expiry, and τ supplies the operational reason for it.

What this story shows about Ignorance:

- Ignorance is not just an entry condition. It is the state that registers "no current engaged footing here," whether the no-footing is *prior to* contact or *consequent on* the staleness of all extant contact.
- The two routes land in the same architectural state for the same architectural reason: there is nothing on which to hold an engaged stance. The kernel does not need to mark them differently because, at the level of the ladder, they are not different.
- The return route is permitted, not prescribed. Whether a particular agent's overlay actually demotes on τ-expiry is application-level. The architecture's contribution is that the slot is there, the transition is not blocked, and the operational driver (τ) is part of the structure.

---

## What Ignorance is not

Four neighbouring confusions worth pulling apart:

- **Not Doubt.** Doubt is a stance against a claim the agent has engaged with — the agent has the claim on radar and is actively weighing it down. Ignorance is the absence of any stance. An agent at Doubt has done work; an agent at Ignorance has not, or no longer has, anything to do work on.
- **Not Denial.** Denial is a closed channel against a known direction — the agent has the claim on radar and has decided not to take in further evidence on it. Ignorance is the absence of any channel state. An agent at Denial knows what they have closed; an agent at Ignorance has nothing closed and nothing open, because there is no engagement to characterise.
- **Not Forgotten.** Forgotten is a bank-side tombstone — operational deletion of a deposit slot for capacity reasons, with the index preserved. It lives on the bank side and solves a different problem: distinguishing "this deposit was deleted for storage" from "this deposit was revoked for epistemic reasons." Ignorance is an agent-side absence of stance. The two sit on opposite sides of the bank/ladder split. In particular, forgetting a deposit does not move any agent back to Ignorance for the underlying claim — Forgotten does not touch the ladder. If the topic is later re-deposited, the new deposit starts from the kernel's defaults, which include Ignorance for any agent who has not engaged with it. That is a void followed by a fresh default, not a return.
- **Not a defect.** The everyday connotation that ignorance is a state an agent should have left behind has no architectural counterpart. Ignorance is what no-engagement looks like, and no-engagement is the correct state to be in for any claim on which the agent has no current footing. The architecture does not adjudicate which claims an agent should have engaged with.

---

## What this file does not buy

A few things to head off explicitly:

- **The architecture does not say *when* an agent should return to Ignorance.** τ-expiry is a sufficient operational reason to demote, and the architecture is built so that demotion is available. Whether a particular agent's overlay actually triggers on τ-expiry, on what timescale, and against what threshold is application-level.
- **The architecture does not adjudicate which claims an agent should have engaged with.** Ignorance is not culpable. An agent at Ignorance for a claim they "should have known about" is in the same architectural state as an agent at Ignorance for a claim no one has heard of.
- **The kernel proves bank-side preservation of Ignorance; it does not prove or disprove agent-side return to it.** The "return is permitted" reading rests on the opacity of `agentTraction` and the absence of any monotonicity theorem, not on a positive theorem that says return happens. The architecture leaves room for return; it does not mandate it.
- **Ignorance is not a pseudonym for low confidence.** An agent at low Belief is at low Belief, not at Ignorance. Ignorance is the absence of a stance, not a weak instance of one.

---

## Takeaway

Ignorance is the unmarked state — what the ladder looks like in the absence of an engaged stance. Every (agent, claim) starts here, and every (agent, claim) for which the supporting deposits have gone stale can return here. The other four stages name engaged relationships an agent has to a claim; Ignorance names the state in which there is no such relationship to name, whether that is because the agent has not yet engaged or because the footing for prior engagement has aged out.

The kernel installs Ignorance by default and the bank/ladder separation keeps it there: bank traces do not touch the ladder, so the default persists until something agent-side acts. On the agent side, the kernel is silent — `agentTraction` is opaque — which is what makes return to Ignorance available as a principled response to staleness rather than an architectural violation. Ignorance is, in that sense, the most populous and the most quietly load-bearing of the five stages: the one every claim starts at, the one most claims stay at, and the one a claim can come back to when the footing for any other position is no longer there.

---

*[← States](states.md) · [Doubt →](doubt.md)*

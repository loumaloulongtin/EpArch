# The Three Siblings Story

*[← Agent](../agent.md) · [States →](states/states.md)*

---

## Cluster

- [Agent](../agent.md) — what the architecture means by *agent*
- [The Three Siblings Story](ladder.md) — what a *stance on a claim* is, and what it isn't *(you are here)*
  - [States](states/states.md) — the five stages walked through one developing case
    - [Ignorance](states/ignorance.md) · [Doubt](states/doubt.md) · [Belief](states/belief.md) · [Certainty](states/certainty.md) · [The Extremes](states/extremes.md)

---

## Same fact, three relations

Three siblings on a group call. Their mother had a small fall that morning. The ER discharged her. The hospital sent a chart that says *patient stable, cleared for home*.

Anya, the eldest, has read the chart. She is going on with her day. She was on the phone with her mother an hour ago and the voice sounded like the voice always sounds. As far as Anya is concerned, mom is fine, and the next time anyone brings it up she will say so.

Ben, in the middle, has also read the chart. He is not going on with his day. The chart said *cleared for home* but the chart said the same thing six months ago and that turned out badly. He is on the kitchen counter making a list of things that would have to be true for *fine* to mean fine — has she eaten, can she stand from the toilet without help, did the discharging doctor actually look at her or did they just look at the report. He is not at *she's not fine.* He is at *I'm not done with this question.*

Caro, the youngest, has not read the chart. Caro is on the call but she is shopping for groceries; she said *oh good* when she heard *cleared for home* and went back to choosing tomatoes. She has not engaged with the question at all. If asked a direct question about the situation, she would have to think about it from scratch, because she has not started thinking about it.

One claim — *mom is fine* — and three siblings sitting in three completely different relations to it. Anya is acting on it. Ben is actively pressing on it. Caro hasn't picked it up. And the one fact about the world is unchanged across all three; nobody's relation to it has moved it. The hospital's chart, the bank record everybody is referring to, says what it says no matter which sibling is doing what.

That picture — one claim, three sibling-shaped slots, each one with its own relation to the claim — is what the architecture means by an agent's *traction* on a claim. Each agent has, for each claim, a stance. The stance is not a number. It is not *how confident* they are. It is the *kind of relation* they are in with the claim: acting on it, pressing on it, ignoring it, and a couple of others the next files name. The architecture's word for this whole apparatus — the per-agent, per-claim relation — is the *ladder*. The five kinds of relations are *ladder stages*. That is what this file is about.

---

## The relation, not the magnitude

Notice what changes if the call is reframed as a numbers question.

*Anya, how confident are you that mom is fine?* She might say 0.9. *Ben?* He might say 0.55. *Caro?* She'd shrug — 0.7 maybe, she hadn't really thought about it. Three numbers in a row, ranged from low to high. Now do something with them: average them, take Ben's as the most cautious, lean toward Anya's as the most informed. Compare them across siblings. Watch them move over the next hour as more information comes in.

Everything important about the original picture has been thrown away.

A magnitude can be averaged; a relation cannot. Anya is *acting* on the claim — she has gone back to her day. Ben is *pressing on* the claim — he is not going back to his day until he is satisfied. There is no number you can pick that captures the difference between acting-on and pressing-on; they are different *kinds of engagement*, not the same engagement at different intensities. If you converted them both to numbers and averaged them, the kitchen-counter list and the going-on-with-the-day would both be replaced by some middle number that nobody is actually doing.

A magnitude flattens diagnosability. With the numbers, all you can do is compare and aggregate; with the relations, you can ask different operational questions of each. Ben is making a list — *which list?*, *what would close the question for him?* are well-formed questions. Caro hasn't engaged — *what would get her to engage?* is well-formed. Anya is acting — *what would get her to stop and re-check?* is well-formed. None of these questions can be asked of a number. The number tells you who to listen to first; the relation tells you what is actually going on with each sibling and what would change it.

A magnitude makes nothing operational. *0.55* doesn't tell you whether Ben is going to do anything next. *Pressing on the claim* tells you exactly what he's doing — he's making the list, he's about to call the discharging doctor, he's not letting it go. The relation has handles you can pull on; the number is just a label.

The architecture's commitment, then: each sibling's stance is one of a small number of *kinds of relation*. Not a position on a slider. There are five of them, named in the next file, and the work each one is doing is not its position in some ordering — it is the operational shape of the engagement it names. A stage is *something the agent is doing with the claim*, not *how much of something the agent has*.

---

## Same name, different traction

The fact that all three siblings can sit in different stances on the same claim, simultaneously, with no contradiction — that is the per-(agent, claim) structure of the ladder, and it is the load-bearing piece.

The architecture's stance vocabulary is a function. It takes an agent and a claim, and it returns the agent's stage on that claim. *Anya on mom-is-fine* → acting on it. *Ben on mom-is-fine* → pressing. *Caro on mom-is-fine* → not engaged. Same claim three times, different agent each time, three different answers. Nothing in the architecture says these have to be reconciled. There is no *the family's stance on the claim*. There are three siblings' stances, each tagged with whose stance it is.

Per-claim matters too. Anya is acting on *mom is fine*. She is not necessarily acting on *the discharging doctor was thorough*. She might be at the *pressing* relation on that one. The same agent can sit in different relations to closely related claims, and the architecture supports that without ever needing to compute a person's "overall stance." There is no overall stance. There are per-claim stances, one per claim the agent has any relation to. Everything richer is the application's job.

This indexing — agent and claim, both — is the agent-side mirror of how the bank cluster handled bubbles. A claim can be deposited in one bubble and revoked in another with no contradiction. An agent can be at one stage on a claim and another agent at a different stage on the same claim with no contradiction. Both refusals — to aggregate across bubbles, to aggregate across agents — are doing the same architectural work: keeping the system's vocabulary granular enough that real disagreements are recordable as disagreements rather than as resolved single answers.

---

## The bank can't move it

Now suppose the chart updates. The hospital amends the discharge to *cleared for home, see follow-up in 48 hours.* The bank's record is now different. The shared ledger, the part of the architecture all three siblings can read, has changed.

What does this do to each sibling's stance?

*Anya is going on with her day.* The chart amendment doesn't reach her — she has already moved on; she wasn't watching the chart. Her stance on *mom is fine* is still *acting on it* unless she goes back and looks. Even if she does look, looking is something *she does*, not something the chart does to her.

*Ben is pressing on the claim.* The amendment is a new piece of information; he reads it and decides whether it adds to his list, subtracts from it, or is irrelevant. The amendment didn't lift him off pressing. He's still pressing, possibly with one item ticked off the list and another added.

*Caro hasn't engaged.* The amendment is sitting in the bank, but Caro hasn't read the chart. The amendment lands in a place she isn't looking. Her stance is unchanged because no one updated *her*.

In the architecture's terms: nothing the bank does, by itself, moves any agent's ladder. The bank can have things added to it, removed from it, repaired, revoked — and an agent who has not engaged with those things stays exactly where they were. This is the architecture's strict separation between the shared ledger and the private stance. The two layers run in parallel. The bank cannot move an agent's stance by itself. What moves the stance belongs to the agent-side overlay: the agent noticing, receiving, reasoning, reacting, or otherwise updating through whatever cognitive or operational dynamics the application supplies.

The kernel proves this directly. A sibling who started at *not engaged* on a claim and then watched any amount of bank activity — additions, challenges, revocations, repairs — is still at *not engaged*. The bank can fill up around the claim and the sibling stays where they were. Symmetrically: if a sibling has chosen to *stop reading* a particular kind of update — *I've stopped looking at the hospital's app notifications, they're too anxiety-making* — no amount of bank activity opens that channel back up. The closure is the sibling's, and the bank does not get to discharge it.

In the kernel, the closure predicate is indexed by agent and claim. When this story speaks about a kind of update or channel, that is application-level structure represented through the claim context, the surrounding deposit/header context, or the agent-side overlay.

This separation is what makes it possible for the architecture to say things like *the agent at acting-on may turn out to have been wrong* and *the agent at not-engaged may turn out to have been right.* The agent's stage and the underlying truth of the claim are different objects. The chart says what it says; the doctor was thorough or not; mom is or isn't fine; and each sibling is in whatever relation they are in to the claim, independently. The architecture holds these apart.

---

## What the kernel commits to

What the kernel actually says about the ladder is small.

Every (agent, claim) pair has a stage. Each pair has exactly one stage at a time. The bank cannot move it. That is essentially the whole list.

What the kernel does *not* say is also worth being explicit about, because of how easy it is to read in things that aren't there.

There is no rule about how an agent gets *from* one stage *to* another. Anya could go from *acting* to *pressing* — overhearing a tone in her mother's voice on the next call, reaching for the chart again, restarting the question. Caro could go from *not engaged* to *acting* — Ben could text her *call mom right now* and Caro could call and end up at *yes she's fine.* The transitions happen. The kernel says nothing about them. The five Bayesian and virtue-epistemic and dual-process and drift-diffusion accounts of how stances move can each sit on top of the architecture; the kernel adjudicates none of them. They are application-level overlays on the slot the kernel defines.

There is no order on the stages in the magnitude sense. Acting-on is not "more than" pressing-on; pressing-on is not "more than" not-engaged. There is no sliding scale they sit along. The five stages are five kinds of relation, and the architecture treats them as a partition — five categories an agent's stance falls into for a given claim — not as five marks on a ruler. The next file walks through what each category actually is and why this is the right cut.

There is no aggregation. No *family's stance*. No *Anya's overall epistemic state*. The function is per-(agent, claim), and the kernel maintains the discrimination at that grain directly, refusing to provide any coarser summary.

That is the whole shape. A per-(agent, claim) stance, one of five kinds, that the bank cannot move and the kernel does not summarise. Every richer story — about how stances change, about how they relate to confidence numbers, about how to compare across agents — sits *on* the architecture, not *in* it.

---

## Takeaway

The ladder is the architecture's vocabulary for what kind of relation an agent is currently in with a claim. Five kinds of relation — the next file walks each one through a developing scene — indexed per-(agent, claim), and not moved by bank activity alone.

It is not a confidence scale. The siblings on the call are not at three different numbers; they are doing three different things with the same claim. *Acting on*, *pressing on*, *not engaged* are not magnitudes of one shared engagement; they are different kinds of engagement, each with its own operational handles. Diagnosability is what the partition buys, and a magnitude flattens diagnosability away.

It is not a model of how minds change. The transitions between stages — what gets Anya to start pressing, what gets Caro to engage, what gets Ben to settle — are real events that happen in real lives, and the architecture says nothing about them. Whichever account of cognition the application installs is what supplies that story; the kernel only requires that the resulting stance function still attach a single stage per agent per claim, and still be unmoveable by bank activity.

The independence from the bank is the agent-side / shared-ledger split, in formal form. The chart can change while a sibling's stance does not, and a sibling's stance can change while the chart does not. The two sides of the architecture run in parallel and meet only when an agent takes an action that touches the bank, or sees a bank entry and chooses to update. Everything else is held apart on purpose.

The next file, [states](states/states.md), walks the five stages through a single developing case so each kind of relation can be felt one at a time. Each stage then gets its own short file. This file is the frame those files hang on.

---

*[← Agent](../agent.md) · [States →](states/states.md)*
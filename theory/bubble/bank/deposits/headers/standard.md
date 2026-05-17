# The Cook Story — Part 1

*[← Header Fields](headers.md) · [Error Model →](error-model.md)*

---

## Same proposition, different reasonable outcomes

Imagine a diner at a restaurant.

The diner asks the waiter:

> Are there peanuts in that meal?

The waiter replies:

> No, we don’t use any in the recipe.

That yields a deposit roughly like this:

* **P**: There are no peanuts in the meal.
* **S**: “No peanuts” is being answered here at the standard: peanuts are not part of the recipe ingredients.
* **E**: The waiter could be lying.
* **V**: An employee of the restaurant—the waiter—asserted it.

There is also a path to redeemability:

* **Path**: order and eat the meal.
* **Contact**: the meal reaches the taste buds.
* **Verdict**: it tastes like peanuts, or it does not.

So the claim is, in principle, redeemable.

But redeemability is not always the right immediate path for adjusting the ladder. Sometimes it is too late, too costly, or too risky to use as the way of finding out. The issue is not only whether the world could eventually settle the matter. The issue is whether the deposit is good enough to rely on **before** that vindication event happens.

So in practice, the answer has to travel over a **trust bridge**. Either the diner accepts the waiter’s assertion for present purposes, or they do not.

The interesting part is that the proposition stays the same while the reasonable outcome can change completely depending on the agent.

---

## Case 1 — The diner simply dislikes peanuts

Suppose the issue is only that the diner dislikes the taste of peanuts.

The deposit is still:

* **P**: There are no peanuts in the meal.
* **S**: no peanuts in the recipe.
* **E**: the waiter could be lying.
* **V**: an employee asserted it.

The path to redeemability still exists, but it is not the path the diner wants to use right now. They do not want to eat the meal in order to test the claim. They want to know whether the answer is good enough to act on *now*.

Here, for these stakes, it is reasonable to accept the deposit.

Why?

Because the **standard** is good enough for what the diner cares about. If they merely dislike peanuts, then “not part of the recipe ingredients” is already a perfectly sensible way to answer the question. That standard fits the concern.

The **error model** is acceptable too. Of course the waiter could be lying. But why would he? The payoff seems low. It is hard to see why he would want to provoke a returned plate, an awkward public conflict, or trouble for the restaurant over something so easy to contest. The risk is not zero, but it is low enough to tolerate.

The **provenance** is also good enough. An employee assertion is acceptable for this level of stakes. The diner might not demand more.

So the deposit clears the trust bridge.

At that point, the diner’s ladder can reasonably move upward.

It may remain at **Belief**: the diner acts as if **P** is true, but stays somewhat vigilant. Maybe they pay a little attention to the first bite.

Or it may move to **open-channel Certainty**: the diner acts as if **P** is true and stops actively monitoring it. The matter is settled for them, but the review channel is still open if reality pushes back.

That distinction matters, because **Certainty is not itself pathology**. Pathology is **Entrenchment**: certainty plus a closed review channel. An entrenched agent is not merely confident; they become uncorrectable. At the limit, an entrenched agent could be chewing a spoonful of peanuts and still insist there are none in the meal, because "the waiter said so." The problem is not high traction. The problem is traction insulated from revision.

But in the ordinary case, none of that pathology is present. The deposit is simply good enough for action.

So the diner accepts it and moves on.

As far as the diner is concerned, there are no peanuts in the meal.

If the later vindication event says otherwise—if peanuts are clearly tasted—then the diner updates the deposit, revises their stance, and issues a challenge. If not, then the deposit remains serviceable. The next time the diner comes back to the restaurant, they may recall that deposit and rely on it again without asking.

---

## Case 2 — The diner is allergic

Now change only one thing:

The diner is allergic to peanuts.

The proposition is still the same.

The waiter still says:

> No, we don’t use any in the recipe.

So again we get something like:

* **P**: There are no peanuts in the meal.
* **S**: “No peanuts” is being answered at the standard: peanuts are not part of the recipe ingredients.
* **E**:

  * the waiter could be lying,
  * there could be cross-contamination,
  * ingredients may come from peanut-handling factories,
  * the kitchen may prepare peanut dishes using the same tools or surfaces.
* **V**: an employee of the restaurant—the waiter—asserted it.

There is still a path to redeemability, but now it looks different:

* **Path**: order and eat the meal.
* **Contact**: the meal enters the body.
* **Verdict**: I survive, or I do not.

So yes, reality can still settle the matter.

But now that redeemability path is **out of the question** as a practical route.

It is a matter of life or death. “Eat it and see” is not an acceptable calibration strategy.

So again, the answer has to be handled over a trust bridge.

But this time the deposit does **not** clear it.

And the reason is crucial:

It is not that **P** changed.
It is not that the waiter’s sentence became meaningless.
It is not even that the provenance is obviously terrible.

What changed is that the **standard is too low for the stakes**, and the **error model is incomplete in exactly the ways that now matter**.

“No peanuts in the recipe” is not the same as “safe for a peanut allergy.”

That difference might not matter in the first case. Here it matters completely.

The waiter’s answer is still a real answer. It just answers the question at a weaker standard than the one now required.

So the diner issues a **challenge**.

And the challenge is not:

> Are you sure?
> Are you really sure?
> Come on, tell me there are definitely no peanuts.

That would just be re-asking the same thing in the hope of getting a stronger answer for free.

The real challenge is more like:

> Okay, but do the ingredients come from factories containing peanuts, or do you cook other recipes with peanuts in the same kitchen?

That matters because it makes the missing standard explicit.

It is tempting to object that the diner could just say "I'm allergic" and skip the long question. That move is not architecturally different — it is a compressed version of the same standard, transmitted in the hope that the other party can decompress it into the diner's actual expectations. In a restaurant setting that compression is often reasonable: it is fair to expect the staff to expand "I'm allergic" into roughly the same checks the long form would have requested. But it is still lossy. If the waiter does not decompress it the way the diner intended, and replies with an equally compressed answer — "Yes, it's safe for allergic people" — both sides have exchanged short strings that each privately decoded into different standards. That mutual compression, with no check that the two expansions match, is fertile ground for an accident. The long form wins not because compression is wrong but because it forces the standard to travel explicitly, where any mismatch is visible immediately rather than after the meal.

The underlying concern has not changed. The diner still wants to know whether the meal is safe with respect to peanuts. A yes or no still matters. The proposition is still doing the same practical job.

What failed was not the proposition by itself. What failed was the **standard at which the proposition was answered**, given the context.

The deposit needs to be rebuilt at a higher standard, with a richer error model.

Maybe the waiter can answer that. Maybe he cannot. Maybe the provenance now needs to shift from “the waiter said so” to “the cook confirmed the preparation conditions.” But whatever happens next, the architectural point is already visible:

the challenge is not necessarily a rejection of **P**.
It is often a rejection of the **conditions under which P was accepted**.

---

## What this shows

This shows that the same proposition can rationally lead to two opposite outcomes.

In both cases, the question is:

> Are there peanuts in the meal?

In both cases, the waiter says no.

In both cases, the claim is in principle redeemable.

And yet:

* in one case, the deposit is acceptable and can settle action;
* in the other, the same deposit must be challenged immediately.

So the difference is not simply truth versus falsity.

The difference lies in:

* the **standard** being used,
* the **error model** considered relevant,
* the acceptable **provenance** for the stakes,
* and therefore the threshold for moving the ladder.

The proposition stays the same.
The agent-context changes.
And once the agent-context changes, the architecture around the claim has to change with it.

That is why the same **P** can produce two opposite but completely reasonable outcomes depending on the agent.

---

## Part 1 takeaway

Same proposition. Same answer. Different stakes. Different trust threshold. Different reasonable ladder outcome.

The deposit carries more than P. It also carries the standard at which P was answered, the error model it is being judged against, the provenance it arrived through, and whether redeemability is available as an immediate route. Two agents reading the same answer at different stakes can read different deposits.

From this angle, a challenge is often not a denial of the claim. It is a demand that the claim be answered at a different standard.

---

# The Cook Story — Part 2

## The unacceptable standard

Part 1 showed that the right standard varies with the stakes. Part 2 runs the same two cases again — but adds a single fact to the error model: the waiter is a known liar. The question is what that changes, and why.

Take the same restaurant situation as before.

Same meal.
Same question.

> Are there peanuts in that meal?

Same answer from the waiter:

> No, we don’t use any in the recipe.

So again we get a deposit like:

* **P**: There are no peanuts in the meal.
* **S**: the claim is being accepted on the waiter’s testimony alone.
* **E**: the waiter could be lying.
* **V**: the waiter is the one who said it.

Now add one more thing to the error model:

* **E**: the waiter is a known liar.

That changes the case.

And the important part is this:

The failure is **not** that V became false.
The failure is **not** that E and V contradict each other.

V is still perfectly correct:

> yes, the claim came from the waiter.

E is also perfectly correct:

> yes, the waiter is unreliable.

So both E and V are structurally fine.

The problem is **S**.

The standard is still:

> waiter testimony alone is enough.

But once E explicitly says the waiter is unreliable, that standard becomes unacceptable.

The void is in S.

---

## Case 1 — The diner simply dislikes peanuts

Take the low-stakes case first.

The diner does not like peanuts.
The diner is not allergic.

In Part 1, the waiter’s answer was good enough.

But not anymore.

Why?

Because now the diner knows that the standard being used is:

> accept the claim on this waiter’s word alone.

And they also know:

> this waiter is a known liar.

So the issue is not mainly the proposition.
The issue is not even mainly the provenance in the sense of tracing where the claim came from.

The issue is that the **standard still permits sole-source testimony from a source already marked by E as unreliable**.

That is too weak.

So the diner does not accept the deposit in its current form.

And the diner’s challenge is not:

> Are you sure?

It is more like:

> Can someone else confirm?

Because what is being challenged is the standard.

The diner is saying:

> I will not accept “the waiter alone said so” as enough anymore.

Maybe another waiter confirms it.
Maybe the cook confirms it.
Maybe the manager confirms it.

The point is not that the diner needs a different proposition.

The point is that they need a **different standard of acceptance**.

The claim may stay exactly the same.

But the deposit cannot keep being grounded in sole-source testimony from someone the error model already marks as untrustworthy.

---

## Case 2 — The diner is allergic

Now take the allergy case again.

The deposit becomes:

* **P**: There are no peanuts in the meal.
* **S**: the claim is being accepted on the waiter’s testimony alone.
* **E**:

  * the waiter is a known liar,
  * there could be cross-contamination,
  * ingredients may come from peanut-handling factories,
  * the kitchen may prepare peanut dishes using the same tools or surfaces.
* **V**: the waiter is the one who said it.

And the redeemability path is still:

* **Path**: order and eat the meal.
* **Contact**: the meal enters the body.
* **Verdict**: I survive, or I do not.

So redeemability still exists in principle.

But again, it is out of the question as an immediate route.

The diner is not going to use possible death as a fact-checking method.

So the answer has to be handled over a trust bridge.

But now the deposit fails twice over.

First, the **standard is already too low** for allergy-level stakes.
Second, that weak standard is being grounded in **sole-source testimony from a known liar**.

So the problem is not just that the answer is incomplete.

The problem is that the acceptance condition is broken from the start.

And again, the right challenge is not:

> Are you really really sure?

The challenge is something like:

> Can someone else confirm?
> And can they answer about cross-contamination and shared preparation too?

That is, the challenge raises the standard in two ways:

1. it asks for **better grounding of V**,
2. and it asks for a **better S**, one that fits the actual risk.

The proposition still has not changed.

What changed is what counts as an acceptable way of answering it.

---

## What this shows

This part is different from Part 1.

In Part 1, the same proposition produced different outcomes because the stakes changed, so the acceptable standard and error model changed with them.

In Part 2, the key point is even more specific:

**the deposit can fail while E is right and V is right.**

It fails because S is still too weak.

The standard says:

> this source alone is enough.

But E already says:

> this source is unreliable.

So the deposit collapses not because the proposition is nonsense, and not because the provenance trace is false, but because the **standard of acceptance is vacuous in light of the error model**.

That is why the challenge remains focused on standard:

> Can someone else confirm?

The proposition stays the same.
The source trace can stay the same.
The error model stays the same.
What must change is the standard under which the deposit is accepted.

---

## Part 2 takeaway

A deposit can fail with P meaningful, E accurate, and V accurate. The failure lives entirely in S: the standard accepts a source that the error model already marks as unreliable.

The repair targets S, not P or V. Moving from

> the waiter said so

to

> someone else can confirm

is a move from sole-source testimony to corroborated testimony. The proposition and the source trace are unchanged; the acceptance condition is what shifts.

---

*[← Header Fields](headers.md) · [Error Model →](error-model.md)*
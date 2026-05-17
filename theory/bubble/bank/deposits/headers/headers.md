
# Headers

*[← The Claim](../claim.md) · [Standard →](standard.md)*

---

## In this series

- [Standard](standard.md) — V and S fields: the cook story
- [Error Model](error-model.md) — E: the throw story
- [Provenance](provenance.md) — V deep dive: the gift box story
- [Access Control](access-control.md) — ACL: the salary spreadsheet story
- [Redeemability](redeemability.md) — redeemability: the bushes story
- [Temporal Validity](temporal-validity.md) — τ: the milk and Rolex stories

---

## Why a deposit is more than P

The simplest mistake is to think that an epistemic system stores bare propositions.

In EpArch, the usable unit is not just a proposition **P**, but a **deposit**: **P** packaged with header structure that makes it diagnosable, challengeable, redeemable, exportable, restricted, refreshed, or rejected.

A bare answer is actionable. A deposit is repairable.

Headers are the metadata an agent uses to decide whether to act on a proposition, how much to rely on it, and how far to move it up or down its ladder in the current situation.

A header helps answer practical questions such as:

- Is this reliable enough for me here?
- What standard does it have to meet?
- What can go wrong if I rely on it?
- Where did it come from?
- Who is allowed to receive or use it?
- How can it be checked, redeemed, or cashed out?
- How stale is it?

In EpArch, a deposit packages a proposition **P** with a validation header. The pancake example below is not a replacement for the formal structure; it is an intuition pump for how the fields behave in ordinary reasoning.

| Prose name | Formal binding | Function |
|---|---:|---|
| Proposition | **P** | The claim or candidate payload. |
| Standard | **S** | What counts as passing here. |
| Error model | **E** | What failure modes have been considered. |
| Provenance | **V** | Where the claim or validation came from. |
| Temporal validity | **τ** / **T** | Currentness, TTL, or staleness marker. |
| Access control | `acl` / ACL | Who may receive, rely on, or use the deposit. |
| Redeemability | `redeem` / redeemability | How the claim can contact a constraint surface. |

Each header field will receive its own dedicated treatment later. For now, the easiest way to see how the fields work together is through a simple scenario.

## What this scenario is, and is not

The pancake walk-through below — and the per-field walk-throughs in the sibling files — is a pedagogical device. Its job is to introduce each header field cleanly and show that the field individually carries weight in a recognisable situation. It is not a model of cognition. It is not a claim about how an agent actually generates, weighs, or commits deposits, and it is not a claim about the timing or sequencing of any such process.

Even this single, deliberately thin scenario is humbling once you let it expand. We follow one deposit through to export, with each field reduced to one or two short strings. A real cooking event would traffic in many more deposits than that — about heat, pan position, batter consistency, splatter, where the child is standing, whether the smoke alarm is calibrated — most of them resolved in fractions of a second and never surfaced consciously. EpArch does not explain how that happens. What it offers is the field structure and the operations under which such data, however it is produced, can be diagnosed, challenged, and repaired. The scenarios show that the fields are the right shape to carry the data; they do not claim to show how the carrying gets done.

---

# Scenario: pancakes

The father's child is hungry and wants pancakes.

He is using an iron pan and asks:

> “What should I use to stop the pancake mix from sticking to the bottom?”

At this moment, the father does not yet have the final proposition he wants to export. He is searching for one.

The initial frame looks like this:

- **P**: Empty. This will eventually hold the answer he decides to rely on.
- **S**: “The ingredient he chooses will prevent the mix from sticking to the bottom of the pan.”
- **E**: Empty. There is no candidate proposition yet, so there is no error model to evaluate.
- **V**: Empty. There is no candidate proposition yet, so there is no provenance to track.

Strictly speaking, this is not a full deposit yet. It is a search frame — a hypothesis-shopping scaffold he fills in before any candidate becomes a deposit. (Distinct from `DepositStatus.Candidate`, which names the post-submission, pre-promotion state of a deposit already inside the bank.)

The goal is to fill this structure with something the child can reliably act on so he can cook the pancakes.

He now searches his memory for relevant hypotheses.

Six come back.

---

## Candidate 1 — Motor oil

He remembers someone on Reddit answering a similar question with:

> “Lol, motor oil!”

He discards this almost immediately.

The father may not consciously reason through the full deposit. He just rejects it. But if we reconstructed it, it might look like this:

- **P**: “Motor oil”
- **S**: “Used as a lubricant in cars; effective at high temperatures.”
- **E**: Empty at first.
- **V**: “Reddit.”

Once even minimal reasoning begins, the error model becomes obvious:

- **P**: “Motor oil”
- **S**: “Used as a lubricant in cars; effective at high temperatures.”
- **E**: “May be harmful to ingest. Potential fire hazard.”
- **V**: “Reddit.”

Given the relevant redeemability path — cooking pancakes in it and eating them — this error model is already enough to reject the candidate.

If someone insisted on pursuing it, the next step would be to investigate whether motor oil is harmful to ingest, whether it creates a fire risk, what quantities matter, whether studies exist, whether those studies are reliable, and so on. There is always more that could be verified. Even if a study showed people died after ingesting motor oil, one could still question whether it really happened, whether the quantities were comparable, whether the context was different, and eventually drift into “Is reality real?”

At some point, recursion has to stop. In this case, it stops almost immediately.

Motor oil is discarded.

---

## Candidate 2 — Animal fat

The next candidate is less absurd and not entirely useless.

- **P**: “Animal fat”
- **S**: “Effective and the most flavorful ingredient.”
- **E**: “May not be readily available. Not suitable for every recipe; duck fat may not be suitable for a chocolate cake.”
- **V**: “The chef at the hotel where he worked as a student asserted it.”

This candidate is interesting. The standard is compelling: effective and flavorful. The provenance is not bad either: a chef he worked with in a real kitchen.

But the decision turns on E.

There are many kinds of animal fat, and not all of them are appropriate for pancakes. More importantly, before even considering flavor compatibility, he realizes he does not have any animal fat readily available.

That forces an update to the standard itself. The original standard was too thin. It only asked whether the ingredient would prevent sticking. But the real task requires availability.

The frame now becomes:

- **P**: Empty. He is still trying to determine the answer.
- **S**: “The ingredient he chooses will prevent the mix from sticking to the bottom of the pan and will be readily available to him.”
- **E**: Empty. No final proposition yet.
- **V**: Empty. No final proposition yet.

Animal fat is discarded for this situation.

---

## Candidate 3 — Cooking spray

The next option is kept aside, but only as a fallback.

- **P**: “Spray”
- **S**: “Effective but unflavorful.”
- **E**: “His mother is not a very good cook. It may not be readily available. The lack of flavor may not produce the desired outcome.”
- **V**: “My mother’s ingredient of choice.”

This candidate is not irrational. It might solve the sticking problem. But it does not meet the emerging quality target very well. It is a practical fallback, not the preferred answer.

He keeps it in reserve.

---

## Candidate 4 — Butter

Now he encounters a serious option.

- **P**: “Butter”
- **S**: “Effective and flavorful.”
- **E**: “May not be readily available.”
- **V**: “Observed as a popular cooking ingredient many times throughout a lifetime. Personal experience.”

Butter is a strong contender.

It satisfies the original anti-sticking standard, and it adds flavor. The provenance is broad and familiar: repeated observation, common practice, and personal experience.

The main unresolved error mode is availability.

---

## Candidate 5 — Oil

Oil is another serious contender.

- **P**: “Oil”
- **S**: “Effective, cheap, and some types are flavorful, especially for pancakes.”
- **E**: “May not be readily available.”
- **V**: “Observed as a popular cooking ingredient many times throughout a lifetime. Personal experience.”

Oil is also plausible.

It is effective, cheap, and depending on the type, potentially suitable for pancakes.

Again, the unresolved error mode is availability.

---

## Candidate 6 — Coconut oil

Finally, the father remembers the ingredient he usually uses when he cooks pancakes himself.

This introduces another header field: **ACL**.

- **P**: “Coconut oil”
- **S**: “Effective, best flavor, and the ingredient that lets him hold the ‘best pancake cook’ title in the household.”
- **E**: “May not be readily available.”
- **V**: “Personal experience. Taught by his grandmother.”
- **ACL**: “Personal.”

The ACL tells the system who is authorized to receive or use this deposit.

Coconut oil is his secret ingredient. It is part of what makes his pancakes special, and he is not willing to share it with the household.

So even though the deposit is strong, he discards it from the export path.

Not because it is unreliable.

Not because it fails S.

Not because E is too scary.

Not because V is weak.

He discards it because the ACL says this deposit is not exportable to the child.

---

# Narrowing the candidates

After the first pass, he has two preferred options and one fallback:

- Butter
- Oil
- Spray, as fallback

Animal fat was interesting but unavailable. Coconut oil was excellent but ACL-restricted. Motor oil was rejected immediately.

The remaining candidates share one unresolved error mode:

> “May not be readily available.”

So the standard updates again.

The new frame is:

- **P**: Empty. He is still trying to determine the final answer.
- **S**: “The ingredient he chooses will prevent the mix from sticking to the bottom of the pan, be readily available to him, and be as flavorful as possible.”
- **E**: Empty. No final proposition yet.
- **V**: Empty. No final proposition yet.
- **ACL**: “Household.”

Now he needs to solve the availability problem.

---

# Checking oil

He decides to evaluate oil first.

He tries memory. But it has been too long since he last used oil, and nothing comes back that feels reliable enough.

So he moves to a redeemability path: he opens the pantry.

This introduces another header field: **redeemability**.

Redeemability names how the deposit can be checked, cashed out, or brought into contact with its constraint surface.

In the pantry, he finds a container that appears to contain some kind of oil, but it has no label.

The candidate deposit becomes:

- **P**: “This container contains oil.”
- **S**: “The texture of the liquid inside is oily.”
- **E**: “May not really be oil. May not be an oil type that fits well with pancakes. Unknown substances may be harmful.”
- **V**: “The content of the container looks like oil.”
- **Redeemability**: “Sensory investigation; cook with it.”
- **ACL**: “Household.”

This is a candidate, but the error model is scary.

So he inspects the container. He opens it, touches the liquid, checks its texture, examines its color, and smells it.

The deposit updates:

- **P**: “This container contains olive oil.”
- **S**: “The texture of the liquid is oily; on his finger the color matches olive oil, and it smells like olive oil.”
- **E**: “May not really be pure olive oil. May not be an oil type that fits well with pancakes. Unknown substances may be harmful.”
- **V**: “The content of the container looks like oil. His sensory experience with the liquid.”
- **Redeemability**: “Cook with it.”
- **ACL**: “Household.”

This is now reasonably convincing as an olive oil deposit.

But that does not settle the original task. Olive oil is not the kind of oil he prefers for pancakes. It may be oil, but it does not meet the updated standard as well as the better candidate.

He searches for another oil and finds none.

So the oil candidate is discarded.

---

# Checking butter

Butter is now the leading contender.

It still has the same unresolved failure mode:

> "May not be readily available."

For butter, memory gives him more to work with. He remembers buying butter during the last grocery trip. This introduces the temporal header: **T** or **τ**.

The availability deposit, formed from memory, looks like this:

- **P**: "We have butter readily available."
- **S**: "We bought butter the last time we went grocery shopping."
- **E**: "His partner could have used it."
- **V**: "His own memory of grocery shopping."
- **ACL**: "Household."
- **Redeemability**: "Open the fridge and observe whether there is butter."
- **T / τ**: "One week ago."

This looks good enough to act on. A week is not long. He did the shopping. He is ready to export "Butter" and move on.

Then he looks up and sees two pans of muffins sitting on the counter.

He did not go looking for this. The environment injected new evidence before he had a chance to export. The deposit mutates before he has done anything:

- **P**: "We have butter readily available."
- **S**: "We bought butter the last time we went grocery shopping."
- **E**: "His partner could have used it. The muffins on the counter suggest butter was used recently — amount unknown."
- **V**: "His own memory of grocery shopping. Two pans of muffins on the counter, consistent with recent butter use."
- **ACL**: "Household."
- **Redeemability**: "Open the fridge and observe whether there is butter."
- **T / τ**: "One week ago."

The muffins are a split signal. They confirm butter was available and was used. That cuts both ways: someone used butter recently, which means it was there; and someone used butter recently, which means less of it remains. The E term that was thin — "his partner could have used it" — has sharpened into something more concrete. The deposit that was almost exportable is now conflicted.

The redeemability path was always there. A moment ago it was optional — the memory alone felt sufficient. Now it is not optional. The split signal has made relying on memory alone the wrong move.

The redeemability path is cheap: open the fridge.

He does.

There is enough butter for the pancakes.

The availability failure mode is resolved for this batch.

It is not erased forever.

That distinction matters. "Butter is available now" can satisfy the current S, while "butter may not be available next time" remains a valid E term for future reliance.

Since butter is available now and meets the flavor standard better than spray, spray is discarded.

---
# The final father-side deposit

He is now prepared to form the final exportable deposit:

- **P**: “Butter.”
- **S**: “Will prevent the mix from sticking to the bottom of the pan. Readily available right now. Most flavorful option available at the moment.”
- **E**: “May not be readily available in future uses. Availability must be checked before relying on this answer again.”
- **V**: “The father: observed as a popular cooking ingredient many times throughout a lifetime. Personal experience. Availability checked directly in the fridge for this batch.”
- **ACL**: “Household.”
- **Redeemability**: “Cook with it.”
- **T / τ**: “Now.”

This is a good deposit.

It is not perfect. No deposit is. But it is good enough for the father’s household pancake situation as he understands it at that moment.

---

# Stripped export: “Butter!”

Of course, most of this can be stripped during export.

He could simply answer:

> “Butter!”

Then the child receives something much thinner:

- **P**: “Butter.”
- **S**: “Will prevent the mix from sticking to the bottom of the pan.”
- **E**: Empty.
- **V**: “Daddy told me.”
- **ACL**: “Household.”
- **Redeemability**: “Cook with it.”
- **T / τ**: “Now.”

This is actionable.

It may even be enough for this moment.

But it is lossy.

The child can act on the proposition, but the reasoning structure has been stripped. In particular, the child does not inherit the availability failure mode:

> “Butter must actually be available before this answer can be relied on.”

That creates downstream risks.

When the child recalls this later:

1. Will he remember to check whether butter is available before making the pancake mix?
2. If he sees someone using another ingredient, will he say, “Eww, that’s not butter”?
3. If he tastes pancakes cooked with canola oil and prefers them, will he conclude, “Daddy told me butter, but canola oil tastes better, so Daddy is not a great source for cooking advice”?
4. If someone asks “Why butter?”, will the answer collapse to “Because Daddy told me”?

The stripped export preserves actionability but weakens diagnosability.

It lets the child act now, but it gives him less structure for future reasoning.

One could argue that exporting more of the candidate set would help. If the child knew that spray was a fallback, oil was considered, olive oil was rejected, and butter was chosen because it was available and flavorful, then “no butter” would not automatically collapse into “no pancakes.”

But agents are not perfect either. The father's deposit failed to model something.

Fortunately, that gives us something useful to discuss while the family finishes making pancakes.

The stripped version is not the path this scenario will follow. It is a branch showing what can happen when P travels with too little header structure.

Return now to the main path: the father exports a reasonably rich household deposit. It carries P, S, V, ACL, redeemability, and τ, but it still has one missing E term — the one his own competence had backgrounded.

---

# The missing E term

Back on the main path, the export happens. The child receives a usable deposit, not merely the word “Butter!”, but the father's export is still incomplete in one important respect.

The child cooks the pancakes.

But they are not as good as anyone expected.

He did everything right as far as he knew.

The problem is that the father's export failed to include a common error mode for cooking with butter:

> “Butter is more difficult. It can burn if left unattended or if the heat is too high.”

This was not catastrophic. The pancakes only have a slight flavor of burnt butter.

But it matters.

His own butter deposit had degraded in one specific way: because he is confident in his own cooking skills, he no longer actively reasons about the “butter can burn” failure mode. His competence absorbs it. For him, that E term is backgrounded.

For the child, it is live.

The father-side deposit was good enough for the father’s ladder calibration, but not complete enough for the child’s ladder calibration.

That is the key lesson.

A deposit that is adequate for one agent may be under-specified when exported to another agent with different skill, experience, context, or feedback loops.

The child updates his own error model:

- **P**: “Butter can be used for pancakes.”
- **S**: “It prevents sticking and tastes good when handled properly.”
- **E**: “Butter may not be available next time. Butter can burn if the heat is too high or if it is left unattended.”
- **V**: “Daddy told me to use butter; I tried it;”
- **Redeemability**: “Try again with lower heat and closer attention.”
- **T / τ**: “Now.”

Stores it in its bank as a candidate.

The next time he cooks pancakes, he will be more careful.

The architecture learned.

---

# What the scenario shows

Headers are not passive metadata. They are the structure an agent uses to calibrate its ladder.

In the scenario:

- **P** carries the candidate answer.
- **S** defines what “good enough” means in context.
- **E** models what can go wrong if the candidate is relied on.
- **V** tracks why the candidate is supported.
- **ACL** controls who may receive or use the deposit.
- **Redeemability** names how the deposit can be checked or cashed out.
- **T / τ** tracks freshness and staleness.

Together, these fields help the agent decide whether to act.

The father does not simply retrieve the word “butter.” He moves through a small epistemic workflow:

1. Generate candidate deposits.
2. Reject absurd or unsafe candidates.
3. Update S when availability becomes relevant.
4. Use E to identify unresolved risks.
5. Use V to rank sources.
6. Use ACL to block non-exportable knowledge.
7. Use redeemability paths to check availability.
8. Use τ to notice stale memory.
9. Export a deposit to the child.
10. Observe failure and update E.

The final answer is simple.

The calibration structure behind it is not.

---

# Takeaway

An export transmits P. It may also transmit some of the header structure around P. The two are independent: how much header structure travels is a separate decision from what proposition is being exported.

Sometimes “Butter!” is enough. Trust, context, and low stakes allow heavy stripping.

Stripping has a cost. It preserves actionability while reducing diagnosability. If something goes wrong later, the receiving agent has less to work with when locating the failure: P, S, E, V, ACL, redeemability, τ, or their own missing competence.

The structure an expert has internalized does not need to be made explicit for the expert. It does for the receiver who has not yet internalized it. Stripping an E term that is obvious to the exporting agent is safe when the receiver has already absorbed it, and lossy when they have not.

---

# How this lands in the bank

The scenario above shows the headers in motion, but it does not yet say how the resulting deposit is recorded — and the moves the child makes after the export are exactly what the bank operations are for. A short walk-through, in lifecycle vocabulary:

**Receiving the export.** The father exports a rich but imperfect deposit — P, S, V, ACL, redeemability, τ, and an error model that covers availability but misses one backgrounded cooking-skill error: "butter can burn if the heat is too high or unattended." The child receives it. At this point nothing has been written into the child's bank yet. Trust in the source plus a serviceable header bundle modulates his ladder enough to act on the proposition: he reaches for the butter and starts cooking. Acting on a deposit and recording one are independent moves; the bank operations describe the recording, not the acting.

**Recording the deposit.** Two routes are coherent here, and the architecture supports both. The child can `Register` the deposit directly once the pancakes are off the heat and the original "won't stick" question has been answered by the redeemability path itself. `Register` records the agent's assertion that the deposit is already sufficiently grounded and enters it directly as `Deposited`.

Or he can `Submit` it earlier as `Candidate` and `Promote` it once the evidence is in. The first route is closer to how a confident receiver actually behaves; the second tracks the lifecycle the reader has just walked.

**Challenge during eating.** The pancakes taste faintly of burnt butter. The child's standard for the deposit silently widens — "prevents sticking" was enough during cooking, but at the table the relevant standard is "prevents sticking *and* tastes good." Measured against the wider standard, the deposit no longer passes. That is a `Challenge`: the deposit moves from `Deposited` to `Quarantined`, with the slightly-burnt taste as the challenge evidence.

**Repair via re-export.** The child re-exports the now-Quarantined deposit upward, this time with the new standard attached. The father reads the standard, locates the missing E term ("butter can burn if the heat is too high or unattended"), and re-exports the deposit with that term added. On the child's side this is a `Repair`: the deposit returns to `Candidate`, not to `Deposited`. Repair restores eligibility to be promoted; it does not, on its own, re-promote.

**Sitting as Candidate.** The repaired deposit waits. There is no live cooking event to drive a promotion, and the child correctly does not promote on the strength of the father's revision alone. The next time he cooks pancakes, the redeemability path is walked again — this time with the burn-aware error model entry and the corrected standard — and a successful run drives the next `Promote`. If a run fails, the deposit gets challenged and repaired again. The lifecycle does not converge to a static final state; it converges to a deposit that has been challenged and repaired enough times that the receiving agent's calibration is doing real work.

This is also where the import becomes architectural rather than narrative: the headers are what makes any of these moves *legible*. Without P there is nothing to challenge. Without S a challenge cannot be phrased. Without E a repair cannot add anything. Without V the receiver cannot decide whether to act before recording. The lifecycle of `Submit`, `Promote`, `Challenge`, `Repair` operates on header-shaped data; the rest of the deposits cluster shows what the operations look like, and this scenario shows where the data they operate on comes from.

---

*[← The Claim](../claim.md) · [Standard →](standard.md)*
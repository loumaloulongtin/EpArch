# Convergence — Why the Menu Isn't Local

## Cluster

- *What a Working System Buys You — the five goals as a menu of outcomes* (`goals.md`)
- *Profiles — which goals a deployment holds, which it explicitly does not* (`profiles.md`)
- **Convergence — why the menu isn't local** *(you are here)*

---

## Sharks, dolphins, ichthyosaurs

A shark, a dolphin, and an ichthyosaur look more like each other than any of them looks like its closest land relative. The shark is a fish; the dolphin is a mammal; the ichthyosaur was a Mesozoic reptile. They are separated by hundreds of millions of years and entire branches of the evolutionary tree. They ended up streamlined, finned, fluked, dorsal-stabilised — converged on roughly the same shape — because the ocean was the same constraint set for each of them. None of them copied the others. The water did the work.

When you see that a charity, a software vendor, a research lab, and a regulator have all ended up with strikingly similar internal apparatus — an intake gate, a separate review tier, a published correction process, a withdrawal procedure, an export channel with provenance tags — your first instinct is probably to assume they read the same management book. Sometimes they did. Often they did not. They ended up with similar apparatus because they were all *operating under the same pressures*: distributed contributors, bounded reviewer time, hostile actors, claims that have to leave the building, multi-party access. Each pressure presses on a working system in roughly the same way. The institutions that responded to all of the pressures end up with roughly the same machinery, not because they coordinated, but because the pressures gave them no other shape to settle into.

This file is about what happens when you take that observation seriously. The five-goal menu from `goals.md` and the typed profile object from `profiles.md` could be read as artefacts of one model — a vocabulary the architecture's author happened to choose, that some deployments happen to land on. The convergence story says they are not floating in that way. The same architectural substrate is what any working system facing the eight pressures is forced toward. Once a deployment is projected into the `CoreModel` / bank-profile layer, the five goal questions are not private inventions of that deployment; they are read against structural slots supplied by the convergent architecture.

The cluster has been about *which goals a deployment holds.* This file is about *why the goal menu can travel across deployments*, and why a reader showing up at a profile from a different deployment than they expected can still read it.

---

## "We didn't copy each other"

A team building a clinical-decision-support system, a team building an industrial-quality-control system, and a team building a publishing platform all show up at the same conference and discover, midway through their respective talks, that they have built strikingly similar internal apparatus. Each has a notion of *accepted but unverified*. Each has a notion of *withdrawn for cause*. Each has a separate audit channel. Each has a way of marking a claim's epistemic standing on the way out the door. None of the three teams have read each other's design documents. Two of them have not heard of the third's industry.

The instinct in the room is to say *we have all converged on best practice.* But *best practice* is a name for something that needs explaining. Why did all three converge? Each was in a different industry, with different users, different regulators, different timelines, different budgets. The thing that was the same was not their domain. The thing that was the same was the *shape of the problem* — distributed contributors filing claims, an audit budget that does not cover everything, occasional bad actors, claims that have to leave the building and stand up elsewhere, multi-party access with different powers. Eight pressures, in roughly the same configuration, in each of three otherwise unrelated domains.

This is what convergence in this cluster means. It is not the lifecycle settling into a fixed point in time. It is *systems settling into the same architectural shape* once they are facing the same pressures. The architecture is what the room has converged on, and the goal menu is what every member of the room ends up able to publish a profile against.

The thing this rules out is the suspicion that a profile from one deployment cannot be read against a profile from a different deployment. If the menu were local — if each working system invented its own goal vocabulary — then the clinical system's *SoundDeposits* and the publishing platform's *SoundDeposits* would be, at best, suggestively similar. They would not be the same predicate. A reader trying to compare profiles across deployments would be doing translation, and the translation would have to be re-done for every new deployment that walked in. The convergence claim is that they don't have to. The five goals are not a brand a deployment opts into; they are *what shows up* once the pressures are in place.

---

## What the kernel actually proves

The kernel makes one narrow claim and labels it convergence. The claim is structural, not behavioural. It is not *the lifecycle approaches a steady state*; it is *any working system facing the full set of pressures contains the full set of forced features*. In `EpArch.Convergence` it is `convergence_structural`: a working system that is structurally forced and that satisfies all the architectural properties contains the bank primitives. Pressure by pressure, capability forces feature. There is no escape route through which a working system can face the eight pressures and end up *without* the apparatus the goal vocabulary speaks against.

What this gives the goals cluster is the warrant for a strong reading of what a profile is. A profile is not a private bookkeeping convention of one model. It is published against a standardized layer that sits on top of an architecture every working system facing these pressures was forced toward. When a deployment publishes *SoundDeposits: yes*, it is answering a standardized `CoreModel` question. Convergence explains why that question is not floating over an arbitrary private vocabulary: the broader architecture has already forced the shared structural setting in which bubble-relative truth, verification budgets, revision, export, and storage can be compared. The goal-name has cross-deployment meaning because the substrate the goal-name reads against is convergent.

This is also what makes the OdometerModel's profile honestly comparable to the lab's, even though one buys one goal substantively and the other buys five. They are answering the *same* questions. Different rows on the same table, not different tables. A reader can hold them next to each other and learn something from the comparison: not just *the lab buys more*, but *the lab buys more along the same axes*. Convergence is what makes the axes mean the same thing in both columns.

The narrow kernel claim does not say that two convergent systems are *identical* — they keep all the local extra structure that was theirs. It says they share *the eight forced features*, and therefore the goal vocabulary speaks against the same parts of each.

---

## What this cluster is not claiming

Convergence here is *structural*, not *temporal*. The claim is *systems facing the same pressures end up with the same architectural apparatus*. It is not a claim that the lifecycle approaches a fixed point as time passes, that claims in the system tend to a stable truth value, that revisions cease, or that disagreement among agents resolves itself in the limit. The kernel does not currently prove any of those temporal-limit things, and a reader expecting a *the system eventually settles* story will not find it here. The temporal-limit family of question — what does the long-run behaviour of the lifecycle actually look like, under what conditions does it stabilise, what counter-examples does it admit — is a separate cluster's worth of work, distinct from the structural convergence the kernel does prove.

Convergence is *given the pressures.* Drop a pressure, and the convergence claim no longer applies — there is no obligation on a system that does not face the eighth pressure to have the eighth feature, and the goal-row that depends on that feature is genuinely out of scope rather than negligently absent. This is the point the forcing cluster makes formal: the eight pressures and the eight features are paired, and dropping one pair undoes one row of the convergence story. A deployment that genuinely does not face, say, multi-agent access has nothing to publish on the row that requires authorization machinery, and is not failing to converge — it is operating in a smaller arena.

Convergence is about architecture, not world-correspondence. Two systems converging on the same architectural shape are still bookkeeping about their own models, not about the world. If the clinical system and the publishing platform both publish *SoundDeposits: yes*, they have both certified something about their internal verification machinery; they have not jointly certified that their respective claims are correct in the world. The world-side question stays where it was — in the bridges of the world cluster, with its own scope guards. Convergence makes the bookkeeping comparable; it does not promote the bookkeeping into a claim about the world.

Convergence does not say the deployments *should* hold the same profiles. The clinical system might land at four substantive yeses, one vacuous, none refused; the publishing platform might land at three substantive, one refused, one not claimed at all. The goal *vocabulary* is convergent; the goal *profile* a deployment holds against that vocabulary is downstream of cost, risk, and use, none of which the kernel models. The architecture's contribution is that the comparison is meaningful; the comparison's verdict is not.

---

## Takeaway

At the `CoreModel` / bank-profile level, the goal menu is not a private convention of one author's model. It is the shape that any working system facing the eight pressures ends up structurally required to have — the same in every domain that faces the same constraints, the same way oceans return streamlined animals from unrelated lineages. That is what makes the menu read across deployments: a *yes* on `SoundDeposits` from the clinical system and a *yes* on `SoundDeposits` from the publishing platform are talking about the same machinery, because the machinery is what the pressures forced in both cases.

Two scope notes ride along. Convergence here is structural, not temporal: the kernel does not currently prove that the lifecycle settles in any limit, and a reader who came looking for a long-run-behaviour story is in the wrong cluster. Convergence is also conditional on the pressures: drop one, and the corresponding row of the menu is genuinely out of scope rather than honestly disclaimed.

What this finishes for the goals cluster is the warrant for the comparison the previous two files have been quietly relying on. The menu is the menu *because the pressures are the pressures*, and a profile published against the menu is comparable to any other profile published against the same menu. The architecture's contribution is the convergent vocabulary; the deployment fills in the rows.

---

← [Profiles](profiles.md) · ↑ [Forcing](../forcing/forcing.md) · Next: [Autonomy](../autonomy/autonomy.md) →

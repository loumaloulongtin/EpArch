# Profiles — Naming a Deployment's Goal Stance

## Cluster

- *[What a Working System Buys You](goals.md) — the five goals as a menu of outcomes*
- **Profiles — which goals a deployment holds, which it explicitly does not** *(you are here)*
- *[Convergence](convergence.md) — why the menu isn't local*

---

## Two restaurants

A restaurant near you advertises *fresh, healthy, ethical food.* Inside, the menu lists six dishes. Each dish has its ingredients listed underneath it. There is a separate card on the table that names the four allergens the kitchen does not handle and the two it cannot guarantee against. There is a hand-stamped certificate by the door from the local food inspector. You can *check.* If you ask the server whether dish three contains shellfish, they will read you the ingredient line. If you ask whether the kitchen handles peanuts, they will read you the allergen card. The phrase *fresh, healthy, ethical* is on the wall but the wall is not what you order from.

A second restaurant advertises *fresh, healthy, ethical food.* That phrase is on the wall, and on the takeaway bag, and at the top of the website. The menu is a single page of dish names with no ingredients. There is no allergen card. There is no inspection certificate. If you ask whether the curry contains shellfish, the server says they will check, and comes back five minutes later having spoken to someone in the kitchen who said they think not. The first restaurant and the second restaurant make the same wall-claim. They are not making the same offer.

The difference is not honesty in the moral sense — the second restaurant may be entirely sincere. The difference is that the first restaurant has *an object you can interrogate* and the second has a slogan. When you walk into the first restaurant, the wall-claim is downstream of the menu, the allergen card, the certificate. When you walk into the second restaurant, the wall-claim is the whole offer, and the kitchen behind it could be doing anything.

A *profile* is what the architecture lets a deployment be the first restaurant about its goals. The wall-claim *we hold these goals* becomes a list of items, each item backed by a witness the kernel will read. A profile can distinguish two different absences: a goal not claimed by the configuration, and a goal explicitly rejected with a counter-witness. Tags chosen come with the receipt. Tags not chosen are not silently certified. When the deployment wants to publish an explicit *no*, it must carry the failing witness as part of the profile.

This file is about the apparatus that makes a deployment's goal stance into the menu-and-allergen-card object instead of the wall-claim. It is the second file in this cluster: `goals.md` was the menu of outcomes; this file is about what it takes for a deployment to honestly publish *which entries on the menu it serves*.

---

## What "we hold these goals" has to be backed by

The trouble with the slogan-restaurant is not that the kitchen is bad. The trouble is that the gap between *what the wall says* and *what the kitchen does* is invisible from the wall. Someone reading the wall has to take the kitchen on trust, and a different kitchen behind the same wall would produce the same wall.

The same gap shows up wherever an institution tells you what it stands for. A university whose admissions page lists *integrity, rigour, mentorship* as its values; a software vendor whose security page lists *encryption, audit, response*; a charity whose mission statement lists *transparency, accountability, impact.* The values are listed. What the listing *commits* the institution to is unclear. A second institution with the same list could be doing entirely different things behind it. The list is doing none of the work that *checking* would do.

The architecture's response to this pattern is not to demand fewer claims. It is to demand that each claim be paired with a witness the kernel can read. A deployment that wants to say *we hold SoundDeposits* has to supply, alongside the claim, the structural object the kernel will accept as a soundness witness. A deployment that holds the goal vacuously — the premise never fires — has to say so, and the kernel records the vacuity. A deployment that wants to publish *we do not hold this goal* as a positive part of its profile cannot get there by silence either; it has to carry a counter-witness exhibiting where the goal fails. A goal a configuration simply does not claim is in a third position — neither certified yes nor certified no — and a profile that wants to say more than that has to do the work.

What this changes is what a reader of a deployment's profile is doing. They are not reading a description; they are reading an inspectable object. *We hold SoundDeposits* with a substantive witness reads differently from *we hold SoundDeposits* with a vacuous witness reads differently from *we do not hold SoundDeposits, and here is the bubble where the goal fails.* All three are honest. None of them is the slogan.

---

## The kitchen and the brand promise

Consider a restaurant chain. The chain has a brand promise — a small set of claims that hold across every location: *all our beef is grass-fed, all our coffee is fairly traded, every dish we serve has its allergens labelled.* Each individual location has more going on than the brand promise mentions: a local supplier the head office has never heard of, a daily soup that doesn't appear on the printed menu, a bilingual server station, a different oven configuration in the kitchen.

When a customer walks into a location and reads the brand promise on the wall, two things have to be true at once for the promise to mean anything. First, the brand promise has to be a *real claim about that kitchen* — not just a claim about an idealised abstract kitchen at head office. Second, the local kitchen has to be *running in a way the brand promise can pull back to* — every grass-fed-beef commitment on the wall has to correspond to actual grass-fed beef in actual local fridges, and the local supplier has to be one whose paperwork the brand promise is willing to claim. If the local kitchen is doing something the brand promise has no way to see — buying its beef from somewhere the head office has never qualified — then the wall and the kitchen are out of contact, and the brand promise stops being checkable.

This is the situation every real deployment of EpArch is in. The deployment is the local kitchen — a richer object than the architecture's bare core, with whatever extra structure that particular deployment needs (extra agent state, instrumentation, scope tags, audit hooks, additional bubbles). The profile is the brand promise — a thinner, standardised object the deployment publishes against the goal vocabulary from `goals.md`. For the profile to be a real claim about the deployment, two things have to be lined up: there has to be a way to *publish* the rich kitchen as the standardised profile, and there has to be a way to *certify* that the publishing has not silently changed what the goals mean.

The architecture provides both. There is a publishing projection that strips the deployment's extra structure and leaves the standardised core the goal predicates speak against. And there is a faithfulness relation that says: when you take a fact about the rich kitchen, run it through the projection, and ask the standardised goal predicate about it, you get the same answer as asking the rich kitchen's own predicate directly. *That is what makes the brand promise a real claim about the kitchen.* Without the faithfulness relation, the kitchen could mean one thing by *sound deposit* and the published profile could mean another, and the wall and the kitchen would be slogan-related rather than evidence-related.

The architecture does not require the rich kitchen to be smaller or simpler. It requires the publishing to be faithful. A kitchen that wants to publish *grass-fed* on the wall must be able to point, for every steak it serves, at a paper trail that survives projection. A kitchen that is doing something the projection cannot see is not free to claim the brand promise covers it.

---

## The three honest stances

Once a deployment is publishing a profile against the standardised goals, every entry on the published menu is in one of three positions, and the architecture insists on telling them apart.

The first is *substantive yes.* The deployment holds the goal, and the goal does work. There is at least one bubble where the goal's premise fires and the conclusion holds non-trivially — actual deposits being soundly verified, actual revisions producing actual sound revised states, actual exports preserving actual epistemic standing across actual boundaries. The lab from `goals.md` is in this position on every one of the five `CoreModel` goals. When a reader sees the lab's profile, the substantive yeses are not paperwork; they correspond to predicates firing in the model.

The second is *vacuous yes.* The deployment holds the goal, but the premise never fires. The goal is satisfied by default because there is nothing to test it against. A factory that does not self-correct *vacuously satisfies* the goal *if you self-correct, then you have revision capability*, because the *if* is never true at that factory. This is not a trick — vacuous truth is still truth — but it is a different kind of holding from the substantive case. The lab and the factory both come in under the column heading *yes* on `SelfCorrectionGoal`, but only the lab's *yes* is doing work; the factory's *yes* is the absence of work being honest about itself. Conflating them is what produces the slogan-restaurant pattern: a profile that displays a row of checkmarks without distinguishing the ones that bind from the ones that are vacuous.

The third is *explicit no.* The deployment does more than omit the goal from its claimed set: it records a counter-witness showing why the goal fails — a bubble where a true deposit is unverifiable in the bubble's effective time, a revision that produces a false post-state, an export that turns false claims true. The kernel can exhibit the failing case. *Explicit no* is therefore not the same as *not yet decided* or *we will get to it next quarter* or even *we left it off the list*; it is a structural commitment to the negation, with the witness available. The slogan-restaurant cannot sit here. It cannot say *we do not hold this goal* because it cannot point at the kitchen-fact that breaks it; it does not have one because it does not have a profile at all.

A fourth position deserves naming, even though it is not a *stance*: a goal a particular configuration simply does not claim. The deployment has not supplied a witness for the goal and has not supplied a counter-witness against it; the goal is just absent from this configuration's certified surface. This is not dishonesty — it is the configuration being narrow on purpose — but it is also not a profile entry. A reader who wants the deployment to commit to one of the three stances above has to ask, and the deployment then has to do the work of supplying a witness or a counter-witness. Silence is not certification, in either direction.

The reason the architecture keeps the three cases distinct is the same reason the allergen card is separate from the wall. *Yes* is the wrong word if it covers both *we are doing this* and *the question never came up.* The allergen card on the first restaurant's table reads *we do not handle peanuts, tree nuts, sesame; we cannot guarantee against gluten, soy.* This is three different stances written down in a way the diner can use. A card that just said *we are nut-free* would be either lying or vacuously true depending on whether peanuts were in the kitchen, and the diner would have no way to tell which.

A profile of a deployment looks the same. The substantive yeses are the dishes the kitchen is in the business of cooking. The vacuous yeses are the questions the kitchen does not face. The explicit nos are the ingredients the kitchen does not handle. All three are part of the published object, and a reader who only consults the wall is consulting the wrong document.

---

## The odometer's profile, walked

The kernel ships a worked example exactly so this distinction is not abstract. The `OdometerModel` (`EpArch.Meta.LeanKernel.OdometerModel`) is a deliberately stripped-down deployment whose profile is published as a typed bundle (the kernel calls it `odometer_is_minimal_goal_witness`). The table the kernel records:

| Goal                  | Holds? | Reason                                                |
|-----------------------|--------|-------------------------------------------------------|
| SoundDepositsGoal     | yes    | every true reading is instantly verifiable            |
| SelfCorrectionGoal    | yes    | vacuously: `selfCorrects` is `False`, premise unfires |
| CorrigibleLedgerGoal  | NO     | no bubble has `hasRevision`                           |
| SafeWithdrawalGoal    | NO     | submission is always allowed; revision never is       |
| ReliableExportGoal    | NO     | truth is local; cross-bubble truth is not preserved   |

Read this as a profile rather than as a feature list. The first row is the odometer's substantive yes — the one thing the artefact is in the business of doing. The reading is true; the verification fits the budget; the goal's premise fires on every reading and the conclusion holds. A consumer who shows up wanting *the number to be true* is being told *yes, that is what this artefact does*, and there is structure behind the yes.

The second row is the row the slogan-restaurant would lie about. This artefact does not self-correct. It contains no apparatus for noticing that a reading was wrong and producing a corrected reading. The goal's premise — *if you describe yourself as self-correcting* — is structurally false here, so the implication holds vacuously. The kernel's bookkeeping says this in the row itself: *vacuously: premise unfires.* A consumer reading the row is not being told *you are getting self-correction.* They are being told *this question does not arise in this artefact, and we are recording why.* That sentence is the difference between an honest profile and a checkmark next to a feature you are not getting.

The bottom three rows are explicit nos, and each carries the structural fact that breaks the goal at this model. The artefact is free to publish them as nos because it has the witness in hand — there really is no bubble with revision capability, the submission really is always allowed regardless of revision, the truth predicate really is bubble-local. A consumer wanting any of these three is being honestly turned away at the published profile, not at the customer service desk after a purchase.

The kernel additionally proves a narrower extension fact: compatible extensions of the odometer preserve the *revision-gate safety property* after projection. It does not claim that every row of the five-goal odometer profile is automatically preserved by arbitrary compatible extension — that would be a much stronger result, and the kernel does not assert it. What survives is the revision-gate piece, which is the safety-side guarantee the lattice-stability cluster is built around. A franchise built on the chain's standards still meets the chain's *safety* standards; whether the rest of the brand promise transfers is a separate question for each row.

The other end of the menu is the lab from `goals.md` — five substantive yeses, no vacuous yeses, no explicit nos. Same architecture, same kind of profile object, different rows filled. The architecture's contribution is the *shape of the bookkeeping that holds both*, not a recommendation about which one a deployment should aim at.

---

## What this cluster is not claiming

The profile is bookkeeping about the model. It is not bookkeeping about the world. The lab publishing *SoundDeposits: yes* is making a checkable claim about its own acceptance, verification, and effective-time machinery. It is not making a claim that the chemicals in its bottles really are what the labels say — that is a world-side question that the architecture handles, with its own scope guards, in the world cluster's bridges. The profile's *yes* is a yes about the model's internal coherence, and a reader reading more into it is reading something the profile is not asserting.

Vacuous yes is not equivalent to substantive yes. The kernel keeps the cases distinct because the underlying model — which premises fire, which do not — is part of the profile and is inspectable. A presentation layer that surfaces only *yes* without surfacing the kernel's vacuity bookkeeping has erased information the profile carries. The architecture's commitment is that the information is *available*; what any particular consumer-facing display does with it is downstream of the architecture, and a display that flattens the distinction is exhibiting a presentation choice, not a kernel claim.

The deployment picks; the profile records the pick. The architecture does not recommend a profile, does not penalise an honest *no*, does not credit a substantive *yes* over a vacuous one in any ordering it imposes from outside. Which profile a deployment should hold is downstream of cost, risk, and use, none of which the kernel models. The architecture is the menu and the allergen card, not the restaurant critic.

The profile menu in this cluster covers the five `CoreModel` transport goals: SoundDeposits, SelfCorrection, CorrigibleLedger, SafeWithdrawal, ReliableExport. The sixth config-selectable goal — `autonomyUnderPRP` — is structurally a different shape and lives over a different model layer; folding it into this menu would either erase the layering or pretend the same publishing machinery applies to it. The autonomy cluster (forthcoming) covers it on its own terms.

---

## Takeaway

At the `CoreModel` / bank-profile level, a deployment's goal stance is a published object, not a slogan. The goals it lists are backed by witnesses the kernel will read; the goals it does not list are honestly disclaimed; the publishing is faithful to the deployment's actual machinery because the architecture demands a projection-and-commuting relation rather than a verbal correspondence.

Every entry on a published profile is in one of three honest positions: substantive yes (the goal does work), vacuous yes (the premise never fires, and the kernel records why), or explicit no (the goal is absent and the failing case is exhibitable). The architecture keeps the three apart because flattening them is exactly the slogan-restaurant move it exists to refuse.

The `OdometerModel`'s profile — one substantive yes, one vacuous yes, three explicit nos — is the worked example. The lab is the same machinery at the other end. Same architecture, different rows filled, both legible as profiles rather than as descriptions.

---

← [What a Working System Buys You](goals.md) · ↑ [Forcing](../forcing/forcing.md) · Next: [Convergence](convergence.md) →

# Realizers — A Recipe, Not a Blueprint

## Cluster

- [Concrete — show me one](concrete.md)
- **Realizers — a recipe, not a blueprint** *(you are here)*
- *[Deficient Systems](deficient.md) — what failure looks like when a structural piece is missing*

---

## "Wait — is *that* what EpArch says a system should look like?"

A reader closes the previous file with the existence question answered: the architecture has inhabitants and the kernel exhibits two of them. The next move that almost everyone makes — and that every reader who is going to actually use the architecture *will* make — is to read the canonical witness as if it were the canonical *answer*. The thin profile becomes "what a thin EpArch deployment looks like." The full forcing-side wiring becomes "what a full EpArch deployment looks like." And from there the architecture starts to look, fairly quickly, like a single fixed design dressed up in proof. That misreading is the one thing this file exists to head off.

The recurring confusion the file disarms is the slip from *the architecture has an inhabitant* to *the architecture has a preferred inhabitant*. The inhabitants in the previous file are existence proofs; they show the structure can be filled. They are not designs anyone is recommended to copy. What the architecture actually offers a deployment is a *recipe* — a set of typed slots that anything claiming to be an EpArch instance has to fill, with constraints that the fillings have to jointly satisfy. The canonical witnesses are one way to fill the recipe. They are not the way.

This file is about the recipe. What the slots are, in broad terms; what the constraints between them look like; why the architecture's `Realizer` and `SuccessfulSystem` types are useful even when no one wants to deploy the canonical fillings; and what the recipe does and does not commit a deployment to.

---

## What the recipe actually is

The architecture's `Realizer` type packages a small number of commitments the deployment has to make good on for the rest of the structure to be inhabited. Each commitment is a typed existence statement — *something exists that satisfies this constraint inside the deployment* — and the realizer is the bundle of all of them at once. Some are negative (a deployment must exhibit a place where authorization is held without certainty, and another where certainty is held without authorization, so that the architecture's separation of those two notions is real on this deployment and not collapsed); some are structural (the deployment's deposits must factor into the named structural components, the deployment's challenges must localize to a recognized field, the deployment's exports must be gated). What every commitment shares is that it is a *constraint on how the slots are filled together*, not a prescription for what fills them.

A reader who takes the recipe seriously sees what the architecture is asking of a deployment as architecturally light. The constraints are about *separations the deployment must exhibit*, *factorings the deployment must be able to perform*, and *gates the deployment must enforce*. They do not say what the deposits are made of, what the agents look like, what the bubbles enclose, what the bank's storage layer is, or what an export means in any particular domain. The architecture is, in this sense, a *thin* requirements layer over a deployment, not a thick model of one. The `Realizer` type is the formal expression of how thin: a deployment that can produce these typed witnesses for these typed slots is an EpArch realizer, no matter what is in the slots.

A second packaging — `SuccessfulSystem` — bundles a deployment with the proof that it discharges the architecture's eight forced pieces simultaneously and converges structurally. This is the heavier recipe. A `Realizer` says *the commitment slots can be filled coherently in this deployment*; a `SuccessfulSystem` says *the deployment also exercises the architecture's full forcing apparatus and the convergence chain goes through on it*. Both are recipes. Both have canonical witnesses in the kernel. Neither is a recommended deployment.

---

## Why this matters when no one wants to deploy the canonical fillings

The canonical witnesses (`ConcreteRealizer`, `ConcreteSuccessfulSystem`) are toys. They are deliberately small, deliberately abstract, and deliberately unmotivated by any particular real-world domain. Their job is to exist, not to be useful. A reader who asks *should we deploy the concrete realizer in our system?* has misread what the witness is for — the witness was built so the architecture's existence claims have referents, and that is the entire job it does.

What a real deployment uses the recipe for is the opposite move. The deployment has its own filling — its own kind of deposit, its own agents, its own bubbles, its own bank — and the question is whether that filling discharges the typed slots the recipe names. The architecture's value to such a deployment is not that the deployment will look like the canonical witness; it is that the deployment can be *checked against the same typed slots* the canonical witness fills, and the architecture's theorems will hold on the deployment exactly when the slots are filled coherently. The recipe is the bridge between *the architecture proves things in general* and *the architecture proves things about this deployment in particular*.

Strictly speaking, the current Lean `Realizer` is not yet a fully generic adapter interface for arbitrary deployment types. It is a thin satisfiability package over the concrete commitment bundle already present in the repo. The architectural reading is broader: a real deployment uses the same recipe shape by exhibiting analogous witnesses in its own data. The current kernel proves the recipe is inhabited; a domain-specific adapter would be the next layer that maps a real deployment into those slots.

This is also why the recipe is more useful than a recommended design would be. A recommended design is a single point in the space of EpArch deployments; it works for the systems that look like it and is a poor fit for everything else. A typed recipe is a *family* of deployments — every deployment that fills the slots is in the family — and the architecture's theorems land on every member. The architecture is precise about what the family is (the typed slots, the joint constraints) and silent on what its members look like (anything compatible with the slots). A deployment that wants to know whether it is a member discharges the slots; a deployment that wants to know what kind of member it is reads the goal-stance profile it publishes; a deployment that wants to be talked out of being a member is in the wrong document.

---

## What the recipe does and does not commit a deployment to

What it commits to is exhibiting the typed slots, jointly, in a way the architecture's predicates can recognize. A deployment that wants to claim it is an EpArch realizer cannot skip a slot because the slot looks awkward in its domain; it cannot supply a witness that fails one of the cross-slot constraints the bundle requires; it cannot claim a goal whose underlying slot is left unfilled. The recipe is typed precisely so these failure modes are *visible at the type level*, not buried as informal qualifications. When the deployment's `Realizer` value type-checks, the slots are filled and the joint constraints are discharged, and that is what it means to be an EpArch realizer.

What it does not commit to is any particular shape for the slot fillings. The architecture does not prescribe what a deposit looks like; the deployment's deposits can be any data structure carrying the structural fields the architecture names. The architecture does not prescribe what an agent looks like; the deployment's agents can be users, services, learned models, or anything else that can hold an ACL position and act through it. The architecture does not prescribe what a bubble encloses; the deployment's bubbles can correspond to scopes in any domain that has a coherent notion of scope. The recipe is a constraint on *how the pieces relate*, not a constraint on *what the pieces are*.

What it also does not commit to is success at any particular goal. A `Realizer` bundles the commitments that make the architecture's structure inhabited on a deployment; it does not bundle the choice of which goals the deployment is buying. That choice is downstream and lives in the goals cluster's profile story. A deployment can be a realizer and publish the narrowest possible profile (one substantive goal, the rest vacuous or out-of-scope); a deployment can be a realizer and publish the fullest possible profile (every goal substantively held). The recipe is about the slots; the profile is about the goals. The two are independent and the cluster keeps them so deliberately.

---

## What this file is not

This file is not the place where the recipe is itemized. The slots have names in the kernel and the cross-slot constraints are written down there; a reader who needs the inventory is reading the wrong document and should be reading the kernel. This file reads what the recipe is *for* and what reading the canonical witnesses as the canonical answer would cost.

This file is not the place where a deployment is walked through filling the recipe. There is no template here, no worked-through example for some named domain, no "filling out the slots for a self-driving system." Every deployment fills the slots in its own way, by exhibiting witnesses inside its own data, and the architecture is silent about what those witnesses look like. The architecture's value is precisely that it does not need to know.

This file is not the place where the goal-stance choice on a realizer is defended. A realizer can pair with any goal-stance profile its commitment-bundle filling supports; *which* profile a deployment publishes is downstream of the deployment's domain, costs, and use, and the goals cluster owns that question. The recipe-and-profile distinction is the cluster's load-bearing one; this file makes it and hands the second half off.

---

## Takeaway

The architecture's `Realizer` and `SuccessfulSystem` types are typed witness packages, not recommended deployments. `Realizer` packages satisfiability of the concrete commitment bundle; `SuccessfulSystem` packages a working system together with structural forcing and satisfaction of all eight operational properties. The canonical witnesses exist so the recipes have inhabitants. They are not designs anyone is recommended to copy, and reading them as designs is the one misreading this file is built to head off.

The next file in the cluster turns the question around. The recipe is what an EpArch realizer fills; what does the architecture say about deployments that satisfy *most* of the recipe but miss one of the forced pieces? That is the deficient-systems story, and it is the dual of this one — non-vacuity exhibited the inhabitants the architecture has; deficient systems exhibit, with the same precision, the systems the architecture's forcing theorems say it does not.

---

← [Concrete — show me one](concrete.md) · ↑ [Goals](../goals/goals.md) · Next: [Deficient Systems](deficient.md) →

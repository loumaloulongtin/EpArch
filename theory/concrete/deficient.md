# Deficient Systems — The Architecture's Negative Existence Claims

## Cluster

- [Concrete — show me one](concrete.md)
- [Realizers — a recipe, not a blueprint](realizers.md)
- **Deficient Systems — the architecture's negative existence claims** *(you are here)*

---

## "What does failure actually look like in here?"

A reader who has worked through the previous two files knows that the architecture has inhabitants and that the architecture's typed witness packages are recipes rather than blueprints. The next question — and it is the question every reader who is going to make decisions on the architecture's strength eventually asks — is what the architecture says happens when a deployment is *not* an inhabitant. Not the abstract version of that question; the concrete version. Show me a system that is missing one of the forced pieces; show me what the architecture proves about it; show me that the failure is the failure the forcing theorems said it would be, and not some other failure or no failure at all.

The recurring confusion this file disarms is the slip from *the architecture proves these pieces are forced* to *the architecture proves nothing about systems that lack them*. That slip is tempting because the forcing theorems are stated as positive facts about what working systems must contain, and a reader who reads only the positive side comes away thinking the negative side is silence. It is not silence. The architecture has its own negative existence claims — explicit deployments, written down, that satisfy most of the structure but are missing one specific forced piece, paired with theorems that say *exactly* what the missing piece costs. The deficient systems are the architecture's way of demonstrating, on real data the kernel exhibits, that the corner theorems are not vacuous on the side where they bite.

This file is about what those negative existence claims look like, what they let the architecture say that the positive side alone does not, and what they do *not* let the architecture say. The cluster's third move — non-vacuity exhibited the inhabitants the architecture has; the recipe story made clear those inhabitants are not designs anyone is recommended to copy; the deficient story closes the cluster by showing the architecture is equally precise about the systems it does *not* have.

---

## What a deficient system actually is

A deficient system in the kernel is a spec-level working-system witness whose feature flags are all present except one. The missing feature is explicitly set to `false`; the other feature flags are set to `true`. The evidence fields on the witness are not populated, so no `handles_*` predicate holds on the witness itself — it is used as the *no-X-spec* witness for the architecture's reasoning, not as a fully-instantiated working deployment.

The pressure that makes the missing feature bite is supplied by separate scenario data: a disagreement scenario for no-bubbles, a bounded-verification scenario for no-trust, a discriminating-import scenario for no-headers, and so on. The deficient system plus that scenario data lets the corresponding structural model fire. The no-bubbles witness paired with the disagreement scenario lets the architecture prove that no flat acceptance function can faithfully represent both agents — the bubble-separation pressure bites, on this scenario, on this witness, with the structural model the kernel uses to define the pressure. The bridge-impossibility theorems then close: a system that handles this scenario data and lacks bubble separation cannot exist as an EpArch instance, because the structural model derives a contradiction.

The same shape repeats for the other seven. Each deficient witness has every other feature flag present, lacks exactly one feature flag, and is paired with constructible scenario data that exercises the missing feature. The scenario data is what makes the corresponding structural model fire. The eight deficient witnesses together exhibit, on real typed data, what each of the eight forcing claims actually says when read on the side where the structural piece is absent.

---

## What the deficient systems let the architecture say

Two things, both load-bearing for how the architecture is read overall.

The first is that the bridge-impossibility and structural forcing arguments are not empty: for each missing feature, there is concrete scenario data on which the corresponding impossibility theorem fires. A reader who looks at the positive side — *every working system that is structurally forced contains all eight pieces* — and worries that the eight-piece requirement might be an empty constraint (perhaps no spec-level witness could lack a piece *and* still carry scenario data the structural model would recognize, in which case the impossibility theorems would be true but say nothing) is closed off by the deficient witnesses. Each deficient witness has every other feature flag in place; each is paired with constructible scenario data the structural model recognizes; and on that combination the architecture proves the structural model fires and the bridge-impossibility theorem closes. The forcing claim has bite because the failure case it rules out is exhibited and proven to fail.

The second is that the failure is *the* failure, not *a* failure. A reader who accepts that something goes wrong when a forced piece is missing might still wonder what it is that goes wrong — whether the architecture knows, whether the failure is the kind of failure the forcing story predicted or some other failure or a failure at a different level of the architecture entirely. The deficient systems pin this down. The structural model that defines the pressure (the disagreement structure for bubble separation, the storage model for storage management, and so on) is *the same* structural model that fires on the deficient system's scenario data. The negation the architecture derives on the deficient system is not a generic incoherence; it is the particular incoherence the forcing theorem said the missing piece produces. The architecture is precise about what the missing piece costs because the missing-piece-cost is the same structural object on both sides of the corner theorem.

Together these two things make the corner theorems readable as architectural claims about real deployments rather than as bookkeeping inside the kernel. *Bubble separation is forced* means *deployments without bubble separation cannot handle the disagreement scenario this deficient system exhibits*. *Revocation is forced* means *deployments without revocation cannot handle the adversarial scenario the no-revocation deficient system exhibits*. The forcing story is grounded in negative existence the same way the realizer story is grounded in positive existence; the architecture's strength on each pressure is exactly the strength of the deficient system that exhibits the pressure's bite.

---

## What the deficient systems do not let the architecture say

What they do not buy is a recommendation against any deployment that happens to lack one of the named features. A deployment that lacks bubble separation but does *not* face the disagreement scenario — perhaps because the deployment's domain has only one agent, or because the agents in the domain are coordinated by some out-of-band channel the deployment does not need to model — is not caught by the no-bubbles deficient system's failure. The corner theorem fires when the pressure is present; the deficient system shows the pressure firing on a deployment that lacks the structural answer to it. A deployment that does not face the pressure does not need the answer, and the architecture is silent about it. The deficient systems do not say *do not deploy without these eight pieces*; they say *if you face the pressure these eight pieces answer, the pieces are not optional*.

What they also do not buy is a claim about the *severity* of the failure in any deployment-meaningful sense. The architecture proves the structural model fires; it does not measure the cost in any operational, financial, or safety unit. Whether the failure the no-bubbles system exhibits is a small failure or a catastrophic one in any particular real-world domain depends on the domain and is not something the architecture is positioned to say. The deficient systems exhibit *that* the failure occurs and *what kind* of failure it is in structural terms; *how much* the failure costs in deployment terms is downstream of facts the kernel does not see.

What they also do not buy is the converse claim — that a deployment with all eight pieces is therefore safe. The deficient systems are negative existence on the missing-piece side; positive existence with all pieces is what the working-system witnesses do. Neither set of witnesses lets the architecture conclude that *any* deployment with the structure is *therefore* a good deployment. Goal-stance, profile choice, configuration, the question of which goals a deployment is buying and at what cost — all of that lives downstream of both witnesses, in the goals and meta clusters, and is not a claim the deficient systems by themselves support.

---

## What this file is not

This file is not the per-pressure walkthrough. The architecture exhibits eight deficient systems, one per forced piece, and the kernel is the place where each one is constructed and its corresponding corner theorem fired. A reader who needs to know *which* failure each deficient system exhibits and *which* structural model fires on it is reading the wrong document and should read the kernel. This file reads what the eight deficient systems are *for* and what their existence buys the architecture's overall claims.

This file is not the place where the corner theorems themselves are walked through. The corner theorems live in the forcing cluster — the positive side of the same coin — and the deficient systems are the negative-existence demonstrations that the corner theorems have bite. The forcing cluster makes the positive case for each pressure; this file shows that the negative case is exhibited rather than asserted. Reading this file as a tour of the corner theorems would put on it weight that belongs in forcing/.

This file is not the place where the architecture's recommendations to deployments are made. There are none. The deficient systems are negative existence claims about *systems missing pieces under pressure*, not normative claims about *what deployments should do*. A deployment that wants to know whether it should adopt EpArch, or which goals it should buy, or how to fill out the recipe in its domain, is asking questions this cluster does not answer and the architecture does not try to.

---

## Takeaway

The architecture exhibits eight deficient systems — one per forced architectural piece — each constructed in the kernel, each paired with scenario data exercising the pressure the missing piece was forced to handle, and each shown to fail on that scenario by the same structural model the corresponding corner theorem uses on the positive side. The deficient systems are the architecture's negative existence claims: a demonstration that the forcing theorems are not vacuous, that the failure they predict is the failure that occurs, and that the architecture is precise about what each missing piece actually costs in structural terms. They do not buy a recommendation against any deployment missing a piece; they do not measure the cost of failure in deployment-meaningful units; and they do not, with the realizers and the working-system witnesses, license the converse claim that a deployment with all eight pieces is therefore safe. What they buy is the demonstration that the architecture's positive forcing claims have bite on the side where they bite — and the cluster's job, with the previous two files, is now closed.

The next cluster turns from *the architecture has inhabitants and the architecture is precise about its non-inhabitants* to *the architecture is configurable* — which inhabitants are required of a deployment, which can be turned off, which goals the deployment is buying with which evidence. That story lives in the meta cluster and is the one this cluster's three files have been making room for.

---

← [Realizers](realizers.md) · ↑ [Goals](../goals/goals.md) · Next: [Meta](../meta/meta.md) →

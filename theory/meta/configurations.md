# Configurations — Typed Deployment Surfaces

## Cluster

- [Meta — the architecture as a configurable kernel](meta.md)
- **Configurations — typed deployment surfaces** *(you are here)*
- *[Transport](transport.md) — what survives a configuration change*
- *[Grounded Evidence](grounded-evidence.md) — the user-facing compliance API and residual risk*
- *[Falsifiability](falsifiability.md) — claims you cannot make true by saying so*

---

## "What does a deployment actually fill out?"

meta.md said the modularity meta-theorem licenses smaller declared surfaces, and that a deployment's compliance posture is exactly the projection of the architecture's universal claims onto its declaration. It did not say what the declaration is, what filling one out looks like, or how the architecture enforces that the declaration the deployment makes is the declaration the architecture's certification is keyed to. That is this file's question. The OdometerModel and the working-system witness from concrete/ have both already been sitting somewhere on the configuration surface; this file walks the surface itself.

The recurring confusion this file disarms is the slip from *the deployment declares which constraints are operative* to *the deployment thereby certifies that it satisfies them*. The two are different things and the architecture treats them as different things. Saying "this constraint is in scope for me" is one act; supplying the proof obligation that ties handling the constraint to the matching architectural feature is another. The configuration surface is layered exactly along that split, and the layering is what makes opting in honest and opting out coherent.

---

## What there is to fill out

The architecture exposes two configuration surfaces, at two different layers, doing two different jobs.

The deployment-facing surface is a flat declaration of which architectural concerns the deployment is asking the architecture to engage with: a list of operative constraints, a list of goals it intends to claim, and a list of named world bundles whose obligations it is acknowledging. The lists are typed — each entry is a tag from a finite menu, not free text — and the architecture's certification machinery routes off them to decide which clusters of theorems are enabled for the deployment. This is the surface a deployment actually writes; it is the architecture's listening posture for the deployment's intent.

The proof-side surface is related to the deployment declaration, but it is not the same object. `EpArchConfig` records the deployment-facing list of constraints, goals, and world bundles and routes theorem clusters from that declaration. `ConstraintSubset` and `PartialGroundedSpec` are the proof-side constraint surface: they say which of the eight Minimality constraints are active and require evidence for the active ones. Conceptually these are two views of the same configuration posture; in the kernel they are separate surfaces.

The two surfaces are deliberately separated, and it is the separation that does the work. The declaration is what the deployment is asking for; the proof-side subset is what the architecture's certification will need from the witness in order to grant it. A deployment that asks for more without supplying more does not get more; a deployment that supplies more than it asks for does not get more either, because the architecture's certification is keyed to the declaration, not to the witness in isolation.

---

## What the worked examples already configured for

The OdometerModel and the working-system witness from concrete/ have been sitting on this surface from the moment they were introduced; what changes here is that the surface has names. The OdometerModel sits on the goal-profile side of the configuration story, not on the `ConstraintSubset` side. It is a `CoreModel` witness with a narrow goal stance: `SoundDepositsGoal` holds substantively, `SelfCorrectionGoal` holds vacuously, and the other three CoreModel goals are explicitly not held. It shows that EpArch can recognise a small honest profile without treating it as a failed full deployment. The concrete working-system witness sits at the full constraint-forcing position: all eight feature flags are present, all eight grounded witnesses are supplied, and the structural convergence chain goes through. That is the full `WorkingSystem` / forcing-side surface, not automatically every goal and world bundle in the broader `EpArchConfig` registry. Neither is a more or less canonical configuration; both are points the surface admits, and the architecture's certificates over each are exactly the projection licensed by their respective declarations.

The empty point is on the surface too. `noConstraints` — the subset that selects nothing — is a real configuration; the architecture recognises it; the modularity meta-theorem applies to it (vacuously, but applies). What it certifies under that declaration is correspondingly empty: no forcing implications, no goal claims, no world-bundle obligations. The architecture does not refuse to engage with a deployment that asks for nothing; it engages by certifying nothing, which is the precisely correct response. The point of naming this is that smallness is not a degenerate edge of the surface — it is the surface's lower endpoint, and the meta-theorem covers it on the same footing as the upper endpoint.

---

## What the configuration surface does and does not commit a deployment to

What it commits a deployment to is the discipline that opting in is paid for. Putting a constraint in the declaration tells the architecture to expect evidence from the deployment for that constraint; without it, the certification does not produce a proof for that constraint's cluster. The deployment cannot collect a forcing certificate by wishful declaration. For an active constraint, `PartialWellFormed` supplies the biconditional between the relevant `handles_*` predicate and the matching `Has*` feature, and the modularity theorem then extracts the forcing direction: if the deployment handles that pressure, the corresponding feature follows. In the `PartialGroundedSpec` path, active constraints are filled with concrete `GroundedX` evidence, which builds a `WorkingSystem` where the corresponding spec flag and evidence field are present. Either way, the deployment must actually show up; declaration alone configures nothing.

What it does not commit a deployment to is matching its declaration to the world. The configuration surface is normative on the deployment's side — the deployment is bound by what it asks for — and silent on the world's side. A deployment that declares the bubble-separation constraint as out of scope while operating across multiple agents is not contradicted by the architecture; the architecture stops claiming anything about how it handles that pressure, and what happens next is the deployment's question, not the configuration surface's. This is the "silence about claims, not silence about the world" point from meta.md, made operational: the configuration is exactly the place where that silence is parameterised.

What the configuration surface also does not commit a deployment to is monotonicity over time. A deployment may move to a different point on the surface — add a constraint, remove a goal, change a world bundle — and the question of what that movement does to its outstanding certificates is the transport file's subject (`transport.md`), not this one. The configuration surface itself is just the space; movements through it are what transport reads.

---

## What this file is not

This file is not the meta-theorem. The modularity meta-theorem is in meta.md; what this file owns is the surface the meta-theorem is parameterised over.

This file is not the transport story. Transport reads the consequences of moving between configurations; this file walks the surface as it stands at a single point. The transport file picks up where this one ends.

This file is not the user-facing certificate. The certified-projection layer that turns a configuration into a typed cluster-by-cluster certificate is described conceptually in meta.md and exposed for deployment use in `grounded-evidence.md`. The configuration is the input to that certification; what the deployment shows downstream consumers is the output, and they live in different files because they are different objects.

---

## Takeaway

The configuration surface has two layers — a deployment-facing declaration of operative constraints, intended goals, and acknowledged world bundles, and a proof-side subset that supplies biconditional witnesses for the constraints in scope — and the separation between them is what makes opting in honest and opting out coherent. Every point on the surface is a recognised EpArch posture: the empty subset, the OdometerModel's narrow position, the working-system witness's full position, and everything between. The architecture's certification is keyed to the declaration and produces exactly the projection meta.md described. The next file walks what happens when a deployment moves between points on this surface.

---

↑ [Theory](../) · ← [Meta](meta.md) · Next: [Transport](transport.md) →

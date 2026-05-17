# Grounded Evidence — The User-Facing Compliance API and Residual Risk

## Cluster

- [Meta — the architecture as a configurable kernel](meta.md)
- [Configurations](configurations.md) — typed deployment surfaces
- [Transport](transport.md) — what survives a configuration change
- **Grounded Evidence — the user-facing compliance API and residual risk** *(you are here)*
- *[Falsifiability](falsifiability.md) — claims you cannot make true by saying so*

---

## "What does the deployment hand a downstream consumer?"

configurations.md walked the surface a deployment fills out and transport.md walked the discipline that movement on the surface must respect. Both files were written from the architecture's vantage — what the kernel sees, what the certification routes, what the transport theorems lift. Neither addressed the other vantage: what the deployment *exports*. A deployment that has filled out its declaration, supplied evidence on the proof-side surface, and obtained the certified projection has one further question to answer — what does it hand a regulator, an auditor, an integrator, or a downstream system that needs to make sense of the deployment's posture without re-running the architecture's certification machinery against it. autonomy/risk.md flagged this file forward as the place where the *compliance-API face* of residual risk lives, separate from its own operational classification of bridge use; this is that file.

The recurring confusion this file disarms is the slip from *the compliance certificate covers what the architecture covers* to *the compliance certificate covers what a deployment's regulator or downstream consumer needed it to cover*. The two are different things and their gap is the thing the residual-risk material in this file is built around. The architecture's certification is precise about what it certifies; what it does not certify is not silently absent from the certificate but is the certificate's other face — the named limits the architecture insists on surfacing alongside what it does promise.

---

## What the API is, and what makes it user-facing

The compliance API, in the current kernel, is best read as the deployment-facing certificate surface around the configuration object, the cluster-routing function, the certification function, and the proof-carrying witness families those functions return. It is not a separate domain-specific report format. The configuration declaration is what the deployment signs; the cluster-routing function turns that declaration into the list of enabled theorem clusters; the certification function supplies the machine-checked projection for those clusters; the proof-side evidence form is what active constraint subsets are filled out against. A downstream export can be built from these objects, but the kernel surface itself is the typed certification layer, not a finished regulator-facing document.

The two sides of that surface are related but kept distinct. The proof-side evidence form carries the witnesses for the active constraint subset — concrete fields the deployment fills in for each pressure it has taken into scope. The cluster-routing certificate is keyed to the declaration as a whole, including the goal and world-bundle lists, and supplies proof witnesses for the theorem clusters that declaration enables. A user-facing export may package the two together, but the kernel separates the evidence form from the cluster-routing certificate; the discipline of the surface is that what the export presents matches what the kernel objects respectively guarantee, on each side, without merging the two into a unified object the kernel does not provide.

The "user-facing" part is load-bearing. The kernel's own certification proceeds in proof witnesses keyed to architectural pressure tags, biconditionals between handle-predicates and feature-predicates, transported goal schemas, and so on — the language of the modularity meta-theorem and the certified projection. None of that is the language a downstream consumer will be in a position to read or check; the surface is shaped so a translation into a vocabulary that names *what evidence was supplied for which constraint* is constructible from the kernel objects, without requiring the consumer to re-derive the mapping between evidence and certificate. The translation is type-safe in both directions: an evidence field cannot be supplied for a constraint outside the declaration, and a constraint inside the declaration cannot be exported as certified without its evidence field having been supplied. The deployment cannot construct a valid export that misrepresents either its declaration or what it has shown.

The enabled-cluster report makes the positive surface explicit. Absences are recoverable by comparison against the finite cluster registry: what is not enabled is not being certified. A downstream export can choose to display those absences explicitly, and should, but the core routing machinery primarily computes the enabled side; the discipline of treating absences as part of what the consumer reads is a property of the export the deployment builds, not something the kernel routing returns on its own.

---

## What the API does and does not promise

What it commits the deployment to is the discipline that the export matches the certification exactly. A deployment that has filled out the surface for a declaration has thereby committed to a precise statement of which clusters are certified on its behalf and which are not, and the kernel objects are typed witnesses to that statement. The deployment cannot widen the export beyond the certification by attaching prose claims; the architecture's discipline is that the export's content is exactly what the kernel objects admit, and what the kernel admits is exactly what the certification has produced. Honesty between the deployment's outward claim and the architecture's inward proof is not a matter of careful wording; it is a typed property of the surface.

What it does not promise is that full architectural compliance, on a maximal declaration with all evidence supplied, exhausts the questions a downstream consumer might reasonably bring to the deployment. The compliance face should also expose the architecture's limits: what the enabled clusters do not certify, what is outside the declaration, and what residual-risk results elsewhere in the architecture say cannot be read as a zero-risk guarantee. In the current kernel, those limits are distributed across the residual-risk, autonomy, world, and certification surfaces rather than packaged as one separate compliance-API object — and the discipline this file installs is that a deployment's export should surface them rather than leave them implicit. A downstream consumer who reads a maximal compliance bundle should read, alongside it, the architecture's named limits in the same vocabulary; treating those as appendix, footnote, or omission would be a misuse of the certificate.

What it also does not promise is the operational classification of any particular use the deployment has made of any particular mechanism. The compliance surface is structural: it certifies that the deployment has supplied the evidence the constraint requires, not that any individual run of the system will land on the safe side of a residual-risk classification when it actually executes. The operational classification of bridge use lives in autonomy/risk.md and is the system's own per-use predicate; the certification function does not absorb it and does not stand in for it. A consumer who wants to know whether a given action the system took was classified risky is asking the operational layer, not the compliance layer.

---

## Residual risk on the compliance face

This is where the cluster's third residual-risk layer lives, the one autonomy/risk.md flagged forward without entering. The compliance API does not promise the absence of residual risk on the deployment's actions; it surfaces, as part of the certificate, the architecture's own list of named structural limits that hold even when every piece of architectural compliance is in place. A reader who treats a maximal compliance certificate as a guarantee that the deployment will not encounter a situation calling for a risky-bridge response, an in-corner decision, an obligation that scratch verification cannot cover, or a pressure the deployment has not declared and so has not certified for, is reading the wrong layer. The architecture's response is not to weaken the certificate — the certificate is precise and the precision matters — but to require that the certificate itself surface the residual-risk material as part of what it exports, in the same typed form as the positive content.

The three layers the autonomy cluster named keep their distinct jobs at the compliance face. The operational classification in autonomy/risk.md is a fact *about the system at runtime*, supplied by the system, propagated by the system; it does not appear on the compliance API because it is not the architecture's to certify. The minimality-layer reason for why budget pressure produces residual risk in the first place is *about the architecture*; it appears in the kernel and in the architecture's bookkeeping but is not the deployment's to export, because the architecture's reason for the existence of residual risk is not parameterised over the deployment. The compliance face is *about what the certificate does and does not promise*; it is the deployment's to export because it bounds, on the deployment's outward side, what consumers may correctly infer from the certificate. Keeping the three apart is most of what makes residual-risk material readable across the architecture.

---

## What this file is not

This file is not the meta-theorem, the configuration syntax, or the transport story; those are the cluster's earlier files and are presupposed here.

This file is not the operational risk-classification layer. autonomy/risk.md owns the system-side per-bridge-use classification; this file owns the compliance-side statement of named limits even under full architectural compliance. The two are distinct objects at distinct layers and the cluster does not collapse them.

This file is not the falsifiability guard. The next file (`falsifiability.md`) covers the standalone result that some claims are not the kind of thing a deployment can authorize into truth by declaring them — a different guard from the one this file installs. The compliance-API face of residual risk is about the architecture's bookkeeping of what compliance does and does not promise; the falsifiability guard is about what *no* declaration could promise, regardless of evidence. Both are guards; they guard against different misreadings.

---

## Takeaway

The compliance API is the deployment's typed export object — the artefact a downstream consumer reads to learn the deployment's certified posture without engaging the kernel directly. It carries exactly what the architecture's certification produced for the deployment's declaration: which constraints are in scope, what evidence was supplied for each, what cluster-by-cluster projection of the architecture's universal claims follows. It commits the deployment to honest correspondence between its outward claim and the architecture's inward proof, by typed construction rather than careful wording. It does not promise that full compliance answers every question a consumer might bring; the architecture's named structural limits ride on the same export as part of the certificate, surfacing what compliance does and does not buy in the same vocabulary as the positive content. The three residual-risk layers the cluster has been keeping apart — operational classification of actual bridge use, minimality-layer reason for residual risk's existence, compliance-API statement of what the certificate does not promise — meet at this file at exactly the third layer; the first two stay where they were named. The next file picks up the standalone guard that some claims sit outside what *any* declaration could authorize, regardless of evidence.

---

↑ [Theory](../) · ← [Transport](transport.md) · Next: [Falsifiability](falsifiability.md) →

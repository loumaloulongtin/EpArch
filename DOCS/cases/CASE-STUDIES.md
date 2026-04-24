# EpArch Case Studies

This file is a corroboration / stress-test doc, not a proof appendix.
Its job is to ask whether real-world systems under adversarial or
distributed-testimony pressure independently converge on the primitives
EpArch forces, and whether removing those primitives recreates the
pathologies EpArch predicts. Classical puzzle bindings (Gettier, Fake
Barn, Lottery, Moorean, …) live in [../reference/THEOREMS.md](../reference/THEOREMS.md) family F5,
not here.

The primitives at stake:

- separation of **S / E / V** rather than one undifferentiated validity mark;
- explicit or functionally implemented **provenance tracking**;
- explicit or functionally implemented **scope boundaries**;
- explicit **standards / thresholds** for acceptance;
- a **bank / ledger substrate with explicit lifecycle status**, rather than free-floating memory or assertion.

S, E, V, and other EpArch-specific terms are defined in the
[START-HERE.md glossary](../START-HERE.md).

The empirical wager: if EpArch is tracking something real, systems that
preserve these primitives should be more robust against the failure
families the theory identifies, and removing the primitives should
predictably recreate those failures.

This is not proof by anecdote. It is a cross-domain convergence test.

---

## Reading rule

Each case study should be read in the same format:

1. What is the relevant epistemic pressure?
2. Where are the EpArch primitives in the system?
3. What goes wrong when those primitives are absent, bypassed, or thinned?
4. Does the observed failure look like the pathology EpArch predicts?

The claim is not that any institution consciously implements EpArch. The
claim is that mature systems facing the same structural pressures keep
reinventing the same control surfaces.

---

## Why one delta case matters

A static case study shows convergence: a mature system under pressure
happens to have EpArch-like primitives. That is good corroboration, but
it leaves a rhetorical opening: "Maybe you just picked systems that
already look like your framework." A before/after intervention case
changes the shape of the claim from static resemblance to observed
improvement after adding the primitive. That is much harder to dismiss
as selection bias.

### Barcode Medication Administration (BCMA) as intervention

**Before**: medication administration relying on nurse memory, manual
label reading, and informal verification.

**Primitive added**: barcode-linked patient–medication verification tied
to an explicit administration record. The nurse scans the patient
wristband, scans the medication, and the system matches both against the
active order before completing the administration event. Each
administration is logged in a durable eMAR (electronic Medication
Administration Record) trace rather than recalled from memory.

**Observed change**: AHRQ (Agency for Healthcare Research and Quality)
data shows a 41% reduction in non-timing medication errors and a 51%
reduction in potential adverse drug events under BCMA. Workaround
studies show a threefold higher medication error risk when the barcode
path is circumvented.

**EpArch reading**: this is not just a system that resembles the
architecture. It is a system that improved when an EpArch-like primitive
was deliberately added, and degraded predictably when that primitive was
deliberately removed by the agent. The pathology is not random. It
tracks the presence or absence of provenance and scope discipline with
enough regularity to be measured.

---

## Case studies

### 1. Hospital medication administration

**Pressure.** Medication administration is adversarial in the weak but
important sense: the system must remain safe under distraction, workflow
friction, label ambiguity, handoff error, and local misperception. It is
also a distributed-testimony environment: physician order, pharmacy
verification, nurse administration, barcode system, and patient identity
all have to line up.

**EpArch primitives.**
- **S**: the rights of administration — right patient, medication, time,
  dose, route.
- **V**: barcode scan of the patient wristband, barcode scan of the
  medication, and linkage to the eMAR.
- **E**: wrong-patient, wrong-dose, wrong-medication, wrong-rate,
  unreadable barcode, missing label, broken workflow, pump
  misconfiguration.
- **Scope**: this patient, this medication order, this administration event.
- **Lifecycle**: electronic MAR and audit trail, not nurse memory alone.

**Predicted pathology if primitives weaken.** Regression toward classic
wrong-patient, wrong-dose, and wrong-medication failure modes.

**Observed.** BCMA systems reduce medication errors when the
scan-and-ledger path is actually used. When nurses work around barcode
checks, the risk of medication error rises sharply. The safer regime is
the one with explicit provenance, scoped matching, and ledger-linked
administration. The degraded regime is not medicine becoming
metaphysically worse — it is the system dropping the epistemic control
surfaces.

---

### 2. Certificate Transparency / Web PKI

**Pressure.** Public-key infrastructure is a distributed-testimony
system under active adversarial pressure. Certificate authorities issue
attestations that browsers and users rely on, often without direct local
verification of the issuing process.

**EpArch primitives.**
- **S**: explicit issuance standard under CA (Certificate Authority) policy.
- **V**: provenance of which CA issued which certificate, when, and for
  what subject.
- **E**: misissuance and inconsistent log views.
- **Scope**: particular domain names and certificate subjects.
- **Lifecycle**: append-only public certificate transparency logs.

**Predicted pathology if primitives weaken.** If issuance provenance is
not forced into an append-only public lifecycle, silent misissuance
should be easier to hide, detect later, or contest poorly.

**Observed.** That is exactly how Certificate Transparency is framed.
The point of CT is not mystical trust. It is making issuance public,
durable, and auditable so that hidden misissuance becomes harder.
Without provenance forced into a public lifecycle, the relying party has
a weaker epistemic object — the certificate may still exist, but the
system has less ability to diagnose, challenge, or contain misissuance.

---

### 3. Software supply-chain provenance (SLSA, Sigstore, in-toto)

**Pressure.** Software supply chains are distributed-testimony systems
under adversarial pressure. Users routinely rely on artifacts they did
not build, produced by workflows they did not observe, with dependencies
they did not inspect directly.

**EpArch primitives.**
- **S**: explicit build and release standard (SLSA formalizes tiered levels for this).
- **V**: verifiable provenance of where, when, and how an artifact was
  produced.
- **E**: tampering, substitution, compromise of builders, provenance gaps.
- **Scope**: repository, source revision, build workflow, builder
  identity, artifact identity.
- **Lifecycle**: signed attestations and transparency-log publication.

**Predicted pathology if primitives weaken.** If the artifact circulates
without verifiable provenance and a durable audit trail, consumers
should be less able to distinguish authentic from substituted or
tampered artifacts, and later diagnosis should be coarser.

**Observed.** The mature response is not "trust harder." It is: stamp
the artifact with provenance, make the build standard explicit, keep a
durable audit trail, and define the consumer threshold for acceptance.
The control surfaces that high-assurance software ecosystems converge on
are very close to the primitives EpArch forces.

---

### 4. Cockpit voice / flight data recorders

**Pressure.** Aviation accident investigation is a high-stakes
retrospective knowledge problem under sparse, noisy, adversarially
incomplete evidence. Once the event has passed, the system needs durable
provenance and time-bounded trace retention to reconstruct what happened.

**EpArch primitives.**
- **S**: standard for what counts as investigation-grade evidence.
- **V**: provenance of recorded cockpit and flight-state data.
- **E**: overwritten or unavailable data.
- **Scope**: this aircraft, this cockpit, this flight, this time window.
- **Lifecycle**: recorder retention and post-incident retrieval.

**Predicted pathology if primitives weaken.** If the evidentiary
lifecycle is too short or too fragile, later diagnosis becomes strictly
worse — not because reality changed, but because the investigation
ledger lost state.

**Observed.** That is exactly what overwritten CVR (Cockpit Voice Recorder) cases show. The event
is fixed. The degradation is in retained epistemic access to it. The
pathology is not ordinary uncertainty — it is the collapse of the
retained trace needed for later audit and reconstruction.

---

### 5. Tacit knowledge transmission (apprenticeship, craft, oral tradition)

This is the strongest attempted disconfirmation and so gets more space.

A master craftsperson can transmit genuine, reliable know-how across
generations with no written S field, no documented E catalogue, no
formal provenance ledger, and no explicit scope-boundary formalism. A
medieval stonemason learned to build cathedrals. It worked. If this
were a genuine success case with no functional equivalents of EpArch's
primitives, it would be the sharpest pressure point in the file.

**The apparent objection.** Maybe tacit craft knowledge works for
reasons that have nothing to do with S/E/V structure — embodied skill,
motor learning, and direct perceptual calibration routing around
provenance, standards, error models, and ledger-like memory altogether.
If that were right, EpArch would either need to absorb tacit knowledge
on new terms or admit that its scope is narrower than reliable knowledge
transmission as such.

**Where the objection bends.** The system works specifically under high
social bandwidth, repeated direct observation, narrow transmission
channels, low scaling pressure, and relatively low adversarial pressure
inside the master–apprentice relation. When those conditions degrade —
diaspora, discontinuity, commercialization, fake teachers, scale beyond
direct observation, loss of shared context — the architecture predicts:

- **V-gaps**: who actually learned from whom becomes hard to verify;
- **E-gaps**: failure modes are not transmitted because they were never
  retained or externalized;
- **scope collapse**: the implicit local boundary breaks when the
  community context that maintained it disappears;
- **challenge/repair degradation**: correction becomes harder once the
  master–apprentice loop is weakened.

**EpArch response.** One available response, within current scope, is a
functional reading: the mechanisms may be present, implemented neurally
and socially rather than institutionally.

- **V** is the remembered transmission chain: the master taught me
  this, I saw it done this way, I learned this correction from this
  person.
- **E** is updated whenever a failure mode is demonstrated, described,
  or personally encountered.
- **S** is the mastery threshold enforced by the craft relation itself:
  this counts as proper practice, this does not.
- **Lifecycle** is memory plus repetition plus correction history.
- **Scope** is the bounded community and its local transmission norms.

When the apprentice makes a mistake, learns from it, and later recalls
the correction, that is functionally an E-field update stored in a
biological bank.

This reading is offered as a possible response to the objection — not
as a proof that EpArch fully covers tacit knowledge. Whether biological
and social hardware genuinely implements the same functions, or only
approximates them under favorable conditions, is an empirical question
in cognitive science and anthropology that the current architecture does
not settle.

**Why this matters.** The tacit-knowledge case forces a nontrivial
distinction: either the mechanisms are genuinely absent and some other
architecture explains reliable transmission, or the same functions are
implemented on biological and social hardware rather than written
institutional hardware. The functional reading holds the second open as
a possibility.

**Result.** The case splits cleanly into three positions:

1. The relevant functions are already present in the tacit system —
   implemented neurally and socially rather than institutionally. Not a
   counterexample; a non-institutional implementation.
2. The functions are not currently present but can be introduced through
   disciplined practice. EpArch identifies an installable configuration.
3. Neither holds: a well-attested tacit system remains robust under
   scale, discontinuity, and adversarial pressure while genuinely
   lacking functional equivalents. The framework is wrong on that
   domain.

The first two positions defuse the tacit case. The third converts it
into a live empirical test. What the tacit discussion does not permit is
a fourth position — that the case is simply outside EpArch's scope and
therefore irrelevant. Either the architecture covers it (1 or 2) or it
fails there (3). Which is true is an empirical question, not a
philosophical one.

---

### 6. Prestige, credentialing, and social-provenance games

**Pressure.** Distributed testimony under adversarial social conditions,
where the agent making the claim is also the agent with the most to gain
from its acceptance. The system must remain reliable under credential
inflation, provenance fabrication, and selective suppression of
error-model information. Unlike the engineering cases, there is no
central ledger and no institution enforcing the primitives. The
primitives exist as social expectations — which makes them gameable, and
makes the gaming observable.

**EpArch primitives.**
- **S**: the implicit acceptance criterion a claim-consumer applies —
  what counts as sufficient ground for taking a claim on board.
- **V**: who said it, under what banner, trained by whom, affiliated
  with what institution, with what track record.
- **E**: the visible record of past failures, retractions, corrections,
  and disconfirmations associated with the claimant.
- **Scope**: the domain within which the claimant's authority actually
  applies.
- **Lifecycle**: the durable record — citations, corrections,
  institutional affiliation history — that allows later audit and
  challenge.

Most consumers evaluate the social header before evaluating the claim
itself: who said it, under what banner, with what apparent track record.
That is provenance doing epistemic work.

**Predicted pathology if primitives are gamed.** If the primitives are
load-bearing, adversarial agents should concentrate effort on gaming
exactly those fields. The predicted attack surface is not random — it
should cluster around V, E, S, scope, and lifecycle, not around
irrelevant properties of the claim.

**The attack surface in practice.** This is a structural observation
about where adversarial effort concentrates when the primitives are
social expectations rather than enforced institutional controls:

- **V-inflation**: credential laundering, name-dropping, prestige
  borrowing, "worked with X," "published at Y," "trained by Z"
- **E-suppression**: hiding error rates, omitting negative results,
  curating feeds, keeping the visible failure model artificially light
- **S-arbitrage**: getting claims accepted under a lenient standard
  through status, affiliation, audience selection, or rhetorical framing
- **trust-bridge borrowing**: using the right institution, recommender,
  or platform to cross a threshold more cheaply than the raw work would
  justify
- **scope laundering**: passing niche credibility off as field-wide
  authority
- **τ / lifecycle gaming** (τ = EpArch temporal validity, F4): relying on stale prestige, burying
  retractions, outrunning record updates

The attack patterns are not random, and — crucially — they are not just
generic status-seeking. Generic social competition would cluster around
visibility, affect, volume, and dominance cues. What we see instead is
sustained effort targeting provenance fields, error-model fields, and
scope fields *as distinct targets*, in ways that map onto the
architecture's separate primitives rather than onto a single
undifferentiated "credibility" surface. That specificity is what the
structural inference rests on.

**EpArch reading.** This case is different in kind from the engineering
cases. It is not a system that was designed to implement the primitives.
It is a system where the primitives exist only as social expectations —
and where adversarial behavior spontaneously reveals which fields are
load-bearing by showing where structured effort concentrates. The
argument is not "people game credibility, therefore credibility is
load-bearing." The argument is that the gaming decomposes into
recognizably distinct operations — each targeting a separate primitive
— in a way that is predicted by the architecture but not by generic
social-dominance accounts.

---

## Interim conclusion

Across very different domains, mature systems under pressure converge on
the same pattern: explicit or functionally real standard; explicit or
functionally real provenance; explicit or functionally real
failure-modeling; explicit or functionally real scope; explicit or
functionally real lifecycle / audit trail.

When those primitives are weakened, bypassed, overwritten, or socially
degraded, diagnosis gets worse in the exact ways EpArch predicts:

- harder localization
- hidden misissuance
- wrong-agent reliance
- unverifiable transfer
- degraded post hoc reconstruction
- loss of correction memory
- breakdown of trusted transmission chains

That is not a proof that EpArch is the final architecture of knowledge.
It is strong corroborative evidence that EpArch is tracking real
structural pressures that high-stakes systems repeatedly rediscover.

---

## Scope condition for genuine counterexamples

Most weak counterexamples fail because they are not actually cases of
the target phenomenon. A case study is not a real stress test for EpArch
unless the target system has all of the following:

1. **Knowledge management rather than mere expression.**
2. **Distributed testimony, delegation, or transmissible know-how.**
3. **Adversarial pressure, contestability, or meaningful failure-cost.**
4. **A need for later audit, challenge, correction, or recovery.**

If one of those is missing, the counterexample usually collapses into
something trivial: a casual conversation, a personal hunch, a one-user
toy system, a domain where nothing important is exported or relied on by
others, or a low-pressure setting where memory loss or provenance
ambiguity carries little cost. Those do not pressure the EpArch claim.
They show that not every human practice needs the full externalized
bank. That was never the thesis.

---

## What would count as a serious disconfirmation attempt

### Candidate form A — Absence beats presence

Find a real institution or device operating under adversarial pressure
or distributed testimony where provenance tracking is weak or absent,
scope boundaries are loose, standards are implicit rather than explicit,
and lifecycle or audit structure is minimal — and yet the predicted
pathologies do not appear, or the system systematically outperforms
comparable systems that preserve those primitives.

### Candidate form B — Presence does not matter

Find a high-stakes domain where the full EpArch-like stack exists, but
removing one of the forced primitives does not make diagnosis,
contestation, transfer, or recovery worse in any stable way.

### Candidate form C — Wrong diagnosis

Find a domain that clearly instantiates the pressure profile EpArch is
about, but where the architecture's predicted pathology diagnosis is
plainly wrong — not merely disputable in rhetoric, but wrong in
structure.

### Candidate form D — Tacit success with no functional equivalents

Find a genuine tacit-knowledge system that remains robust under scale,
discontinuity, charlatan pressure, and transfer beyond direct
observation, while still lacking functional equivalents of provenance
tracking, correction memory, accepted mastery standards, bounded
transmission scope, and lifecycle update after failure. This is the
strongest live disconfirmation target identified so far.

### Stronger disconfirmation targets

If a genuine disconfirmation section is developed, it should look at:

- tacit craft traditions under diaspora and scaling stress;
- informal but high-performing incident-response cultures;
- safety-critical environments with unusually thin audit trails that
  still outperform thicker ones;
- scientific subdomains where lifecycle traceability is surprisingly
  weak but error containment is still excellent;
- reputation-heavy systems that seem to work with minimal explicit
  provenance.

The burden is to show that the missing EpArch primitive is not merely
absent in appearance, but absent in the function EpArch cares about.
That bar is higher than the informal appearance of these domains
suggests.

---

## Recommended use in the repo

This file should be treated as a cross-domain corroboration document,
not as a proof appendix and not as rhetorical padding. Its job is to
answer a specific challenge: why think the formal architecture maps onto
anything real? The answer is that independent high-stakes systems keep
reinventing the same primitives under the same pressures, and the
absence or degradation of those primitives keeps recreating the same
families of failure.

The tacit-knowledge case is the sharpest pressure point in the file. It
does not undermine the corroboration from the other cases, but it does
mark the honest boundary of what the current architecture explicitly
covers — and the boundary where extension work would begin.

The forcing direction ("these primitives are necessary under the stated
pressures") lives in [../reference/THEOREMS.md](../reference/THEOREMS.md)
families F7 and F16 and in [../PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md).
The formal case bindings for classical puzzles live in family F5 of the
theorem registry.

---

## Go next

- [../START-HERE.md](../START-HERE.md) — terminology and reading routes for
  the rest of the documentation.

---

## Sources

1. PSNet / AHRQ, Medication Administration Errors. <https://psnet.ahrq.gov/primer/medication-administration-errors>
2. AHRQ Digital Healthcare Research, Bar-coded Medication Administration. <https://digital.ahrq.gov/bar-coded-medication-administration>
3. Poon EG et al. Effect of bar-code technology on the safety of medication administration. *N Engl J Med.* 2010;362(18):1698–707. PMID 20445181. <https://pubmed.ncbi.nlm.nih.gov/20445181/>
4. Truitt E et al. Effect of the Implementation of Barcode Technology and an Electronic Medication Administration Record on Adverse Drug Events. *Hosp Pharm.* 2016;51(6):474–83. PMID 27354749. <https://pubmed.ncbi.nlm.nih.gov/27354749/>
5. Morriss FH Jr et al. Effectiveness of a barcode medication administration system in reducing preventable adverse drug events in a neonatal intensive care unit: a prospective cohort study. *J Pediatr.* 2009;154(3):363–8. PMID 18823912. <https://pubmed.ncbi.nlm.nih.gov/18823912/>
6. Bonkowski J et al. Effect of barcode-assisted medication administration on emergency department medication errors. *Acad Emerg Med.* 2013;20(8):801–6. PMID 24033623. <https://pubmed.ncbi.nlm.nih.gov/24033623/>
7. IETF RFC 9162, Certificate Transparency Version 2.0. <https://www.ietf.org/rfc/rfc9162.html>
8. SLSA, Provenance v1.2. <https://slsa.dev/spec/v1.2/provenance>
9. NTSB, Cockpit Voice Recorders and Flight Data Recorders. <https://www.ntsb.gov/news/Pages/cvr_fdr.aspx>
10. NTSB, Press Release on CVR retention (February 2024). <https://www.ntsb.gov/news/press-releases/Pages/NR20240213.aspx>

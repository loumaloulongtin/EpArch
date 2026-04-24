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
- a **ledger-style lifecycle** rather than free-floating memory or assertion.

The empirical wager: if EpArch is tracking something real, systems that
preserve these primitives should be more robust against the failure
families the theory identifies, and removing the primitives should
predictably recreate those failures.

---

## Reading rule

Each case follows the same four-question format:

1. What is the relevant epistemic pressure?
2. Where are the EpArch primitives in the system?
3. What goes wrong when those primitives are absent, bypassed, or thinned?
4. Does the observed failure look like the pathology EpArch predicts?

The claim is not that any institution consciously implements EpArch. The
claim is that mature systems facing the same structural pressures keep
reinventing the same control surfaces.

---

## Why one delta case matters

Static convergence cases — a mature system under pressure happens to
have EpArch-like primitives — are good corroboration but vulnerable to
the selection-bias objection ("you picked systems that already look like
your framework"). A before/after intervention case changes the shape of
the claim from static resemblance to observed improvement after adding
the primitive. That is harder to dismiss.

**BCMA as intervention.** Pre-BCMA medication administration relied on
nurse memory, manual label reading, and informal verification. The
intervention adds a barcode-linked patient–medication match tied to an
explicit administration record; each administration is logged in a
durable eMAR trace. AHRQ reports a 41% reduction in non-timing
medication errors and a 51% reduction in potential adverse drug events
under BCMA. Workaround studies show roughly threefold higher medication
error risk when the barcode path is circumvented. The system improved
when an EpArch-like primitive was deliberately added and degraded
predictably when the primitive was deliberately removed.

---

## External cases

### 1. Hospital medication administration (BCMA / eMAR)

- **Pressure.** Distributed-testimony medication delivery under
  distraction, workflow friction, label ambiguity, and handoff error.
- **Primitives.** S: the rights of administration (patient, medication,
  dose, time, route). V: barcode scan of wristband and medication,
  linked to eMAR. E: wrong-patient, wrong-dose, wrong-rate,
  unreadable-barcode, pump misconfiguration. Scope: this patient, this
  order, this event. Lifecycle: eMAR audit trail, not memory.
- **Predicted pathology if thinned.** Regression toward wrong-patient,
  wrong-dose, wrong-medication failure modes.
- **Observed.** The BCMA evidence above.

### 2. Certificate Transparency / Web PKI

- **Pressure.** Distributed-testimony attestation under active
  adversarial pressure; relying parties cannot directly audit CAs.
- **Primitives.** S: CA issuance policy. V: CA-to-certificate-to-subject
  provenance. E: misissuance, inconsistent log views. Scope: domain
  name and subject. Lifecycle: append-only public CT logs.
- **Predicted pathology if thinned.** Silent misissuance easier to
  hide, detect late, or contest poorly.
- **Observed.** That is precisely what CT is designed to close.

### 3. Software supply-chain provenance (SLSA, Sigstore, in-toto)

- **Pressure.** Users rely on artifacts they did not build, from
  workflows they did not observe, with dependencies they did not inspect.
- **Primitives.** S: build and release standard. V: verifiable build
  provenance (where, when, how, by whom). E: tampering, substitution,
  builder compromise, provenance gaps. Scope: repo, revision, workflow,
  builder, artifact identity. Lifecycle: signed attestations in
  transparency logs.
- **Predicted pathology if thinned.** Consumers lose the ability to
  distinguish authentic from substituted artifacts; diagnosis becomes
  coarser after the fact.
- **Observed.** The mature response across high-assurance software
  ecosystems is not "trust harder" but stamp-plus-standard-plus-ledger.

### 4. Cockpit voice / flight data recorders

- **Pressure.** High-stakes retrospective reconstruction under sparse,
  noisy, adversarially incomplete evidence.
- **Primitives.** S: investigation-grade evidence standard. V:
  recorded cockpit and flight-state data. E: overwritten or
  unavailable data. Scope: this aircraft, this flight, this window.
  Lifecycle: recorder retention and post-incident retrieval.
- **Predicted pathology if thinned.** Later diagnosis becomes strictly
  worse — not because reality changed, but because the investigation
  ledger lost state.
- **Observed.** Overwritten-CVR cases show exactly this: the event is
  fixed, the degradation is in retained epistemic access to it.

### 5. Tacit knowledge transmission (apprenticeship, craft, oral tradition)

This is the strongest attempted disconfirmation and so gets more space.
A master craftsperson can transmit reliable know-how with no written S
field, no documented E catalogue, no formal provenance ledger, and no
explicit scope formalism. Medieval stonemasons built cathedrals. If
this were a clean success case with no functional analogues of the
primitives, the framework's scope would be narrower than reliable
knowledge transmission as such.

Where the objection bends: the system works specifically under high
social bandwidth, repeated direct observation, narrow transmission
channels, low scaling pressure, and low adversarial pressure inside the
master–apprentice relation. When those conditions degrade — diaspora,
discontinuity, commercialization, fake teachers, scale beyond direct
observation — the architecture predicts V-gaps (who learned from whom),
E-gaps (failure modes never externalized), scope collapse (local
boundary breaks when shared context goes), and challenge/repair
degradation.

One available response, within current scope, is a functional reading:
the mechanisms are present but implemented neurally and socially rather
than institutionally. V is the remembered transmission chain; E is
updated on each demonstrated or described failure; S is the mastery
threshold enforced by the craft relation; lifecycle is memory plus
repetition plus correction history; scope is the bounded community.

This is offered as a possible response, not a proof that EpArch fully
covers tacit knowledge. The case splits cleanly into three positions:
(1) the functions are already present, implemented neurally/socially
rather than institutionally — not a counterexample; (2) the functions
are not present but can be introduced through disciplined practice —
EpArch identifies an installable configuration; (3) a well-attested
tacit system remains robust under scale, discontinuity, and adversarial
pressure while genuinely lacking functional equivalents — the framework
is wrong on that domain. The case does not permit a fourth "outside the
scope" position. Which of 1–3 holds is empirical.

### 6. Prestige, credentialing, social-provenance games

- **Pressure.** Social attribution of competence and authority under
  selection, gaming, and reputation-laundering incentives.
- **Primitives.** S: the ostensible credential standard. V: who
  granted the credential and under what process. E: grade inflation,
  credential theft, fraudulent signatures, laundered prestige. Scope:
  the issuing institution's remit. Lifecycle: the credential record
  and its later verifiability.
- **Predicted pathology if thinned.** When V is opaque and lifecycle
  is non-auditable, credentials drift from their standard and become
  social-provenance tokens rather than epistemic objects. The failure
  is not random: it targets V and S jointly.
- **Observed.** Credential-fraud cases, accreditation-mill dynamics,
  and prestige laundering in academic and professional pipelines track
  the predicted degradation; countermeasures (public accreditation
  ledgers, credential verification services, revocable digital
  credentials) reintroduce V and lifecycle discipline.

---

## Interim conclusion

Across these six domains the pattern is consistent. Systems that
preserve separation of S / E / V, explicit provenance, explicit scope,
explicit standards, and a ledger-style lifecycle are more robust against
the failure families EpArch names. Systems that thin those surfaces —
by workaround, by design cut, or by social drift — regress toward the
pathologies the theory predicts. This is convergence under pressure,
not proof.

---

## Scope condition for genuine counterexamples

A case only counts against EpArch if it meets all four conditions:

1. The system is a knowledge-producing or knowledge-sustaining system
   under non-trivial adversarial or distributed-testimony pressure.
2. It demonstrably lacks functional equivalents of S, E, V, scope, and
   lifecycle — not merely their institutional form.
3. It remains robust against the failure families EpArch predicts,
   including under scale, discontinuity, and adversarial pressure.
4. Its robustness is not an artifact of unreported external scaffolding
   (co-located expert, narrow bandwidth, etc.) that itself carries the
   missing primitives.

A case that fails (2) by implementing the primitives in
non-institutional form is a non-institutional implementation, not a
counterexample. A case that satisfies (1)–(4) would be a live empirical
problem for the framework.

---

## What would count as a serious disconfirmation attempt

- A longitudinal study where a mature system deliberately removes one
  of the primitives and the predicted failure family does not appear.
- A well-attested knowledge-sustaining system satisfying the four scope
  conditions above, showing long-run robustness without functional
  analogues of the primitives.
- A domain where introducing the primitives measurably worsens
  reliability rather than improving it — the inverse of the BCMA
  intervention.

Anecdote, selection-biased convergence, and "my favorite institution
happens to resemble EpArch" are not disconfirmation attempts; but they
are not corroboration either, and the cases above are included only
because each presents a specific, named pressure and a specific, named
failure mode.

---

## Recommended use in the repo

Cite this file as corroboration, not as proof. The forcing direction
("these primitives are necessary under the stated pressures") lives in
[../reference/THEOREMS.md](../reference/THEOREMS.md) families F7 and
F16 and in the proof route in
[../PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md). The formal case
bindings for classical puzzles live in family F5 of the theorem
registry. This file is the empirical-correspondence / stress-test
surface, and nothing else.

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

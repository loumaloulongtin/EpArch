# Trust Bridge Design Notes

This document compares two trust-bridge ontologies considered for the concrete
model and explains the design choice reflected in `EpArch/Concrete/Types.lean`.
Its job is narrow: describe the two designs, show what each requires, and explain
why Agent-scoped is the simpler default. It does not evaluate which design is
better for a given deployment — both are coherent, and the choice is the
implementer's.

---

## Two Ontologies

### Bubble-scoped bridges

A `CTrustBridge` names `source_bubble` and `target_bubble`. The bridge is a
relationship between epistemic contexts. The receiving bubble accepts any deposit
that arrives with a valid bridge covering the source context, regardless of which
agent presents it.

`c_valid_export` would check:

```
tb.source_bubble == req.source  ∧  tb.verify (withdrawal_attestation req.deposit)
```

The presenting agent's identity is not part of the gate. Any agent that can produce
a deposit with a valid attestation from the source bubble can complete the transfer.

### Agent-scoped bridges (EpArch's choice)

A `CTrustBridge` names `authorized_agent`. The bridge is a relationship between an
accountable party and a receiving context. Only the named agent can rely on it.

`c_valid_export` checks:

```
tb.authorized_agent.id == req.presenting_agent.id
```

The presenting agent's identity is the gate condition. The bridge cannot be exercised
by a relay or proxy — the accountability is tied directly to the individual who asserts
the transfer.

---

## What Bubble-Scoped Requires

A correct Bubble-scoped implementation has to solve two problems that the Agent-scoped
design sidesteps.

**Bounded verification.** `CAuditChannel.capacity` is finite (the same finiteness the
DDoS proofs in `Adversarial/Concrete.lean` use). A receiving bubble cannot always
re-verify provenance from scratch: sources may be unreachable, or the capacity budget
may be exhausted. A Bubble-scoped bridge that covers all presenting agents must therefore
certify that *for any deposit arriving via this bridge, the source bubble has already done
the work*. The natural mechanism is a cryptographic signature: the source bubble signs the
withdrawal event, and the gate checks the signature. Without it, the bridge is a blanket
trust grant with no attestation anchor.

**Decentralization.** Bubble B has no read access to bubble A's ledger. The claim "deposit
d was withdrawn from bubble A" is an assertion in `CExportRequest`, not a verifiable fact
at the architecture level. A Bubble-scoped gate cannot check the source ledger directly; it
can only check what the source bubble has cryptographically attested. The crypto path is
therefore not optional — it is load-bearing for correctness.

So a correct Bubble-scoped implementation requires:

1. The source bubble to hold a signing key and emit signed withdrawal attestations.
2. The target bubble to hold the corresponding verification key (and a revocation
   mechanism if keys can be rotated).
3. `c_valid_export` to verify the attestation signature before admitting the deposit.

The presenting agent's identity plays no role. That is the feature, not a gap: any relay,
daemon, or pub/sub consumer can carry the deposit from A to B, and accountability rests
with the source bubble's key infrastructure.

---

## Why Agent-Scoped Is Simpler

Any correct Bubble-scoped implementation needs an entity that: holds the source bubble's
signing key, monitors the withdrawal ledger, signs events, manages key rotation, and
asserts "this signature is valid and covers this deposit." That entity is an agent by
EpArch's definition — it holds claims about A's state and asserts them into B's context.

Once that entity exists, tying the bridge directly to it is the minimal design:

- No key management at the bubble level.
- No anonymous presenting surface — the gate always names who is accountable.
- The accountability chain terminates at a party that `c_valid_export` can directly
  check, not at a signing key whose holder is not tracked by the architecture.

The tradeoff: Agent-scoped bridges cannot be used by anonymous relayers or by
architectures where the source bubble, not an individual agent, is the accountable party.

---

## When Bubble-Scoped Fits

Bubble-scoped bridges are the right design when:

- Many agents legitimately relay claims from bubble A to bubble B, and tracking each
  relayer's identity in a bridge entry would be impractical or unnecessary.
- The deployment runs a pub/sub or event-relay architecture where the source bubble
  signs withdrawal events as a matter of course, and any subscriber may deliver them.
- The accountability model places responsibility at the institutional (bubble) level
  rather than the individual (agent) level — for example, inter-organisation claim
  exchange where organisation A endorses its exports as a whole.

In these cases the `CTrustBridge` type would carry a `verify : ByteArray → Bool` field
(or a public key reference), and `c_valid_export` would apply it to a
`withdrawal_attestation` extracted from the request. The presenting agent's identity
field could be omitted from `CExportRequest` entirely, or retained for auditing without
being part of the gate check.

**Important:** "unauthenticated presenter" in this design does not mean "no trust anchor."
The trust anchor is the source bubble's signing key. An implementation that removes the
signature check entirely degrades the bridge to a blanket grant and loses the correctness
properties described above.

---

## Gate Invariants That Hold in Both Designs

In both designs, `c_import_deposit` returns `none` when the gate condition fails. The
gate is un-bypassable regardless of ontology — that property follows from the structure
of `c_import_deposit`, not from the specific check inside `c_valid_export`.

The theorems in `EpArch.Adversarial.Concrete` (`invalid_export_requires_reval_or_bridge`,
`missing_export_gate_blocks_import`) are proved over the Agent-scoped definition of
`c_valid_export`. A Bubble-scoped implementation would require analogous theorems over
its own `c_valid_export` — the proof structure would be identical; only the gate check
being unfolded changes.

# Trust Bridge Design Notes

This document describes the two trust-bridge authorization modes in
`EpArch/Concrete/Types.lean`, explains the topology of trust chains across
bubble boundaries, and states the one invariant that both modes share.
Its job is narrow: describe what each mode does, when each fits, and what
never changes regardless of which is used.

---

## The One Invariant

Bubbles never communicate directly. There is always an agent in the middle.

This is not a constraint imposed for simplicity — it is what a bubble *is*.
A bubble is an epistemic context: a scoped ledger of accepted claims. It does
not have a communication channel, a transport layer, or an intent. Only agents
do. Any deposit crossing a bubble boundary was placed there by an agent, and
`c_valid_export` is the gate that asks: is this agent authorised to do that?

The two modes in `CTrustBridgeAuth` are two answers to that question.

---

## Two Auth Modes

### `.byAgent` — named presenter

The bridge names a specific `CAgent`. The gate checks that the presenting agent
matches:

```
tb.auth = .byAgent a  →  gate: a.id == req.presenting_agent.id
```

Accountability is explicit: the bridge names exactly who may use it. No relay,
proxy, or daemon can exercise the bridge unless it is the named agent.

Fits when: the accountable party is known in advance and individual identity is
trackable.

### `.byToken` — credential-checked presenter

The bridge carries a `token_ok : ByteArray → Bool` predicate. The gate checks
that the request carries a passing credential:

```
tb.auth = .byToken ok  →  gate: req.auth_token.any ok
```

The presenting agent's identity is not part of the gate. Any agent that obtains
a valid credential can exercise the bridge. Accountability rests with whoever
configures and manages `token_ok` — typically the source bubble's administrator
or the issuing institution.

The credential mechanism is not prescribed. `token_ok` can verify an email-domain
assertion, a company badge ID, a JWT, a delegated OAuth scope, a cryptographic
signature, or any other serialisable proof of authority. The architecture does not
care what bytes are in `auth_token`; that is the deployer's choice.

Fits when: many agents legitimately relay claims from bubble A to bubble B, or
when accountability is institutional rather than individual.

**Important:** anonymous presenter does not mean no trust anchor. The anchor is
whatever `token_ok` accepts. Setting `token_ok := fun _ => true` degrades the
bridge to a blanket grant.

---

## Multi-Hop Chains

A single bubble-to-bubble transfer does not have to be a one-edge graph. The
normal real-world structure is often:

```
Bubble A  ←→  Agent₁  ←→  Agent₂  ←→  Bubble B
```

or longer chains. A lawyer speaks for a client. A company rep speaks for an
institution. An auditor vouches for a report. A manager authorises an employee
who submits something to another organisation. Nested represented authority is
ordinary, not pathological.

EpArch handles this naturally: each bubble boundary is a separate `CExportRequest`
with its own gate check. Agent₁ receives a deposit into its bubble via
`c_import_deposit`, then presents a new export request as Agent₂'s counterpart
into Bubble B. The gate fires independently at each crossing. No hop is gate-free.

The recursion that earlier seemed like a modeling problem — "who validates the
validator?" — is just the normal structure of delegated representation. The
architecture does not need to collapse it; it enforces accountability at each hop.

What matters at each crossing is not whether the chain is long but whether:
- the presenter is identifiable (`.byAgent`) or carries a valid credential (`.byToken`)
- the gate check is not vacuous

The `CTrustBridge.scope` field is available for deployers to record which claim categories
a bridge is intended to cover, but `c_valid_export` does not inspect it — scope enforcement
is an agent-layer policy obligation, not an architectural gate. The architecture enforces
presenter identity or credential validity; it does not substitute for the agent's claim routing
judgment.

---

## What Neither Mode Proves

Neither `.byAgent` nor `.byToken` proves that the deposit was validly withdrawn
from the source bubble before the export request was constructed. Bubble B has
no read access to bubble A's ledger, and `CAuditChannel.capacity` is finite —
full re-verification is not always possible even if the ledger were accessible.

Both modes delegate that responsibility to the agent layer. The gate EpArch
proves sound is transfer legitimacy: was the presenter authorised to make this
cross-bubble assertion? Whether the underlying withdrawal was valid is the
presenting agent's protocol obligation, enforced by whatever mechanism it uses.

The deeper structural point: deposits carry *epistemic standing*, not truth. A
claim that has cleared bubble A's standards has been accepted as meeting A's
epistemic regime — its V chain, its S threshold, its E model, its current τ.
None of that transfers automatically to bubble B. B may impose different
standards on any of those dimensions. The trust bridge authorises the
presenter; it does not resolve whether the deposit meets B's standards. That
is a separate question, and the architecture keeps it permanently separate.

This is why `revalidated = true` exists as a first-class export path alongside
the two bridge modes. Revalidation is the path where B explicitly ran the
lifecycle at its own standards. The bridge paths are the path where B accepts
the presenting agent's authority instead of rerunning the full check locally — a
legitimate decision, but a decision about trust in the agent, not a claim about
the deposit's epistemic adequacy under B's regime.

The full lifecycle — repair, staleness, headers, bank consultation — is
necessary precisely because deposits are process records, not truth
certificates. If a Deposited claim were guaranteed true everywhere and
indefinitely, none of that machinery would be needed: a deposit in any bubble
would be valid in all bubbles for all time. It is the formal argument for
conservatism: the full epistemic process is non-negotiable at each site of
reliance, regardless of how the cross-bubble transfer was authorised.

---

## Gate Invariants That Hold in Both Modes

`c_import_deposit` returns `none` when `c_valid_export` returns `false`. This
holds regardless of which auth mode the bridge uses — it follows from the
structure of `c_import_deposit`, not from anything inside `c_valid_export`.

The theorems in `EpArch.Adversarial.Concrete` (`invalid_export_requires_reval_or_bridge`,
`missing_export_gate_blocks_import`, `V_spoof_blocks_cross_bubble_reliance`) are proved
over the current `c_valid_export` definition, which dispatches on `CTrustBridgeAuth`.
They hold for both modes because the proofs only rely on the absence of any bridge
(`via_trust_bridge = none`), not on which auth variant is present.

The `.byToken` path is concretely instantiated by `olean_trust_bridge` in
`EpArch.Meta.LeanKernel.World` (the `OleanStaleness` section). The bridge
checks `decide (bytes.data = r.sourceHash.data)` — comparing `Array UInt8`
fields rather than `ByteArray` directly, since `ByteArray` lacks a synthesized
`BEq` or `DecidableEq` instance in Lean 4.3.0. The key architectural claim is
unchanged: the presenting machine's identity is irrelevant; only content
identity (hash equality) matters. `olean_hash_match_imports`,
`olean_hash_mismatch_rejects`, and `olean_multi_hop_both_gates_required` in
`EpArch.Meta.LeanKernel.RepairLoop` prove the gate's two outcomes and the
multi-hop independence property for this concrete instantiation.

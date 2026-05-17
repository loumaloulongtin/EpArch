# The Salary Spreadsheet Story

*[← Provenance](provenance.md) · [Redeemability →](redeemability.md)*

---

## Same deposit, different receivers

A manager has access to a compensation spreadsheet for the team. It lists names, titles, salaries, bonuses, and start dates.

The spreadsheet is accurate. It comes from payroll. It is the version everyone in the management chain works from.

A coworker from another department stops by the manager's desk and asks, casually:

> Hey, can I take a look at that? I'm curious what the new hires are getting paid.

Nothing about the spreadsheet changes.

The working deposit is:

* **P**: These are the current compensation figures for the team.
* **S**: Payroll-issued spreadsheets are the canonical record.
* **E**: A row may be out of date if a recent change has not yet propagated.
* **V**: Pulled from the payroll system; reviewed by HR last cycle.

P is the same proposition it was a minute ago. S is the same standard. E is the same model. V is the same chain.

The manager declines.

Not because the claim became false.
Not because the standard became too weak.
Not because the error model grew.
Not because the provenance got worse.

The manager declines because of a separate field:

* **ACL**: Compensation data may be disclosed to direct managers, payroll, HR, and legal, in connection with their role.

The curious coworker is a real person, a real employee, with real reasons of their own. They do not satisfy the ACL for this deposit.

The deposit is not exportable to them.

---

## Same deposit, different receiver, different outcome

Now change one thing.

The person asking is from HR, working on a pay-equity audit that has been formally scoped and approved.

The deposit is identical:

* **P**: These are the current compensation figures for the team.
* **S**: Payroll-issued spreadsheets are the canonical record.
* **E**: A row may be out of date if a recent change has not yet propagated.
* **V**: Pulled from the payroll system; reviewed by HR last cycle.
* **ACL**: Compensation data may be disclosed to direct managers, payroll, **HR**, and legal, in connection with their role.

But now the receiver clears the ACL. The export proceeds.

The same deposit is blocked for one agent and exportable to another, with nothing about the claim itself changing. ACL is the field that moves.

---

## What this shows

ACL does not decide whether P is true.
ACL does not decide whether S, E, or V are good.
ACL decides whether *this receiver*, in *this role*, for *this purpose*, may receive or use the deposit.

A deposit can be perfectly grounded in P, S, E, and V and still fail to export, because the field that fails is none of those.

---

# The Bank Call Story

## When the requester claims to clear the ACL gate

A customer's phone rings. The caller says:

> Hi, I'm calling from the fraud department at your bank. We've detected suspicious activity on your account. To verify your identity, can you confirm your account number and the answer to your security question?

The deposit being requested is restricted:

* **P**: Account number, security question, recent transaction details.
* **ACL**: May be disclosed to the bank through an authorized channel, or to a verified bank employee acting within a legitimate support process.

The caller offers something that looks like an ACL clearance:

> I'm from the bank's fraud department.

But the ACL question is not:

> Did someone claim to be from the bank?

It is:

> Has this requester been verified as an authorized agent through a channel that does not depend on the requester's own assertion?

Inside this call, no such verification is available. The caller controls the framing of the call. The caller picked the number to dial. The caller picked the words "fraud department." Any verification offered from inside the call is verification the caller composed.

The deposit does not export through this channel.

The repair path is to break the inbound channel and use an independent one: hang up, then contact the bank through the number on the back of the card, the official app, or a known-good URL. If the alert was real, it will be visible from that side too. If it was not, no harm has been done.

The caller's move was not against P, S, E, or V of the account data. They were not disputing the claim at all.

The move was a V-spoof aimed at the ACL gate: construct a provenance chain for the *authorization itself* ("I'm from the fraud department") that, if accepted, would clear the ACL check. ACL has its own provenance question — not where the claim came from, but where the requester's authorization came from — and the caller was fabricating the answer to that second question.

---

## What this shows

ACL is structurally closer to S than to V or E.

S holds a *policy over claims*: the criteria the claim must satisfy to be accepted here. ACL holds a *policy over receivers*: the criteria a requester must satisfy to receive the deposit here. Both are policies that get evaluated against something external. V is a chain of facts about origin. E is a model of failure modes. S and ACL are rules.

Because ACL is a policy, checking it requires establishing that the requester actually satisfies it — which requires evidence that does not originate with the requester. That is why the bank call attack has the shape it does. The caller was not attacking the claim. They were presenting a forged policy-satisfaction ("authorized fraud-department employee") without submitting to independent evaluation. The repair path — hang up, call back on a known-good channel — is just policy verification through a channel the requester does not control.

Self-asserted authorization does not clear an ACL gate. The structural test is whether the evaluation runs through a channel the requester does not compose.

---

# Takeaway

ACL is the deposit field that names who, in what role, for what purpose, may receive or use the deposit. ACL is distinct from P, S, E, and V. A deposit can be flawless in those fields and still fail to export, and the same flawless deposit can export to one receiver and not another with nothing about the claim itself changing. But ACL evaluation often requires its own provenance check: not provenance for the claim, but provenance for the requester's authorization.

ACL failures cluster around a small number of patterns:

* **Wrong receiver.** The requester is a real agent but not in the authorized class.
* **Wrong purpose.** The requester is in the authorized class but for a different use.
* **Wrong context.** The requester is normally authorized but not in this situation.
* **Stale authorization.** The requester used to be authorized and no longer is.
* **Impersonated authorization.** The requester is presenting themselves as authorized through a channel they control.
* **Overbroad export.** The sender discloses more of the deposit than the receiver needs.

The salary story is mostly about the first. The bank call story is mostly about the fifth, and shows that ACL has its own verification problem distinct from the deposit's own V.

---

*[← Provenance](provenance.md) · [Redeemability →](redeemability.md)*

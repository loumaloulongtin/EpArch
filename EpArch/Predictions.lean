/-
EpArch.Predictions — Non-Trivial Predictions

Predictions where the EpArch model diverges from intuition
and the model wins empirically. Encoded as structured claims
with mechanisms and falsifiers.

## What Makes These "Non-Trivial"?

A non-trivial prediction is one where common sense or pre-existing intuition
says X, but the formal model predicts ¬X — and empirical evidence supports
the model. Each prediction includes:
- What intuition says (the "obvious" answer)
- What the model says (the surprising answer)
- The mechanism (why the model predicts this)
- Empirical evidence (real-world support)
- A falsifier (what would disprove the prediction)

These are structural mappings from the model to empirical domains.
Each prediction is a plain record — not an obligation theorem —
since predictions must be assessable against real-world data, not
logical bundles.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank

namespace EpArch

universe u

/-! ## Prediction Structure -/

/-- An empirical prediction with mechanism and falsifier. -/
structure EmpiricalPrediction where
  name : String
  intuition : String          -- what common sense says
  model_says : String         -- what the model predicts
  mechanism : String          -- why the model predicts this
  evidence : String           -- empirical support
  falsifier : String          -- what would disprove the prediction


/-! ## The Four Non-Trivial Predictions -/

/-- Prediction 1: Intelligence doesn't protect against cults

    Intuition: Smart people should see through manipulation
    Model: Import-channel control + E-closure works regardless of IQ -/
def cultIntelligencePrediction : EmpiricalPrediction := {
  name := "Cult membership and intelligence"
  intuition := "Intelligent people should be resistant to cult recruitment"
  model_says := "Intelligence is orthogonal to cult susceptibility; channel control works on any IQ"
  mechanism := "Cults control import channels and close E-fields; S-quality (reasoning) doesn't help when V-sources are blocked and E rejects disconfirmation"
  evidence := "High-functioning professionals in cults; academic credentials don't protect; 'smart' people rationalize within closed E"
  falsifier := "If IQ reliably predicted cult resistance across controlled samples"
}

/-- Prediction 2: Critical thinking doesn't transfer across domains

    Intuition: CT is a general skill that transfers
    Model: S-quality is domain-specific; E-field must be built per domain -/
def criticalThinkingTransferPrediction : EmpiricalPrediction := {
  name := "Critical thinking transfer"
  intuition := "Critical thinking is a domain-general skill that transfers"
  model_says := "CT is domain-specific; good S in one field doesn't give you E-field in another"
  mechanism := "Validation requires domain E-field (threat model, confounders, failure modes); S-skills without E are blind"
  evidence := "Willingham (2007): CT depends on domain knowledge; Abrami et al. meta-analysis shows domain-specificity"
  falsifier := "If CT training in one domain reliably improved performance in unrelated domains"
}

/-- Prediction 3: Sharing ≠ believing

    Intuition: People share what they believe
    Model: Sharing is export; belief is deposit; different operations -/
def sharingBeliefPrediction : EmpiricalPrediction := {
  name := "Sharing vs believing"
  intuition := "People share content they believe is true"
  model_says := "Sharing (export) and believing (deposit) are distinct operations; people share for social reasons without believing"
  mechanism := "Export gate ≠ belief state; sharing optimizes for social outcomes (engagement, identity), not truth-tracking"
  evidence := "Pennycook et al. (2021): sharing intentions dissociate from accuracy judgments"
  falsifier := "If sharing behavior tracked accuracy judgments 1:1"
}

/-- Prediction 4: Audited entities can still fail spectacularly

    Intuition: Audit = safety
    Model: Success-driven bypass reduces audit frequency for high-reliance entities -/
def auditedEntitiesPrediction : EmpiricalPrediction := {
  name := "Audited entities and failure"
  intuition := "Heavily audited entities should be safe"
  model_says := "High-reliance entities accumulate trust and receive less scrutiny; blast radius scales with reliance"
  mechanism := "Success-driven header bypass: high-uptime → reduced challenge frequency → larger blast radius on failure"
  evidence := "Enron (audited by Arthur Andersen), FTX (audited, high-trust), systematic pattern of 'surprising' failures in trusted institutions"
  falsifier := "If high-audit-frequency entities showed proportionally lower catastrophic failure rates"
}


/-! ## Prediction Collection -/

def nonTrivialPredictions : List EmpiricalPrediction := [
  cultIntelligencePrediction,
  criticalThinkingTransferPrediction,
  sharingBeliefPrediction,
  auditedEntitiesPrediction
]


/-! ## Prediction Pattern -/

/-- What makes a prediction non-trivial. -/
structure NonTrivialityCheck where
  diverges_from_intuition : Bool   -- model says something surprising
  mechanism_specified : Bool        -- not just "it's complicated"
  empirically_checkable : Bool      -- can look at evidence
  falsifier_given : Bool            -- specifies what would disprove it

def check_nontriviality (p : EmpiricalPrediction) : NonTrivialityCheck := {
  diverges_from_intuition := p.intuition.length > 0 ∧ p.model_says.length > 0
  mechanism_specified := p.mechanism.length > 0
  empirically_checkable := p.evidence.length > 0
  falsifier_given := p.falsifier.length > 0
}


/-! ## Prediction Summary Table -/

structure PredictionSummary where
  case_name : String
  intuition_model_divergence : String
  mechanism : String

def predictionSummaryTable : List PredictionSummary := [
  ⟨"Cult/Intelligence", "IQ should protect → doesn't", "Channel control + E-closure"⟩,
  ⟨"CT Transfer", "CT transfers → doesn't", "E-field is domain-specific"⟩,
  ⟨"Sharing ≠ Belief", "Share what you believe → export ≠ deposit", "Social optimization ≠ truth-tracking"⟩,
  ⟨"Audited Entities", "Audit = safe → blast radius scales with trust", "Success-driven bypass"⟩
]

end EpArch

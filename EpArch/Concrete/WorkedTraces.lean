/-
EpArch.Concrete.WorkedTraces — Worked Diagnostic Traces

These are case studies from epistemic failure, encoded as structured data.
Each trace shows: where the failure localized, what primitive broke,
and what intervention the model predicts.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank

namespace EpArch

/-! ## Worked Trace Structure -/

/-- A worked trace captures a diagnostic case study.

    Classification localizes the problem to a specific primitive or field.
    Disconfirmation is specified in advance.
    Interventions target primitives, not just surface behavior. -/
structure WorkedTrace where
  name : String
  traceSection : String
  location : String           -- where in the model the failure lives
  traceLocalization : String  -- specific primitive/field failure
  end_state : String          -- final deposit status
  traceIntervention : String  -- what the model says to fix
  traceFalsifier : String     -- what would show this diagnosis wrong


/-! ## The Four Main Traces -/

/-- Ulcer Dispute (Barry Marshall / H. pylori)

    Location: S/E/V introduction
    Problem: E-field mismatch (stress model vs bacterial model)
    Key feature: V-independence (Koch's postulates were met) -/
def ulcerTrace : WorkedTrace where
  name := "Ulcer Dispute (H. pylori)"
  traceSection := "Bank lifecycle"
  location := "S/E/V intro"
  traceLocalization := "E-field mismatch; V-independence held"
  end_state := "Revoked (stress theory) → Redeposited (bacterial, new E)"
  traceIntervention := "Update E-field to include bacterial etiology"
  traceFalsifier := "If stress theory deposits had survived despite Koch's postulates being met for H. pylori"

/-- Hydroxychloroquine Episode

    Location: Export
    Problem: Header stripping during rapid export
    Key feature: Premature export of preliminary results -/
def hcqTrace : WorkedTrace where
  name := "HCQ Episode"
  traceSection := "Export protocol"
  location := "Export"
  traceLocalization := "Header stripping; premature export"
  end_state := "Revoked (scientific); Challenged (public)"
  traceIntervention := "Header-preserving export ('preliminary, single-site, uncontrolled')"
  traceFalsifier := "If header-preserved export had produced same downstream confusion"

/-- Replication Crisis

    Location: Recipe (E/V failure)
    Problem: Miscalibrated acceptance gate (S-inflation, E-gaps, V-weakness)
    Key feature: Systematic rather than individual failure -/
def replicationCrisisTrace : WorkedTrace where
  name := "Replication Crisis"
  traceSection := "Convergence (replication)"
  location := "Recipe"
  traceLocalization := "E/V failure (miscalibrated gate): S-inflation, E-gaps, V-weakness"
  end_state := "Quarantine/Revoke ongoing; governance change"
  traceIntervention := "Tighten S (pre-registration), expand E (publication bias), strengthen V (multi-lab)"
  traceFalsifier := "If fields with strong S/E/V showed same replication rates as weak ones"

/-- Vaccine Misinformation

    Location: Recipe
    Problem: Bridge failure (blocked import); E-field entrenchment
    Key feature: Two distinct failures — channel failure and filter failure -/
def vaccineMisinfoTrace : WorkedTrace where
  name := "Vaccine Misinformation"
  traceSection := "Convergence (misinformation)"
  location := "Recipe"
  traceLocalization := "Bridge failure (blocked import); E-field entrenchment"
  end_state := "Deposited (challenge-blocked; revision-resistant)"
  traceIntervention := "Reopen import channels (bridge repair); expand E-field to admit disconfirmation (entrenchment revision)"
  traceFalsifier := "If 'more facts' reliably corrected without channel repair"


/-! ## Trace Collection -/

def mainTraces : List WorkedTrace := [
  ulcerTrace,
  hcqTrace,
  replicationCrisisTrace,
  vaccineMisinfoTrace
]


/-! ## Pattern Across Traces -/

/-- The structural pattern that holds across all traces. -/
structure TracePattern where
  classification_localizes : Bool     -- model identifies specific locus
  disconfirmation_specified : Bool    -- diagnosis predicts what would falsify
  intervention_targets_primitive : Bool -- fix aims at S/E/V/channel, not "change minds"
  progress_measurable : Bool          -- "faster detection", "lower persistence", etc.

/-- All main traces should satisfy the pattern. -/
def trace_satisfies_pattern (t : WorkedTrace) : TracePattern where
  classification_localizes := t.traceLocalization.length > 0
  disconfirmation_specified := t.traceFalsifier.length > 0
  intervention_targets_primitive := t.traceIntervention.length > 0
  progress_measurable := true  -- all traces specify measurable outcomes


/-! ## Trace Summary Table -/

/-- Summary row for a trace. -/
structure TraceSummary where
  case_name : String
  location : String
  localization : String
  end_state : String

def traceSummaryTable : List TraceSummary := [
  ⟨"Ulcer Dispute", "S/E/V intro", "E-field mismatch; V-independence", "Revoked → Redeposited (new E)"⟩,
  ⟨"HCQ Episode", "Export", "Header stripping; premature export", "Revoked (sci); Challenged (pub)"⟩,
  ⟨"Replication Crisis", "Recipe", "E/V failure (miscalibrated gate)", "Quarantine/Revoke ongoing"⟩,
  ⟨"Vaccine Misinfo", "Recipe", "Bridge failure; E-field entrenchment", "Deposited (challenge-blocked)"⟩
]

end EpArch

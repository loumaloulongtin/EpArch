Set-Location "E:\Research\EpArch\lean-formalization"
$enc = [System.Text.UTF8Encoding]::new($false)

$map = [ordered]@{
  "traction_broader_than_authorization"="Theorems/Corners.lean";"authorization_implies_traction"="Theorems/Corners.lean"
  "candidate_blocks_withdrawal"="Theorems/Corners.lean";"withdrawal_requires_deposited"="Theorems/Corners.lean"
  "submit_produces_candidate"="Theorems/Corners.lean";"frozen_canon_no_revocation"="Theorems/Corners.lean"
  "frozen_canon_no_revocation_trace"="Theorems/Corners.lean";"stale_blocks_withdrawal"="Theorems/Corners.lean"
  "Stale"="Theorems/Corners.lean";"tick_can_cause_staleness"="Theorems/Corners.lean"
  "withdrawal_requires_fresh"="Theorems/Corners.lean";"credence_does_not_auto_close"="Theorems/Corners.lean"
  "status_distinction_blocks_lottery"="Theorems/Corners.lean"
  "lottery_paradox_dissolved_architecturally"="Theorems/Corners.lean"
  "lottery_no_deposit_blocks_withdraw"="Theorems/Corners.lean";"EntrenchedAgent"="Theorems/Corners.lean"
  "deposit_no_longer_active"="Theorems/Corners.lean";"entrenchment_breaks_safe_withdrawal"="Theorems/Corners.lean"
  "entrenched_cannot_withdraw"="Theorems/Corners.lean";"export_creates_visibility"="Theorems/Corners.lean"
  "export_creates_B2_deposit"="Theorems/Corners.lean";"export_ignores_target_acl"="Theorems/Corners.lean"
  "finite_budget_forces_triage"="Theorems/Corners.lean"
  "GettierCase"="Theorems/Cases.lean";"gettier_is_V_failure"="Theorems/Cases.lean"
  "gettier_ground_disconnected"="Theorems/Cases.lean";"canonical_gettier_is_gettier"="Theorems/Cases.lean"
  "canonical_gettier_conditions"="Theorems/Cases.lean";"FakeBarnCase"="Theorems/Cases.lean"
  "fake_barn_is_E_failure"="Theorems/Cases.lean";"fake_barn_profile_yields_E_failure"="Theorems/Cases.lean"
  "canonical_fake_barn_is_fake_barn"="Theorems/Cases.lean";"LotterySituation"="Theorems/Cases.lean"
  "LotteryIsTypeError"="Theorems/Cases.lean";"ConfabulationCase"="Theorems/Cases.lean"
  "confabulation_is_type_error"="Theorems/Cases.lean";"standard_case_is_S_failure"="Theorems/Cases.lean"
  "canonical_standard_case_is_standard"="Theorems/Cases.lean";"standard_failure_targets_S"="Theorems/Cases.lean"
  "standard_failure_is_relational"="Theorems/Cases.lean"
  "same_deposit_standard_split_yields_relational_S_failure"="Theorems/Cases.lean"
  "canonical_allergy_is_relational_split"="Theorems/Cases.lean";"s_failure_v_is_sound"="Theorems/Cases.lean"
  "s_failure_e_is_sound"="Theorems/Cases.lean";"s_failure_v_mode_and_e_threat"="Theorems/Cases.lean"
  "relational_S_requires_matching_VE_data"="Theorems/Cases.lean";"vacuous_standard_is_S_failure"="Theorems/Cases.lean"
  "testimony_only_plus_unreliable_source_yields_void_S"="Theorems/Cases.lean"
  "canonical_liar_cook_is_void"="Theorems/Cases.lean";"absolute_vs_relational_S_failure"="Theorems/Cases.lean"
  "canWithdrawAt_iff_gates"="Theorems/Withdrawal.lean";"withdrawal_gates"="Theorems/Withdrawal.lean"
  "repair_enforces_revalidation"="Theorems/Withdrawal.lean";"repair_requires_prior_challenge"="Theorems/Withdrawal.lean"
  "submit_enforces_revalidation"="Theorems/Withdrawal.lean";"withdrawal_requires_canWithdrawAt"="Theorems/Withdrawal.lean"
  "canWithdrawAt_enables_step"="Theorems/Withdrawal.lean";"current_from_clock"="Theorems/Withdrawal.lean"
  "current_stable"="Theorems/Withdrawal.lean";"diagnose_finds_broken"="Theorems/Withdrawal.lean"
  "no_strip_left_inverse"="Theorems/Strip.lean";"strip_not_injective_if"="Theorems/Strip.lean"
  "import_cannot_reconstruct"="Theorems/Strip.lean";"different_headers_same_strip"="Theorems/Strip.lean"
  "different_headers_different_deposits"="Theorems/Strip.lean";"strip_loses_header_info"="Theorems/Strip.lean"
  "content_eq_not_implies_deposit_eq"="Theorems/Strip.lean";"provenance_matters"="Theorems/Strip.lean"
  "stripV_irreversible"="Theorems/Strip.lean";"stripV_idempotent"="Theorems/Strip.lean"
  "stripV_preserves_claim"="Theorems/Strip.lean";"stripV_not_injective"="Theorems/Strip.lean"
  "strip_reduces_field_count"="Theorems/Strip.lean";"fewer_fields_coarser_repair"="Theorems/Strip.lean"
  "v8_implies_v7_strip_reduces"="Theorems/Strip.lean";"stripped_repair_must_be_coarse"="Theorems/Strip.lean"
  "full_repair_can_be_surgical"="Theorems/Strip.lean";"fieldcount_full_eq_diagnosability"="Theorems/Strip.lean"
  "stripped_diagnosability_is_zero"="Theorems/Strip.lean";"FieldCount_Full"="Theorems/Strip.lean"
  "FieldCount_Stripped"="Theorems/Strip.lean"
  "field_checkable_iff_header"="Theorems/Headers.lean";"harder_without_headers"="Theorems/Headers.lean"
  "header_stripped_harder"="Theorems/Headers.lean";"header_improves_diagnosability"="Theorems/Headers.lean"
  "header_localization_link"="Theorems/Headers.lean"
  "safety_ctx_V_link"="Theorems/Modal.lean";"sensitivity_ctx_E_link"="Theorems/Modal.lean"
  "gettier_profile_yields_V_failure"="Theorems/Modal.lean";"gettier_ctx_exhibits_provenance_gap"="Theorems/Modal.lean"
  "deposits_survive_revision_free_trace"="Theorems/Pathologies.lean"
  "bridge_monolithic_opaque"="Theorems/Pathologies.lean";"bridge_stripped_ungrounded"="Theorems/Pathologies.lean"
  "local_redeemability_survives"="Theorems/Pathologies.lean";"context_is_policy"="Theorems/Pathologies.lean"
  "testimony_is_export"="Theorems/Pathologies.lean";"disagreement_is_routing"="Theorems/Pathologies.lean"
  "forgotten_evidence_persistence"="Theorems/Pathologies.lean";"group_bubble_separation"="Theorems/Pathologies.lean"
  "deposit_exportability"="Theorems/Pathologies.lean";"certainty_not_exportable"="Theorems/Pathologies.lean"
  "certainty_not_exportable_link"="Theorems/Pathologies.lean";"injustice_is_import_corruption"="Theorems/Pathologies.lean"
  "artifact_bubble_membership"="Theorems/Pathologies.lean";"no_semantic_shift"="Theorems/Pathologies.lean"
  "closure_type_separation"="Theorems/Dissolutions.lean";"luminosity_type_separation"="Theorems/Dissolutions.lean"
  "moorean_export_contradiction"="Theorems/Dissolutions.lean";"moorean_is_export_contradiction"="Theorems/Dissolutions.lean"
  "preface_dissolution"="Theorems/Dissolutions.lean";"bank_cannot_generate_certainty"="Theorems/Dissolutions.lean"
  "higher_order_relocation"="Theorems/Dissolutions.lean";"apriori_domain_parameterization"="Theorems/Dissolutions.lean"
  "math_practice_is_bubble_distinct"="Theorems/Dissolutions.lean"
  "notation_invariance_of_redeemability"="Theorems/Dissolutions.lean"
  "notation_invariance_of_empirical_redeemability"="Theorems/Dissolutions.lean"
  "valid_dissolution"="Theorems/Dissolutions.lean"
}

function Apply-TableFixes([string]$content) {
  foreach ($entry in $map.GetEnumerator()) {
    $name = $entry.Key; $sub = $entry.Value
    $escaped = [regex]::Escape($name)
    # Pattern A: `name` | Theorems.lean (table cell, no line number)
    $content = [regex]::Replace($content, "``$escaped`` \| Theorems\.lean(?!/)(?::\d+)?", "``$name`` | $sub")
    # Pattern B: lines with Theorems.lean:NNNN where the theorem name also appears
    $content = [regex]::Replace($content, "(?<=``$escaped``[^\n]*?)Theorems\.lean:\d+", $sub)
  }
  return $content
}

# DOCS/THEOREMS.md
$path = "DOCS\THEOREMS.md"; $c = [System.IO.File]::ReadAllText($path)
$c = Apply-TableFixes $c
$c = $c -replace '### Bridge Theorems \(Theorems\.lean\)', '### Bridge Theorems (Theorems/Headers.lean)'
$c = $c -replace '### Diagnosability Metric Theorems \(Theorems\.lean\)', '### Diagnosability Metric Theorems (Theorems/Headers.lean)'
$c = $c -replace '### Diagnosability Coupling Theorems \(Theorems\.lean\)', '### Diagnosability Coupling Theorems (Theorems/Strip.lean)'
$c = $c -replace '### Modal Case Theorems \(Theorems\.lean\)', '### Modal Case Theorems (Theorems/Modal.lean)'
$c = $c -replace 'coupling the Diagnosability\.lean and Theorems\.lean metric', 'coupling the Diagnosability.lean and Theorems/Strip.lean metric'
$c = $c -replace '\*\*File:\*\* `Theorems\.lean`', '**Files:** `Theorems/Dissolutions.lean`, `Theorems/Pathologies.lean`'
[System.IO.File]::WriteAllText($path, $c, $enc); Write-Host "DOCS/THEOREMS.md updated"

# DOCS/PAPER-MAP.md
$path = "DOCS\PAPER-MAP.md"; $c = [System.IO.File]::ReadAllText($path)
$c = Apply-TableFixes $c
$c = $c -replace '\| 3 \| JTB Underspecified \| Theorems\.lean', '| 3 | JTB Underspecified | Theorems/Cases.lean'
$c = $c -replace '\| 10 \| Export \| StepSemantics\.lean, Theorems\.lean', '| 10 | Export | StepSemantics.lean, Theorems/Strip.lean'
$c = $c -replace '\| 12 \| Failure Modes \| Theorems\.lean', '| 12 | Failure Modes | Theorems/Withdrawal.lean, Theorems/Corners.lean'
$c = $c -replace '\| 15 \| Explanatory Recipe \| Diagnosability\.lean, Theorems\.lean', '| 15 | Explanatory Recipe | Diagnosability.lean, Theorems/Headers.lean, Theorems/Strip.lean'
$c = $c -replace '`strip` \| `def` \| Header\.lean/Theorems\.lean', '`strip` | `def` | Header.lean/Theorems/Strip.lean'
[System.IO.File]::WriteAllText($path, $c, $enc); Write-Host "DOCS/PAPER-MAP.md updated"

# DOCS/README.md
$path = "DOCS\README.md"; $c = [System.IO.File]::ReadAllText($path)
$c = $c -replace '`Theorems\.lean` \| Derived theorems, corner gates, case diagnoses \| 0', '`Theorems/` | Primary theorem library split into 8 focused sub-modules (Withdrawal, Cases, Headers, Modal, Strip, Corners, Dissolutions, Pathologies) | 0'
[System.IO.File]::WriteAllText($path, $c, $enc); Write-Host "DOCS/README.md updated"

# DOCS/MODULARITY.md
$path = "DOCS\MODULARITY.md"; $c = [System.IO.File]::ReadAllText($path)
$c = $c -replace '`Commitments\.lean`, `Theorems\.lean`, `Diagnosability\.lean`', '`Commitments.lean`, `Theorems/` (8 sub-modules), `Diagnosability.lean`'
$c = $c -replace 'The withdrawal/repair/submit theorems from `Theorems\.lean` are', 'The withdrawal/repair/submit theorems from `Theorems/Withdrawal.lean` are'
[System.IO.File]::WriteAllText($path, $c, $enc); Write-Host "DOCS/MODULARITY.md updated"

# DOCS/AXIOMS.md
$path = "DOCS\AXIOMS.md"; $c = [System.IO.File]::ReadAllText($path)
$c = $c -replace '\| `Theorems\.lean` \| Derived theorems \|', '| `Theorems/` | Derived theorems (8 sub-modules) |'
[System.IO.File]::WriteAllText($path, $c, $enc); Write-Host "DOCS/AXIOMS.md updated"

# README.md -- Core Claims Formalized table (no Unicode in these patterns)
$path = "README.md"; $c = [System.IO.File]::ReadAllText($path)
$c = $c -replace '\| `traction_broader_than_authorization` \| Theorems\.lean \|', '| `traction_broader_than_authorization` | Theorems/Corners.lean |'
$c = $c -replace '\| `no_strip_left_inverse` \| Theorems\.lean \|', '| `no_strip_left_inverse` | Theorems/Strip.lean |'
$c = $c -replace '\| `lottery_paradox_dissolved_architecturally` \| Theorems\.lean \|', '| `lottery_paradox_dissolved_architecturally` | Theorems/Corners.lean |'
$c = $c -replace '\| `stale_blocks_withdrawal` \| Theorems\.lean \|', '| `stale_blocks_withdrawal` | Theorems/Corners.lean |'
[System.IO.File]::WriteAllText($path, $c, $enc); Write-Host "README.md (Core Claims table) updated"

Write-Host "Done. Remaining manual fixes needed in README.md (Exploring table + Module table + What EpArch Does table)"
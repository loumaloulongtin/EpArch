/-
EpArch.Theorems.Cases — Classic Epistemology Diagnoses (umbrella re-export)

Re-exports all case-type modules.  Import this file to get the complete taxonomy.

## Layout

| File                        | Failure mode                                         |
|-----------------------------|------------------------------------------------------|
| Cases/Gettier.lean          | V-independence failure (provenance ≠ truth-maker)    |
| Cases/FakeBarn.lean         | E-field failure (unmodeled environmental threat)     |
| Cases/Standard.lean         | S-field failure — relational (threshold mismatch)    |
| Cases/VacuousStandard.lean  | S-field failure — absolute (E + V expose S-void)     |
| Cases/TypeErrors.lean       | Ladder/Bank type errors (Lottery, Confabulation)     |

## Contributing a new case

Create `EpArch/Theorems/Cases/YourCase.lean` with `namespace EpArch`,
implement the structure + canonical instance + routing theorem, then add an
`import` line below.  No other files need to change.
-/
import EpArch.Theorems.Cases.Gettier
import EpArch.Theorems.Cases.FakeBarn
import EpArch.Theorems.Cases.Standard
import EpArch.Theorems.Cases.VacuousStandard
import EpArch.Theorems.Cases.TypeErrors


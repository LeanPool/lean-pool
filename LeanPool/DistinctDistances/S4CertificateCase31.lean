/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase31Summary0
public import LeanPool.DistinctDistances.S4CertificateCase31Summary1

/-!
# Case 31 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case31Summary0.combine case31Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case31Build rows31 fullSummary := by
  rw [case31RowsShape]
  exact case31Summary0Checked.node case31Summary1Checked

/-- The case 31 certificate passes the original weighted-row checker. -/
theorem case31_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 31) (caseY.get 32)) rows31 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

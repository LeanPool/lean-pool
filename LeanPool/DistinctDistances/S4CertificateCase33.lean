/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase33Summary0
public import LeanPool.DistinctDistances.S4CertificateCase33Summary1

/-!
# Case 33 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case33Summary0.combine case33Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case33Build rows33 fullSummary := by
  rw [case33RowsShape]
  exact case33Summary0Checked.node case33Summary1Checked

/-- The case 33 certificate passes the original weighted-row checker. -/
theorem case33_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 33) (caseY.get 34)) rows33 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

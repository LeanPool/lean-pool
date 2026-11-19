/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase27Summary0
public import LeanPool.DistinctDistances.S4CertificateCase27Summary1

/-!
# Case 27 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case27Summary0.combine case27Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case27Build rows27 fullSummary := by
  rw [case27RowsShape]
  exact case27Summary0Checked.node case27Summary1Checked

/-- The case 27 certificate passes the original weighted-row checker. -/
theorem case27_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 27) (caseY.get 28)) rows27 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

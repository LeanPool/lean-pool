/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase17Summary0
public import LeanPool.DistinctDistances.S4CertificateCase17Summary1

/-!
# Case 17 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case17Summary0.combine case17Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case17Build rows17 fullSummary := by
  rw [case17RowsShape]
  exact case17Summary0Checked.node case17Summary1Checked

/-- The case 17 certificate passes the original weighted-row checker. -/
theorem case17_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 17) (caseY.get 18)) rows17 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

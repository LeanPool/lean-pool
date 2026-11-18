/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase26Summary0
public import LeanPool.DistinctDistances.S4CertificateCase26Summary1

/-!
# Case 26 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case26Summary0.combine case26Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case26Build rows26 fullSummary := by
  rw [case26RowsShape]
  exact case26Summary0Checked.node case26Summary1Checked

/-- The case 26 certificate passes the original weighted-row checker. -/
theorem case26_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 26) (caseY.get 27)) rows26 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

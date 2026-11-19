/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase09Summary0
public import LeanPool.DistinctDistances.S4CertificateCase09Summary1
public import LeanPool.DistinctDistances.S4CertificateCase09Summary2
public import LeanPool.DistinctDistances.S4CertificateCase09Summary3

/-!
# Case 9 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case09Summary0.combine case09Summary1).combine
    (case09Summary2.combine case09Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case09Build rows09 fullSummary := by
  rw [case09RowsShape]
  exact (case09Summary0Checked.node case09Summary1Checked).node
    (case09Summary2Checked.node case09Summary3Checked)

/-- The case 9 certificate passes the original weighted-row checker. -/
theorem case09_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 9) (caseY.get 10)) rows09 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

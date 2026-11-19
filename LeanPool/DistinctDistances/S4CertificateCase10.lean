/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase10Summary0
public import LeanPool.DistinctDistances.S4CertificateCase10Summary1
public import LeanPool.DistinctDistances.S4CertificateCase10Summary2
public import LeanPool.DistinctDistances.S4CertificateCase10Summary3

/-!
# Case 10 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case10Summary0.combine case10Summary1).combine
    (case10Summary2.combine case10Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case10Build rows10 fullSummary := by
  rw [case10RowsShape]
  exact (case10Summary0Checked.node case10Summary1Checked).node
    (case10Summary2Checked.node case10Summary3Checked)

/-- The case 10 certificate passes the original weighted-row checker. -/
theorem case10_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 10) (caseY.get 11)) rows10 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

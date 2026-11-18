/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase08Summary0
public import LeanPool.DistinctDistances.S4CertificateCase08Summary1
public import LeanPool.DistinctDistances.S4CertificateCase08Summary2
public import LeanPool.DistinctDistances.S4CertificateCase08Summary3

/-!
# Case 8 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case08Summary0.combine case08Summary1).combine
    (case08Summary2.combine case08Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case08Build rows08 fullSummary := by
  rw [case08RowsShape]
  exact (case08Summary0Checked.node case08Summary1Checked).node
    (case08Summary2Checked.node case08Summary3Checked)

/-- The case 8 certificate passes the original weighted-row checker. -/
theorem case08_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 8) (caseY.get 9)) rows08 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

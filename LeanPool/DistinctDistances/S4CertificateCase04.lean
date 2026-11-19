/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase04Summary0
public import LeanPool.DistinctDistances.S4CertificateCase04Summary1
public import LeanPool.DistinctDistances.S4CertificateCase04Summary2
public import LeanPool.DistinctDistances.S4CertificateCase04Summary3

/-!
# Case 4 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case04Summary0.combine case04Summary1).combine
    (case04Summary2.combine case04Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case04Build rows04 fullSummary := by
  rw [case04RowsShape]
  exact (case04Summary0Checked.node case04Summary1Checked).node
    (case04Summary2Checked.node case04Summary3Checked)

/-- The case 4 certificate passes the original weighted-row checker. -/
theorem case04_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 4) (caseY.get 5)) rows04 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

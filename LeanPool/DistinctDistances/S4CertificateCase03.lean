/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase03Summary0
public import LeanPool.DistinctDistances.S4CertificateCase03Summary1
public import LeanPool.DistinctDistances.S4CertificateCase03Summary2
public import LeanPool.DistinctDistances.S4CertificateCase03Summary3

/-!
# Case 3 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case03Summary0.combine case03Summary1).combine
    (case03Summary2.combine case03Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case03Build rows03 fullSummary := by
  rw [case03RowsShape]
  exact (case03Summary0Checked.node case03Summary1Checked).node
    (case03Summary2Checked.node case03Summary3Checked)

/-- The case 3 certificate passes the original weighted-row checker. -/
theorem case03_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 3) (caseY.get 4)) rows03 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

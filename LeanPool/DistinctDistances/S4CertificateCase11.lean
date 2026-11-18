/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase11Summary0
public import LeanPool.DistinctDistances.S4CertificateCase11Summary1
public import LeanPool.DistinctDistances.S4CertificateCase11Summary2
public import LeanPool.DistinctDistances.S4CertificateCase11Summary3

/-!
# Case 11 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case11Summary0.combine case11Summary1).combine
    (case11Summary2.combine case11Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case11Build rows11 fullSummary := by
  rw [case11RowsShape]
  exact (case11Summary0Checked.node case11Summary1Checked).node
    (case11Summary2Checked.node case11Summary3Checked)

/-- The case 11 certificate passes the original weighted-row checker. -/
theorem case11_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 11) (caseY.get 12)) rows11 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

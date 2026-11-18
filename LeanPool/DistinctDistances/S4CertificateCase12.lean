/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase12Summary0
public import LeanPool.DistinctDistances.S4CertificateCase12Summary1
public import LeanPool.DistinctDistances.S4CertificateCase12Summary2
public import LeanPool.DistinctDistances.S4CertificateCase12Summary3

/-!
# Case 12 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case12Summary0.combine case12Summary1).combine
    (case12Summary2.combine case12Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case12Build rows12 fullSummary := by
  rw [case12RowsShape]
  exact (case12Summary0Checked.node case12Summary1Checked).node
    (case12Summary2Checked.node case12Summary3Checked)

/-- The case 12 certificate passes the original weighted-row checker. -/
theorem case12_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 12) (caseY.get 13)) rows12 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase06Summary0
public import LeanPool.DistinctDistances.S4CertificateCase06Summary1
public import LeanPool.DistinctDistances.S4CertificateCase06Summary2
public import LeanPool.DistinctDistances.S4CertificateCase06Summary3

/-!
# Case 6 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case06Summary0.combine case06Summary1).combine
    (case06Summary2.combine case06Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case06Build rows06 fullSummary := by
  rw [case06RowsShape]
  exact (case06Summary0Checked.node case06Summary1Checked).node
    (case06Summary2Checked.node case06Summary3Checked)

/-- The case 6 certificate passes the original weighted-row checker. -/
theorem case06_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 6) (caseY.get 7)) rows06 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

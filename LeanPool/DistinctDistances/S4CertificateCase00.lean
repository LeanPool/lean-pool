/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase00Summary0
public import LeanPool.DistinctDistances.S4CertificateCase00Summary1
public import LeanPool.DistinctDistances.S4CertificateCase00Summary2
public import LeanPool.DistinctDistances.S4CertificateCase00Summary3

/-!
# Case 0 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case00Summary0.combine case00Summary1).combine
    (case00Summary2.combine case00Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case00Build rows00 fullSummary := by
  rw [case00RowsShape]
  exact (case00Summary0Checked.node case00Summary1Checked).node
    (case00Summary2Checked.node case00Summary3Checked)

/-- The case 0 certificate passes the original weighted-row checker. -/
theorem case00_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 0) (caseY.get 1)) rows00 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase02Summary0
public import LeanPool.DistinctDistances.S4CertificateCase02Summary1
public import LeanPool.DistinctDistances.S4CertificateCase02Summary2
public import LeanPool.DistinctDistances.S4CertificateCase02Summary3

/-!
# Case 2 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case02Summary0.combine case02Summary1).combine
    (case02Summary2.combine case02Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case02Build rows02 fullSummary := by
  rw [case02RowsShape]
  exact (case02Summary0Checked.node case02Summary1Checked).node
    (case02Summary2Checked.node case02Summary3Checked)

/-- The case 2 certificate passes the original weighted-row checker. -/
theorem case02_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 2) (caseY.get 3)) rows02 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

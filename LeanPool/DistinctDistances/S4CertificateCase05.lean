/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase05Summary0
public import LeanPool.DistinctDistances.S4CertificateCase05Summary1
public import LeanPool.DistinctDistances.S4CertificateCase05Summary2
public import LeanPool.DistinctDistances.S4CertificateCase05Summary3

/-!
# Case 5 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case05Summary0.combine case05Summary1).combine
    (case05Summary2.combine case05Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case05Build rows05 fullSummary := by
  rw [case05RowsShape]
  exact (case05Summary0Checked.node case05Summary1Checked).node
    (case05Summary2Checked.node case05Summary3Checked)

/-- The case 5 certificate passes the original weighted-row checker. -/
theorem case05_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 5) (caseY.get 6)) rows05 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

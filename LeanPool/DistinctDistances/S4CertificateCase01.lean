/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase01Summary0
public import LeanPool.DistinctDistances.S4CertificateCase01Summary1
public import LeanPool.DistinctDistances.S4CertificateCase01Summary2
public import LeanPool.DistinctDistances.S4CertificateCase01Summary3

/-!
# Case 1 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case01Summary0.combine case01Summary1).combine
    (case01Summary2.combine case01Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case01Build rows01 fullSummary := by
  rw [case01RowsShape]
  exact (case01Summary0Checked.node case01Summary1Checked).node
    (case01Summary2Checked.node case01Summary3Checked)

/-- The case 1 certificate passes the original weighted-row checker. -/
theorem case01_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 1) (caseY.get 2)) rows01 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

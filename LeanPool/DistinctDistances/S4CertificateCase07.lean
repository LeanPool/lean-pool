/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase07Summary0
public import LeanPool.DistinctDistances.S4CertificateCase07Summary1
public import LeanPool.DistinctDistances.S4CertificateCase07Summary2
public import LeanPool.DistinctDistances.S4CertificateCase07Summary3

/-!
# Case 7 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  (case07Summary0.combine case07Summary1).combine
    (case07Summary2.combine case07Summary3)

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case07Build rows07 fullSummary := by
  rw [case07RowsShape]
  exact (case07Summary0Checked.node case07Summary1Checked).node
    (case07Summary2Checked.node case07Summary3Checked)

/-- The case 7 certificate passes the original weighted-row checker. -/
theorem case07_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 7) (caseY.get 8)) rows07 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4

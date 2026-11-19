/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.AreaCertificateInputs

/-!
# Gerver niche area certificate

The kernel checks the rectangle subtotals independently for the seven roof pieces.
-/

public section

namespace MovingSofa.GerverAreaCert

private theorem foldl_seven_rows (row : ℕ → ℤ) :
    (List.range 7).foldl (fun acc r => acc + row r) 0 =
      row 0 + row 1 + row 2 + row 3 + row 4 + row 5 + row 6 := by
  simp only [show List.range 7 = [0, 1, 2, 3, 4, 5, 6] from rfl,
    List.foldl_cons, List.foldl_nil, zero_add]

private theorem nicheSumZ_fold :
    nicheSumZ = (List.range 7).foldl (fun acc r => acc + rowSumZ r) 0 := rfl

private theorem nicheRow0 : rowSumZ 0 =
    19597308591660707364944755134035008938771026659031816206 := by decide +kernel

private theorem nicheRow1 : rowSumZ 1 =
    5856875057996799485250513348384378957256987446894464959957 := by decide +kernel

private theorem nicheRow2 : rowSumZ 2 =
    242852289672707308963614021870115390121539327939709517267908 := by decide +kernel

private theorem nicheRow3 : rowSumZ 3 =
    162965232735903788059681880617089601229045807787548862477321 := by decide +kernel

private theorem nicheRow4 : rowSumZ 4 =
    240263012254565236231505114936779405270726902827089784322830 := by decide +kernel

private theorem nicheRow5 : rowSumZ 5 =
    8135271455504708705889233641436272496231820289483051847936 := by decide +kernel

private theorem nicheRow6 : rowSumZ 6 =
    48907151599245840266954674339698275590971679490228711932 := by decide +kernel

/-- The sum of the rectangle areas meets the niche threshold. -/
theorem niche_bound_checked : 5000 * nicheSumZ ≤ 3301 * M * M := by
  rewrite [nicheSumZ_fold, foldl_seven_rows, nicheRow0, nicheRow1, nicheRow2,
    nicheRow3, nicheRow4, nicheRow5, nicheRow6]
  norm_num [M]

end MovingSofa.GerverAreaCert

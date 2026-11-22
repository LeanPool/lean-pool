/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.AreaCertificateInputs
import Mathlib.Tactic.NormNum

/-!
# Gerver niche area certificate

The kernel checks two rectangle subtotals for each of the seven roof pieces.
The proofs add the checked subtotals to recover each original row sum.
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

private def rectangleBlock (row start length : ℕ) : ℤ :=
  ((List.range' start length).map (rectAreaZ row)).sum

private theorem rowSumZ_halves (row : ℕ) :
    rowSumZ row = rectangleBlock row 0 32 + rectangleBlock row 32 32 := by
  unfold rowSumZ rectangleBlock
  rw [← List.foldl_map (f := rectAreaZ row) (g := (· + ·)),
    ← List.sum_eq_foldl, List.range_eq_range']
  change ((List.range' 0 (32 + 32)).map (rectAreaZ row)).sum = _
  rw [← List.range'_append_1, List.map_append, List.sum_append]

private theorem nicheRow0First : rectangleBlock 0 0 32 =
    8845072297334670692780361894254852519218486529319646026 := by decide +kernel

private theorem nicheRow0Second : rectangleBlock 0 32 32 =
    10752236294326036672164393239780156419552540129712170180 := by decide +kernel

private theorem nicheRow0 : rowSumZ 0 =
    19597308591660707364944755134035008938771026659031816206 := by
  as_aux_lemma =>
    rw [rowSumZ_halves, nicheRow0First, nicheRow0Second]
    norm_num

private theorem nicheRow1First : rectangleBlock 1 0 32 =
    2708481671659416488318451183130789065356171958140593962722 := by decide +kernel

private theorem nicheRow1Second : rectangleBlock 1 32 32 =
    3148393386337382996932062165253589891900815488753870997235 := by decide +kernel

private theorem nicheRow1 : rowSumZ 1 =
    5856875057996799485250513348384378957256987446894464959957 := by
  as_aux_lemma =>
    rw [rowSumZ_halves, nicheRow1First, nicheRow1Second]
    norm_num

private theorem nicheRow2First : rectangleBlock 2 0 32 =
    191523535334679161804488598779785897537327239225707555957215 := by decide +kernel

private theorem nicheRow2Second : rectangleBlock 2 32 32 =
    51328754338028147159125423090329492584212088714001961310693 := by decide +kernel

private theorem nicheRow2 : rowSumZ 2 =
    242852289672707308963614021870115390121539327939709517267908 := by
  as_aux_lemma =>
    rw [rowSumZ_halves, nicheRow2First, nicheRow2Second]
    norm_num

private theorem nicheRow3First : rectangleBlock 3 0 32 =
    81474276046697370875279695655475247556136298288961395005276 := by decide +kernel

private theorem nicheRow3Second : rectangleBlock 3 32 32 =
    81490956689206417184402184961614353672909509498587467472045 := by decide +kernel

private theorem nicheRow3 : rowSumZ 3 =
    162965232735903788059681880617089601229045807787548862477321 := by
  as_aux_lemma =>
    rw [rowSumZ_halves, nicheRow3First, nicheRow3Second]
    norm_num

private theorem nicheRow4First : rectangleBlock 4 0 32 =
    50079494598729017197543153120492313635811476661823528347987 := by decide +kernel

private theorem nicheRow4Second : rectangleBlock 4 32 32 =
    190183517655836219033961961816287091634915426165266255974843 := by decide +kernel

private theorem nicheRow4 : rowSumZ 4 =
    240263012254565236231505114936779405270726902827089784322830 := by
  as_aux_lemma =>
    rw [rowSumZ_halves, nicheRow4First, nicheRow4Second]
    norm_num

private theorem nicheRow5First : rectangleBlock 5 0 32 =
    3618779434301211958834651458191232116562583828408130271885 := by decide +kernel

private theorem nicheRow5Second : rectangleBlock 5 32 32 =
    4516492021203496747054582183245040379669236461074921576051 := by decide +kernel

private theorem nicheRow5 : rowSumZ 5 =
    8135271455504708705889233641436272496231820289483051847936 := by
  as_aux_lemma =>
    rw [rowSumZ_halves, nicheRow5First, nicheRow5Second]
    norm_num

private theorem nicheRow6First : rectangleBlock 6 0 32 =
    25315253832865482835763120035682201616329557215732924368 := by decide +kernel

private theorem nicheRow6Second : rectangleBlock 6 32 32 =
    23591897766380357431191554304016073974642122274495787564 := by decide +kernel

private theorem nicheRow6 : rowSumZ 6 =
    48907151599245840266954674339698275590971679490228711932 := by
  as_aux_lemma =>
    rw [rowSumZ_halves, nicheRow6First, nicheRow6Second]
    norm_num

/-- The sum of the rectangle areas meets the niche threshold. -/
theorem niche_bound_checked : 5000 * nicheSumZ ≤ 3301 * M * M := by
  rewrite [nicheSumZ_fold, foldl_seven_rows, nicheRow0, nicheRow1, nicheRow2,
    nicheRow3, nicheRow4, nicheRow5, nicheRow6]
  norm_num [M]

end MovingSofa.GerverAreaCert

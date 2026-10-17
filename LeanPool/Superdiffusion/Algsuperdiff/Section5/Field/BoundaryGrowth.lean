/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.LocalizedTailData
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.LocalizedConservativity

/-!
# BoundaryGrowth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Logarithmic active-support constants on exhaustion cubes

The boundary cutoff on `U_m` requires coefficient control on
its full topological support.  That support lies in `B(0,3^m)`.  The stream
field's rough-size and smooth-divergence constants there grow at most linearly
in `m`, i.e. logarithmically in the physical radius.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open DivergenceFormProcess.Decay DivergenceFormProcess.Form
open HCPolySupport HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Linear-in-scale envelope for the rough active-support constant. -/
def streamBoundaryRoughConst (M : ABKModel d)
    (omega : FullSample d M.gamma) : ℝ :=
  2 * streamFieldSmallBallConst M omega

/-- Linear-in-scale envelope for the smooth-divergence active-support
constant. -/
def streamBoundarySmoothDivConst (M : ABKModel d)
    (omega : FullSample d M.gamma) : ℝ :=
  2 * (Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega)

omit [NeZero d] in
theorem streamBoundaryRoughConst_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    0 ≤ streamBoundaryRoughConst M omega := by
  unfold streamBoundaryRoughConst
  exact mul_nonneg (by norm_num) (streamFieldSmallBallConst_nonneg M omega)

omit [NeZero d] in
theorem streamBoundarySmoothDivConst_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    0 ≤ streamBoundarySmoothDivConst M omega := by
  unfold streamBoundarySmoothDivConst
  exact mul_nonneg (by norm_num)
    (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d))
      (streamFieldLargeGradientConst_nonneg M omega))

private theorem streamLogWeight_one_add_triadic_le (m : ℕ) :
    streamLogWeight (1 + (3 : ℝ) ^ m) ≤ 2 * ((m : ℝ) + 1) := by
  have hp : 1 ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have harg : 1 + (3 : ℝ) ^ m ≤ 2 * (3 : ℝ) ^ m := by
    linarith only [hp]
  have hlog := Real.strictMonoOn_log.monotoneOn
    (by positivity : 0 < 1 + (3 : ℝ) ^ m)
    (by positivity : 0 < 2 * (3 : ℝ) ^ m) harg
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    norm_num at h ⊢
    exact h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (pow_pos (by norm_num) m)), Real.log_pow] at hlog
  unfold streamLogWeight
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmul := mul_le_mul_of_nonneg_left hlog3 hm0
  linarith only [hlog, hlog2, hmul]

omit [NeZero d] in
/-- The rough constant on the active cutoff support is at most linear in the
exhaustion index. -/
theorem streamFieldSmallLocalConst_zero_triadic_le (M : ABKModel d)
    (omega : FullSample d M.gamma) (m : ℕ) :
    streamFieldSmallLocalConst M omega 0 ((3 : ℝ) ^ m) ≤
      streamBoundaryRoughConst M omega * ((m : ℝ) + 1) := by
  have hlog := streamLogWeight_one_add_triadic_le m
  have hC := streamFieldSmallBallConst_nonneg M omega
  unfold streamFieldSmallLocalConst streamSplitObservationRadius
    streamBoundaryRoughConst
  simp only [euclideanNorm_zero, add_zero]
  convert mul_le_mul_of_nonneg_left hlog hC using 1
  all_goals first | rfl | ring

omit [NeZero d] in
/-- The smooth-divergence constant on the active cutoff support is at most
linear in the exhaustion index. -/
theorem streamFieldLargeDivLocalConst_zero_triadic_le (M : ABKModel d)
    (omega : FullSample d M.gamma) (m : ℕ) :
    streamFieldLargeDivLocalConst M omega 0 ((3 : ℝ) ^ m) ≤
      streamBoundarySmoothDivConst M omega * ((m : ℝ) + 1) := by
  have hlog := streamLogWeight_one_add_triadic_le m
  have hC : 0 ≤ Real.sqrt d * (d : ℝ) *
      streamFieldLargeGradientConst M omega :=
    mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d))
      (streamFieldLargeGradientConst_nonneg M omega)
  unfold streamFieldLargeDivLocalConst streamSplitObservationRadius
    streamBoundarySmoothDivConst
  simp only [euclideanNorm_zero, add_zero]
  convert mul_le_mul_of_nonneg_left hlog hC using 1
  all_goals first | rfl | ring

end

end Algsuperdiff.Section5.Field

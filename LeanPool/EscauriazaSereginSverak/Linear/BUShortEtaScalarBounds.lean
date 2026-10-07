/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEtaScalarDerivatives

/-!
# Growth bounds for the normal cutoff derivatives

The fixed normal transition and the phase transition give a single
quadratic height bound for all derivatives used by the heat product rule.
-/

public section


open CKN

noncomputable section

namespace ESS

private theorem buShortNormalCutoff_abs_le_one (scale y : ℝ) :
    |buShortNormalCutoff scale y| ≤ 1 := by
  unfold buShortNormalCutoff
  rw [abs_of_nonneg (smoothTransitionProfile.nonneg _)]
  exact smoothTransitionProfile.le_one _

private theorem buShortPhaseFactor_abs_le_one (scale y s : ℝ) :
    |buShortPhaseFactor scale y s| ≤ 1 := by
  unfold buShortPhaseFactor
  rw [abs_of_nonneg (smoothTransitionProfile.nonneg _)]
  exact smoothTransitionProfile.le_one _

/-- The height derivative of the normal cutoff has linear growth on the
active strip. -/
theorem buShortEtaScalar_deriv_height_bound
    {scale y s : ℝ} (hscale : 0 < scale)
    (hy : 2 < y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    |deriv (fun r : ℝ => buShortEtaScalar scale r s) y| ≤
      (16 + 48 * (12 / buShortB scale)) * (1 + y) := by
  let K := 12 / buShortB scale
  have hK : 0 ≤ K := (div_pos (by norm_num) (buShortB_pos hscale)).le
  have hheight : 1 ≤ 1 + y := by linarith only [hy]
  have hfirst :
      |deriv (buShortNormalCutoff scale) y *
        buShortPhaseFactor scale y s| ≤ 16 := by
    rw [abs_mul]
    calc
      _ ≤ (16 : ℝ) * 1 := by
        exact mul_le_mul
          (buShortNormalCutoff_abs_deriv_le scale y)
          (buShortPhaseFactor_abs_le_one scale y s)
          (abs_nonneg _) (by norm_num)
      _ = (16 : ℝ) := by ring
  have hsecond :
      |buShortNormalCutoff scale y *
        deriv (fun r : ℝ => buShortPhaseFactor scale r s) y| ≤
        (48 * K) * (1 + y) := by
    rw [abs_mul]
    calc
      _ ≤ 1 * ((48 * K) * (1 + y)) := by
        gcongr
        · exact buShortNormalCutoff_abs_le_one scale y
        · exact buShortPhaseFactor_deriv_height_bound hscale hy hs hs1
      _ = _ := by ring
  rw [buShortEtaScalar_deriv_height]
  calc
    _ ≤ |deriv (buShortNormalCutoff scale) y *
          buShortPhaseFactor scale y s| +
        |buShortNormalCutoff scale y *
          deriv (fun r : ℝ => buShortPhaseFactor scale r s) y| :=
      abs_add_le _ _
    _ ≤ 16 + (48 * K) * (1 + y) := add_le_add hfirst hsecond
    _ ≤ (16 + 48 * K) * (1 + y) := by
      have h := mul_le_mul_of_nonneg_left hheight
        (by norm_num : (0 : ℝ) ≤ 16)
      nlinarith only [h]

/-- The time derivative of the normal cutoff has quadratic height
growth on the active strip. -/
theorem buShortEtaScalar_deriv_time_bound
    {scale y s : ℝ} (hscale : 0 < scale)
    (hy : 2 < y) (hs : 1 / 2 < s) (hs1 : s ≤ 1) :
    |deriv (fun t : ℝ => buShortEtaScalar scale y t) s| ≤
      (56 * (12 / buShortB scale)) * (1 + y) ^ 2 := by
  rw [buShortEtaScalar_deriv_time, abs_mul]
  calc
    _ ≤ 1 * ((56 * (12 / buShortB scale)) * (1 + y) ^ 2) := by
      gcongr
      · exact buShortNormalCutoff_abs_le_one scale y
      · exact buShortPhaseFactor_deriv_time_bound hscale hy hs hs1
    _ = _ := by ring

/-- The second height derivative of the normal cutoff has quadratic
height growth on the active strip. -/
theorem buShortEtaScalar_deriv_height_twice_bound
    {scale y s C₁ C₂ : ℝ} (hscale : 0 < scale)
    (hy : 2 < y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂) :
    |deriv (fun r : ℝ =>
      deriv (fun q : ℝ => buShortEtaScalar scale q s) r) y| ≤
      (C₁ + 1536 * (12 / buShortB scale) +
        36 * C₂ * (12 / buShortB scale) ^ 2 +
        24 * (12 / buShortB scale)) * (1 + y) ^ 2 := by
  let K := 12 / buShortB scale
  have hK : 0 ≤ K := (div_pos (by norm_num) (buShortB_pos hscale)).le
  have hbase : 1 ≤ 1 + y := by linarith only [hy]
  have hsq : 1 + y ≤ (1 + y) ^ 2 := by nlinarith only [hy]
  have hsq1 : 1 ≤ (1 + y) ^ 2 := hbase.trans hsq
  let A := deriv (deriv (buShortNormalCutoff scale)) y *
    buShortPhaseFactor scale y s
  let B := 2 * deriv (buShortNormalCutoff scale) y *
    deriv (fun r : ℝ => buShortPhaseFactor scale r s) y
  let C := buShortNormalCutoff scale y *
    deriv (fun r : ℝ =>
      deriv (fun q : ℝ => buShortPhaseFactor scale q s) r) y
  have hA : |A| ≤ C₁ * (1 + y) ^ 2 := by
    dsimp [A]
    rw [abs_mul]
    calc
      _ ≤ C₁ * 1 := by
        gcongr
        · exact hN scale y
        · exact buShortPhaseFactor_abs_le_one scale y s
      _ ≤ C₁ * (1 + y) ^ 2 := by gcongr
  have hB : |B| ≤ (1536 * K) * (1 + y) ^ 2 := by
    dsimp [B]
    rw [abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ 2 * 16 * ((48 * K) * (1 + y)) := by
        gcongr
        · exact buShortNormalCutoff_abs_deriv_le scale y
        · exact buShortPhaseFactor_deriv_height_bound hscale hy hs hs1
      _ = (1536 * K) * (1 + y) := by ring
      _ ≤ (1536 * K) * (1 + y) ^ 2 := by gcongr
  have hC : |C| ≤
      (36 * C₂ * K ^ 2 + 24 * K) * (1 + y) ^ 2 := by
    dsimp [C]
    rw [abs_mul]
    calc
      _ ≤ 1 * ((36 * C₂ * K ^ 2 + 24 * K) * (1 + y) ^ 2) := by
        gcongr
        · exact buShortNormalCutoff_abs_le_one scale y
        · exact buShortPhaseFactor_deriv_height_twice_bound
            hscale hy hs hs1 hC₂ hP
      _ = _ := by ring
  rw [buShortEtaScalar_deriv_height_twice scale y s hy hs]
  change |A + B + C| ≤
    (C₁ + 1536 * K + 36 * C₂ * K ^ 2 + 24 * K) * (1 + y) ^ 2
  calc
    _ ≤ |A| + |B| + |C| := by
      have h₁ := abs_add_le (A + B) C
      have h₂ := abs_add_le A B
      linarith only [h₁, h₂]
    _ ≤ C₁ * (1 + y) ^ 2 +
        (1536 * K) * (1 + y) ^ 2 +
        (36 * C₂ * K ^ 2 + 24 * K) * (1 + y) ^ 2 := by
      exact add_le_add (add_le_add hA hB) hC
    _ = _ := by ring

end ESS

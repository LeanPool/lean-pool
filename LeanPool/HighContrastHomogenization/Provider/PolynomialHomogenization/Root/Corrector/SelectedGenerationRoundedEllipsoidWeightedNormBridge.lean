/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.SelectedGenerationRoundedEllipsoidTerminalCubeSolution
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedEllipsoidWeightedNormBridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedFiniteEnergyENNRealBridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector
.SelectedGenerationRoundedEllipsoidWeightedNormBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Weighted norms on a selected rounded generation

The mixed-order recurrence chooses its rounded coordinate matrix after the
analytic constants have been fixed.  The matrix remains uniformly close to
the normalized reference, so the standard rounded-ellipsoid volume and
weighted-norm comparisons hold with the same dimension-only constants.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal Matrix MatrixOrder

noncomputable section


variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem vecDot_matVecMul_smul_one_weighted
    (c : ℝ) (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  have hone : matVecMul (1 : Mat d) x = x := by
    funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  rw [smul_matVecMul, hone, vecDot_smul_right]
  rfl

omit [NeZero d] in
private theorem vecDot_matVecMul_le_of_matrix_le_weighted
    {A B : Mat d} (h : A ≤ B) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x) := by
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hx := hdiff.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hx
  change x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x
  simp only [star_trivial] at hx
  linarith only [hx]

private theorem selectedRoundedReferenceMatrix_inv_le_weighted
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    (geom.referenceMatrix abar hS)⁻¹ ≤
      (100 / 99 : ℝ) • (1 : Mat d) := by
  have hlower := geom.reference_lower abar hS
  have hB : (geom.referenceMatrix abar hS).PosDef :=
    geom.reference_posDef abar hS
  have hscalar : ((99 / 100 : ℝ) • (1 : Mat d)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  have h := inv_le_inv_of_le hscalar hB hlower
  rw [inv_smul_of_isUnit (by norm_num : (99 / 100 : ℝ) ≠ 0)
    (by simp : IsUnit (1 : Mat d).det), inv_one] at h
  norm_num at h ⊢
  exact h

/-- The Euclidean ball of half the physical radius lies in the pullback for
every admissible selected rounded generation. -/
theorem euclideanBall_half_subset_selectedRoundedPullbackEllipsoid
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) (r : ℝ) :
    euclideanBall d (r / 2) ⊆
      selectedRoundedPullbackEllipsoid geom abar r := by
  rw [selectedRoundedPullbackEllipsoid_eq geom abar hS r]
  intro y hy
  have hynorm : vecNormSq y < (r / 2) ^ 2 := by
    simpa only [euclideanBall, euclideanBallAt, sub_zero, Set.mem_ofPred_eq]
      using hy
  have hquad := vecDot_matVecMul_le_of_matrix_le_weighted
    (selectedRoundedReferenceMatrix_inv_le_weighted geom abar hS) y
  rw [vecDot_matVecMul_smul_one_weighted] at hquad
  exact hquad.trans_lt (by nlinarith only [hynorm]) |>.le

/-- The selected pullback ellipsoid lies in the Euclidean ball of twice the
physical radius. -/
theorem selectedRoundedPullbackEllipsoid_subset_euclideanBall_two_mul
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r : ℝ} (hr : 0 < r) :
    selectedRoundedPullbackEllipsoid geom abar r ⊆
      euclideanBall d (2 * r) := by
  rw [selectedRoundedPullbackEllipsoid_eq geom abar hS r]
  intro y hy
  have hlower := (geom.reference_elliptic abar hS).2.2.2 y
  have hlower' :
      (100 / 101 : ℝ) * vecNormSq y ≤
        vecDot y (matVecMul (geom.referenceMatrix abar hS)⁻¹ y) := by
    norm_num at hlower ⊢
    exact hlower
  change vecNormSq (y - 0) < (2 * r) ^ 2
  rw [sub_zero]
  calc
    vecNormSq y = (101 / 100 : ℝ) *
        ((100 / 101 : ℝ) * vecNormSq y) := by ring
    _ ≤ (101 / 100 : ℝ) *
        vecDot y (matVecMul (geom.referenceMatrix abar hS)⁻¹ y) :=
      mul_le_mul_of_nonneg_left hlower' (by norm_num)
    _ ≤ (101 / 100 : ℝ) * r ^ 2 :=
      mul_le_mul_of_nonneg_left hy (by norm_num)
    _ < (2 * r) ^ 2 := by nlinarith only [sq_pos_of_pos hr]

/-- The selected pullback lies in the canonical dimension-free outer cube. -/
theorem selectedRoundedPullbackEllipsoid_subset_outerCube
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r : ℝ} (hr : 0 < r) :
    selectedRoundedPullbackEllipsoid geom abar r ⊆
      openCubeSet (originCube d (roundedEllipsoidOuterGeneration r hr)) := by
  have hball :=
    selectedRoundedPullbackEllipsoid_subset_euclideanBall_two_mul
      geom abar hS hr
  have hcube :=
    euclideanBall_subset_openCubeSet_originCube_outerTriadicGeneration
      (d := d) (r := 2 * r) (by positivity)
  simpa only [roundedEllipsoidOuterGeneration,
    show 2 * (2 * r) = 4 * r by ring] using hball.trans hcube

/-- The selected rounded pullback is monotone in its positive radius. -/
theorem selectedRoundedPullbackEllipsoid_mono
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    selectedRoundedPullbackEllipsoid geom abar r ⊆
      selectedRoundedPullbackEllipsoid geom abar R := by
  rw [selectedRoundedPullbackEllipsoid_eq geom abar hS r,
    selectedRoundedPullbackEllipsoid_eq geom abar hS R]
  intro y hy
  exact hy.trans (pow_le_pow_left₀ hr.le hrR 2)

/-- A positive-radius selected pullback ellipsoid has positive volume. -/
theorem volume_selectedRoundedPullbackEllipsoid_ne_zero
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r : ℝ} (hr : 0 < r) :
    volume (selectedRoundedPullbackEllipsoid geom abar r) ≠ 0 := by
  have hballPos : 0 < volume (euclideanBall d (r / 2)) :=
    IsOpen.measure_pos volume (isOpen_euclideanBall d (r / 2))
      (euclideanBall_nonempty (0 : Vec d) (by positivity))
  have hmono : volume (euclideanBall d (r / 2)) ≤
      volume (selectedRoundedPullbackEllipsoid geom abar r) :=
    measure_mono
      (euclideanBall_half_subset_selectedRoundedPullbackEllipsoid
        geom abar hS r)
  exact ne_of_gt (hballPos.trans_le hmono)

/-- A positive-radius selected pullback ellipsoid has finite volume. -/
theorem volume_selectedRoundedPullbackEllipsoid_ne_top
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r : ℝ} (hr : 0 < r) :
    volume (selectedRoundedPullbackEllipsoid geom abar r) ≠ ⊤ := by
  have hmono : volume (selectedRoundedPullbackEllipsoid geom abar r) ≤
      volume (openCubeSet
        (originCube d (roundedEllipsoidOuterGeneration r hr))) :=
    measure_mono
      (selectedRoundedPullbackEllipsoid_subset_outerCube geom abar hS hr)
  exact (hmono.trans_lt
    (volume_openCubeSet_lt_top
      (originCube d (roundedEllipsoidOuterGeneration r hr)))).ne

/-- The canonical outer cube has a dimension-only real volume ratio over a
selected pullback ellipsoid. -/
theorem outerCube_volume_ratio_lt_selectedRoundedPullbackEllipsoid
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r : ℝ} (hr : 0 < r) :
    (volume (openCubeSet
        (originCube d (roundedEllipsoidOuterGeneration r hr)))).toReal /
        (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal <
      (12 * Real.sqrt d) ^ d := by
  let j : ℤ := roundedEllipsoidOuterGeneration r hr
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hUtop :=
    volume_selectedRoundedPullbackEllipsoid_ne_top geom abar hS hr
  have hballMono : volume (euclideanBall d (r / 2)) ≤
      volume (selectedRoundedPullbackEllipsoid geom abar r) :=
    measure_mono
      (euclideanBall_half_subset_selectedRoundedPullbackEllipsoid
        geom abar hS r)
  have hballReal := ENNReal.toReal_mono hUtop hballMono
  have hballLower :=
    two_mul_div_sqrt_pow_le_volume_euclideanBall_toReal
      (d := d) (show 0 < r / 2 by positivity)
  have hdenLower :
      (r / Real.sqrt d) ^ d ≤
        (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal := by
    have heq : 2 * ((r / 2) / Real.sqrt d) = r / Real.sqrt d := by ring
    rw [heq] at hballLower
    exact hballLower.trans hballReal
  have hdenPos :
      0 < (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal :=
    (pow_pos (div_pos hr hsqrt) d).trans_le hdenLower
  have hscale : (3 : ℝ) ^ j < 12 * r := by
    have h := outerTriadicGeneration_scale_lt_three_mul
      (show 0 < 4 * r by positivity)
    change (3 : ℝ) ^ j < 3 * (4 * r) at h
    calc
      (3 : ℝ) ^ j < 3 * (4 * r) := h
      _ = 12 * r := by ring
  have hnum :
      (volume (openCubeSet (originCube d j))).toReal < (12 * r) ^ d := by
    rw [volume_openCubeSet_toReal, cubeVolume_eq_scaleFactor_pow,
      cubeScaleFactor_originCube]
    exact pow_lt_pow_left₀ hscale (by positivity) (NeZero.ne d)
  calc
    (volume (openCubeSet (originCube d j))).toReal /
          (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal <
        (12 * r) ^ d /
          (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal :=
      div_lt_div_of_pos_right hnum hdenPos
    _ ≤ (12 * r) ^ d / (r / Real.sqrt d) ^ d :=
      div_le_div_of_nonneg_left (by positivity)
        (pow_pos (div_pos hr hsqrt) d) hdenLower
    _ = (12 * Real.sqrt d) ^ d := by
      rw [← div_pow]
      congr 1
      field_simp

/-- ENNReal form of the selected outer-cube volume-ratio bound. -/
theorem outerCube_volume_ratio_le_selectedRoundedPullbackEllipsoid_ofReal
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r : ℝ} (hr : 0 < r) :
    volume (openCubeSet
        (originCube d (roundedEllipsoidOuterGeneration r hr))) /
        volume (selectedRoundedPullbackEllipsoid geom abar r) ≤
      ENNReal.ofReal ((12 * Real.sqrt d) ^ d) := by
  have hcubeTop := volume_openCubeSet_lt_top
    (originCube d (roundedEllipsoidOuterGeneration r hr)) |>.ne
  have hUzero :=
    volume_selectedRoundedPullbackEllipsoid_ne_zero geom abar hS hr
  have hratioTop :
      volume (openCubeSet
          (originCube d (roundedEllipsoidOuterGeneration r hr))) /
          volume (selectedRoundedPullbackEllipsoid geom abar r) ≠ ⊤ :=
    ENNReal.div_ne_top hcubeTop hUzero
  apply (ENNReal.le_ofReal_iff_toReal_le hratioTop (by positivity)).2
  rw [ENNReal.toReal_div]
  exact le_of_lt
    (outerCube_volume_ratio_lt_selectedRoundedPullbackEllipsoid
      geom abar hS hr)

/-- The selected pullback at the terminal radius has a dimension-only real
volume ratio over the interior terminal cube. -/
theorem selectedRoundedPullbackEllipsoid_volume_ratio_lt_terminalCube
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {R : ℝ} (hR : 0 < R) :
    (volume (selectedRoundedPullbackEllipsoid geom abar R)).toReal /
        (volume (openCubeSet (originCube d
          (roundedEllipsoidTerminalGeneration (d := d) R hR)))).toReal <
      (1200 * (d : ℝ)) ^ d := by
  let j : ℤ := roundedEllipsoidOuterGeneration R hR
  let m : ℤ := roundedEllipsoidTerminalGeneration (d := d) R hR
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have houterMono :
      volume (selectedRoundedPullbackEllipsoid geom abar R) ≤
        volume (openCubeSet (originCube d j)) :=
    measure_mono
      (selectedRoundedPullbackEllipsoid_subset_outerCube geom abar hS hR)
  have houterTop := volume_openCubeSet_lt_top (originCube d j) |>.ne
  have houterReal := ENNReal.toReal_mono houterTop houterMono
  have houterScale : (3 : ℝ) ^ j < 12 * R := by
    have h := outerTriadicGeneration_scale_lt_three_mul
      (show 0 < 4 * R by positivity)
    change (3 : ℝ) ^ j < 3 * (4 * R) at h
    calc
      (3 : ℝ) ^ j < 3 * (4 * R) := h
      _ = 12 * R := by ring
  have houterVolume :
      (volume (openCubeSet (originCube d j))).toReal < (12 * R) ^ d := by
    rw [volume_openCubeSet_toReal, cubeVolume_eq_scaleFactor_pow,
      cubeScaleFactor_originCube]
    exact pow_lt_pow_left₀ houterScale (by positivity) (NeZero.ne d)
  have hnum :
      (volume (selectedRoundedPullbackEllipsoid geom abar R)).toReal <
        (12 * R) ^ d := houterReal.trans_lt houterVolume
  have hinnerScale : R / (100 * (d : ℝ)) ≤ (3 : ℝ) ^ m := by
    simpa only [m, roundedEllipsoidTerminalGeneration] using
      le_outerTriadicGeneration_scale
        (show 0 < R / (100 * (d : ℝ)) by positivity)
  have hdenLower :
      (R / (100 * (d : ℝ))) ^ d ≤
        (volume (openCubeSet (originCube d m))).toReal := by
    rw [volume_openCubeSet_toReal, cubeVolume_eq_scaleFactor_pow,
      cubeScaleFactor_originCube]
    exact pow_le_pow_left₀ (by positivity) hinnerScale d
  have hdenPos :
      0 < (volume (openCubeSet (originCube d m))).toReal :=
    (pow_pos (div_pos hR (by positivity)) d).trans_le hdenLower
  calc
    (volume (selectedRoundedPullbackEllipsoid geom abar R)).toReal /
          (volume (openCubeSet (originCube d m))).toReal <
        (12 * R) ^ d /
          (volume (openCubeSet (originCube d m))).toReal :=
      div_lt_div_of_pos_right hnum hdenPos
    _ ≤ (12 * R) ^ d / (R / (100 * (d : ℝ))) ^ d :=
      div_le_div_of_nonneg_left (by positivity)
        (pow_pos (div_pos hR (by positivity)) d) hdenLower
    _ = (1200 * (d : ℝ)) ^ d := by
      rw [← div_pow]
      congr 1
      field_simp
      norm_num

/-- ENNReal form of the selected terminal volume-ratio bound. -/
theorem selectedRoundedPullbackEllipsoid_volume_ratio_le_terminalCube_ofReal
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {R : ℝ} (hR : 0 < R) :
    volume (selectedRoundedPullbackEllipsoid geom abar R) /
        volume (openCubeSet (originCube d
          (roundedEllipsoidTerminalGeneration (d := d) R hR))) ≤
      ENNReal.ofReal ((1200 * (d : ℝ)) ^ d) := by
  have hUtop :=
    volume_selectedRoundedPullbackEllipsoid_ne_top geom abar hS hR
  have hcubeZero : volume (openCubeSet (originCube d
      (roundedEllipsoidTerminalGeneration (d := d) R hR))) ≠ 0 := by
    have hreal : (volume (openCubeSet (originCube d
        (roundedEllipsoidTerminalGeneration (d := d) R hR)))).toReal
        ≠ 0 := by
      rw [volume_openCubeSet_toReal]
      exact (cubeVolume_pos _).ne'
    exact (ENNReal.toReal_ne_zero.mp hreal).1
  have hratioTop :
      volume (selectedRoundedPullbackEllipsoid geom abar R) /
        volume (openCubeSet (originCube d
          (roundedEllipsoidTerminalGeneration (d := d) R hR))) ≠ ⊤ :=
    ENNReal.div_ne_top hUtop hcubeZero
  apply (ENNReal.le_ofReal_iff_toReal_le hratioTop (by positivity)).2
  rw [ENNReal.toReal_div]
  exact le_of_lt
    (selectedRoundedPullbackEllipsoid_volume_ratio_lt_terminalCube
      geom abar hS hR)

/-- Near the terminal radius, selected pullback volumes have a
dimension-only ratio. -/
theorem selectedRoundedPullbackEllipsoid_volume_ratio_lt_of_near_terminal
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hnear : R < 400 * (d : ℝ) * r) :
    (volume (selectedRoundedPullbackEllipsoid geom abar R)).toReal /
        (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal <
      (4800 * (d : ℝ) * Real.sqrt d) ^ d := by
  let j : ℤ := roundedEllipsoidOuterGeneration R hR
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have houterMono :
      volume (selectedRoundedPullbackEllipsoid geom abar R) ≤
        volume (openCubeSet (originCube d j)) :=
    measure_mono
      (selectedRoundedPullbackEllipsoid_subset_outerCube geom abar hS hR)
  have houterTop := volume_openCubeSet_lt_top (originCube d j) |>.ne
  have houterReal := ENNReal.toReal_mono houterTop houterMono
  have houterScale : (3 : ℝ) ^ j < 12 * R := by
    have h := outerTriadicGeneration_scale_lt_three_mul
      (show 0 < 4 * R by positivity)
    change (3 : ℝ) ^ j < 3 * (4 * R) at h
    calc
      (3 : ℝ) ^ j < 3 * (4 * R) := h
      _ = 12 * R := by ring
  have houterVolume :
      (volume (openCubeSet (originCube d j))).toReal < (12 * R) ^ d := by
    rw [volume_openCubeSet_toReal, cubeVolume_eq_scaleFactor_pow,
      cubeScaleFactor_originCube]
    exact pow_lt_pow_left₀ houterScale (by positivity) (NeZero.ne d)
  have hnum :
      (volume (selectedRoundedPullbackEllipsoid geom abar R)).toReal <
        (12 * R) ^ d := houterReal.trans_lt houterVolume
  have hsmallMono : volume (euclideanBall d (r / 2)) ≤
      volume (selectedRoundedPullbackEllipsoid geom abar r) :=
    measure_mono
      (euclideanBall_half_subset_selectedRoundedPullbackEllipsoid
        geom abar hS r)
  have hsmallTop :=
    volume_selectedRoundedPullbackEllipsoid_ne_top geom abar hS hr
  have hsmallReal := ENNReal.toReal_mono hsmallTop hsmallMono
  have hballLower :=
    two_mul_div_sqrt_pow_le_volume_euclideanBall_toReal
      (d := d) (show 0 < r / 2 by positivity)
  have hdenLower : (r / Real.sqrt d) ^ d ≤
      (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal := by
    have heq : 2 * ((r / 2) / Real.sqrt d) = r / Real.sqrt d := by ring
    rw [heq] at hballLower
    exact hballLower.trans hsmallReal
  have hdenPos :
      0 < (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal :=
    (pow_pos (div_pos hr hsqrt) d).trans_le hdenLower
  have hbase : 12 * R * Real.sqrt d / r <
      4800 * (d : ℝ) * Real.sqrt d := by
    apply (div_lt_iff₀ hr).2
    calc
      12 * R * Real.sqrt d < 12 * (400 * (d : ℝ) * r) * Real.sqrt d :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hnear (by norm_num)) hsqrt
      _ = (4800 * (d : ℝ) * Real.sqrt d) * r := by ring
  calc
    (volume (selectedRoundedPullbackEllipsoid geom abar R)).toReal /
          (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal <
        (12 * R) ^ d /
          (volume (selectedRoundedPullbackEllipsoid geom abar r)).toReal :=
      div_lt_div_of_pos_right hnum hdenPos
    _ ≤ (12 * R) ^ d / (r / Real.sqrt d) ^ d :=
      div_le_div_of_nonneg_left (by positivity)
        (pow_pos (div_pos hr hsqrt) d) hdenLower
    _ = (12 * R * Real.sqrt d / r) ^ d := by
      rw [← div_pow]
      congr 1
      field_simp
    _ < (4800 * (d : ℝ) * Real.sqrt d) ^ d :=
      pow_lt_pow_left₀ hbase (by positivity) (NeZero.ne d)

/-- ENNReal form of the selected near-terminal volume-ratio bound. -/
theorem selectedRoundedPullbackEllipsoid_volume_ratio_le_of_near_terminal_ofReal
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hnear : R < 400 * (d : ℝ) * r) :
    volume (selectedRoundedPullbackEllipsoid geom abar R) /
        volume (selectedRoundedPullbackEllipsoid geom abar r) ≤
      ENNReal.ofReal ((4800 * (d : ℝ) * Real.sqrt d) ^ d) := by
  have hRtop :=
    volume_selectedRoundedPullbackEllipsoid_ne_top geom abar hS hR
  have hrzero :=
    volume_selectedRoundedPullbackEllipsoid_ne_zero geom abar hS hr
  have hratioTop :
      volume (selectedRoundedPullbackEllipsoid geom abar R) /
        volume (selectedRoundedPullbackEllipsoid geom abar r) ≠ ⊤ :=
    ENNReal.div_ne_top hRtop hrzero
  apply (ENNReal.le_ofReal_iff_toReal_le hratioTop (by positivity)).2
  rw [ENNReal.toReal_div]
  exact le_of_lt
    (selectedRoundedPullbackEllipsoid_volume_ratio_lt_of_near_terminal
      geom abar hS hr hR hnear)

/-- Weighted energy on a selected pullback is controlled by its canonical
outer origin cube. -/
theorem weightedGradNorm_selectedRoundedPullbackEllipsoid_le_outerCube
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r : ℝ} (hr : 0 < r) (b : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm b (selectedRoundedPullbackEllipsoid geom abar r) F ≤
      (ENNReal.ofReal ((12 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
        weightedGradNorm b
          (openCubeSet
            (originCube d (roundedEllipsoidOuterGeneration r hr))) F := by
  let Q : TriadicCube d :=
    originCube d (roundedEllipsoidOuterGeneration r hr)
  have hrestrict := weightedGradNorm_mono_set_le_volumeRatio
    (selectedRoundedPullbackEllipsoid_subset_outerCube geom abar hS hr)
    (volume_selectedRoundedPullbackEllipsoid_ne_zero geom abar hS hr)
    (volume_selectedRoundedPullbackEllipsoid_ne_top geom abar hS hr)
    (volume_openCubeSet_ne_zero Q)
    (volume_openCubeSet_lt_top Q).ne b F
  have hratio :=
    outerCube_volume_ratio_le_selectedRoundedPullbackEllipsoid_ofReal
      geom abar hS hr
  have hfactor := ENNReal.rpow_le_rpow hratio
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    weightedGradNorm b (selectedRoundedPullbackEllipsoid geom abar r) F ≤
        (volume (openCubeSet Q) /
          volume (selectedRoundedPullbackEllipsoid geom abar r)) ^
            (1 / 2 : ℝ) * weightedGradNorm b (openCubeSet Q) F :=
      hrestrict
    _ ≤ (ENNReal.ofReal ((12 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
          weightedGradNorm b (openCubeSet Q) F :=
      mul_le_mul_left hfactor _

/-- Weighted energy on the terminal cube is controlled by the selected
pullback at the terminal radius. -/
theorem weightedGradNorm_terminalCube_le_selectedRoundedPullbackEllipsoid
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {R : ℝ} (hR : 0 < R) (b : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm b
        (openCubeSet (originCube d
          (roundedEllipsoidTerminalGeneration (d := d) R hR))) F ≤
      (ENNReal.ofReal ((1200 * (d : ℝ)) ^ d)) ^ (1 / 2 : ℝ) *
        weightedGradNorm b
          (selectedRoundedPullbackEllipsoid geom abar R) F := by
  let Q : TriadicCube d := originCube d
    (roundedEllipsoidTerminalGeneration (d := d) R hR)
  have hrestrict := weightedGradNorm_mono_set_le_volumeRatio
    (openCube_terminalGeneration_subset_selectedRoundedPullbackEllipsoid
      geom abar hS hR)
    (volume_openCubeSet_ne_zero Q)
    (volume_openCubeSet_lt_top Q).ne
    (volume_selectedRoundedPullbackEllipsoid_ne_zero geom abar hS hR)
    (volume_selectedRoundedPullbackEllipsoid_ne_top geom abar hS hR) b F
  have hratio :=
    selectedRoundedPullbackEllipsoid_volume_ratio_le_terminalCube_ofReal
      geom abar hS hR
  have hfactor := ENNReal.rpow_le_rpow hratio
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    weightedGradNorm b (openCubeSet Q) F ≤
        (volume (selectedRoundedPullbackEllipsoid geom abar R) /
          volume (openCubeSet Q)) ^ (1 / 2 : ℝ) *
            weightedGradNorm b
              (selectedRoundedPullbackEllipsoid geom abar R) F := hrestrict
    _ ≤ (ENNReal.ofReal ((1200 * (d : ℝ)) ^ d)) ^ (1 / 2 : ℝ) *
          weightedGradNorm b
            (selectedRoundedPullbackEllipsoid geom abar R) F :=
      mul_le_mul_left hfactor _

/-- The selected near-terminal branch closes directly by normalized-domain
restriction. -/
theorem weightedGradNorm_selectedRoundedPullbackEllipsoid_le_of_near_terminal
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hnear : R < 400 * (d : ℝ) * r)
    (b : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm b (selectedRoundedPullbackEllipsoid geom abar r) F ≤
      (ENNReal.ofReal ((4800 * (d : ℝ) * Real.sqrt d) ^ d)) ^
          (1 / 2 : ℝ) *
        weightedGradNorm b
          (selectedRoundedPullbackEllipsoid geom abar R) F := by
  have hrestrict := weightedGradNorm_mono_set_le_volumeRatio
    (selectedRoundedPullbackEllipsoid_mono geom abar hS hr hrR)
    (volume_selectedRoundedPullbackEllipsoid_ne_zero geom abar hS hr)
    (volume_selectedRoundedPullbackEllipsoid_ne_top geom abar hS hr)
    (volume_selectedRoundedPullbackEllipsoid_ne_zero geom abar hS hR)
    (volume_selectedRoundedPullbackEllipsoid_ne_top geom abar hS hR) b F
  have hratio :=
    selectedRoundedPullbackEllipsoid_volume_ratio_le_of_near_terminal_ofReal
      geom abar hS hr hR hnear
  have hfactor := ENNReal.rpow_le_rpow hratio
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    weightedGradNorm b (selectedRoundedPullbackEllipsoid geom abar r) F ≤
        (volume (selectedRoundedPullbackEllipsoid geom abar R) /
          volume (selectedRoundedPullbackEllipsoid geom abar r)) ^
            (1 / 2 : ℝ) *
          weightedGradNorm b
            (selectedRoundedPullbackEllipsoid geom abar R) F := hrestrict
    _ ≤ (ENNReal.ofReal ((4800 * (d : ℝ) * Real.sqrt d) ^ d)) ^
          (1 / 2 : ℝ) *
        weightedGradNorm b
          (selectedRoundedPullbackEllipsoid geom abar R) F :=
      mul_le_mul_left hfactor _

omit [NeZero d] in
/-- A finite centered-energy estimate lifts to the selected-generation
coefficient by the application's almost-everywhere identification. -/
theorem weightedGradNorm_roundedCenteredCoefficientAtGeneration_le_of_finiteEnergy
    (l : ℤ) (hl : (kZero d : ℤ) ≤ l)
    (aPhysical : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef)
    (aRounded : Book.Ch03.CoeffFamily d)
    (hRoundedAE : ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =ᵐ[volume]
        roundedCenteredCoefficientAtGeneration l hl abar hS (⇑aPhysical.1))
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) aRounded)
    (h : ℤ) (hhm : h ≤ m) (H : ℝ) (hH : 0 ≤ H)
    (henergy : finiteCenteredCubeSolutionEnergy aRounded m u h ≤
      H * finiteCenteredCubeSolutionEnergy aRounded m u m) :
    weightedGradNorm
        (roundedCenteredCoefficientAtGeneration
          l hl abar hS (⇑aPhysical.1))
        (openCubeSet (originCube d h)) u.toH1.grad ≤
      ENNReal.ofReal H *
        weightedGradNorm
          (roundedCenteredCoefficientAtGeneration
            l hl abar hS (⇑aPhysical.1))
          (openCubeSet (originCube d m)) u.toH1.grad := by
  have hcoeffH :
      (aRounded.coeffOn (originCube d h)).toCoeffField =ᵐ[
        volumeMeasureOn (openCubeSet (originCube d h))]
          roundedCenteredCoefficientAtGeneration
            l hl abar hS (⇑aPhysical.1) :=
    ae_restrict_of_ae (hRoundedAE (originCube d h))
  have hcoeffM :
      (aRounded.coeffOn (originCube d m)).toCoeffField =ᵐ[
        volumeMeasureOn (openCubeSet (originCube d m))]
          roundedCenteredCoefficientAtGeneration
            l hl abar hS (⇑aPhysical.1) :=
    ae_restrict_of_ae (hRoundedAE (originCube d m))
  have hinner := weightedGradNorm_eq_ofReal_finiteCenteredCubeSolutionEnergy
    aRounded m u h hhm
  have hterminal :=
    weightedGradNorm_eq_ofReal_finiteCenteredCubeSolutionEnergy
      aRounded m u m le_rfl
  have hlift := ENNReal.ofReal_le_ofReal henergy
  rw [ENNReal.ofReal_mul hH] at hlift
  calc
    weightedGradNorm
        (roundedCenteredCoefficientAtGeneration
          l hl abar hS (⇑aPhysical.1))
        (openCubeSet (originCube d h)) u.toH1.grad =
        weightedGradNorm
          (aRounded.coeffOn (originCube d h)).toCoeffField
          (openCubeSet (originCube d h)) u.toH1.grad :=
      (weightedGradNorm_congr_coeff_ae_on u.toH1.grad hcoeffH).symm
    _ = ENNReal.ofReal
        (finiteCenteredCubeSolutionEnergy aRounded m u h) := hinner
    _ ≤ ENNReal.ofReal H * ENNReal.ofReal
        (finiteCenteredCubeSolutionEnergy aRounded m u m) := hlift
    _ = ENNReal.ofReal H * weightedGradNorm
        (aRounded.coeffOn (originCube d m)).toCoeffField
        (openCubeSet (originCube d m)) u.toH1.grad := by rw [hterminal]
    _ = ENNReal.ofReal H * weightedGradNorm
        (roundedCenteredCoefficientAtGeneration
          l hl abar hS (⇑aPhysical.1))
        (openCubeSet (originCube d m)) u.toH1.grad := by
      rw [weightedGradNorm_congr_coeff_ae_on u.toH1.grad hcoeffM]

/-- The normalized skew-centered physical weighted norm is exactly the norm
of its selected-generation coefficient and gradient pullback. -/
theorem weightedGradNorm_selectedRoundedCenteredPullback
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} (hU : MeasurableSet U)
    (a : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm
        (fun x ↦ specBound ((symmPart abar)⁻¹) •
          (a x - skewPart abar)) U F =
      weightedGradNorm
        (roundedCenteredCoefficientAtGeneration
          geom.generation geom.admissible abar hS a)
        (matImage (geom.grid (symmPart abar))⁻¹ U)
        (fun y ↦ matVecMul (geom.grid (symmPart abar))
          (F (matVecMul (geom.grid (symmPart abar)) y))) := by
  let Q : Mat d := geom.grid (symmPart abar)
  let b : CoeffField d := fun x ↦
    specBound ((symmPart abar)⁻¹) • (a x - skewPart abar)
  have hQ : IsUnit Q.det := geom.grid_det_isUnit hS
  have hV : MeasurableSet (matImage Q⁻¹ U) :=
    measurableSet_affinePullback hQ hU
  have hnorm := weightedGradNorm_matImage hQ hV b F
  rw [matImage_matImage_inv hQ] at hnorm
  have htranspose : matTranspose Q = Q := geom.grid_transpose hS
  simpa only [Q, b,
    roundedCenteredCoefficientAtGeneration, htranspose] using! hnorm

end

end Root
end HighContrast
end HCPolySupport

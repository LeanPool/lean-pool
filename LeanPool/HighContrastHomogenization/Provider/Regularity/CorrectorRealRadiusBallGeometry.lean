/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusGeometry
public import LeanPool.HighContrastHomogenization.Analytic.AntiVacuityInstances

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorRealRadiusBallGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Euclidean-ball geometry at a real radius

The frozen Liouville class is normalized on Euclidean balls, whereas the
corrector estimates are normalized on centered triadic cubes.  This module
provides both inclusions and a dimension-only volume-ratio bound.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

private theorem coord_sq_le_vecNormSq_ballGeometry
    {d : ℕ} (x : Vec d) (i : Fin d) :
    x i ^ 2 ≤ vecNormSq x := by
  unfold vecNormSq vecDot
  simpa only [pow_two] using
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- A Euclidean ball of radius `r` lies in the centered open cube of side
length `2r`. -/
theorem euclideanBall_subset_centeredOpenCube_two_mul
    {d : ℕ} {r : ℝ} (hr : 0 < r) :
    euclideanBall d r ⊆ centeredOpenCube d (2 * r) := by
  intro x hx
  have hxnorm : vecNormSq x < r ^ 2 := by
    simpa only [euclideanBall, euclideanBallAt, sub_zero, Set.mem_ofPred_eq] using hx
  have hxcoord : ∀ i : Fin d, -r < x i ∧ x i < r := by
    intro i
    have hi : x i ^ 2 < r ^ 2 :=
      (coord_sq_le_vecNormSq_ballGeometry x i).trans_lt hxnorm
    exact abs_lt_of_sq_lt_sq' hi hr.le
  rw [centeredOpenCube, axisCube]
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo]
  intro i
  rcases hxcoord i with ⟨hlo, hhi⟩
  constructor <;> linarith only [hlo, hhi]

/-- The centered sup-norm cube with half-side `r / √d` lies in the
Euclidean ball of radius `r`. -/
theorem centeredOpenCube_two_mul_div_sqrt_subset_euclideanBall
    {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r) :
    centeredOpenCube d (2 * (r / Real.sqrt d)) ⊆ euclideanBall d r := by
  have hd : 0 < d := NeZero.pos d
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hrho : 0 < r / Real.sqrt d := div_pos hr hsqrt
  intro x hx
  have hxraw : ∀ i : Fin d,
      -(2 * (r / Real.sqrt d)) / 2 < x i ∧
        x i < -(2 * (r / Real.sqrt d)) / 2 + 2 * (r / Real.sqrt d) := by
    simpa only [centeredOpenCube, axisCube, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Ioo] using hx
  have hxcoord : ∀ i : Fin d, ‖x i‖ < r / Real.sqrt d := by
    intro i
    rw [Real.norm_eq_abs, abs_lt]
    rcases hxraw i with ⟨hlo, hhi⟩
    constructor <;> linarith only [hlo, hhi]
  have hnorm : ‖x‖ < r / Real.sqrt d :=
    (pi_norm_lt_iff hrho).2 hxcoord
  have hmetric : x ∈ Metric.ball (0 : Vec d) (r / Real.sqrt d) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hnorm
  exact metricBall_subset_euclideanBallAt hd (0 : Vec d) hr hmetric

/-- The Euclidean ball is enclosed by the canonical origin-centered triadic
cube chosen from side length `2r`. -/
theorem euclideanBall_subset_openCubeSet_originCube_outerTriadicGeneration
    {d : ℕ} {r : ℝ} (hr : 0 < r) :
    euclideanBall d r ⊆
      openCubeSet (originCube d (outerTriadicGeneration (2 * r) (by positivity))) :=
  (euclideanBall_subset_centeredOpenCube_two_mul hr).trans
    (centeredOpenCube_subset_openCubeSet_originCube_outerTriadicGeneration
      (by positivity : 0 < 2 * r))

/-- The explicit inner centered cube gives a positive dimension-only lower
bound for the real volume of a Euclidean ball. -/
theorem two_mul_div_sqrt_pow_le_volume_euclideanBall_toReal
    {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r) :
    (2 * (r / Real.sqrt d)) ^ d ≤ (volume (euclideanBall d r)).toReal := by
  have hside : 0 < 2 * (r / Real.sqrt d) := by
    have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
    positivity
  have hmono :
      volume (centeredOpenCube d (2 * (r / Real.sqrt d))) ≤
        volume (euclideanBall d r) :=
    measure_mono (centeredOpenCube_two_mul_div_sqrt_subset_euclideanBall hr)
  have htop : volume (euclideanBall d r) ≠ ⊤ :=
    (isOpenBoundedConvexDomain_euclideanBallAt (0 : Vec d) hr).volume_lt_top.ne
  have hreal := ENNReal.toReal_mono htop hmono
  rw [volume_centeredOpenCube_toReal hside] at hreal
  exact hreal

/-- The canonical enclosing triadic cube has at most a dimension-only real
volume ratio over the Euclidean ball. -/
theorem outerTriadicGeneration_volume_ratio_lt_euclideanBall
    {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r) :
    (volume (openCubeSet
        (originCube d (outerTriadicGeneration (2 * r) (by positivity))))).toReal /
        (volume (euclideanBall d r)).toReal <
      (3 * Real.sqrt d) ^ d := by
  let m : ℤ := outerTriadicGeneration (2 * r) (by positivity)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hinnerpos : 0 < (2 * (r / Real.sqrt d)) ^ d := by positivity
  have hdenlower :=
    two_mul_div_sqrt_pow_le_volume_euclideanBall_toReal (d := d) hr
  have hdenpos : 0 < (volume (euclideanBall d r)).toReal :=
    hinnerpos.trans_le hdenlower
  have hscale : (3 : ℝ) ^ m < 6 * r := by
    have h := outerTriadicGeneration_scale_lt_three_mul
      (by positivity : 0 < 2 * r)
    have h' : (3 : ℝ) ^ m < 3 * (2 * r) := by
      simpa only [m] using h
    linarith only [h']
  have hscale_nonneg : 0 ≤ (3 : ℝ) ^ m :=
    (zpow_pos (by norm_num : (0 : ℝ) < 3) m).le
  have hnum :
      (volume (openCubeSet (originCube d m))).toReal < (6 * r) ^ d := by
    rw [volume_openCubeSet_toReal, cubeVolume_eq_scaleFactor_pow,
      cubeScaleFactor_originCube]
    exact pow_lt_pow_left₀ hscale hscale_nonneg (NeZero.ne d)
  have hA : 0 ≤ (6 * r) ^ d := by positivity
  calc
    (volume (openCubeSet (originCube d m))).toReal /
          (volume (euclideanBall d r)).toReal <
        (6 * r) ^ d / (volume (euclideanBall d r)).toReal :=
      div_lt_div_of_pos_right hnum hdenpos
    _ ≤ (6 * r) ^ d / (2 * (r / Real.sqrt d)) ^ d :=
      div_le_div_of_nonneg_left hA hinnerpos hdenlower
    _ = (3 * Real.sqrt d) ^ d := by
      rw [← div_pow]
      congr 1
      field_simp
      ring

end

end HighContrast
end HCPolySupport

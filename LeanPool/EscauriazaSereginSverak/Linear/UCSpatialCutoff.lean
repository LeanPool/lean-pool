/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCTimeCutoff
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Cutoff

/-!
# Spatial cutoff for Gaussian unique continuation

The canonical smooth ball cutoff has a unit-width transition collar when
the normalized cylinder radius is at least four.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The spatial cutoff in `lem:uc-gaussian`. -/
@[expose] def ucSpatialCutoff (ρ : ℝ) (hρ : 0 < ρ) : Vec3 → ℝ :=
  mollifiedBallCutoff 0 hρ

/-- The spatial cutoff is smooth for normalized radii at least four. -/
theorem ucSpatialCutoff_smooth {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (ucSpatialCutoff ρ hρ) :=
  mollifiedBallCutoff_smooth 0 hρ

/-- The spatial cutoff equals one on the inner ball. -/
theorem ucSpatialCutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ)
    {y : Vec3} (hy : y ∈ vec3Ball 0 (ρ / 2)) :
    ucSpatialCutoff ρ hρ y = 1 := by
  apply mollifiedBallCutoff_eq_one_on_inner 0 hρ
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (show (0 : ℝ) < 13 * ρ / 20 by positivity)).2
  have hy' : vec3EuclideanNorm (y - 0) < ρ / 2 := (mem_vec3Ball).1 hy
  have hlt : ρ / 2 < 13 * ρ / 20 := by nlinarith only [hρ]
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
    using hy'.trans hlt

/-- The topological support of the spatial cutoff is inside the outer ball. -/
theorem ucSpatialCutoff_tsupport {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (ucSpatialCutoff ρ hρ) ⊆ vec3Ball 0 ρ := by
  intro y hy
  have h : y ∈ euclideanBall 0 (3 * ρ / 4) :=
    mollifiedBallCutoff_tsupport_subset_outer 0 hρ hy
  have hlt : 3 * ρ / 4 < ρ := by linarith only [hρ]
  have h' : vecEuclideanNorm (y - 0) < ρ :=
    ((mem_euclideanBall_iff_vecEuclideanNorm_lt
      (show (0 : ℝ) < 3 * ρ / 4 by positivity)).1 h).trans hlt
  apply (mem_vec3Ball).2
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
    using h'

/-- The spatial cutoff takes values between zero and one. -/
theorem ucSpatialCutoff_bounds {ρ : ℝ} (hρ : 0 < ρ) (y : Vec3) :
    0 ≤ ucSpatialCutoff ρ hρ y ∧ ucSpatialCutoff ρ hρ y ≤ 1 :=
  ⟨mollifiedBallCutoff_nonneg 0 hρ y,
    mollifiedBallCutoff_le_one 0 hρ y⟩

/-- Each coordinate derivative of the spatial cutoff has a uniform bound. -/
theorem ucSpatialCutoff_spatialPartial_bound {ρ : ℝ} (hρ : 0 < ρ)
    (z : ParabolicPoint) (j : Fin 3) :
    |spatialPartial (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j z| ≤
      cutoffGradientConstant / ρ := by
  have hgrad := caccioppoli_spatial_cutoff_gradient_bound 0 ρ hρ z.1
  have hcoord := abs_apply_le_vecEuclideanNorm
    (classicalGradient (ucSpatialCutoff ρ hρ) z.1) j
  have hfirst : |spatialPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j z| ≤
      vecEuclideanNorm (classicalGradient (ucSpatialCutoff ρ hρ) z.1) := by
    simpa only [spatialPartial, classicalGradient_apply] using hcoord
  exact hfirst.trans hgrad

private theorem uc_spatialSecondPartial_of_spatial
    (g : Vec3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (z : ParabolicPoint) (i j : Fin 3) :
    spatialSecondPartial (fun q : ParabolicPoint => g q.1) i j z =
      (fderiv ℝ (classicalGradient g) z.1 (basisVec j)) i := by
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (classicalGradient g) := by
    unfold classicalGradient
    apply contDiff_pi.mpr
    intro k
    have h := hg.contDiff_fderiv_apply
      (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
    convert h.comp (contDiff_id.prodMk
      (contDiff_const (c := basisVec k))) using 1
    funext y
    rfl
  have hfd := fderiv_apply
    (hgrad.contDiffAt.differentiableAt (by simp) :
      DifferentiableAt ℝ (classicalGradient g) z.1) i
  unfold spatialSecondPartial
  change (fderiv ℝ (fun y : Vec3 => classicalGradient g y i) z.1)
      (basisVec j) = _
  rw [hfd]
  rfl

/-- The spatial cutoff has a second derivative bound given by the fixed
CKN cutoff constant. -/
theorem ucSpatialCutoff_spatialSecondPartial_bound {ρ : ℝ} (hρ : 0 < ρ)
    (z : ParabolicPoint) (i j : Fin 3) :
    |spatialSecondPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) i j z| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  rw [uc_spatialSecondPartial_of_spatial _
    (ucSpatialCutoff_smooth hρ) z i j]
  exact caccioppoli_spatial_cutoff_second_derivative_bound
    0 ρ hρ z.1 i j

end ESS

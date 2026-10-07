/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffHeatPlateau

/-!
# Spatial localization for Gaussian average cutoffs

The spatial cutoff is constant on a larger inner ball and vanishes outside
its compact support. These regions localize the two collar errors in
`lem:bu-gaussian`.
-/

public section


open Set CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- The CKN ball cutoff is constant on the inner plateau used for the
Gaussian average collar estimate. -/
theorem buGaussian_spatial_cutoff_eq_one_on_plateau
    {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : y ∈ vec3Ball 0 (13 * ρ / 20)) :
    ucSpatialCutoff ρ hρ y = 1 := by
  apply mollifiedBallCutoff_eq_one_on_inner 0 hρ
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (show (0 : ℝ) < 13 * ρ / 20 by positivity)).2
  have hy' : vec3EuclideanNorm (y - 0) < 13 * ρ / 20 := by
    simpa only [mem_vec3Ball] using hy
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
    using hy'

/-- The spatial derivative vanishes on the larger Gaussian plateau. -/
theorem buGaussian_spatial_cutoff_partial_zero_on_plateau
    {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : y ∈ vec3Ball 0 (13 * ρ / 20)) (j : Fin 3) (s : ℝ) :
    spatialPartial (fun z : ParabolicPoint => ucSpatialCutoff ρ hρ z.1)
      j (y, s) = 0 := by
  have heq : (ucSpatialCutoff ρ hρ) =ᶠ[𝓝 y]
      (fun _ : Vec3 => (1 : ℝ)) := by
    filter_upwards [((isOpen_vec3Ball 0 (13 * ρ / 20)).mem_nhds hy)]
      with y' hy'
    exact buGaussian_spatial_cutoff_eq_one_on_plateau hρ hy'
  change (fderiv ℝ (ucSpatialCutoff ρ hρ) y) (basisVec j) = 0
  rw [heq.fderiv_eq]
  simp

/-- The spatial Hessian vanishes on the larger Gaussian plateau. -/
theorem buGaussian_spatial_cutoff_second_zero_on_plateau
    {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : y ∈ vec3Ball 0 (13 * ρ / 20)) (i j : Fin 3) (s : ℝ) :
    spatialSecondPartial
      (fun z : ParabolicPoint => ucSpatialCutoff ρ hρ z.1) i j (y, s) = 0 := by
  have heq : (fun q : Vec3 => spatialPartial
      (fun z : ParabolicPoint => ucSpatialCutoff ρ hρ z.1) i (q, s))
      =ᶠ[𝓝 y] (fun _ : Vec3 => (0 : ℝ)) := by
    filter_upwards [((isOpen_vec3Ball 0 (13 * ρ / 20)).mem_nhds hy)]
      with y' hy'
    exact buGaussian_spatial_cutoff_partial_zero_on_plateau hρ hy' i s
  change (fderiv ℝ (fun q : Vec3 => spatialPartial
    (fun z : ParabolicPoint => ucSpatialCutoff ρ hρ z.1) i (q, s)) y)
      (basisVec j) = 0
  rw [heq.fderiv_eq]
  simp

private theorem buGaussian_spatial_cutoff_notMem_tsupport
    {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : 3 * ρ / 4 < vec3EuclideanNorm y) :
    y ∉ tsupport (ucSpatialCutoff ρ hρ) := by
  have hnot : y ∉ tsupport (ucSpatialCutoff ρ hρ) := by
    intro hyts
    have hyball := mollifiedBallCutoff_tsupport_subset_outer 0 hρ hyts
    have hnorm' : vecEuclideanNorm (y - 0) < 3 * ρ / 4 :=
      (mem_euclideanBall_iff_vecEuclideanNorm_lt
        (show (0 : ℝ) < 3 * ρ / 4 by positivity)).1 hyball
    have hnorm : vec3EuclideanNorm y < 3 * ρ / 4 := by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
        using hnorm'
    exact (not_lt_of_ge hy.le) hnorm
  exact hnot

private theorem buGaussian_spatial_cutoff_locally_zero
    {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : 3 * ρ / 4 < vec3EuclideanNorm y) :
    (ucSpatialCutoff ρ hρ) =ᶠ[𝓝 y] (fun _ : Vec3 => (0 : ℝ)) := by
  have hnot := buGaussian_spatial_cutoff_notMem_tsupport hρ hy
  have hopen : IsOpen ((tsupport (ucSpatialCutoff ρ hρ))ᶜ) :=
    (isClosed_tsupport (ucSpatialCutoff ρ hρ)).isOpen_compl
  filter_upwards [hopen.mem_nhds hnot] with y' hy'
  exact image_eq_zero_of_notMem_tsupport hy'

/-- The spatial derivative of the ball cutoff vanishes outside its support
ball. -/
theorem buGaussian_spatial_cutoff_partial_zero_outside
    {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : 3 * ρ / 4 < vec3EuclideanNorm y) (j : Fin 3) (s : ℝ) :
    spatialPartial (fun z : ParabolicPoint => ucSpatialCutoff ρ hρ z.1)
      j (y, s) = 0 := by
  change (fderiv ℝ (ucSpatialCutoff ρ hρ) y) (basisVec j) = 0
  rw [(buGaussian_spatial_cutoff_locally_zero hρ hy).fderiv_eq]
  simp

/-- The spatial Hessian of the ball cutoff vanishes outside its support
ball. -/
theorem buGaussian_spatial_cutoff_second_zero_outside
    {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : 3 * ρ / 4 < vec3EuclideanNorm y) (i j : Fin 3) (s : ℝ) :
    spatialSecondPartial
      (fun z : ParabolicPoint => ucSpatialCutoff ρ hρ z.1) i j (y, s) = 0 := by
  have hopen : IsOpen {q : Vec3 | 3 * ρ / 4 < vec3EuclideanNorm q} :=
    isOpen_lt continuous_const continuous_vec3EuclideanNorm
  have hlocal : (fun q : Vec3 => spatialPartial
      (fun z : ParabolicPoint => ucSpatialCutoff ρ hρ z.1) i (q, s))
      =ᶠ[𝓝 y] (fun _ : Vec3 => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hy] with y' hy'
    exact buGaussian_spatial_cutoff_partial_zero_outside hρ hy' i s
  have hsecond : spatialSecondPartial
      (fun z : ParabolicPoint => ucSpatialCutoff ρ hρ z.1) i j (y, s) = 0 := by
    change (fderiv ℝ (fun q : Vec3 => spatialPartial
      (fun z : ParabolicPoint => ucSpatialCutoff ρ hρ z.1) i (q, s)) y)
      (basisVec j) = 0
    rw [hlocal.fderiv_eq]
    simp
  exact hsecond

/-- The Gaussian cutoff heat operator vanishes outside the spatial support
ball, independently of its time cutoffs. -/
theorem buGaussian_cutoff_heat_zero_outside
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ) {z : ParabolicPoint}
    (hz : 3 * ρ / 4 < vec3EuclideanNorm z.1)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) :
    ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v Dtv z = 0 := by
  rcases z with ⟨y, s⟩
  have hy : 3 * ρ / 4 < vec3EuclideanNorm y := hz
  have hθ : ucSpatialCutoff ρ hρ y = 0 :=
    image_eq_zero_of_notMem_tsupport
      (buGaussian_spatial_cutoff_notMem_tsupport hρ hy)
  have hsp (j : Fin 3) :
      spatialPartial (ucGaussianCutoff ρ hρ ε) j (y, s) = 0 := by
    rw [ucGaussianCutoff_spatialPartial hρ ε (y, s) j]
    have h := buGaussian_spatial_cutoff_partial_zero_outside hρ hy j s
    rw [show spatialPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j (y, s) = 0 by
        simpa only [ParabolicPoint] using h]
    simp
  have hsp2 (j : Fin 3) :
      spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j (y, s) = 0 := by
    rw [ucGaussianCutoff_spatialSecondPartial hρ ε (y, s) j j]
    have h := buGaussian_spatial_cutoff_second_zero_outside hρ hy j j s
    rw [show spatialSecondPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j j (y, s) = 0 by
        simpa only [ParabolicPoint] using h]
    simp
  have htime : timePartial (ucGaussianCutoff ρ hρ ε) (y, s) = 0 := by
    rw [ucGaussianCutoff_timePartial hρ ε (y, s), hθ]
    simp
  have htime' : timePartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) (y, s) = 0 := by
    simpa only [ucGaussianCutoff] using htime
  have hsp' (j : Fin 3) : spatialPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) j (y, s) = 0 := by
    simpa only [ucGaussianCutoff] using hsp j
  have hsp2' (j : Fin 3) : spatialSecondPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) j j (y, s) = 0 := by
    simpa only [ucGaussianCutoff] using hsp2 j
  funext i
  simp [ucCutoffHeat, ucCutoffScalar, hθ, htime', hsp', hsp2']

/-- On the enlarged spatial plateau after the initial transition, the cutoff
heat operator has only the final-time cutoff error. -/
theorem buGaussian_cutoff_heat_eq_on_plateau_after_initial
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) {z : ParabolicPoint}
    (hy : z.1 ∈ vec3Ball 0 (13 * ρ / 20))
    (hεtime : 2 * ε < z.2)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) :
    ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v Dtv z =
        ucFinalTimeCutoff z.2 • ucWeakHeatVector D2v Dtv z +
          (deriv ucFinalTimeCutoff z.2) • v z := by
  rcases z with ⟨y, s⟩
  have hy' : y ∈ vec3Ball 0 (13 * ρ / 20) := hy
  have hεtime' : 2 * ε < s := by simpa using hεtime
  have hθ := buGaussian_spatial_cutoff_eq_one_on_plateau hρ hy'
  have hχ := ucInitialTimeCutoff_eq_one hε hεtime'.le
  have hcut : ucGaussianCutoff ρ hρ ε (y, s) = ucFinalTimeCutoff s := by
    simp [ucGaussianCutoff, ucCutoffScalar, hθ, hχ]
  have htime : timePartial (ucGaussianCutoff ρ hρ ε) (y, s) =
      deriv ucFinalTimeCutoff s := by
    rw [ucGaussianCutoff_timePartial hρ ε (y, s)]
    rw [ucGaussianTimeCutoff_deriv,
      ucInitialTimeCutoff_deriv_zero hε hεtime']
    simp [hχ, hθ]
  have hgrad (j : Fin 3) :
      spatialPartial (ucGaussianCutoff ρ hρ ε) j (y, s) = 0 := by
    rw [ucGaussianCutoff_spatialPartial hρ ε (y, s) j]
    have h := buGaussian_spatial_cutoff_partial_zero_on_plateau hρ hy' j s
    rw [show spatialPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j (y, s) = 0 by
        simpa only [ParabolicPoint] using h]
    simp
  have hhess (j : Fin 3) :
      spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j (y, s) = 0 := by
    rw [ucGaussianCutoff_spatialSecondPartial hρ ε (y, s) j j]
    have h := buGaussian_spatial_cutoff_second_zero_on_plateau hρ hy' j j s
    rw [show spatialSecondPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j j (y, s) = 0 by
        simpa only [ParabolicPoint] using h]
    simp
  have hcut' : ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) (y, s) = ucFinalTimeCutoff s := by
    simpa only [ucGaussianCutoff] using hcut
  have htime' : timePartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) (y, s) = deriv ucFinalTimeCutoff s := by
    simpa only [ucGaussianCutoff] using htime
  have hgrad' (j : Fin 3) : spatialPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) j (y, s) = 0 := by
    simpa only [ucGaussianCutoff] using hgrad j
  have hhess' (j : Fin 3) : spatialSecondPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) j j (y, s) = 0 := by
    simpa only [ucGaussianCutoff] using hhess j
  funext i
  simp [ucCutoffHeat, hcut', htime', hgrad', hhess']

end ESS

end

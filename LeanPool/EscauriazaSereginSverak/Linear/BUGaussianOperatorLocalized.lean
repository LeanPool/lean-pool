/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCutoffSupport
public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffOperatorBound
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimatesBasic

/-!
# Localized Gaussian cutoff operator bound

The cutoff error is separated into the spatial transition shell, the final
time transition, and the initial trace transition (`lem:bu-gaussian`).
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
attribute [local instance] Classical.propDecidable
open scoped Topology

noncomputable section

namespace ESS

private theorem buGaussian_final_cutoff_deriv_local_bound (s : ℝ) :
    |deriv ucFinalTimeCutoff s| ≤
      if 3 / 2 ≤ s ∧ s ≤ 7 / 4 then 32 else 0 := by
  classical
  by_cases hlo : 3 / 2 ≤ s
  · by_cases hhi : s ≤ 7 / 4
    · simpa [hlo, hhi] using ucFinalTimeCutoff_abs_deriv_le s
    · have hs : 7 / 4 < s := lt_of_not_ge hhi
      have hzero : ucFinalTimeCutoff =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds hs] with t ht
        exact ucFinalTimeCutoff_eq_zero (le_of_lt ht)
      rw [hzero.deriv_eq]
      simp [hhi]
  · have hs : s < 3 / 2 := lt_of_not_ge hlo
    rw [ucFinalTimeCutoff_deriv_zero hs]
    simp [hlo]

private theorem buGaussian_nonneg_mul_add_le {k a g : ℝ}
    (hk : 0 ≤ k) (hg : 0 ≤ g) : k * (a + g) ≤ k * (a + 3 * g) := by
  have hgrad : g ≤ 3 * g := by nlinarith only [hg]
  exact mul_le_mul_of_nonneg_left (add_le_add_right hgrad a) hk

private theorem buGaussian_shell_indicator_zero {ρ : ℝ} {y : Vec3} {a : ℝ}
    (h : ¬ (13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
      vec3EuclideanNorm y ≤ 3 * ρ / 4)) :
    (if 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
        vec3EuclideanNorm y ≤ 3 * ρ / 4 then a else 0) = 0 := by
  by_cases hshell : 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
      vec3EuclideanNorm y ≤ 3 * ρ / 4
  · exact (h hshell).elim
  · simp only [hshell, ↓reduceIte]

private theorem buGaussian_cutoff_heat_eq_on_plateau_early
    {ρ ε : ℝ} (hρ : 0 < ρ) {z : ParabolicPoint}
    (hy : z.1 ∈ vec3Ball 0 (13 * ρ / 20))
    (hs : z.2 ≤ 2 * ε) (hεsmall : 2 * ε ≤ 1 / 2)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) :
    ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v Dtv z =
      ucInitialTimeCutoff ε z.2 • ucWeakHeatVector D2v Dtv z +
        (deriv (ucInitialTimeCutoff ε) z.2) • v z := by
  rcases z with ⟨y, s⟩
  have hy' : y ∈ vec3Ball 0 (13 * ρ / 20) := hy
  have hslate : s < 3 / 2 :=
    lt_of_le_of_lt hs (lt_of_le_of_lt hεsmall (by norm_num))
  have hθ := buGaussian_spatial_cutoff_eq_one_on_plateau hρ hy'
  have hη := ucFinalTimeCutoff_eq_one hslate.le
  have hηderiv := ucFinalTimeCutoff_deriv_zero hslate
  have hcut : ucGaussianCutoff ρ hρ ε (y, s) = ucInitialTimeCutoff ε s := by
    simp [ucGaussianCutoff, ucCutoffScalar, hθ, hη]
  have htime : timePartial (ucGaussianCutoff ρ hρ ε) (y, s) =
      deriv (ucInitialTimeCutoff ε) s := by
    rw [ucGaussianCutoff_timePartial hρ ε (y, s),
      ucGaussianTimeCutoff_deriv, hηderiv, hη]
    simp [hθ]
  have hsp (j : Fin 3) :
      spatialPartial (ucGaussianCutoff ρ hρ ε) j (y, s) = 0 := by
    rw [ucGaussianCutoff_spatialPartial hρ ε (y, s) j]
    have h := buGaussian_spatial_cutoff_partial_zero_on_plateau hρ hy' j s
    rw [show spatialPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j (y, s) = 0 by
        simpa only [ParabolicPoint] using h]
    simp
  have hsp2 (j : Fin 3) :
      spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j (y, s) = 0 := by
    rw [ucGaussianCutoff_spatialSecondPartial hρ ε (y, s) j j]
    have h := buGaussian_spatial_cutoff_second_zero_on_plateau hρ hy' j j s
    rw [show spatialSecondPartial
      (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j j (y, s) = 0 by
        simpa only [ParabolicPoint] using h]
    simp
  have hcut' : ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) (y, s) = ucInitialTimeCutoff ε s := by
    simpa only [ucGaussianCutoff] using hcut
  have htime' : timePartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) (y, s) = deriv (ucInitialTimeCutoff ε) s := by
    simpa only [ucGaussianCutoff] using htime
  have hgrad' (j : Fin 3) : spatialPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) j (y, s) = 0 := by
    simpa only [ucGaussianCutoff] using hsp j
  have hhess' (j : Fin 3) : spatialSecondPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) j j (y, s) = 0 := by
    simpa only [ucGaussianCutoff] using hsp2 j
  funext i
  simp [ucCutoffHeat, hcut', htime', hgrad', hhess']

private theorem buGaussian_cutoff_plateau_energy
    {ρ ε : ℝ} (hρ : 0 < ρ) {z : ParabolicPoint}
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hcut : ucGaussianCutoff ρ hρ ε z = κ)
    (hpartial : ∀ j : Fin 3,
      spatialPartial (ucGaussianCutoff ρ hρ ε) j z = 0)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3) :
    vec3EuclideanNorm
        (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v z) = κ * vec3EuclideanNorm (v z) ∧
      Real.sqrt (spatialGradientSq
        (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v)
        (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dv) z) =
        κ * Real.sqrt (spatialGradientSq v Dv z) := by
  have hscalar : ucCutoffScalar (ucSpatialCutoff ρ hρ)
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) z = κ := by
    simpa only [ucGaussianCutoff] using hcut
  have hpartial' (j : Fin 3) : spatialPartial
      (ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε)) j z = 0 := by
    simpa only [ucGaussianCutoff] using hpartial j
  have hfield : ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v z = κ • v z := by
    simp [ucCutoffField, hscalar]
  have hdw : ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv z = fun i j => κ * Dv z i j := by
    funext i j
    simp [ucCutoffDw, hscalar, hpartial' j]
  have hgrad : spatialGradientSq
      (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v)
      (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv) z =
        κ ^ 2 * spatialGradientSq v Dv z := by
    simp only [spatialGradientSq, hdw]
    simp_rw [mul_pow]
    simp_rw [← Finset.mul_sum]
  constructor
  · rw [hfield, vec3EuclideanNorm_smul, abs_of_nonneg hκ]
  · rw [hgrad, Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hκ]

private def buGaussian_cutoff_localized_target
    {ρ ε c₁ scale : ℝ} (hρ : 0 < ρ)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) (z : ParabolicPoint) : Prop :=
  vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
    c₁ * scale *
        (vec3EuclideanNorm
          (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
            (ucInitialTimeCutoff ε) v z) +
          3 * Real.sqrt (spatialGradientSq
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v)
            (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v Dv) z)) +
    (if z.1 ∈ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
        vec3EuclideanNorm y ≤ 3 * ρ / 4} then
      (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
        3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
          vec3EuclideanNorm (v z) +
      18 * (cutoffGradientConstant / ρ) *
        Real.sqrt (spatialGradientSq v Dv z) else 0) +
    (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
      32 * vec3EuclideanNorm (v z) else 0) +
    (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
      vec3EuclideanNorm (v z)

private theorem buGaussian_cutoff_early_transition_bound
    {ρ ε c₁ scale : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hεsmall : 2 * ε ≤ 1 / 2) (_hc₁ : 0 ≤ c₁) (_hscale : 0 ≤ scale)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) {z : ParabolicPoint}
    (hheat : vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
      c₁ * scale * (vec3EuclideanNorm (v z) +
        Real.sqrt (spatialGradientSq v Dv z)))
    (hinner : z.1 ∈ vec3Ball 0 (13 * ρ / 20))
    (hearly : z.2 ≤ 2 * ε) :
    vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
      c₁ * scale *
        (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
          Real.sqrt (spatialGradientSq
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v)
            (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v Dv) z)) +
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z) ∧
    (0 ≤ if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
      32 * vec3EuclideanNorm (v z) else 0) ∧
    (if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
        vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
      (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
        3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
          vec3EuclideanNorm (v z) +
      18 * (cutoffGradientConstant / ρ) *
        Real.sqrt (spatialGradientSq v Dv z) else 0) = 0 := by
  have hnorm : 0 ≤ vec3EuclideanNorm (v z) := vec3EuclideanNorm_nonneg _
  have hformula := buGaussian_cutoff_heat_eq_on_plateau_early
    hρ hinner hearly hεsmall v Dv D2v Dtv
  have hcut : ucGaussianCutoff ρ hρ ε z =
      ucInitialTimeCutoff ε z.2 := by
    simp [ucGaussianCutoff, ucCutoffScalar,
      buGaussian_spatial_cutoff_eq_one_on_plateau hρ hinner,
      ucFinalTimeCutoff_eq_one (by
        exact (lt_of_le_of_lt hearly
          (lt_of_le_of_lt hεsmall (by norm_num))).le)]
  have hpartial (j : Fin 3) :
      spatialPartial (ucGaussianCutoff ρ hρ ε) j z = 0 := by
    rw [ucGaussianCutoff_spatialPartial hρ ε z j]
    have hp := buGaussian_spatial_cutoff_partial_zero_on_plateau
      hρ hinner j z.2
    have hp' : spatialPartial
        (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j z = 0 := by
      change spatialPartial
          (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j
            (z.1, z.2) = 0
      exact hp
    rw [hp']
    simp
  have henergy := buGaussian_cutoff_plateau_energy hρ
    (ucInitialTimeCutoff ε z.2)
    (ucInitialTimeCutoff_bounds ε z.2).1 hcut hpartial v Dv
  have hnormL : vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
      c₁ * scale * (vec3EuclideanNorm (v z) +
        Real.sqrt (spatialGradientSq v Dv z)) := hheat
  have hderiv := ucInitialTimeCutoff_abs_deriv_le_early hε z.2
  have htriangle : vec3EuclideanNorm
      (ucInitialTimeCutoff ε z.2 • ucWeakHeatVector D2v Dtv z +
        deriv (ucInitialTimeCutoff ε) z.2 • v z) ≤
      ucInitialTimeCutoff ε z.2 *
          vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) +
        |deriv (ucInitialTimeCutoff ε) z.2| * vec3EuclideanNorm (v z) := by
    calc
      _ ≤ vec3EuclideanNorm (ucInitialTimeCutoff ε z.2 •
          ucWeakHeatVector D2v Dtv z) +
          vec3EuclideanNorm (deriv (ucInitialTimeCutoff ε) z.2 • v z) :=
        vec3EuclideanNorm_add_le _ _
      _ = _ := by
        rw [vec3EuclideanNorm_smul, vec3EuclideanNorm_smul,
          abs_of_nonneg (ucInitialTimeCutoff_bounds ε z.2).1]
  have hmain : ucInitialTimeCutoff ε z.2 *
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
      c₁ * scale *
        (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
          Real.sqrt (spatialGradientSq
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v)
            (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v Dv) z)) := by
    calc
      _ ≤ ucInitialTimeCutoff ε z.2 *
          (c₁ * scale * (vec3EuclideanNorm (v z) +
            Real.sqrt (spatialGradientSq v Dv z))) :=
        mul_le_mul_of_nonneg_left hnormL
          (ucInitialTimeCutoff_bounds ε z.2).1
      _ = c₁ * scale *
          (vec3EuclideanNorm
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v z) +
            Real.sqrt (spatialGradientSq
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v)
              (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v Dv) z)) := by
        rw [henergy.1, henergy.2]
        ring
  have hlate : 0 ≤ if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
      32 * vec3EuclideanNorm (v z) else 0 := by positivity
  have h := htriangle.trans (add_le_add hmain
    (mul_le_mul_of_nonneg_right hderiv hnorm))
  have hearly' : |deriv (ucInitialTimeCutoff ε) z.2| *
      vec3EuclideanNorm (v z) ≤
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z) :=
    mul_le_mul_of_nonneg_right hderiv hnorm
  have hlo : ¬ 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 := by
    have hlt : vec3EuclideanNorm z.1 < 13 * ρ / 20 := by
      simpa only [mem_vec3Ball, sub_zero] using hinner
    exact not_le_of_gt hlt
  have hnotShell : z.1 ∉ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
      vec3EuclideanNorm y ≤ 3 * ρ / 4} := by
    intro h
    exact hlo h.1
  have hShellZero : (if z.1 ∈
      {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
        vec3EuclideanNorm y ≤ 3 * ρ / 4} then
      (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
        3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
          vec3EuclideanNorm (v z) +
      18 * (cutoffGradientConstant / ρ) *
        Real.sqrt (spatialGradientSq v Dv z) else 0) = 0 := by
    by_cases h : z.1 ∈ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
        vec3EuclideanNorm y ≤ 3 * ρ / 4}
    · exact (hnotShell h).elim
    · simp [h]
  have hShellZero' : (if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
      vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
      (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
        3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
          vec3EuclideanNorm (v z) +
      18 * (cutoffGradientConstant / ρ) *
        Real.sqrt (spatialGradientSq v Dv z) else 0) = 0 := by
    simpa only [Set.mem_ofPred_eq] using hShellZero
  have hbound : vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
      c₁ * scale *
        (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
          Real.sqrt (spatialGradientSq
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v)
            (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v Dv) z)) +
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z) := by
    rw [hformula]
    exact htriangle.trans (add_le_add hmain hearly')
  exact ⟨hbound, hlate, hShellZero'⟩

private theorem buGaussian_cutoff_localized_interior_early
    {ρ ε c₁ scale : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hεsmall : 2 * ε ≤ 1 / 2) (hc₁ : 0 ≤ c₁) (hscale : 0 ≤ scale)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) {z : ParabolicPoint}
    (hheat : vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
      c₁ * scale * (vec3EuclideanNorm (v z) +
        Real.sqrt (spatialGradientSq v Dv z)))
    (hinner : z.1 ∈ vec3Ball 0 (13 * ρ / 20))
    (hearly : z.2 ≤ 2 * ε) :
    buGaussian_cutoff_localized_target (ε := ε) (c₁ := c₁) (scale := scale)
      hρ v Dv D2v Dtv z := by
  have hnorm : 0 ≤ vec3EuclideanNorm (v z) := vec3EuclideanNorm_nonneg _
  have hgrad : 0 ≤ Real.sqrt (spatialGradientSq v Dv z) := Real.sqrt_nonneg _
  have hmainGrad : 0 ≤ Real.sqrt (spatialGradientSq
      (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v)
      (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv) z) := Real.sqrt_nonneg _
  rcases buGaussian_cutoff_early_transition_bound
      hρ hε hεsmall hc₁ hscale v Dv D2v Dtv hheat hinner hearly with
    ⟨hbound, hlate, hShellZero'⟩
  have htargetBase : vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
      c₁ * scale *
        (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
          3 * Real.sqrt (spatialGradientSq
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v)
            (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v Dv) z)) +
      (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
        32 * vec3EuclideanNorm (v z) else 0) +
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z) := by
    have hcoef : 0 ≤ c₁ * scale := mul_nonneg hc₁ hscale
    have hmainUpgrade := buGaussian_nonneg_mul_add_le
      (a := vec3EuclideanNorm
        (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v z)) hcoef hmainGrad
    have hlateAdd :
        c₁ * scale *
            (vec3EuclideanNorm
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v z) +
              3 * Real.sqrt (spatialGradientSq
                (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                  (ucInitialTimeCutoff ε) v)
                (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                  (ucInitialTimeCutoff ε) v Dv) z)) ≤
          c₁ * scale *
              (vec3EuclideanNorm
                (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                  (ucInitialTimeCutoff ε) v z) +
                3 * Real.sqrt (spatialGradientSq
                  (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                    (ucInitialTimeCutoff ε) v)
                  (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                    (ucInitialTimeCutoff ε) v Dv) z)) +
            (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
              32 * vec3EuclideanNorm (v z) else 0) :=
      le_add_of_nonneg_right hlate
    have htarget0 := add_le_add_left hmainUpgrade
      ((if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z))
    have htarget1 := add_le_add_left hlateAdd
      ((if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z))
    calc
    _ ≤ c₁ * scale *
          (vec3EuclideanNorm
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v z) +
            Real.sqrt (spatialGradientSq
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v)
              (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v Dv) z)) +
          (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
            vec3EuclideanNorm (v z) := hbound
    _ ≤ _ := htarget0
    _ ≤ _ := htarget1
  have htarget : vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
      c₁ * scale *
        (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
          3 * Real.sqrt (spatialGradientSq
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v)
            (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v Dv) z)) +
      (if z.1 ∈ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
          vec3EuclideanNorm y ≤ 3 * ρ / 4} then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
          3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
            vec3EuclideanNorm (v z) +
        18 * (cutoffGradientConstant / ρ) *
          Real.sqrt (spatialGradientSq v Dv z) else 0) +
      (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
        32 * vec3EuclideanNorm (v z) else 0) +
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z) := by
    simpa only [Set.mem_ofPred_eq, hShellZero', add_zero] using htargetBase
  exact htarget

private theorem buGaussian_cutoff_localized_interior_late
    {ρ ε c₁ scale : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (_hεsmall : 2 * ε ≤ 1 / 2) (hc₁ : 0 ≤ c₁) (hscale : 0 ≤ scale)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) {z : ParabolicPoint}
    (hheat : vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
      c₁ * scale * (vec3EuclideanNorm (v z) +
        Real.sqrt (spatialGradientSq v Dv z)))
    (hinner : z.1 ∈ vec3Ball 0 (13 * ρ / 20))
    (hpost : 2 * ε < z.2) :
    buGaussian_cutoff_localized_target (ε := ε) (c₁ := c₁) (scale := scale)
      hρ v Dv D2v Dtv z := by
  have hnorm : 0 ≤ vec3EuclideanNorm (v z) := vec3EuclideanNorm_nonneg _
  have hgrad : 0 ≤ Real.sqrt (spatialGradientSq v Dv z) := Real.sqrt_nonneg _
  have hmainGrad : 0 ≤ Real.sqrt (spatialGradientSq
      (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v)
      (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv) z) := Real.sqrt_nonneg _
  have hformula := buGaussian_cutoff_heat_eq_on_plateau_after_initial
    hρ hε hinner hpost v Dv D2v Dtv
  have hcut : ucGaussianCutoff ρ hρ ε z = ucFinalTimeCutoff z.2 := by
    simp [ucGaussianCutoff, ucCutoffScalar,
      buGaussian_spatial_cutoff_eq_one_on_plateau hρ hinner,
      ucInitialTimeCutoff_eq_one hε (le_of_lt hpost)]
  have hpartial (j : Fin 3) :
      spatialPartial (ucGaussianCutoff ρ hρ ε) j z = 0 := by
    rw [ucGaussianCutoff_spatialPartial hρ ε z j]
    have hp := buGaussian_spatial_cutoff_partial_zero_on_plateau
      hρ hinner j z.2
    have hp' : spatialPartial
        (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j z = 0 := by
      change spatialPartial
          (fun q : ParabolicPoint => ucSpatialCutoff ρ hρ q.1) j
            (z.1, z.2) = 0
      exact hp
    rw [hp']
    simp
  have henergy := buGaussian_cutoff_plateau_energy hρ
    (ucFinalTimeCutoff z.2) (ucFinalTimeCutoff_bounds z.2).1
    hcut hpartial v Dv
  have hnormL : vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
      c₁ * scale * (vec3EuclideanNorm (v z) +
        Real.sqrt (spatialGradientSq v Dv z)) := hheat
  have hderiv := buGaussian_final_cutoff_deriv_local_bound z.2
  have htriangle : vec3EuclideanNorm
      (ucFinalTimeCutoff z.2 • ucWeakHeatVector D2v Dtv z +
        deriv ucFinalTimeCutoff z.2 • v z) ≤
      ucFinalTimeCutoff z.2 *
          vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) +
        |deriv ucFinalTimeCutoff z.2| * vec3EuclideanNorm (v z) := by
    calc
      _ ≤ vec3EuclideanNorm (ucFinalTimeCutoff z.2 •
          ucWeakHeatVector D2v Dtv z) +
          vec3EuclideanNorm (deriv ucFinalTimeCutoff z.2 • v z) :=
        vec3EuclideanNorm_add_le _ _
      _ = _ := by
        rw [vec3EuclideanNorm_smul, vec3EuclideanNorm_smul,
          abs_of_nonneg (ucFinalTimeCutoff_bounds z.2).1]
  have hmain : ucFinalTimeCutoff z.2 *
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
      c₁ * scale *
        (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
          Real.sqrt (spatialGradientSq
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v)
            (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v Dv) z)) := by
    calc
      _ ≤ ucFinalTimeCutoff z.2 *
          (c₁ * scale * (vec3EuclideanNorm (v z) +
            Real.sqrt (spatialGradientSq v Dv z))) :=
        mul_le_mul_of_nonneg_left hnormL
          (ucFinalTimeCutoff_bounds z.2).1
      _ = c₁ * scale *
          (vec3EuclideanNorm
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v z) +
            Real.sqrt (spatialGradientSq
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v)
              (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v Dv) z)) := by
        rw [henergy.1, henergy.2]
        ring
  have hfinal := mul_le_mul_of_nonneg_right hderiv hnorm
  have hfinal' : |deriv ucFinalTimeCutoff z.2| *
      vec3EuclideanNorm (v z) ≤
      (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
        32 * vec3EuclideanNorm (v z) else 0) := by
    by_cases htime : 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4
    · simpa [htime] using hfinal
    · have hderiv0 : |deriv ucFinalTimeCutoff z.2| ≤ 0 := by
        simpa [htime] using hderiv
      have hmul := mul_le_mul_of_nonneg_right hderiv0 hnorm
      simpa [htime] using hmul
  have hsum := add_le_add hmain hfinal'
  have hnotShell' :
      ¬ (13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
        vec3EuclideanNorm z.1 ≤ 3 * ρ / 4) := by
    intro hs
    have hlt : vec3EuclideanNorm z.1 < 13 * ρ / 20 := by
      simpa only [mem_vec3Ball, sub_zero] using hinner
    exact (not_le_of_gt hlt) hs.1
  have hShellZero : (if z.1 ∈
      {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
        vec3EuclideanNorm y ≤ 3 * ρ / 4} then
      (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
        3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
          vec3EuclideanNorm (v z) +
      18 * (cutoffGradientConstant / ρ) *
        Real.sqrt (spatialGradientSq v Dv z) else 0) = 0 := by
    change (if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
        vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then _ else 0) = 0
    exact buGaussian_shell_indicator_zero (a :=
      (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
        3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
          vec3EuclideanNorm (v z) +
        18 * (cutoffGradientConstant / ρ) *
          Real.sqrt (spatialGradientSq v Dv z)) hnotShell'
  have hShellZero' : (if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
      vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
      (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
        3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
          vec3EuclideanNorm (v z) +
      18 * (cutoffGradientConstant / ρ) *
        Real.sqrt (spatialGradientSq v Dv z) else 0) = 0 := by
    simpa only [Set.mem_ofPred_eq] using hShellZero
  have hnotEarly : ¬ (ε ≤ z.2 ∧ z.2 ≤ 2 * ε) := by
    intro h
    exact (not_lt_of_ge h.2) hpost
  have hearlyZero : (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
      8 / ε else 0) * vec3EuclideanNorm (v z) = 0 := by
    by_cases htime : ε ≤ z.2 ∧ z.2 ≤ 2 * ε
    · exact (hnotEarly htime).elim
    · simp [htime]
  have hgradcut : 0 ≤ Real.sqrt (spatialGradientSq
      (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v)
      (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv) z) := by positivity
  have hsumBase : vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
      c₁ * scale *
        (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
          3 * Real.sqrt (spatialGradientSq
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v)
            (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v Dv) z)) +
      (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
        32 * vec3EuclideanNorm (v z) else 0) := by
    calc
      _ ≤ c₁ * scale *
            (vec3EuclideanNorm
                (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                  (ucInitialTimeCutoff ε) v z) +
              Real.sqrt (spatialGradientSq
                (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                  (ucInitialTimeCutoff ε) v)
                (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                  (ucInitialTimeCutoff ε) v Dv) z)) +
            (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
              32 * vec3EuclideanNorm (v z) else 0) := by
        rw [hformula]
        exact htriangle.trans (add_le_add hmain hfinal')
      _ ≤ _ := by
        exact add_le_add_left
          (buGaussian_nonneg_mul_add_le
            (a := vec3EuclideanNorm
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v z))
            (mul_nonneg hc₁ hscale) hgradcut)
          (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
            32 * vec3EuclideanNorm (v z) else 0)
  have hsum'' : vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
      c₁ * scale *
        (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
          3 * Real.sqrt (spatialGradientSq
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v)
            (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v Dv) z)) +
      (if z.1 ∈ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
          vec3EuclideanNorm y ≤ 3 * ρ / 4} then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
          3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
            vec3EuclideanNorm (v z) +
        18 * (cutoffGradientConstant / ρ) *
          Real.sqrt (spatialGradientSq v Dv z) else 0) +
      (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
        32 * vec3EuclideanNorm (v z) else 0) +
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z) := by
    rw [hShellZero, hearlyZero]
    simp only [add_zero]
    exact hsumBase
  exact hsum''

/-- The Gaussian cutoff heat operator is bounded separately on the spatial
transition shell, the final-time strip, and the initial-time strip
(`lem:bu-gaussian`). -/
theorem buGaussian_cutoff_operator_localized_ae_bound
    {ρ ε c₁ scale : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hεsmall : 2 * ε ≤ 1 / 2)
    (hc₁ : 0 ≤ c₁) (hscale : 0 ≤ scale)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    (hineq : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c₁ * scale * (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z))) :
    ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      z ∈ ucCylinder ρ →
      vec3EuclideanNorm
        (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
        c₁ * scale *
          (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
            3 * Real.sqrt (spatialGradientSq
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v)
              (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v Dv) z)) +
        (if z.1 ∈ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
            vec3EuclideanNorm y ≤ 3 * ρ / 4} then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
            3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
              vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) else 0) +
        (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
          32 * vec3EuclideanNorm (v z) else 0) +
        (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
          vec3EuclideanNorm (v z) := by
  classical
  have hoperator := ucGaussianCutoff_operator_ae_bound hρ hε hc₁ hscale
    v Dv D2v Dtv hineq
  filter_upwards [hoperator, hineq] with z hop hheat hz
  have hnorm : 0 ≤ vec3EuclideanNorm (v z) := vec3EuclideanNorm_nonneg _
  have hgrad : 0 ≤ Real.sqrt (spatialGradientSq v Dv z) := Real.sqrt_nonneg _
  have hmainGrad : 0 ≤ Real.sqrt (spatialGradientSq
      (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v)
      (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv) z) := Real.sqrt_nonneg _
  have hcoefC₂ : 0 ≤ cutoffSecondDerivativeConstant :=
    CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  have hcoefG : 0 ≤ cutoffGradientConstant :=
    CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  by_cases hlo : 13 * ρ / 20 ≤ vec3EuclideanNorm z.1
  · by_cases hhi : vec3EuclideanNorm z.1 ≤ 3 * ρ / 4
    · have hshell : z.1 ∈ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
          vec3EuclideanNorm y ≤ 3 * ρ / 4} := ⟨hlo, hhi⟩
      have hrad : ρ / 2 ≤ vec3EuclideanNorm z.1 := by
        nlinarith only [hlo, hρ]
      have hregion : z ∈ ucCutoffRegion ρ := by
        change z ∈ ucCylinder ρ ∧ z ∉ ucInnerRegion ρ
        refine ⟨hz, ?_⟩
        intro hi
        have hi' : vec3EuclideanNorm z.1 < ρ / 2 := by
          simpa only [mem_vec3Ball, sub_zero] using hi.1
        exact (not_lt_of_ge hrad) hi'
      have hop' := hop hz
      simp only [hregion, ↓reduceIte, ite_mul, zero_mul] at hop'
      have hlate : 0 ≤ if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
          32 * vec3EuclideanNorm (v z) else 0 := by positivity
      let main := c₁ * scale *
          (vec3EuclideanNorm
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v z) +
            3 * Real.sqrt (spatialGradientSq
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v)
              (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v Dv) z))
      let shell := (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
            3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
              vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z)
      let initial := (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z)
      have hinitialEq : initial =
          (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
            8 / ε * vec3EuclideanNorm (v z) else 0) := by
        by_cases htime : ε ≤ z.2 ∧ z.2 ≤ 2 * ε <;>
          simp [initial, htime]
      have hshellLate : shell ≤ shell +
          (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
            32 * vec3EuclideanNorm (v z) else 0) :=
        le_add_of_nonneg_right hlate
      have hcore : main + shell ≤ main + (shell +
          (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
            32 * vec3EuclideanNorm (v z) else 0)) :=
        add_le_add_right hshellLate main
      have hcore' : (main + shell) + initial ≤
          (main + (shell +
            (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
              32 * vec3EuclideanNorm (v z) else 0))) + initial :=
        add_le_add_left hcore initial
      have hop'' : vec3EuclideanNorm
          (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
            (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤ (main + shell) + initial := by
        simpa only [main, shell, initial, hinitialEq] using hop'
      have htarget : vec3EuclideanNorm
          (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
            (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
          (main + shell +
            (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
              32 * vec3EuclideanNorm (v z) else 0)) + initial := by
        calc
          _ ≤ (main + shell) + initial := hop''
          _ ≤ _ := by simpa only [add_assoc] using hcore'
      have hshellCond : 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
          vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 := by
        simpa only [Set.mem_ofPred_eq] using hshell
      simpa [hshellCond, hregion, main, shell, initial, hinitialEq] using htarget
    · have houter : 3 * ρ / 4 < vec3EuclideanNorm z.1 := lt_of_not_ge hhi
      have hzero := buGaussian_cutoff_heat_zero_outside hρ ε houter
        v Dv D2v Dtv
      rw [hzero]
      have hnonneg : 0 ≤ c₁ * scale *
          (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
            3 * Real.sqrt (spatialGradientSq
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v)
              (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v Dv) z)) := by
        have hcoef : 0 ≤ c₁ * scale := mul_nonneg hc₁ hscale
        have hfieldnonneg : 0 ≤ vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) := vec3EuclideanNorm_nonneg _
        exact mul_nonneg hcoef
          (add_nonneg hfieldnonneg (mul_nonneg (by norm_num) hmainGrad))
      have hshellerr : 0 ≤ if z.1 ∈
          {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
            vec3EuclideanNorm y ≤ 3 * ρ / 4} then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
            3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
              vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) else 0 := by
        by_cases hshell : z.1 ∈
            {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
              vec3EuclideanNorm y ≤ 3 * ρ / 4}
        · simp only [hshell, ↓reduceIte]
          positivity
        · simp only [hshell, ↓reduceIte, Std.le_refl]
      have hlate : 0 ≤ if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
          32 * vec3EuclideanNorm (v z) else 0 := by positivity
      have hearly : 0 ≤ (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
          vec3EuclideanNorm (v z) := by split_ifs <;> positivity
      have hnotShell : z.1 ∉ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
          vec3EuclideanNorm y ≤ 3 * ρ / 4} := by
        intro h
        exact (not_lt_of_ge h.2) houter
      have hShellZero : (if z.1 ∈
          {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
            vec3EuclideanNorm y ≤ 3 * ρ / 4} then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
            3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
              vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) else 0) = 0 := by
        by_cases h : z.1 ∈ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
            vec3EuclideanNorm y ≤ 3 * ρ / 4}
        · exact (hnotShell h).elim
        · simp [h]
      have hShellZero' : (if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
          vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
            3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
              vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) else 0) = 0 := by
        simpa only [Set.mem_ofPred_eq] using hShellZero
      have hsumNonneg : 0 ≤ c₁ * scale *
          (vec3EuclideanNorm
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v z) +
            3 * Real.sqrt (spatialGradientSq
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v)
              (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v Dv) z)) +
          (if z.1 ∈ {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
              vec3EuclideanNorm y ≤ 3 * ρ / 4} then
            (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
              3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
                vec3EuclideanNorm (v z) +
            18 * (cutoffGradientConstant / ρ) *
              Real.sqrt (spatialGradientSq v Dv z) else 0) +
          (if 3 / 2 ≤ z.2 ∧ z.2 ≤ 7 / 4 then
            32 * vec3EuclideanNorm (v z) else 0) +
          (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
            vec3EuclideanNorm (v z) := by
        rw [hShellZero]
        simp only [add_zero]
        exact add_nonneg (add_nonneg hnonneg hlate) hearly
      simpa only [vec3EuclideanNorm_zero, Set.mem_ofPred_eq] using hsumNonneg
  · have hinner : z.1 ∈ vec3Ball 0 (13 * ρ / 20) := by
      simpa only [mem_vec3Ball, sub_zero] using lt_of_not_ge hlo
    by_cases hearly : z.2 ≤ 2 * ε
    · exact buGaussian_cutoff_localized_interior_early hρ hε hεsmall
        hc₁ hscale v Dv D2v Dtv hheat hinner hearly
    · exact buGaussian_cutoff_localized_interior_late hρ hε hεsmall
        hc₁ hscale v Dv D2v Dtv hheat hinner (lt_of_not_ge hearly)

end ESS

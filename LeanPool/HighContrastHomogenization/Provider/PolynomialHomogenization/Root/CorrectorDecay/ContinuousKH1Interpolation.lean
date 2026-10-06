/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.FullNormEquivalence

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.ContinuousKH1Interpolation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Continuous interpolation for coordinatewise H1 fields

An exact coordinatewise H1 representative is an admissible competitor for
the continuous K-functional.  Its zero residual and weak-gradient energy
give the endpoint needed to interpolate between normalized L2 and H1.
-/

namespace HCPolySupport

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem continuousKResidualNorm_eq_zero_of_eq_toField {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) (G : ContinuousKCompetitor d)
    (hFG : F.toField = G.toField) :
    continuousKResidualNorm F G = 0 := by
  unfold continuousKResidualNorm
  have hzero : (fun x ↦ F x - G.toField x) = 0 := by
    funext x
    rw [show F x = G.toField x by exact congrFun hFG x]
    simp
  have hzeroAe : (fun x ↦ F x - G.toField x) =ᵐ[
      (unitCenteredCubeDomain d).normalizedVolume] (0 : Vec d → Vec d) :=
    Filter.Eventually.of_forall fun x ↦ congrFun hzero x
  let hz : MemLp (fun x : Vec d ↦ euclideanNorm ((0 : Vec d → Vec d) x))
      2 (unitCenteredCubeDomain d).normalizedVolume := by simp
  calc
    (unitCenteredCubeDomain d).normalizedEuclideanLpNorm 2
        (fun x ↦ F x - G.toField x) _ =
      (unitCenteredCubeDomain d).normalizedEuclideanLpNorm 2
        (0 : Vec d → Vec d) hz := by
          apply (unitCenteredCubeDomain d).normalizedEuclideanLpNorm_congr_ae
          exact hzeroAe
    _ = 0 := by
      simp [BoundedMeasurableDomain.normalizedEuclideanLpNorm,
        BoundedMeasurableDomain.normalizedLpNorm,
        BoundedMeasurableDomain.normalizedLpFiniteENorm,
        BoundedMeasurableDomain.normalizedLpENorm]

private theorem continuousKFunctional_le_scale_mul_gradientNorm {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d)
    (G : ContinuousKCompetitor d) (hFG : F.toField = G.toField) :
    continuousKFunctional t F ≤ t.1 * continuousKGradientNorm G := by
  calc
    continuousKFunctional t F ≤
        continuousKFunctionalCompetitorValue t F G :=
      continuousKFunctional_le_competitor t F G
    _ = t.1 * continuousKGradientNorm G := by
      unfold continuousKFunctionalCompetitorValue
      rw [continuousKResidualNorm_eq_zero_of_eq_toField F G hFG]
      rw [zero_pow (by norm_num), zero_add]
      rw [show t.1 ^ 2 * continuousKGradientNorm G ^ 2 =
          (t.1 * continuousKGradientNorm G) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg]
      exact mul_nonneg t.2.1.le (continuousKGradientNorm_nonneg G)

private theorem interpolationWeight_lintegral (s : FractionalOrder) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.rpow t (1 - 2 * s.1))) =
      ENNReal.ofReal ((2 - 2 * s.1)⁻¹) := by
  let r : ℝ := 1 - 2 * s.1
  have hr : -1 < r := by
    dsimp [r]
    linarith only [FractionalOrder.lt_one s]
  have hint : IntegrableOn (fun t : ℝ ↦ Real.rpow t r) (Set.Ioo (0 : ℝ) 1) := by
    have hi : IntervalIntegrable (fun t : ℝ ↦ Real.rpow t r)
        MeasureTheory.volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' hr
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp hi
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)]
      fun t : ℝ ↦ Real.rpow t r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le r
  have hformula :
      ∫ t in Set.Ioo (0 : ℝ) 1, Real.rpow t r = (r + 1)⁻¹ := by
    calc
      ∫ t in Set.Ioo (0 : ℝ) 1, Real.rpow t r =
          ∫ t in (0 : ℝ)..1, Real.rpow t r := by
        rw [intervalIntegral.integral_of_le (by norm_num)]
        exact integral_Ioc_eq_integral_Ioo.symm
      _ = (Real.rpow 1 (r + 1) - Real.rpow 0 (r + 1)) / (r + 1) :=
        integral_rpow (Or.inl hr)
      _ = (r + 1)⁻¹ := by
        have hr1 : 0 < r + 1 := by linarith only [hr]
        norm_num [Real.zero_rpow hr1.ne']
  rw [show (fun t : ℝ ↦ ENNReal.ofReal (Real.rpow t (1 - 2 * s.1))) =
      fun t : ℝ ↦ ENNReal.ofReal (Real.rpow t r) by rfl]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    hformula]
  congr 2
  dsimp [r]
  ring

/-- A coordinatewise H1 representative controls the continuous interpolation
seminorm by its normalized weak-gradient energy. -/
theorem continuousKSeminorm_le_gradientNorm_of_eq_toField {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (G : ContinuousKCompetitor d) (hFG : F.toField = G.toField) :
    continuousKSeminorm s F ≤
      (ENNReal.ofReal ((2 - 2 * s.1)⁻¹)) ^ ((2 : ℝ)⁻¹) *
        ENNReal.ofReal (continuousKGradientNorm G) := by
  let B : ℝ := continuousKGradientNorm G
  have hB : 0 ≤ B := continuousKGradientNorm_nonneg G
  have hintegrand : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      continuousKSeminormIntegrand s.1 F t ≤
        ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) *
          (ENNReal.ofReal B) ^ (2 : ℕ) := by
    intro t ht
    let kt : ContinuousKScale := ⟨t, ⟨ht.1, ht.2.le⟩⟩
    have hK := continuousKFunctional_le_scale_mul_gradientNorm kt F G hFG
    have hKsq : continuousKFunctional kt F ^ 2 ≤ (t * B) ^ 2 :=
      (sq_le_sq₀ (continuousKFunctional_nonneg kt F)
        (mul_nonneg ht.1.le hB)).2 hK
    rw [continuousKSeminormIntegrand_eq_of_mem s.1 F ht]
    calc
      ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
          ENNReal.ofReal (continuousKFunctional kt F ^ 2) *
            ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
          ENNReal.ofReal ((t * B) ^ 2) * ENNReal.ofReal t⁻¹ := by
            gcongr
      _ = ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) *
          (ENNReal.ofReal B) ^ (2 : ℕ) := by
        have htinv : t⁻¹ = Real.rpow t (-1 : ℝ) := by
          exact (Real.rpow_neg_one t).symm
        have ht2 : t ^ (2 : ℕ) = Real.rpow t (2 : ℝ) :=
          (Real.rpow_natCast t 2).symm
        have htpow : Real.rpow t (-2 * s.1) * t ^ 2 * t⁻¹ =
            Real.rpow t (1 - 2 * s.1) := by
          calc
            Real.rpow t (-2 * s.1) * t ^ 2 * t⁻¹ =
                (Real.rpow t (-2 * s.1) * Real.rpow t (2 : ℝ)) *
                  Real.rpow t (-1 : ℝ) := by
                    rw [ht2, htinv]
            _ = Real.rpow t (-2 * s.1 + 2) * Real.rpow t (-1 : ℝ) := by
              exact congrArg (fun z : ℝ ↦ z * Real.rpow t (-1 : ℝ))
                (Real.rpow_add ht.1 (-2 * s.1) 2).symm
            _ = Real.rpow t ((-2 * s.1 + 2) + (-1 : ℝ)) := by
              exact (Real.rpow_add ht.1 (-2 * s.1 + 2) (-1 : ℝ)).symm
            _ = Real.rpow t (1 - 2 * s.1) := by ring_nf
        have hreal : Real.rpow t (-2 * s.1) * (t * B) ^ 2 * t⁻¹ =
            Real.rpow t (1 - 2 * s.1) * B ^ 2 := by
          calc
            Real.rpow t (-2 * s.1) * (t * B) ^ 2 * t⁻¹ =
                (Real.rpow t (-2 * s.1) * t ^ 2 * t⁻¹) * B ^ 2 := by ring
            _ = Real.rpow t (1 - 2 * s.1) * B ^ 2 := by rw [htpow]
        calc
          ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
              ENNReal.ofReal ((t * B) ^ 2) * ENNReal.ofReal t⁻¹ =
            ENNReal.ofReal
              (Real.rpow t (-2 * s.1) * (t * B) ^ 2 * t⁻¹) := by
                symm
                calc
                  ENNReal.ofReal
                      (Real.rpow t (-2 * s.1) * (t * B) ^ 2 * t⁻¹) =
                    ENNReal.ofReal (Real.rpow t (-2 * s.1) * (t * B) ^ 2) *
                      ENNReal.ofReal t⁻¹ :=
                        ENNReal.ofReal_mul (mul_nonneg
                          (Real.rpow_nonneg ht.1.le _) (sq_nonneg (t * B)))
                  _ = (ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
                        ENNReal.ofReal ((t * B) ^ 2)) * ENNReal.ofReal t⁻¹ := by
                    exact congrArg
                      (fun z : ℝ≥0∞ ↦ z * ENNReal.ofReal t⁻¹)
                      (ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _))
          _ = ENNReal.ofReal (Real.rpow t (1 - 2 * s.1) * B ^ 2) := by
            rw [hreal]
          _ = ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) *
              (ENNReal.ofReal B) ^ (2 : ℕ) := by
            calc
              ENNReal.ofReal (Real.rpow t (1 - 2 * s.1) * B ^ 2) =
                  ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) *
                    ENNReal.ofReal (B ^ 2) :=
                ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _)
              _ = ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) *
                    (ENNReal.ofReal B) ^ (2 : ℕ) := by
                rw [ENNReal.ofReal_pow hB]
  rw [continuousKSeminorm_eq_lintegral]
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        continuousKSeminormIntegrand s.1 F t) ^ (1 / 2 : ℝ) ≤
      ((∫⁻ t in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (Real.rpow t (1 - 2 * s.1)) *
            (ENNReal.ofReal B) ^ (2 : ℕ))) ^ (1 / 2 : ℝ) := by
        apply ENNReal.rpow_le_rpow
        · exact setLIntegral_mono' measurableSet_Ioo hintegrand
        · norm_num
    _ = ((∫⁻ t in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (Real.rpow t (1 - 2 * s.1))) *
            (ENNReal.ofReal B) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
      rw [lintegral_mul_const']
      exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    _ = (ENNReal.ofReal ((2 - 2 * s.1)⁻¹) *
          (ENNReal.ofReal B) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
      rw [interpolationWeight_lintegral]
    _ = (ENNReal.ofReal ((2 - 2 * s.1)⁻¹)) ^ ((2 : ℝ)⁻¹) *
        ENNReal.ofReal B := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

end

end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.UnitCubeDirichletContinuousKLowScaleIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# High-contrast homogenization: Provider.Regularity.UnitCubeDirichletContinuousKIntegralSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Split continuous K-energy for the unit-cube Dirichlet map

The low-scale rescaling estimate is paired with the complementary root-scale
interval.  On that interval the zero competitor and the exact normalized
Euclidean `L²` energy inequality give a closed-form endpoint contribution.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

@[expose]
public noncomputable def unitCubeEuclideanL2FieldToCenteredCubeZero
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    CenteredCubeEuclideanL2Field d 0 where
  toField := F
  euclideanMemL2 := by
    simpa only [centeredCubeDomain, unitCenteredCubeDomain] using F.euclideanMemL2

@[simp] private theorem unitCubeEuclideanL2FieldToCenteredCubeZero_apply
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) (x : Vec d) :
    unitCubeEuclideanL2FieldToCenteredCubeZero F x = F x :=
  rfl

private theorem unitCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_le
    {d : ℕ} [NeZero d] (h : UnitCubeEuclideanL2Field d)
    (w : H10Function (openCubeSet (originCube d 0)))
    (hproblem : CubeDirichletDivergenceProblem (originCube d 0) w h) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (unitCubeGradientEuclideanL2Field w) ≤
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) h := by
  have hbound :=
    centeredCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_le
      (unitCubeEuclideanL2FieldToCenteredCubeZero h) w
      (by
        simpa only [unitCubeEuclideanL2FieldToCenteredCubeZero_apply] using! hproblem)
  simpa only [centeredCubeDomain, unitCenteredCubeDomain,
    unitCubeEuclideanL2FieldToCenteredCubeZero_apply,
    centeredCubeGradientEuclideanL2Field_apply,
    unitCubeGradientEuclideanL2Field_apply] using! hbound

private theorem continuousKGradientNorm_default_eq_zero {d : ℕ} :
    continuousKGradientNorm (default : ContinuousKCompetitor d) = 0 := by
  unfold continuousKGradientNorm
  calc
    (unitCenteredCubeDomain d).normalizedLpNorm (2 : ℝ≥0∞)
        (fun x => matrixFrobeniusMagnitude
          ((default : ContinuousKCompetitor d).gradient x))
        (default : ContinuousKCompetitor d).gradientFrobeniusMemL2 =
      (unitCenteredCubeDomain d).normalizedLpNorm (2 : ℝ≥0∞)
        (fun _ => (0 : ℝ)) MeasureTheory.MemLp.zero' := by
          apply BoundedMeasurableDomain.normalizedLpNorm_congr_ae
          filter_upwards [] with x
          rw [show (default : ContinuousKCompetitor d).gradient x = 0 by
            ext i j
            rfl]
          exact matrixFrobeniusMagnitude_zero
    _ = 0 := by
      unfold BoundedMeasurableDomain.normalizedLpNorm
        BoundedMeasurableDomain.normalizedLpFiniteENorm
        BoundedMeasurableDomain.normalizedLpENorm
      simp

private theorem ofReal_continuousKResidualNorm_default_eq_normalizedEuclideanLpENorm
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    ENNReal.ofReal
        (continuousKResidualNorm F (default : ContinuousKCompetitor d)) =
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F := by
  have hresidual :
      (fun x => euclideanNorm (F x - (default : ContinuousKCompetitor d).toField x)) =
        fun x => euclideanNorm (F x) := by
    funext x
    rw [show (default : ContinuousKCompetitor d).toField x = 0 by
      ext i
      rfl]
    exact congrArg euclideanNorm (sub_zero (F x))
  unfold continuousKResidualNorm BoundedMeasurableDomain.normalizedEuclideanLpNorm
    BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpNorm
    BoundedMeasurableDomain.normalizedLpFiniteENorm
    BoundedMeasurableDomain.normalizedLpENorm
  change ENNReal.ofReal
      (MeasureTheory.eLpNorm
        (fun x => euclideanNorm (F x - (default : ContinuousKCompetitor d).toField x))
        (2 : ℝ≥0∞) (unitCenteredCubeDomain d).normalizedVolume).toReal =
    MeasureTheory.eLpNorm (fun x => euclideanNorm (F x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume
  rw [hresidual, ENNReal.ofReal_toReal F.euclideanMagnitudeMemL2.eLpNorm_ne_top]

private theorem continuousKFunctional_le_residualNorm_default {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) :
    continuousKFunctional t F ≤
      continuousKResidualNorm F (default : ContinuousKCompetitor d) := by
  calc
    continuousKFunctional t F ≤
        continuousKFunctionalCompetitorValue t F default :=
      continuousKFunctional_le_competitor t F default
    _ = continuousKResidualNorm F default := by
      unfold continuousKFunctionalCompetitorValue
      rw [continuousKGradientNorm_default_eq_zero]
      simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero,
        Real.sqrt_sq_eq_abs,
        abs_of_nonneg (continuousKResidualNorm_nonneg F default)]

private theorem normalizedEuclideanLpENorm_lt_top {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F < ∞ := by
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm] using
    F.euclideanMagnitudeMemL2.eLpNorm_lt_top

private theorem continuousKWeight_eq_single_rpow
    {t sigma : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Real.rpow t (-2 * sigma)) * ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal (Real.rpow t (-2 * sigma - 1)) := by
  have hinv : Real.rpow t (-1 : ℝ) = t⁻¹ := Real.rpow_neg_one t
  have hadd :
      Real.rpow t (-2 * sigma) * Real.rpow t (-1 : ℝ) =
        Real.rpow t (-2 * sigma - 1) := by
    calc
      Real.rpow t (-2 * sigma) * Real.rpow t (-1 : ℝ) =
          Real.rpow t (-2 * sigma + (-1 : ℝ)) :=
        (Real.rpow_add ht (-2 * sigma) (-1 : ℝ)).symm
      _ = Real.rpow t (-2 * sigma - 1) := by
        congr 1
  calc
    ENNReal.ofReal (Real.rpow t (-2 * sigma)) * ENNReal.ofReal t⁻¹ =
        ENNReal.ofReal (Real.rpow t (-2 * sigma) * t⁻¹) :=
      (ENNReal.ofReal_mul (Real.rpow_nonneg ht.le (-2 * sigma))).symm
    _ = ENNReal.ofReal (Real.rpow t (-2 * sigma) *
        Real.rpow t (-1 : ℝ)) := by rw [hinv]
    _ = ENNReal.ofReal (Real.rpow t (-2 * sigma - 1)) :=
      congrArg ENNReal.ofReal hadd

private theorem continuousKWeight_lintegral_inv_one
    {A : ℝ} (honeA : 1 ≤ A) (s : FractionalOrder) :
    (∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ),
        ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹) =
      ENNReal.ofReal
        ((Real.rpow A (2 * s.1) - 1) / (2 * s.1)) := by
  have hA : 0 < A := zero_lt_one.trans_le honeA
  have hinvPos : 0 < A⁻¹ := inv_pos.mpr hA
  have hinvOne : A⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ honeA
  let r : ℝ := -2 * s.1 - 1
  have hzero : (0 : ℝ) ∉ Set.uIcc A⁻¹ 1 := by
    rw [Set.uIcc_of_le hinvOne]
    intro hmem
    exact (not_lt_of_ge hmem.1) hinvPos
  have hrne : r ≠ -1 := by
    have hmul : (-2 : ℝ) * s.1 ≠ 0 :=
      mul_ne_zero (by norm_num) (FractionalOrder.pos s).ne'
    intro hr
    apply hmul
    calc
      (-2 : ℝ) * s.1 = r + 1 := by simp only [r]; ring
      _ = -1 + 1 := congrArg (fun x : ℝ => x + 1) hr
      _ = 0 := by ring
  have hinterval : IntervalIntegrable (fun t : ℝ => Real.rpow t r)
      MeasureTheory.volume A⁻¹ 1 :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have hintegrable : IntegrableOn (fun t : ℝ => Real.rpow t r)
      (Set.Ioo A⁻¹ 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hinvOne).mp hinterval
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo A⁻¹ 1)]
      fun t : ℝ => Real.rpow t r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg (hinvPos.trans ht.1).le r
  have hlintegral :
      (∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ), ENNReal.ofReal (Real.rpow t r)) =
        ENNReal.ofReal (∫ t in Set.Ioo A⁻¹ (1 : ℝ), Real.rpow t r) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintegrable hnonneg).symm
  have hinvRpow : Real.rpow A⁻¹ (-(2 * s.1)) =
      Real.rpow A (2 * s.1) := by
    simpa only [inv_inv] using!
      (Real.rpow_neg_eq_inv_rpow A⁻¹ (2 * s.1))
  have hintegral :
      (∫ t in Set.Ioo A⁻¹ (1 : ℝ), Real.rpow t r) =
        (Real.rpow A (2 * s.1) - 1) / (2 * s.1) := by
    have hformula :
        (∫ t in A⁻¹..(1 : ℝ), Real.rpow t r) =
          (Real.rpow 1 (r + 1) - Real.rpow A⁻¹ (r + 1)) / (r + 1) :=
      integral_rpow (Or.inr ⟨hrne, hzero⟩)
    have hexponent : r + 1 = -(2 * s.1) := by
      simp only [r]
      ring
    have honeRpow : Real.rpow (1 : ℝ) (r + 1) = 1 := Real.one_rpow (r + 1)
    calc
      (∫ t in Set.Ioo A⁻¹ (1 : ℝ), Real.rpow t r) =
          ∫ t in Set.Ioc A⁻¹ (1 : ℝ), Real.rpow t r :=
        integral_Ioc_eq_integral_Ioo.symm
      _ = ∫ t in A⁻¹..(1 : ℝ), Real.rpow t r :=
        (intervalIntegral.integral_of_le hinvOne).symm
      _ = (Real.rpow 1 (r + 1) - Real.rpow A⁻¹ (r + 1)) / (r + 1) :=
        hformula
      _ = (Real.rpow A (2 * s.1) - 1) / (2 * s.1) := by
        rw [honeRpow, hexponent, hinvRpow]
        ring
  calc
    (∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ),
        ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹) =
        ∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ), ENNReal.ofReal (Real.rpow t r) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simpa only [r] using continuousKWeight_eq_single_rpow
        (hinvPos.trans ht.1) (sigma := s.1)
    _ = ENNReal.ofReal (∫ t in Set.Ioo A⁻¹ (1 : ℝ), Real.rpow t r) :=
      hlintegral
    _ = ENNReal.ofReal
        ((Real.rpow A (2 * s.1) - 1) / (2 * s.1)) :=
      congrArg ENNReal.ofReal hintegral

/-- One dimension-dependent expansion factor, fixed before all analytic
inputs, simultaneously gives the exact low-scale rescaling bound and the
closed-form normalized-`L²` bound on the complementary root interval. -/
theorem exists_unitCubeDirichletContinuousKIntegralSplitBound
    (d : ℕ) [NeZero d] :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (s : FractionalOrder) (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0))),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          ((∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹,
                continuousKSeminormIntegrand s.1
                  (unitCubeGradientEuclideanL2Field w) t) ≤
              (ENNReal.ofReal A) ^ (2 * s.1) *
                ∫⁻ u in Set.Ioo (0 : ℝ) 1,
                  continuousKSeminormIntegrand s.1 h u) ∧
            ((∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ),
                continuousKSeminormIntegrand s.1
                  (unitCubeGradientEuclideanL2Field w) t) ≤
              ENNReal.ofReal
                  ((Real.rpow A (2 * s.1) - 1) / (2 * s.1)) *
                ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
                  (2 : ℝ≥0∞) h) ^ 2) := by
  rcases exists_unitCubeDirichletContinuousKLowScaleIntegralBound d with
    ⟨A, honeA, hlow⟩
  have hA : 0 < A := zero_lt_one.trans_le honeA
  have hinvPos : 0 < A⁻¹ := inv_pos.mpr hA
  refine ⟨A, honeA, ?_⟩
  intro s h w hproblem
  refine ⟨hlow s h w hproblem, ?_⟩
  let out : UnitCubeEuclideanL2Field d := unitCubeGradientEuclideanL2Field w
  let Lout : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) out
  let Lin : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) h
  have henergy : Lout ≤ Lin := by
    simpa only [Lout, Lin, out] using
      unitCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_le h w hproblem
  have hLinTop : Lin < ∞ := by
    simpa only [Lin] using normalizedEuclideanLpENorm_lt_top h
  have hintegrand : ∀ t ∈ Set.Ioo A⁻¹ (1 : ℝ),
      continuousKSeminormIntegrand s.1 out t ≤
        (ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹) *
          Lin ^ 2 := by
    intro t ht
    have htOpen : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨hinvPos.trans ht.1, ht.2⟩
    let kt : ContinuousKScale := ⟨t, ⟨htOpen.1, htOpen.2.le⟩⟩
    have hK := continuousKFunctional_le_residualNorm_default kt out
    have hKsq : continuousKFunctional kt out ^ 2 ≤
        continuousKResidualNorm out (default : ContinuousKCompetitor d) ^ 2 :=
      (sq_le_sq₀ (continuousKFunctional_nonneg kt out)
        (continuousKResidualNorm_nonneg out default)).mpr hK
    have hKsqEndpoint :
        ENNReal.ofReal (continuousKFunctional kt out ^ 2) ≤ Lin ^ 2 := by
      calc
        ENNReal.ofReal (continuousKFunctional kt out ^ 2) ≤
            ENNReal.ofReal
              (continuousKResidualNorm out (default : ContinuousKCompetitor d) ^ 2) :=
          ENNReal.ofReal_le_ofReal hKsq
        _ = ENNReal.ofReal
              (continuousKResidualNorm out (default : ContinuousKCompetitor d)) ^ 2 := by
          rw [ENNReal.ofReal_pow (continuousKResidualNorm_nonneg out default)]
        _ = Lout ^ 2 := by
          rw [ofReal_continuousKResidualNorm_default_eq_normalizedEuclideanLpENorm]
        _ ≤ Lin ^ 2 := by
          gcongr
    rw [continuousKSeminormIntegrand_eq_of_mem s.1 out htOpen]
    change
      ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
          ENNReal.ofReal (continuousKFunctional kt out ^ 2) * ENNReal.ofReal t⁻¹ ≤
        (ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹) *
          Lin ^ 2
    calc
      ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
          ENNReal.ofReal (continuousKFunctional kt out ^ 2) * ENNReal.ofReal t⁻¹ =
        (ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹) *
          ENNReal.ofReal (continuousKFunctional kt out ^ 2) := by
        ring
      _ ≤ (ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹) *
          Lin ^ 2 := by
        simpa only [mul_comm] using
          (mul_le_mul_left hKsqEndpoint
            (ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹))
  calc
    (∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ),
        continuousKSeminormIntegrand s.1
          (unitCubeGradientEuclideanL2Field w) t) =
        ∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ),
          continuousKSeminormIntegrand s.1 out t := rfl
    _ ≤ ∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ),
        (ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹) *
          Lin ^ 2 :=
      setLIntegral_mono' measurableSet_Ioo hintegrand
    _ = (∫⁻ t in Set.Ioo A⁻¹ (1 : ℝ),
          ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹) *
        Lin ^ 2 := by
      rw [lintegral_mul_const' _ _
        (ENNReal.pow_ne_top (ne_of_lt hLinTop))]
    _ = ENNReal.ofReal
          ((Real.rpow A (2 * s.1) - 1) / (2 * s.1)) * Lin ^ 2 := by
      rw [continuousKWeight_lintegral_inv_one honeA s]

end

end HighContrast
end HCPolySupport

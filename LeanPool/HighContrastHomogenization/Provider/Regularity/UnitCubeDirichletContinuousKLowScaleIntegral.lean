/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.UnitCubeDirichletContinuousKRescaling
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# High-contrast homogenization: Provider.Regularity.UnitCubeDirichletContinuousKLowScaleIntegral

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Low-scale continuous K-energy for the unit-cube Dirichlet map

The exact rescaled pointwise comparison is integrated on the interval where
the expanded parameter remains in the source carrier.  The Jacobian and the
interpolation weight combine to give precisely the factor `A^(2s)`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem continuousKWeight_rescale
    {A t sigma : ℝ} (hA : 0 < A) (ht : 0 < t) :
    ENNReal.ofReal (Real.rpow t (-2 * sigma)) * ENNReal.ofReal t⁻¹ =
      (ENNReal.ofReal A) ^ (2 * sigma) * ENNReal.ofReal A *
        (ENNReal.ofReal (Real.rpow (A * t) (-2 * sigma)) *
          ENNReal.ofReal (A * t)⁻¹) := by
  have hpowCancel : Real.rpow A (2 * sigma) * Real.rpow A (-2 * sigma) = 1 := by
    have hneg : Real.rpow A (-2 * sigma) =
        (Real.rpow A (2 * sigma))⁻¹ := by
      rw [show -2 * sigma = -(2 * sigma) by ring]
      exact Real.rpow_neg hA.le (2 * sigma)
    rw [hneg]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hA (2 * sigma)).ne'
  have hreal :
      Real.rpow t (-2 * sigma) * t⁻¹ =
        Real.rpow A (2 * sigma) * A *
          (Real.rpow (A * t) (-2 * sigma) * (A * t)⁻¹) := by
    have hmul : Real.rpow (A * t) (-2 * sigma) =
        Real.rpow A (-2 * sigma) * Real.rpow t (-2 * sigma) :=
      Real.mul_rpow hA.le ht.le
    rw [hmul, mul_inv]
    calc
      Real.rpow t (-2 * sigma) * t⁻¹ =
          (Real.rpow A (2 * sigma) * Real.rpow A (-2 * sigma)) *
            (A * A⁻¹) * (Real.rpow t (-2 * sigma) * t⁻¹) := by
        rw [hpowCancel, mul_inv_cancel₀ hA.ne']
        ring
      _ = Real.rpow A (2 * sigma) * A *
          (Real.rpow A (-2 * sigma) * Real.rpow t (-2 * sigma) *
            (A⁻¹ * t⁻¹)) := by
        ring
  calc
    ENNReal.ofReal (Real.rpow t (-2 * sigma)) * ENNReal.ofReal t⁻¹ =
        ENNReal.ofReal (Real.rpow t (-2 * sigma) * t⁻¹) := by
      exact (ENNReal.ofReal_mul (Real.rpow_nonneg ht.le (-2 * sigma))).symm
    _ = ENNReal.ofReal
        (Real.rpow A (2 * sigma) * A *
          (Real.rpow (A * t) (-2 * sigma) * (A * t)⁻¹)) :=
      congrArg ENNReal.ofReal hreal
    _ = ENNReal.ofReal (Real.rpow A (2 * sigma)) * ENNReal.ofReal A *
        (ENNReal.ofReal (Real.rpow (A * t) (-2 * sigma)) *
          ENNReal.ofReal (A * t)⁻¹) := by
      calc
        ENNReal.ofReal
            (Real.rpow A (2 * sigma) * A *
              (Real.rpow (A * t) (-2 * sigma) * (A * t)⁻¹)) =
            ENNReal.ofReal (Real.rpow A (2 * sigma) * A) *
              ENNReal.ofReal
                (Real.rpow (A * t) (-2 * sigma) * (A * t)⁻¹) :=
          ENNReal.ofReal_mul
            (mul_nonneg (Real.rpow_nonneg hA.le (2 * sigma)) hA.le)
        _ = (ENNReal.ofReal (Real.rpow A (2 * sigma)) * ENNReal.ofReal A) *
              (ENNReal.ofReal (Real.rpow (A * t) (-2 * sigma)) *
                ENNReal.ofReal (A * t)⁻¹) := by
          have hAprod :
              ENNReal.ofReal (Real.rpow A (2 * sigma) * A) =
                ENNReal.ofReal (Real.rpow A (2 * sigma)) * ENNReal.ofReal A :=
            ENNReal.ofReal_mul (Real.rpow_nonneg hA.le (2 * sigma))
          have hAtprod :
              ENNReal.ofReal
                  (Real.rpow (A * t) (-2 * sigma) * (A * t)⁻¹) =
                ENNReal.ofReal (Real.rpow (A * t) (-2 * sigma)) *
                  ENNReal.ofReal (A * t)⁻¹ :=
            ENNReal.ofReal_mul
              (Real.rpow_nonneg (mul_nonneg hA.le ht.le) (-2 * sigma))
          rw [hAprod, hAtprod]
        _ = ENNReal.ofReal (Real.rpow A (2 * sigma)) * ENNReal.ofReal A *
              (ENNReal.ofReal (Real.rpow (A * t) (-2 * sigma)) *
                ENNReal.ofReal (A * t)⁻¹) := by
          ring
    _ = (ENNReal.ofReal A) ^ (2 * sigma) * ENNReal.ofReal A *
        (ENNReal.ofReal (Real.rpow (A * t) (-2 * sigma)) *
          ENNReal.ofReal (A * t)⁻¹) := by
      have hOfRealRpow : ENNReal.ofReal (Real.rpow A (2 * sigma)) =
          (ENNReal.ofReal A) ^ (2 * sigma) :=
        (ENNReal.ofReal_rpow_of_pos hA).symm
      rw [hOfRealRpow]

/-- A dimension-dependent expansion factor can be selected before the
fractional order, datum, and solution so that the low-scale continuous
`K`-energy is bounded with the exact factor `A^(2s)`. -/
theorem exists_unitCubeDirichletContinuousKLowScaleIntegralBound
    (d : ℕ) [NeZero d] :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (s : FractionalOrder) (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0))),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          (∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹,
              continuousKSeminormIntegrand s.1
                (unitCubeGradientEuclideanL2Field w) t) ≤
            (ENNReal.ofReal A) ^ (2 * s.1) *
              ∫⁻ u in Set.Ioo (0 : ℝ) 1,
                continuousKSeminormIntegrand s.1 h u := by
  rcases exists_unitCubeDirichletContinuousKFunctional_rescaled d with
    ⟨A, honeA, hpoint⟩
  have hA : 0 < A := zero_lt_one.trans_le honeA
  refine ⟨A, honeA, ?_⟩
  intro s h w hproblem
  let out : UnitCubeEuclideanL2Field d := unitCubeGradientEuclideanL2Field w
  let c : ℝ≥0∞ := (ENNReal.ofReal A) ^ (2 * s.1)
  have hintegrand : ∀ t ∈ Set.Ioo (0 : ℝ) A⁻¹,
      continuousKSeminormIntegrand s.1 out t ≤
        c * (ENNReal.ofReal A * continuousKSeminormIntegrand s.1 h (A * t)) := by
    intro t ht
    have htOpen : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨ht.1, ht.2.trans_le (inv_le_one_of_one_le₀ honeA)⟩
    have hAtOpen : A * t ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨mul_pos hA ht.1, ?_⟩
      calc
        A * t < A * A⁻¹ := mul_lt_mul_of_pos_left ht.2 hA
        _ = 1 := mul_inv_cancel₀ hA.ne'
    let kt : ContinuousKScale := ⟨t, ⟨ht.1, htOpen.2.le⟩⟩
    let ku : ContinuousKScale :=
      ⟨A * t, ⟨hAtOpen.1, hAtOpen.2.le⟩⟩
    have hK : continuousKFunctional kt out ≤ continuousKFunctional ku h := by
      simpa only [kt, ku, out] using hpoint h w kt ku hproblem rfl
    have hKsq : continuousKFunctional kt out ^ 2 ≤
        continuousKFunctional ku h ^ 2 :=
      (sq_le_sq₀ (continuousKFunctional_nonneg kt out)
        (continuousKFunctional_nonneg ku h)).mpr hK
    have hKsqOfReal :
        ENNReal.ofReal (continuousKFunctional kt out ^ 2) ≤
          ENNReal.ofReal (continuousKFunctional ku h ^ 2) :=
      ENNReal.ofReal_le_ofReal hKsq
    rw [continuousKSeminormIntegrand_eq_of_mem s.1 out htOpen,
      continuousKSeminormIntegrand_eq_of_mem s.1 h hAtOpen]
    change
      ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
          ENNReal.ofReal (continuousKFunctional kt out ^ 2) * ENNReal.ofReal t⁻¹ ≤
        c * (ENNReal.ofReal A *
          (ENNReal.ofReal (Real.rpow (A * t) (-2 * s.1)) *
            ENNReal.ofReal (continuousKFunctional ku h ^ 2) *
              ENNReal.ofReal (A * t)⁻¹))
    calc
      ENNReal.ofReal (Real.rpow t (-2 * s.1)) *
          ENNReal.ofReal (continuousKFunctional kt out ^ 2) * ENNReal.ofReal t⁻¹ =
        (ENNReal.ofReal (Real.rpow t (-2 * s.1)) * ENNReal.ofReal t⁻¹) *
          ENNReal.ofReal (continuousKFunctional kt out ^ 2) := by
            ring
      _ = (c * ENNReal.ofReal A *
          (ENNReal.ofReal (Real.rpow (A * t) (-2 * s.1)) *
            ENNReal.ofReal (A * t)⁻¹)) *
          ENNReal.ofReal (continuousKFunctional kt out ^ 2) := by
        rw [continuousKWeight_rescale hA ht.1]
      _ ≤ (c * ENNReal.ofReal A *
          (ENNReal.ofReal (Real.rpow (A * t) (-2 * s.1)) *
            ENNReal.ofReal (A * t)⁻¹)) *
          ENNReal.ofReal (continuousKFunctional ku h ^ 2) := by
        simpa only [mul_comm] using
          (mul_le_mul_left hKsqOfReal
            (c * ENNReal.ofReal A *
              (ENNReal.ofReal (Real.rpow (A * t) (-2 * s.1)) *
                ENNReal.ofReal (A * t)⁻¹)))
      _ = c * (ENNReal.ofReal A *
          (ENNReal.ofReal (Real.rpow (A * t) (-2 * s.1)) *
            ENNReal.ofReal (continuousKFunctional ku h ^ 2) *
              ENNReal.ofReal (A * t)⁻¹)) := by
        ring
  have hchange :
      (∫⁻ u in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 h u) =
        ∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹,
          ENNReal.ofReal A * continuousKSeminormIntegrand s.1 h (A * t) := by
    have hraw := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
      (s := Set.Ioo (0 : ℝ) A⁻¹) (f := fun t : ℝ => A * t)
      (f' := fun _ : ℝ => A) measurableSet_Ioo
      (fun x _ => (hasDerivAt_const_mul A).hasDerivWithinAt)
      (fun _ _ _ _ hxy => mul_left_cancel₀ hA.ne' hxy)
      (continuousKSeminormIntegrand s.1 h)
    have himage : (fun t : ℝ => A * t) '' Set.Ioo (0 : ℝ) A⁻¹ =
        Set.Ioo (0 : ℝ) 1 := by
      simpa only [mul_zero, mul_inv_cancel₀ hA.ne'] using
        (Set.image_mul_left_Ioo hA (0 : ℝ) A⁻¹)
    rw [himage] at hraw
    simpa only [abs_of_pos hA] using hraw
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹,
        continuousKSeminormIntegrand s.1
          (unitCubeGradientEuclideanL2Field w) t) =
        ∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹,
          continuousKSeminormIntegrand s.1 out t := rfl
    _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹,
          c * (ENNReal.ofReal A * continuousKSeminormIntegrand s.1 h (A * t)) :=
      setLIntegral_mono' measurableSet_Ioo hintegrand
    _ = c * ∫⁻ t in Set.Ioo (0 : ℝ) A⁻¹,
          ENNReal.ofReal A * continuousKSeminormIntegrand s.1 h (A * t) := by
      rw [lintegral_const_mul' _ _
        (ne_of_lt (ENNReal.rpow_lt_top_of_nonneg
          (mul_nonneg (by norm_num) (FractionalOrder.pos s).le)
            ENNReal.ofReal_ne_top))]
    _ = (ENNReal.ofReal A) ^ (2 * s.1) *
        ∫⁻ u in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand s.1 h u := by
      rw [hchange]

end

end HighContrast
end HCPolySupport

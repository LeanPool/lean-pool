/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.DampedShellMoments

/-!
# Literal damped spatial Fourier kernels on complex affine lines

All bounds retain the physical energy, use the real spatial inner product, and
lose only half the damping on a stated strip. They will supply actual dominated
complex differentiation; no analytic continuation theorem is postulated.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate

/-- Damped spatial kernel defined as `Complex.exp (-(a : ℂ) * (dispersion m p : ℂ) - Complex.I *
((⟪p, x⟫_ℝ : ℂ) + z * (⟪p, v⟫_ℝ : ℂ)))`. -/
noncomputable def dampedSpatialKernel (m a : ℝ)
    (x v : EuclideanSpace ℝ (Fin 3)) (z : ℂ) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (-(a : ℂ) * (dispersion m p : ℂ) -
    Complex.I * ((⟪p, x⟫_ℝ : ℂ) + z * (⟪p, v⟫_ℝ : ℂ)))

theorem continuous_dampedSpatialKernel (m a : ℝ)
    (x v : EuclideanSpace ℝ (Fin 3)) (z : ℂ) :
    Continuous (dampedSpatialKernel m a x v z) := by
  unfold dampedSpatialKernel
  have hω := continuous_dispersion m
  fun_prop

theorem hasDerivAt_dampedSpatialKernel (m a : ℝ)
    (x v : EuclideanSpace ℝ (Fin 3)) (z : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun w => dampedSpatialKernel m a x v w p)
      (dampedSpatialKernel m a x v z p * (-Complex.I * (⟪p, v⟫_ℝ : ℂ))) z := by
  have h := ((hasDerivAt_const z (-(a : ℂ) * (dispersion m p : ℂ))).sub
    ((hasDerivAt_const z Complex.I).mul
      ((hasDerivAt_const z (⟪p, x⟫_ℝ : ℂ)).add
        ((hasDerivAt_id z).mul_const (⟪p, v⟫_ℝ : ℂ))))).cexp
  simpa [dampedSpatialKernel, mul_neg, neg_mul] using h

theorem norm_dampedSpatialKernel (m a : ℝ)
    (x v : EuclideanSpace ℝ (Fin 3)) (z : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖dampedSpatialKernel m a x v z p‖ =
      Real.exp (-a * dispersion m p + z.im * ⟪p, v⟫_ℝ) := by
  rw [dampedSpatialKernel, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_dampedShellAmplitude {m : ℝ} (a : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖dampedShellAmplitude a ψ p‖ = Real.exp (-a * dispersion m p) * ‖ψ p‖ := by
  simp only [dampedShellAmplitude, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_conj]

theorem norm_dampedSpatialKernel_mul_le {m a b : ℝ} (hm : 0 < m)
    (x v : EuclideanSpace ℝ (Fin 3)) (hbv : b * ‖v‖ ≤ a / 2)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) {z : ℂ} (hz : |z.im| ≤ b)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖dampedSpatialKernel m a x v z p * conj (ψ p)‖ ≤
      ‖dampedShellAmplitude (a / 2) ψ p‖ := by
  have hω : 0 ≤ dispersion m p := hm.le.trans (le_dispersion hm.le p)
  have hdot : |⟪p, v⟫_ℝ| ≤ dispersion m p * ‖v‖ :=
    (abs_real_inner_le_norm p v).trans (mul_le_mul_of_nonneg_right (norm_le_dispersion m p)
      (norm_nonneg _))
  have hphase : z.im * ⟪p, v⟫_ℝ ≤ (a / 2) * dispersion m p := by
    calc
      _ ≤ |z.im| * |⟪p, v⟫_ℝ| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ b * (dispersion m p * ‖v‖) :=
        mul_le_mul hz hdot (abs_nonneg _) (le_trans (abs_nonneg _) hz)
      _ = (b * ‖v‖) * dispersion m p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbv hω
  rw [norm_mul, norm_dampedSpatialKernel, Complex.norm_conj, norm_dampedShellAmplitude]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  linarith

theorem norm_dampedSpatialKernel_derivative_mul_le {m a b : ℝ} (hm : 0 < m)
    (x v : EuclideanSpace ℝ (Fin 3)) (hbv : b * ‖v‖ ≤ a / 2)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) {z : ℂ} (hz : |z.im| ≤ b)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖dampedSpatialKernel m a x v z p * (-Complex.I * (⟪p, v⟫_ℝ : ℂ)) * conj (ψ p)‖ ≤
      ‖v‖ * (dispersion m p * ‖dampedShellAmplitude (a / 2) ψ p‖) := by
  have hdot : |⟪p, v⟫_ℝ| ≤ dispersion m p * ‖v‖ :=
    (abs_real_inner_le_norm p v).trans (mul_le_mul_of_nonneg_right (norm_le_dispersion m p)
      (norm_nonneg _))
  calc
    _ = |⟪p, v⟫_ℝ| * ‖dampedSpatialKernel m a x v z p * conj (ψ p)‖ := by
      simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      ring
    _ ≤ (dispersion m p * ‖v‖) * ‖dampedShellAmplitude (a / 2) ψ p‖ :=
      mul_le_mul hdot (norm_dampedSpatialKernel_mul_le hm x v hbv ψ hz p)
        (norm_nonneg _) (mul_nonneg (hm.le.trans (le_dispersion hm.le p)) (norm_nonneg _))
    _ = _ := by ring

end VacuumBellSeparation

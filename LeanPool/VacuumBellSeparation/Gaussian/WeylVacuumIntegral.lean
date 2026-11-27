/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylVacuumKernel
public import LeanPool.VacuumBellSeparation.Gaussian.L2ProductInner

/-!
# Strong vector integration gives the actual vacuum projection

Each orbit is strongly continuous and has constant vector norm. The
Gaussian-weighted vector integral therefore defines a bounded linear map.
The proved exponential matrix elements and their dense span identify it
with π^m times the actual rank-one vacuum projection. No operator-norm
measurability of the Weyl operator family is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped ComplexConjugate

/-- Weyl vacuum weight defined as `Complex.exp ((-‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 /
2 : ℝ) : ℂ)`. -/
def weylVacuumWeight (m : ℕ) (z : Fin m → ℂ) : ℂ :=
  Complex.exp ((-‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 / 2 : ℝ) : ℂ)

theorem integrable_weylVacuumWeight (m : ℕ) : Integrable (weylVacuumWeight m) := by
  have h := integrable_multiComplexGaussianBilinear
    (s := fun _ : Fin m => 1 / 2) (fun _ => by norm_num)
    (fun _ => 0) (fun _ => 0)
  convert h using 1
  funext z
  simp only [weylVacuumWeight, EuclideanSpace.norm_sq_eq,
    zero_mul, add_zero, ← Complex.exp_sum, ← Complex.ofReal_sum,
    ← Finset.sum_neg_distrib, Finset.sum_div]
  congr 1
  push_cast
  ring_nf

theorem continuous_multiOscillatorWeyl_apply {m : ℕ} (x : MultiModeOscillatorSpace m) :
    Continuous (fun z : MultiModePhaseSpace m => multiOscillatorWeyl z x) := by
  have h := (multiWeylCoherentEquiv m).continuous.comp
    (continuous_weylCLM_id_apply ((multiWeylCoherentEquiv m).symm x))
  simpa only [multiOscillatorWeyl, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    Function.comp_apply] using! h

theorem norm_multiOscillatorWeyl_apply {m : ℕ} (z : MultiModePhaseSpace m)
    (x : MultiModeOscillatorSpace m) : ‖multiOscillatorWeyl z x‖ = ‖x‖ :=
  norm_map_of_mem_unitary (multiOscillatorWeyl_mem_unitary z) x

theorem integrable_weylVacuumOrbit {m : ℕ} (x : MultiModeOscillatorSpace m) :
    Integrable (fun z : Fin m → ℂ =>
      weylVacuumWeight m z • multiOscillatorWeyl (WithLp.toLp 2 z) x) := by
  have hc : Continuous (fun z : Fin m → ℂ =>
      weylVacuumWeight m z • multiOscillatorWeyl (WithLp.toLp 2 z) x) := by
    have hW := (continuous_multiOscillatorWeyl_apply x).comp (PiLp.continuous_toLp 2 _)
    have hw : Continuous (weylVacuumWeight m) := by unfold weylVacuumWeight; fun_prop
    exact hw.smul hW
  apply ((integrable_weylVacuumWeight m).norm.mul_const ‖x‖).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [norm_smul, norm_multiOscillatorWeyl_apply]

/-- Linear map for the weyl vacuum integral linear, of type `MultiModeOscillatorSpace m →ₗ[ℂ]
MultiModeOscillatorSpace m where toFun x`. -/
def weylVacuumIntegralLinear (m : ℕ) : MultiModeOscillatorSpace m →ₗ[ℂ]
    MultiModeOscillatorSpace m where
  toFun x := ∫ z : Fin m → ℂ,
    weylVacuumWeight m z • multiOscillatorWeyl (WithLp.toLp 2 z) x
  map_add' x y := by
    simp only [map_add, smul_add]
    exact integral_add (integrable_weylVacuumOrbit x) (integrable_weylVacuumOrbit y)
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    simp_rw [smul_comm (weylVacuumWeight m _) c]
    exact integral_smul c _

theorem norm_weylVacuumIntegralLinear_le {m : ℕ} (x : MultiModeOscillatorSpace m) :
    ‖weylVacuumIntegralLinear m x‖ ≤
      (∫ z : Fin m → ℂ, ‖weylVacuumWeight m z‖) * ‖x‖ := by
  calc
    _ ≤ ∫ z : Fin m → ℂ,
        ‖weylVacuumWeight m z • multiOscillatorWeyl (WithLp.toLp 2 z) x‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      simp only [norm_smul, norm_multiOscillatorWeyl_apply]
      exact integral_mul_const ‖x‖ _

/-- Continuous linear map for the weyl vacuum integral, of type `MultiModeOscillatorSpace m →L[ℂ]
MultiModeOscillatorSpace m`. -/
def weylVacuumIntegral (m : ℕ) : MultiModeOscillatorSpace m →L[ℂ]
    MultiModeOscillatorSpace m :=
  (weylVacuumIntegralLinear m).mkContinuous
    (∫ z : Fin m → ℂ, ‖weylVacuumWeight m z‖) norm_weylVacuumIntegralLinear_le

@[simp] theorem weylVacuumIntegral_apply {m : ℕ} (x : MultiModeOscillatorSpace m) :
    weylVacuumIntegral m x = ∫ z : Fin m → ℂ,
      weylVacuumWeight m z • multiOscillatorWeyl (WithLp.toLp 2 z) x := rfl

theorem inner_weylVacuumIntegral_exponential {m : ℕ} (a b : Fin m → ℂ) :
    inner ℂ (multiExponentialVector a) (weylVacuumIntegral m (multiExponentialVector b)) =
      (Real.pi : ℂ) ^ m := by
  rw [weylVacuumIntegral_apply, ← integral_inner (integrable_weylVacuumOrbit _)]
  simp only [inner_smul_right, weylVacuumWeight]
  exact integral_gaussianWeyl_exponential_kernel a b

/-- Genuine weak Weyl inversion as equality of actual bounded operators. -/
theorem weylVacuumIntegral_eq_rankOne (m : ℕ) :
    weylVacuumIntegral m = (Real.pi : ℂ) ^ m •
      rankOne ℂ (multiExponentialVector (0 : Fin m → ℂ))
        (multiExponentialVector (0 : Fin m → ℂ)) := by
  apply continuousLinearMap_eq_of_dense_span (multiExponentialVector (m := m))
    (multiExponentialVector_dense_span m)
  intro b
  apply (innerSL_inj (𝕜 := ℂ)).mp
  apply continuousLinearMap_eq_of_dense_span (multiExponentialVector (m := m))
    (multiExponentialVector_dense_span m)
  intro a
  have hk : inner ℂ (multiExponentialVector a)
      (weylVacuumIntegral m (multiExponentialVector b)) =
        inner ℂ (multiExponentialVector a)
          (((Real.pi : ℂ) ^ m • rankOne ℂ
            (multiExponentialVector (0 : Fin m → ℂ))
            (multiExponentialVector (0 : Fin m → ℂ))) (multiExponentialVector b)) := by
    rw [inner_weylVacuumIntegral_exponential]
    simp only [smul_apply, rankOne_apply, inner_smul_right,
      inner_multiExponentialVector, Pi.zero_apply, map_zero, zero_mul, mul_zero,
      Finset.sum_const_zero, Complex.exp_zero, mul_one]
  simpa only [innerSL_apply_apply, inner_conj_symm] using congrArg conj hk

/-- Every scalar matrix element has the literal Gaussian-weighted Weyl
integral, now on arbitrary vectors rather than a formal coherent kernel. -/
theorem integral_gaussianWeyl_kernel {m : ℕ} (x y : MultiModeOscillatorSpace m) :
    (∫ z : Fin m → ℂ, weylVacuumWeight m z *
      inner ℂ x (multiOscillatorWeyl (WithLp.toLp 2 z) y)) =
        (Real.pi : ℂ) ^ m * inner ℂ x (multiExponentialVector (0 : Fin m → ℂ)) *
          inner ℂ (multiExponentialVector (0 : Fin m → ℂ)) y := by
  have h := integral_inner (𝕜 := ℂ) (integrable_weylVacuumOrbit y) x
  simp only [inner_smul_right, ← weylVacuumIntegral_apply] at h
  rw [h, weylVacuumIntegral_eq_rankOne, smul_apply, rankOne_apply,
    inner_smul_right, inner_smul_right]
  ring

end VacuumBellSeparation.Gaussian

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCoherentPositiveTrace
public import LeanPool.VacuumBellSeparation.Gaussian.WeylCoherentInversion
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Fourier multipliers of the actual coherent frame

The frame is the actual Bargmann L² isometry followed by measure-preserving
complex conjugation. Bounded Fourier multiplication on L² and the adjoint
frame give a bounded operator. Its exponential-vector matrix elements are
actual Gaussian integrals, which identify it with a Gaussian multiple of
Weyl displacement. No operator-valued integral over the infinite-volume
coherent frame is asserted.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap
open scoped ComplexConjugate

/-- Multi coherent frame L². -/
def multiCoherentFrameL2 (m : ℕ) : MultiModeOscillatorSpace m →ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure (Fin m → ℂ)) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (multiConjugation m)
    (multiConjugation_measurePreserving m)).comp (multiBargmannL2 m)

theorem multiCoherentFrameL2_ae_eq_coordinate {m : ℕ} (x : MultiModeOscillatorSpace m) :
    (multiCoherentFrameL2 m x : (Fin m → ℂ) → ℂ) =ᵐ[volume]
      multiCoherentFrameCoordinate x := by
  have h₁ := Lp.coeFn_compMeasurePreserving (multiBargmannL2 m x)
    (multiConjugation_measurePreserving m)
  have h₂ := (multiConjugation_measurePreserving m).quasiMeasurePreserving.ae_eq_comp
    (multiBargmannL2_ae_eq_function x)
  filter_upwards [h₁, h₂] with z hz hz'
  change Lp.compMeasurePreserving (multiConjugation m)
    (multiConjugation_measurePreserving m) (multiBargmannL2 m x) z = _
  rw [hz, hz']
  exact multiBargmannFunction_conj x z

theorem continuous_coherentFourierPhase {m : ℕ} (z : MultiModePhaseSpace m) :
    Continuous (fun w : Fin m → ℂ => coherentFourierPhase z (WithLp.toLp 2 w)) := by
  unfold coherentFourierPhase
  fun_prop

theorem memLp_top_coherentFourierPhase {m : ℕ} (z : MultiModePhaseSpace m) :
    MemLp (fun w : Fin m → ℂ => coherentFourierPhase z (WithLp.toLp 2 w)) ⊤ volume :=
  memLp_top_of_bound (continuous_coherentFourierPhase z).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _w => (norm_coherentFourierPhase z _).le)

/-- Coherent Fourier multiplier. -/
def coherentFourierMultiplier {m : ℕ} (z : MultiModePhaseSpace m) :
    Lp ℂ 2 (volume : Measure (Fin m → ℂ)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Fin m → ℂ)) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2
    ((memLp_top_coherentFourierPhase z).toLp _)

theorem coeFn_coherentFourierMultiplier {m : ℕ} (z : MultiModePhaseSpace m)
    (f : Lp ℂ 2 (volume : Measure (Fin m → ℂ))) :
    (coherentFourierMultiplier z f : (Fin m → ℂ) → ℂ) =ᵐ[volume]
      fun w => coherentFourierPhase z (WithLp.toLp 2 w) * f w := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((memLp_top_coherentFourierPhase z).toLp _) f
  filter_upwards [h, (memLp_top_coherentFourierPhase z).coeFn_toLp] with w hw hw'
  simpa only [coherentFourierMultiplier, ContinuousLinearMap.holderL_apply_apply,
    hw', ContinuousLinearMap.mul_apply'] using hw

/-- The Weyl displacement in the coherent frame, with the Fourier change of phase-space
variables. -/
def coherentFrameFourier {m : ℕ} (z : MultiModePhaseSpace m) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  (multiCoherentFrameL2 m).toContinuousLinearMap.adjoint.comp
    ((coherentFourierMultiplier z).comp (multiCoherentFrameL2 m).toContinuousLinearMap)

theorem integrable_coherentFrameFourier_kernel {m : ℕ} (z : MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    Integrable (fun w : Fin m → ℂ => coherentFourierPhase z (WithLp.toLp 2 w) *
      inner ℂ (multiCoherentFrameCoordinate x w) (multiCoherentFrameCoordinate y w)) := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).integrable_of_bilin_of_bdd_left 1
    (continuous_coherentFourierPhase z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => (norm_coherentFourierPhase z _).le)
    (integrable_inner_multiCoherentFrameCoordinate x y)
  simpa only [ContinuousLinearMap.mul_apply'] using h

theorem inner_coherentFrameFourier {m : ℕ} (z : MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    inner ℂ x (coherentFrameFourier z y) =
      ∫ w : Fin m → ℂ, coherentFourierPhase z (WithLp.toLp 2 w) *
        inner ℂ (multiCoherentFrameCoordinate x w) (multiCoherentFrameCoordinate y w) := by
  change inner ℂ x ((multiCoherentFrameL2 m).toContinuousLinearMap.adjoint
    (coherentFourierMultiplier z (multiCoherentFrameL2 m y))) = _
  rw [(multiCoherentFrameL2 m).toContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiCoherentFrameL2_ae_eq_coordinate x,
    multiCoherentFrameL2_ae_eq_coordinate y,
    coeFn_coherentFourierMultiplier z (multiCoherentFrameL2 m y)] with w hx hy hmul
  change inner ℂ ((multiCoherentFrameL2 m x : (Fin m → ℂ) → ℂ) w)
    ((coherentFourierMultiplier z (multiCoherentFrameL2 m y) : (Fin m → ℂ) → ℂ) w) = _
  rw [hx, hmul, hy]
  simp only [RCLike.inner_apply']
  ring

theorem coherentFourierPhase_eq_exp_inner {m : ℕ} (z w : MultiModePhaseSpace m) :
    coherentFourierPhase z w = Complex.exp (inner ℂ w z - inner ℂ z w) := by
  rw [coherentFourierPhase]
  congr 1
  have h : inner ℂ w z = conj (inner ℂ z w) := (inner_conj_symm w z).symm
  rw [h]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im] <;>
      norm_num; ring

theorem coherentFrame_normalization_sq (m : ℕ) :
    conj (((Real.sqrt Real.pi : ℂ) ^ m)⁻¹) * ((Real.sqrt Real.pi : ℂ) ^ m)⁻¹ =
      ((Real.pi : ℂ) ^ m)⁻¹ := by
  simp only [map_inv₀, map_pow, Complex.conj_ofReal, ← mul_inv_rev, ← mul_pow]
  congr 2
  rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]

theorem coherentFrameFourier_exponential_product {m : ℕ}
    (z : MultiModePhaseSpace m) (a b w : Fin m → ℂ) :
    coherentFourierPhase z (WithLp.toLp 2 w) *
      inner ℂ (multiCoherentFrameCoordinate (multiExponentialVector a) w)
        (multiCoherentFrameCoordinate (multiExponentialVector b) w) =
      ((Real.pi : ℂ) ^ m)⁻¹ * ∏ j,
        Complex.exp (((-‖w j‖ ^ 2 : ℝ) : ℂ) +
          (conj (a j) - conj (z j)) * w j + (b j + z j) * conj (w j)) := by
  rw [coherentFourierPhase_eq_exp_inner]
  simp only [multiCoherentFrameCoordinate, RCLike.inner_apply', map_mul,
    multiCoherentVector, inner_smul_left,
    ← Complex.exp_conj, Complex.conj_ofReal, inner_multiExponentialVector]
  calc
    _ = (conj (((Real.sqrt Real.pi : ℂ) ^ m)⁻¹) *
        ((Real.sqrt Real.pi : ℂ) ^ m)⁻¹) *
        Complex.exp ((inner ℂ (WithLp.toLp 2 w : MultiModePhaseSpace m) z -
          inner ℂ z (WithLp.toLp 2 w)) +
          ((-(‖(WithLp.toLp 2 w : MultiModePhaseSpace m)‖ ^ 2 / 2) : ℝ) : ℂ) +
          ((-(‖(WithLp.toLp 2 w : MultiModePhaseSpace m)‖ ^ 2 / 2) : ℝ) : ℂ) +
          (∑ j, conj (a j) * w j) + (∑ j, conj (w j) * b j)) := by
      simp only [Complex.exp_add, map_sum, map_mul, starRingEnd_self_apply]
      have haSum : (∑ j, w j * conj (a j)) = ∑ j, conj (a j) * w j := by
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
      rw [haSum]
      ring
    _ = _ := by
      rw [coherentFrame_normalization_sq, ← Complex.exp_sum]
      congr 2
      simp only [PiLp.inner_apply, RCLike.inner_apply',
        EuclideanSpace.norm_sq_eq, Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_sum, Complex.ofReal_ofNat, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        sub_mul, add_mul, Finset.sum_neg_distrib]
      have hcomm : (∑ j, conj (w j) * z j) = ∑ j, z j * conj (w j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hcomm' : (∑ j, conj (w j) * b j) = ∑ j, b j * conj (w j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hcomm, hcomm']
      ring

theorem inner_coherentFrameFourier_exponential {m : ℕ}
    (z : MultiModePhaseSpace m) (a b : Fin m → ℂ) :
    inner ℂ (multiExponentialVector a) (coherentFrameFourier z (multiExponentialVector b)) =
      weylVacuumWeight m (fun j => z j) *
        inner ℂ (multiExponentialVector a) (multiOscillatorWeyl z (multiExponentialVector b)) := by
  rw [inner_coherentFrameFourier]
  simp_rw [coherentFrameFourier_exponential_product]
  rw [integral_const_mul]
  have h := integral_multiComplexGaussianBilinear (s := fun _ : Fin m => 1)
    (fun _ => zero_lt_one) (fun j => conj (a j) - conj (z j)) (fun j => b j + z j)
  simp only [neg_one_mul, div_one, Complex.ofReal_one] at h
  rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Complex.exp_sum, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)), one_mul]
  rw [multiOscillatorWeyl_exponential_kernel z (WithLp.toLp 2 a) (WithLp.toLp 2 b),
    weylVacuumWeight, ← Complex.exp_add]
  congr 1
  simp only [PiLp.inner_apply, PiLp.add_apply, RCLike.inner_apply',
    EuclideanSpace.norm_sq_eq, sub_mul, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_sum,
    Complex.ofReal_ofNat]
  have hn : (∑ j, conj (z j) * z j) = ∑ j, ((‖z j‖ ^ 2 : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← RCLike.inner_apply', inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow]
  rw [hn]
  ring

/-- An actual bounded operator identity obtained from the actual coherent
L² frame. Its scalar integral is defined and integrable on every pair of vectors. -/
theorem coherentFrameFourier_eq_weyl {m : ℕ} (z : MultiModePhaseSpace m) :
    coherentFrameFourier z = weylVacuumWeight m (fun j => z j) • multiOscillatorWeyl z := by
  apply continuousLinearMap_eq_of_dense_span (multiExponentialVector (m := m))
    (multiExponentialVector_dense_span m)
  intro b
  apply (innerSL_inj (𝕜 := ℂ)).mp
  apply continuousLinearMap_eq_of_dense_span (multiExponentialVector (m := m))
    (multiExponentialVector_dense_span m)
  intro a
  have h := inner_coherentFrameFourier_exponential z a b
  simpa only [innerSL_apply_apply, smul_apply, inner_smul_right, inner_smul_left,
    map_mul, inner_conj_symm] using
    congrArg conj h

theorem integral_coherentFrameFourier_kernel {m : ℕ} (z : MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    (∫ w : Fin m → ℂ, coherentFourierPhase z (WithLp.toLp 2 w) *
      inner ℂ (multiCoherentFrameCoordinate x w) (multiCoherentFrameCoordinate y w)) =
        weylVacuumWeight m (fun j => z j) * inner ℂ x (multiOscillatorWeyl z y) := by
  rw [← inner_coherentFrameFourier, coherentFrameFourier_eq_weyl,
    smul_apply, inner_smul_right]

end VacuumBellSeparation.Gaussian

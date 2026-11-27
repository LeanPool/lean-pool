/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityOffDiagonalInversion
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeInverseBargmann

/-!
# Actual Bargmann inversion from the complex Weyl characteristic

A genuine Lebesgue translation of mixed coherent inversion gives the
independent-label exponential-vector kernel. Its Gaussian weight has an
arbitrary holomorphic/antiholomorphic linear part and is integrable.
This supplies off-diagonal information directly, without assuming an
entire-kernel polarization theorem.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap
open scoped ComplexConjugate

theorem densityExpectation_smul {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (b : HilbertBasis ι ℂ E)
    (A B : E →L[ℂ] E) (c : ℂ) :
    densityExpectation b A (c • B) = c * densityExpectation b A B := by
  simp only [densityExpectation, familyExpectation, smul_apply, inner_smul_right, tsum_mul_left]

/-- Bargmann inversion weight given by `Complex.exp (((-‖z‖ ^ 2 / 2 : ℝ) : ℂ) + inner ℂ z b - inner
ℂ a z)`. -/
def bargmannInversionWeight {m : ℕ} (a b z : MultiModePhaseSpace m) : ℂ :=
  Complex.exp (((-‖z‖ ^ 2 / 2 : ℝ) : ℂ) + inner ℂ z b - inner ℂ a z)

theorem bargmannInversionWeight_product {m : ℕ} (a b : MultiModePhaseSpace m)
    (z : Fin m → ℂ) :
    bargmannInversionWeight a b (WithLp.toLp 2 z) =
      ∏ j, Complex.exp (((-(1 / 2) * ‖z j‖ ^ 2 : ℝ) : ℂ) +
        (-conj (a j)) * z j + b j * conj (z j)) := by
  rw [bargmannInversionWeight, ← Complex.exp_sum]
  congr 1
  simp only [EuclideanSpace.norm_sq_eq, PiLp.inner_apply,
    RCLike.inner_apply', Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_mul]
  have hc : (∑ j, conj (z j) * b j) = ∑ j, b j * conj (z j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hc]
  simp only [← Finset.mul_sum]
  ring

theorem integrable_bargmannInversionWeight {m : ℕ} (a b : MultiModePhaseSpace m) :
    Integrable (fun z : Fin m → ℂ => bargmannInversionWeight a b (WithLp.toLp 2 z)) := by
  simp_rw [bargmannInversionWeight_product]
  exact integrable_multiComplexGaussianBilinear (s := fun _ : Fin m => 1 / 2)
    (fun _ => by norm_num) (fun j => -conj (a j)) (fun j => b j)

theorem mixedDisplacement_shift {m : ℕ} (b a z : MultiModePhaseSpace m) :
    mixedDisplacement b a (z + a - b) =
      (weylPhase id b (z + a - b) * weylPhase id (z + a) (-a)) • multiOscillatorWeyl z := by
  rw [mixedDisplacement, multiOscillatorWeyl_adjoint, multiOscillatorWeyl_mul,
    smul_mul_assoc, multiOscillatorWeyl_mul, smul_smul,
    show b + (z + a - b) = z + a by abel,
    show z + a + -a = z by abel]

theorem shiftedMixedWeyl_weight {m : ℕ} (a b z : MultiModePhaseSpace m) :
    weylVacuumWeight m (fun j => (z + a - b) j) *
      (weylPhase id b (z + a - b) * weylPhase id (z + a) (-a)) =
      Complex.exp (((-(‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 : ℝ) : ℂ) + inner ℂ a b) *
        bargmannInversionWeight a b z := by
  rw [weylVacuumWeight, weylPhase, weylPhase, bargmannInversionWeight]
  have hz : (WithLp.toLp 2 (fun j => (z + a - b) j) : MultiModePhaseSpace m) = z + a - b := rfl
  rw [hz]
  simp only [id_eq, ← Complex.exp_add]
  congr 1
  rw [norm_sub_sq (𝕜 := ℂ) (z + a) b, norm_add_sq (𝕜 := ℂ) z a]
  simp only [inner_sub_right, inner_add_left, inner_add_right, inner_neg_right,
    Complex.sub_im, Complex.add_im, Complex.neg_im,
    Complex.add_re, RCLike.re_to_complex]
  have hr : (inner ℂ a z).re = (inner ℂ z a).re := inner_re_symm (𝕜 := ℂ) a z
  have hi₁ : (inner ℂ b z).im = -(inner ℂ z b).im := inner_im_symm (𝕜 := ℂ) b z
  have hi₂ : (inner ℂ b a).im = -(inner ℂ a b).im := inner_im_symm (𝕜 := ℂ) b a
  have hi₃ : (inner ℂ a z).im = -(inner ℂ z a).im := inner_im_symm (𝕜 := ℂ) a z
  have hia : (inner ℂ a a).im = 0 := inner_self_im (𝕜 := ℂ) a
  have hib : (inner ℂ b b).im = 0 := inner_self_im (𝕜 := ℂ) b
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      hr, hi₁, hi₂, hi₃, hia, hib] <;> ring

theorem multiCoherent_density_kernel {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (a b : MultiModePhaseSpace m) :
    inner ℂ (multiCoherentVector a) (A (multiCoherentVector b)) =
      Complex.exp ((-(‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 : ℝ) : ℂ) *
        multiBargmannKernel A (fun j => a j) (fun j => b j) := by
  rw [multiCoherentVector, multiCoherentVector, map_smul, inner_smul_left, inner_smul_right]
  simp only [← Complex.exp_conj, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

theorem integrable_densityBargmannInversion {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (a b : MultiModePhaseSpace m) :
    Integrable (fun z : Fin m → ℂ => bargmannInversionWeight a b (WithLp.toLp 2 z) *
      densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl (WithLp.toLp 2 z))) := by
  have hc : Continuous (fun z : Fin m → ℂ =>
      densityExpectation (multiModeNumberBasis m) A
        (multiOscillatorWeyl (WithLp.toLp 2 z))) := by
    change Continuous ((fun w : MultiModePhaseSpace m =>
      familyExpectation (fun k => CFC.sqrt A (multiModeNumberBasis m k))
        (multiOscillatorWeyl w)) ∘
      (WithLp.toLp 2 : (Fin m → ℂ) → MultiModePhaseSpace m))
    exact (continuous_familyExpectation_weyl
      (fun k => CFC.sqrt A (multiModeNumberBasis m k))
      (summable_sqrt_basis_norm_sq (multiModeNumberBasis m) hA)).comp
        (PiLp.continuous_toLp 2 (fun _ : Fin m => ℂ))
  have hw : Continuous (fun z : Fin m → ℂ => bargmannInversionWeight a b (WithLp.toLp 2 z)) := by
    unfold bargmannInversionWeight
    fun_prop
  have hi : Continuous (fun z : Fin m → ℂ =>
      bargmannInversionWeight a b (WithLp.toLp 2 z) *
        densityExpectation (multiModeNumberBasis m) A
          (multiOscillatorWeyl (WithLp.toLp 2 z))) := hw.mul hc
  apply ((integrable_bargmannInversionWeight a b).norm.mul_const
    (∑' k, ‖CFC.sqrt A (multiModeNumberBasis m k)‖ ^ 2)).mono' hi.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    change ‖bargmannInversionWeight a b (WithLp.toLp 2 z) *
      densityExpectation (multiModeNumberBasis m) A
        (multiOscillatorWeyl (WithLp.toLp 2 z))‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_familyExpectation_weyl_le _
      (summable_sqrt_basis_norm_sq (multiModeNumberBasis m) hA) _) (norm_nonneg _)

/-- The actual independent-label Bargmann kernel recovered from the
actual complex Weyl characteristic by a genuinely integrable formula. -/
theorem integral_densityBargmannInversion {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (a b : MultiModePhaseSpace m) :
    Complex.exp (inner ℂ a b) *
      (∫ z : Fin m → ℂ, bargmannInversionWeight a b (WithLp.toLp 2 z) *
        densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl (WithLp.toLp 2 z))) =
      (Real.pi : ℂ) ^ m * multiBargmannKernel A (fun j => a j) (fun j => b j) := by
  let f (z : Fin m → ℂ) := weylVacuumWeight m z *
    densityExpectation (multiModeNumberBasis m) A (mixedDisplacement b a (WithLp.toLp 2 z))
  have h := integral_densityMixedWeyl hA b a
  change (∫ z : Fin m → ℂ, f z) = _ at h
  rw [← integral_add_right_eq_self f (fun j => a j - b j)] at h
  have he (z : Fin m → ℂ) : f (z + fun j => a j - b j) =
      Complex.exp (((-(‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 : ℝ) : ℂ) + inner ℂ a b) *
        (bargmannInversionWeight a b (WithLp.toLp 2 z) *
          densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl
            (WithLp.toLp 2 z))) := by
    have hz : (WithLp.toLp 2 (z + fun j => a j - b j) : MultiModePhaseSpace m) =
        WithLp.toLp 2 z + a - b := by
      ext j
      simp only [PiLp.add_apply, PiLp.sub_apply, Pi.add_apply]
      ring
    dsimp only [f]
    rw [hz, mixedDisplacement_shift, densityExpectation_smul]
    have hz' : z + (fun j => a j - b j) = fun j => (WithLp.toLp 2 z + a - b) j := by
      ext j
      simp only [Pi.add_apply, PiLp.add_apply, PiLp.sub_apply]
      ring
    rw [hz', ← mul_assoc, shiftedMixedWeyl_weight]
    ring
  simp_rw [he] at h
  rw [integral_const_mul, multiCoherent_density_kernel, Complex.exp_add] at h
  have hn : Complex.exp ((-(‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  apply mul_left_cancel₀ hn
  exact (by
    calc
      _ = (Complex.exp ((-(‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 : ℝ) : ℂ) *
          Complex.exp (inner ℂ a b)) *
          (∫ z : Fin m → ℂ, bargmannInversionWeight a b (WithLp.toLp 2 z) *
            densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl
              (WithLp.toLp 2 z))) := by ring
      _ = _ := h
      _ = _ := by ring)

end VacuumBellSeparation.Gaussian

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityBargmannInversion
public import LeanPool.VacuumBellSeparation.Gaussian.CoherentGaussianComplexLinear
public import LeanPool.VacuumBellSeparation.Gaussian.PhysicalGaussianHusimi

/-!
# Actual independent-label Gaussian Bargmann kernel

The actual Weyl characteristic is inserted in the proved integrable
Bargmann inversion. The genuine complex-linear Gaussian integral gives
the off-diagonal exponential-vector matrix element. A literal coefficient
vector records the real/imaginary coordinates; the next algebraic step
rewrites it into the manuscript D_B block notation.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped ComplexConjugate MatrixOrder Matrix.Norms.L2Operator

/-- Bargmann Fourier coefficient defined by `fun i => if i.2 = 0 then b i.1 - conj (a i.1) else
-Complex.I * (b i.1 + conj (a i.1))`. -/
def bargmannFourierCoefficient {m : ℕ} (a b : MultiModePhaseSpace m) : Fin m × Fin 2 → ℂ :=
  fun i => if i.2 = 0 then b i.1 - conj (a i.1) else -Complex.I * (b i.1 + conj (a i.1))

theorem bargmannFourierCoefficient_dot {m : ℕ} (a b : MultiModePhaseSpace m)
    (z : Fin m → ℂ) :
    bargmannFourierCoefficient a b ⬝ᵥ (fun i => (complexRealCoordinates m z i : ℂ)) =
      inner ℂ (WithLp.toLp 2 z : MultiModePhaseSpace m) b - inner ℂ a (WithLp.toLp 2 z) := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, bargmannFourierCoefficient,
    ite_true, Fin.isValue, (by decide : (1 : Fin 2) ≠ 0), ite_false,
    complexRealCoordinates_apply, complexRealCoordinates_apply_one,
    PiLp.inner_apply, RCLike.inner_apply']
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im] <;> ring

theorem gaussianDensity_bargmannIntegral_integrand {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianDisplacementCharacteristic A V)
    (a b : MultiModePhaseSpace m) (z : Fin m → ℂ) :
    bargmannInversionWeight a b (WithLp.toLp 2 z) *
      densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl (WithLp.toLp 2 z)) =
        coherentGaussianComplexLinear (V + (1 / 2 : ℝ) • 1) (bargmannFourierCoefficient a b) z := by
  rw [hG z, bargmannInversionWeight, coherentGaussianComplexLinear,
    ← Complex.exp_add, bargmannFourierCoefficient_dot]
  congr 1
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, complexRealCoordinates_dot_self]
  push_cast
  ring

/-- Off-diagonal kernel obtained from the actual Gaussian displacement
characteristic; no diagonal-polarization or formal kernel hypothesis occurs. -/
theorem gaussianDisplacement_bargmannKernel {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianDisplacementCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) (a b : MultiModePhaseSpace m) :
    multiBargmannKernel A (fun j => a j) (fun j => b j) =
      ((Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℂ) *
        Complex.exp (inner ℂ a b + (1 / 4 : ℂ) *
          (bargmannFourierCoefficient a b ⬝ᵥ
            (complexifyMatrix (V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ bargmannFourierCoefficient a b))) := by
  have h := integral_densityBargmannInversion hA a b
  simp_rw [gaussianDensity_bargmannIntegral_integrand hG] at h
  rw [integral_coherentGaussianComplexLinear hC] at h
  have hp : (Real.pi : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  apply mul_left_cancel₀ hp
  calc
    _ = Complex.exp (inner ℂ a b) *
        (((Real.pi ^ m / Real.sqrt (V + (1 / 2 : ℝ) • 1).det : ℝ) : ℂ) *
          Complex.exp ((1 / 4 : ℂ) * (bargmannFourierCoefficient a b ⬝ᵥ
            (complexifyMatrix (V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ bargmannFourierCoefficient a b)))) :=
              h.symm
    _ = _ := by
      rw [Complex.exp_add]
      push_cast
      ring

theorem gaussianPhysical_bargmannKernel_fourier {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) (a b : MultiModePhaseSpace m) :
    multiBargmannKernel A (fun j => a j) (fun j => b j) =
      ((Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℂ) *
        Complex.exp (inner ℂ a b + (1 / 4 : ℂ) *
          (bargmannFourierCoefficient a b ⬝ᵥ
            (complexifyMatrix (physicalDisplacementCovariance (V + (1 / 2 : ℝ) • 1)⁻¹) *ᵥ
              bargmannFourierCoefficient a b))) := by
  have hc : (physicalDisplacementCovariance V + (1 / 2 : ℝ) • 1).PosDef := by
    rw [← physicalDisplacementCovariance_add_scalar]
    exact physicalDisplacementCovariance_posDef hC
  have h := gaussianDisplacement_bargmannKernel hA hG hc a b
  rw [← physicalDisplacementCovariance_add_scalar, physicalDisplacementCovariance_det,
    physicalDisplacementCovariance_inv] at h
  exact h

end VacuumBellSeparation.Gaussian

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroInner

/-!
# The time-zero Gram identity in Fourier variables

The covariance below uses precisely the multipliers `ωₘ⁻¹` and `ωₘ`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

/-- Reality of the source gives the usual conjugation symmetry of its transform. -/
theorem spatialFourier_neg (f : SpatialTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    spatialFourier f (-p) = conj (spatialFourier f p) := by
  unfold spatialFourier
  rw [← integral_conj]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [inner_neg_left, Complex.ofReal_neg, map_mul, map_neg,
    ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal]
  congr 2; ring

/-- A real even Fourier multiplier pairs two real sources to a real number.
This symmetry identity holds for the Bochner integral; applications establish
integrability separately in `TimeZeroInner`. -/
theorem conj_integral_spatialFourier_even_weight (f g : SpatialTestFunction)
    (w : EuclideanSpace ℝ (Fin 3) → ℝ) (hw : ∀ p, w (-p) = w p) :
    conj (∫ p, (conj (spatialFourier f p) * spatialFourier g p) * (w p : ℂ)) =
      ∫ p, (conj (spatialFourier f p) * spatialFourier g p) * (w p : ℂ) := by
  calc
    _ = ∫ p, conj ((conj (spatialFourier f p) * spatialFourier g p) * (w p : ℂ)) :=
      integral_conj.symm
    _ = ∫ p, (conj (spatialFourier f (-p)) * spatialFourier g (-p)) * (w (-p) : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simp only [spatialFourier_neg, hw, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    _ = _ := by
      simpa [finrank_momentum] using
        Measure.integral_comp_smul volume
          (fun p => (conj (spatialFourier f p) * spatialFourier g p) * (w p : ℂ)) (-1 : ℝ)

theorem conj_timeZeroFourierDiagonal (m : ℝ) (u v : TimeZeroSource) :
    conj (timeZeroFourierDiagonal m u v) = timeZeroFourierDiagonal m u v := by
  have hw : ∀ p, dispersion m (-p) = dispersion m p := by
    intro p
    simp only [dispersion, norm_neg]
  unfold timeZeroFourierDiagonal
  rw [map_mul, map_add, Complex.conj_ofReal,
    conj_integral_spatialFourier_even_weight u.1 v.1 _ (fun p => congrArg Inv.inv (hw p)),
    conj_integral_spatialFourier_even_weight u.2 v.2 _ hw]

theorem timeZeroFourierDiagonal_eq_covariance (m : ℝ) (u v : TimeZeroSource) :
    timeZeroFourierDiagonal m u v = (timeZeroFourierCovariance m u v : ℂ) := by
  have h := congrArg Complex.im (conj_timeZeroFourierDiagonal m u v)
  have him : (timeZeroFourierDiagonal m u v).im = 0 := by
    simp only [Complex.conj_im] at h
    linarith
  apply Complex.ext
  · rfl
  · simpa using him

/-- Equation (2.6) for the explicit, integrable Fourier-multiplier covariance. -/
theorem timeZeroGram_identity {m : ℝ} (hm : 0 < m) (u v : TimeZeroSource) :
    timeZeroOneParticleInner m u v = (timeZeroFourierCovariance m u v : ℂ) +
      (Complex.I / 2) * (timeZeroSymplectic u v : ℂ) := by
  have hff := integrable_inv_dispersion_spatialFourier_product hm u.1 v.1
  have hgg := integrable_dispersion_spatialFourier_product hm.le u.2 v.2
  have hfg := integrable_spatialFourier_product u.1 v.2
  have hgf := integrable_spatialFourier_product u.2 v.1
  have hcross : (∫ p, conj (spatialFourier u.1 p) * spatialFourier v.2 p -
      conj (spatialFourier u.2 p) * spatialFourier v.1 p) =
      (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * (timeZeroSymplectic u v : ℂ) := by
    rw [integral_sub hfg hgf, integral_spatialFourier_product,
      integral_spatialFourier_product, ← mul_sub]
    congr 1
    have hi1 := u.1.2.1.continuous.mul v.2.2.1.continuous
    have hi2 := u.2.2.1.continuous.mul v.1.2.1.continuous
    have hint1 := hi1.integrable_of_hasCompactSupport (μ := volume) u.1.2.2.mul_right
    have hint2 := hi2.integrable_of_hasCompactSupport (μ := volume) u.2.2.2.mul_right
    simp_rw [← Complex.ofReal_mul]
    change (∫ x, ((u.1.1 x * v.2.1 x : ℝ) : ℂ)) -
      (∫ x, ((u.2.1 x * v.1.1 x : ℝ) : ℂ)) = (timeZeroSymplectic u v : ℂ)
    rw [integral_complex_ofReal (f := fun x => u.1.1 x * v.2.1 x),
      integral_complex_ofReal (f := fun x => u.2.1 x * v.1.1 x), ← Complex.ofReal_sub]
    congr 1
    exact (integral_sub hint1 hint2).symm
  unfold timeZeroOneParticleInner
  simp_rw [timeZeroOneParticle_product_expand hm]
  have hsum := integral_add (hff.add hgg) ((hfg.sub hgf).const_mul Complex.I)
  have hdiag := integral_add hff hgg
  simp only [Pi.add_apply, Pi.sub_apply] at hsum hdiag
  rw [integral_mul_const, hsum, hdiag, integral_const_mul, hcross, add_mul]
  change timeZeroFourierDiagonal m u v + _ = _
  rw [timeZeroFourierDiagonal_eq_covariance]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hpi]

end VacuumBellSeparation

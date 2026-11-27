/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialFieldCovarianceKernel
public import LeanPool.VacuumBellSeparation.FreeField.SpatialMomentumCovarianceKernel

/-!
# The actual two-component separated spatial covariance

Both literal Fourier multipliers are now identified with their Bessel
kernels, including all convergence and normalization factors. This is a
statement about the original compact spatial sources and their actual
one-particle Gram covariance.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ComplexConjugate

theorem integrable_timeZeroBesselCovariance {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (u v : TimeZeroSource)
    (hff : ∀ x y, u.1.1 x ≠ 0 → v.1.1 y ≠ 0 → d ≤ ‖x - y‖)
    (hgg : ∀ x y, u.2.1 x ≠ 0 → v.2.1 y ≠ 0 → d ≤ ‖x - y‖) :
    Integrable (fun xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      spatialFieldBesselKernel m (xy.1 - xy.2) * u.1.1 xy.1 * v.1.1 xy.2 +
      spatialMomentumBesselKernel m (xy.1 - xy.2) * u.2.1 xy.1 * v.2.1 xy.2)
      (volume.prod volume) := by
  have hf := (integrable_spatialFieldKernel_pairing hm hd u.1 v.1 hff).re
  have hg := (integrable_spatialMomentumKernel_pairing hm hd u.2 v.2 hgg).re
  apply (hf.add hg).congr
  filter_upwards with xy
  simp only [Pi.add_apply, RCLike.re_eq_complex_re, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem timeZeroFourierCovariance_eq_bessel_kernel {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (u v : TimeZeroSource)
    (hff : ∀ x y, u.1.1 x ≠ 0 → v.1.1 y ≠ 0 → d ≤ ‖x - y‖)
    (hgg : ∀ x y, u.2.1 x ≠ 0 → v.2.1 y ≠ 0 → d ≤ ‖x - y‖) :
    timeZeroFourierCovariance m u v =
      ∫ xy, spatialFieldBesselKernel m (xy.1 - xy.2) * u.1.1 xy.1 * v.1.1 xy.2 +
        spatialMomentumBesselKernel m (xy.1 - xy.2) * u.2.1 xy.1 * v.2.1 xy.2
        ∂volume.prod volume := by
  have hf := spatialFourier_field_covariance_real_kernel hm hd u.1 v.1 hff
  have hg := spatialFourier_momentum_covariance_real_kernel hm hd u.2 v.2 hgg
  have hfi : Integrable (fun xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      spatialFieldBesselKernel m (xy.1 - xy.2) * u.1.1 xy.1 * v.1.1 xy.2)
      (volume.prod volume) := by
    simpa only [RCLike.re_eq_complex_re, ← Complex.ofReal_mul,
      Complex.ofReal_re, Pi.add_apply] using
      (integrable_spatialFieldKernel_pairing hm hd u.1 v.1 hff).re
  have hgi : Integrable (fun xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      spatialMomentumBesselKernel m (xy.1 - xy.2) * u.2.1 xy.1 * v.2.1 xy.2)
      (volume.prod volume) := by
    simpa only [RCLike.re_eq_complex_re, ← Complex.ofReal_mul,
      Complex.ofReal_re, Pi.add_apply] using
      (integrable_spatialMomentumKernel_pairing hm hd u.2 v.2 hgg).re
  unfold timeZeroFourierCovariance timeZeroFourierDiagonal
  rw [add_mul, Complex.add_re, integral_add hfi hgi]
  have hfc : (∫ p : EuclideanSpace ℝ (Fin 3),
      (conj (spatialFourier u.1 p) * spatialFourier v.1 p) * ((dispersion m p)⁻¹ : ℝ)) =
      ∫ p : EuclideanSpace ℝ (Fin 3), ((dispersion m p)⁻¹ : ℝ) *
        (conj (spatialFourier u.1 p) * spatialFourier v.1 p) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)
  have hgc : (∫ p : EuclideanSpace ℝ (Fin 3),
      (conj (spatialFourier u.2 p) * spatialFourier v.2 p) * (dispersion m p : ℂ)) =
      ∫ p : EuclideanSpace ℝ (Fin 3), (dispersion m p : ℂ) *
        (conj (spatialFourier u.2 p) * spatialFourier v.2 p) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)
  rw [hfc, hgc, mul_comm _ (((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ)),
    mul_comm _ (((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ)), hf, hg]

theorem timeZeroOneParticleInner_re_eq_bessel_kernel {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (u v : TimeZeroSource)
    (hff : ∀ x y, u.1.1 x ≠ 0 → v.1.1 y ≠ 0 → d ≤ ‖x - y‖)
    (hgg : ∀ x y, u.2.1 x ≠ 0 → v.2.1 y ≠ 0 → d ≤ ‖x - y‖) :
    (timeZeroOneParticleInner m u v).re =
      ∫ xy, spatialFieldBesselKernel m (xy.1 - xy.2) * u.1.1 xy.1 * v.1.1 xy.2 +
        spatialMomentumBesselKernel m (xy.1 - xy.2) * u.2.1 xy.1 * v.2.1 xy.2
        ∂volume.prod volume := by
  rw [timeZeroGram_identity hm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.div_ofNat_re,
    Complex.I_re, zero_div, zero_mul, Complex.ofReal_im, mul_zero, sub_zero, add_zero]
  exact timeZeroFourierCovariance_eq_bessel_kernel hm hd u v hff hgg

end VacuumBellSeparation

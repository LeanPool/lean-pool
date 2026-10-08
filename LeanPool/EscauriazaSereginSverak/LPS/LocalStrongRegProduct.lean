/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1TransportBound

/-!
# Square integrability of products of smooth `H¹` functions

Hölder's inequality with exponents `(6, 3, 2)`, the interpolation of `L³` between `L²` and `L⁶`,
and the homogeneous `H¹ → L⁶` inequality bound the `L²` norm of the product of two smooth functions
with square integrable gradients (`prop:lps-local-strong`, the time derivative bound of the
regularized solutions).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The product of two smooth functions with square integrable gradients is square integrable,
with the
`L²` norm bounded by `S ‖∇V‖₂ ‖d‖₂^{1/2} (S ‖∇d‖₂)^{1/2}`, `S` the Sobolev constant. -/
theorem lps_smooth_mul_memLp_two_norm_le {V d : Vec3 → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV2 : MemLp V 2 volume)
    (hVd : ∀ k, MemLp (spatialDeriv V k) 2 volume)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (hd2 : MemLp d 2 volume)
    (hdd : ∀ k, MemLp (spatialDeriv d k) 2 volume) :
    MemLp (fun x => V x * d x) 2 volume ∧
      (eLpNorm (fun x => V x * d x) 2 volume).toReal ≤
        gagliardoNirenbergSobolevConstant.toReal *
          Real.sqrt (∑ k : Fin 3, ∫ x, spatialDeriv V k x ^ 2) *
          (Real.sqrt (∫ x, d x ^ 2) ^ (1 / 2 : ℝ) *
            (gagliardoNirenbergSobolevConstant.toReal *
              Real.sqrt (∑ k : Fin 3, ∫ x, spatialDeriv d k x ^ 2)) ^ (1 / 2 : ℝ)) := by
  have hV6 := lps_smooth_memLp_six hV hV2 hVd
  have hd6 := lps_smooth_memLp_six hd hd2 hdd
  have hdm : AEStronglyMeasurable d volume := hd.continuous.aestronglyMeasurable
  have hVm : AEStronglyMeasurable V volume := hV.continuous.aestronglyMeasurable
  have hd3 : eLpNorm d 3 volume ≤
      eLpNorm d 2 volume ^ (1 / 2 : ℝ) * eLpNorm d 6 volume ^ (1 / 2 : ℝ) :=
    lps_eLpNorm_three_le_two_six hdm
  have hd3fin : eLpNorm d 3 volume ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hd3
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hd2.eLpNorm_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hd6.eLpNorm_ne_top)
  have hVd2 : eLpNorm (fun x => V x * d x) 2 volume ≤ eLpNorm V 6 volume * eLpNorm d 3 volume :=
    lps_eLpNorm_mul_two_le hVm hdm
  have hVdfin : eLpNorm (fun x => V x * d x) 2 volume ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hV6.eLpNorm_ne_top hd3fin) hVd2
  have hVdmem : MemLp (fun x => V x * d x) 2 volume :=
    lt_top_iff_ne_top.mpr hVdfin
  refine ⟨hVdmem, ?_⟩
  have h1 : (eLpNorm (fun x => V x * d x) 2 volume).toReal ≤
      (eLpNorm V 6 volume).toReal * ((eLpNorm d 2 volume).toReal ^ (1 / 2 : ℝ) *
        (eLpNorm d 6 volume).toReal ^ (1 / 2 : ℝ)) := by
    have hfin : eLpNorm V 6 volume * (eLpNorm d 2 volume ^ (1 / 2 : ℝ) *
        eLpNorm d 6 volume ^ (1 / 2 : ℝ)) ≠ ⊤ :=
      ENNReal.mul_ne_top hV6.eLpNorm_ne_top (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hd2.eLpNorm_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hd6.eLpNorm_ne_top))
    have h2 := ENNReal.toReal_mono hfin (hVd2.trans (by gcongr))
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ← ENNReal.toReal_rpow] at h2
    exact h2
  have hA := lps_smooth_six_toReal_le hV hV2 hVd
  have hB6 := lps_smooth_six_toReal_le hd hd2 hdd
  rw [lps_eLpNorm_two_toReal hd2] at h1
  have hA0 : 0 ≤ (eLpNorm V 6 volume).toReal := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ (eLpNorm d 6 volume).toReal := ENNReal.toReal_nonneg
  refine h1.trans ?_
  gcongr

/-- The squared `L²` norm of the product of two smooth functions with square integrable gradients,
in integral form. -/
theorem lps_smooth_mul_sq_integral_le {V d : Vec3 → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV2 : MemLp V 2 volume)
    (hVd : ∀ k, MemLp (spatialDeriv V k) 2 volume)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (hd2 : MemLp d 2 volume)
    (hdd : ∀ k, MemLp (spatialDeriv d k) 2 volume)
    {y0 h0 : ℝ} (hy : 0 ≤ y0) (hh : 0 ≤ h0)
    (h1 : (∑ k : Fin 3, ∫ x, spatialDeriv V k x ^ 2) ≤ y0) (h2 : (∫ x, d x ^ 2) ≤ y0)
    (h3 : (∑ k : Fin 3, ∫ x, spatialDeriv d k x ^ 2) ≤ h0) :
    (∫ x, (V x * d x) ^ 2) ≤
      gagliardoNirenbergSobolevConstant.toReal ^ (3 : ℕ) * y0 ^ (3 / 2 : ℝ) * h0 ^ (1 / 2 : ℝ) := by
  obtain ⟨hmem, hbound⟩ := lps_smooth_mul_memLp_two_norm_le hV hV2 hVd hd hd2 hdd
  set S := gagliardoNirenbergSobolevConstant.toReal with hS
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hsq : (∫ x, (V x * d x) ^ 2) = (eLpNorm (fun x => V x * d x) 2 volume).toReal ^ 2 := by
    rw [lps_eLpNorm_two_toReal hmem, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
  rw [hsq]
  have p1 : 0 ≤ ∫ x, d x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have p2 : 0 ≤ ∑ k : Fin 3, ∫ x, spatialDeriv d k x ^ 2 :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have p3 : 0 ≤ ∑ k : Fin 3, ∫ x, spatialDeriv V k x ^ 2 :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have hcore : S * Real.sqrt (∑ k : Fin 3, ∫ x, spatialDeriv V k x ^ 2) *
      (Real.sqrt (∫ x, d x ^ 2) ^ (1 / 2 : ℝ) *
        (S * Real.sqrt (∑ k : Fin 3, ∫ x, spatialDeriv d k x ^ 2)) ^ (1 / 2 : ℝ)) ≤
      S ^ (3 / 2 : ℝ) * y0 ^ (3 / 4 : ℝ) * h0 ^ (1 / 4 : ℝ) := by
    have e1 : Real.sqrt y0 = y0 ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow y0
    have e2 : Real.sqrt h0 = h0 ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow h0
    have m1 : S * Real.sqrt (∑ k : Fin 3, ∫ x, spatialDeriv V k x ^ 2) ≤ S * y0 ^ (1 / 2 : ℝ) := by
      rw [← e1]; gcongr
    have m2 : Real.sqrt (∫ x, d x ^ 2) ^ (1 / 2 : ℝ) ≤ (y0 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [← e1]; gcongr
    have m3 : (S * Real.sqrt (∑ k : Fin 3, ∫ x, spatialDeriv d k x ^ 2)) ^ (1 / 2 : ℝ) ≤
        (S * h0 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [← e2]; gcongr
    refine (mul_le_mul m1 (mul_le_mul m2 m3 (by positivity) (by positivity))
      (by positivity) (by positivity)).trans (le_of_eq ?_)
    rw [Real.mul_rpow hS0 (Real.rpow_nonneg hh _)]
    have a1 : (y0 ^ (1 / 2 : ℝ)) * (y0 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = y0 ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_mul hy, ← Real.rpow_add' hy (by norm_num)]; norm_num
    have a2 : (h0 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = h0 ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_mul hh]; norm_num
    have a3 : S * S ^ (1 / 2 : ℝ) = S ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hS0 (by norm_num),
        Real.rpow_one]
    calc S * y0 ^ (1 / 2 : ℝ) * ((y0 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
          (S ^ (1 / 2 : ℝ) * (h0 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)))
        = (S * S ^ (1 / 2 : ℝ)) * ((y0 ^ (1 / 2 : ℝ)) * (y0 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)) *
            (h0 ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by ring
      _ = S ^ (3 / 2 : ℝ) * y0 ^ (3 / 4 : ℝ) * h0 ^ (1 / 4 : ℝ) := by rw [a1, a2, a3]
  have hnn : 0 ≤ (eLpNorm (fun x => V x * d x) 2 volume).toReal := ENNReal.toReal_nonneg
  have hle := hbound.trans hcore
  have := pow_le_pow_left₀ hnn hle 2
  refine this.trans (le_of_eq ?_)
  have hS3 : (S ^ (3 / 2 : ℝ)) ^ 2 = S ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0]; norm_num
  have hy3 : (y0 ^ (3 / 4 : ℝ)) ^ 2 = y0 ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num
  have hh3 : (h0 ^ (1 / 4 : ℝ)) ^ 2 = h0 ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh]; norm_num
  rw [mul_pow, mul_pow, hS3, hy3, hh3]

end ESS.LPS

end

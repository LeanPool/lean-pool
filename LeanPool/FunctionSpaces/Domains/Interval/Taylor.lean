/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Polynomials
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Polynomial approximation of smooth functions on intervals

For `g ∈ C^r(ℝ)`, `1 ≤ p ≤ ∞` and `u ≤ v` there is a polynomial `Q` of degree `< r` with

`‖g - Q‖_{L_p[u, v]} ≤ (v - u)^r ‖g^(r)‖_{L_p[u, v]}`   (`Interval.exists_eLpNorm_sub_polyFun_le`).

The proof is by induction on `r`: approximate `g'` by `Q'` of degree `< r - 1`, take an
antiderivative `Q` of `Q'` with `Q(u) = g(u)` (`Interval.exists_derivative_eq`), and bound
`g - Q` by the fundamental theorem of calculus and Hölder's inequality,
`|(g - Q)(x)| ≤ ∫_u^v |g' - Q'| ≤ (v - u)^(1 - 1/p) ‖g' - Q'‖_{L_p}`.  This is Taylor's theorem in
the form needed for approximation in `L_p`; the constant `1` is not optimal.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Interval

/-- **Antiderivatives of polynomials**: every polynomial of degree `< r` is the derivative of a
polynomial of degree `< r + 1`. -/
theorem exists_derivative_eq {r : ℕ} {Q : ℂ[X]} (hQ : Q ∈ degreeLT ℂ r) :
    ∃ R ∈ degreeLT ℂ (r + 1), derivative R = Q := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · exact ⟨0, Submodule.zero_mem _, by simp⟩
  have hdeg : Q.natDegree < r := (natDegree_lt_iff_degree_lt hQ0).2 (mem_degreeLT.1 hQ)
  refine ⟨∑ i ∈ Finset.range r, C (Q.coeff i / (i + 1)) * X ^ (i + 1), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i hi => ?_
    rw [mem_degreeLT]
    refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
    have := Finset.mem_range.1 hi
    exact_mod_cast (by omega : i + 1 < r + 1)
  · rw [derivative_sum]
    conv_rhs => rw [Q.as_sum_range' r hdeg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [derivative_C_mul_X_pow, Nat.add_sub_cancel, ← C_mul_X_pow_eq_monomial]
    congr 2
    push_cast
    field_simp

/-- The derivative of a polynomial along the real line. -/
theorem hasDerivAt_polyFun (P : ℂ[X]) (x : ℝ) :
    HasDerivAt (polyFun P) (polyFun (derivative P) x) x :=
  (P.hasDerivAt (x : ℂ)).comp_ofReal

/-- **Taylor's theorem in `L_p`**: for `g ∈ C^r` and `u ≤ v` there is `Q` of degree `< r` with
`‖g - Q‖_{L_p[u, v]} ≤ (v - u)^r ‖g^(r)‖_{L_p[u, v]}`. -/
theorem exists_eLpNorm_sub_polyFun_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) {g : ℝ → ℂ}
    (hg : ContDiff ℝ r g) {u v : ℝ} (huv : u ≤ v) :
    ∃ Q ∈ degreeLT ℂ r, eLpNorm (fun x => g x - polyFun Q x) p (volume.restrict (Icc u v)) ≤
      ENNReal.ofReal (v - u) ^ r * eLpNorm (iteratedDeriv r g) p (volume.restrict (Icc u v)) := by
  induction r generalizing g with
  | zero => exact ⟨0, Submodule.zero_mem _, by simp [polyFun]⟩
  | succ r ih =>
    have hg1 : ContDiff ℝ ((r : WithTop ℕ∞) + 1) g := by exact_mod_cast hg
    obtain ⟨hdiff, -, hg'⟩ := contDiff_succ_iff_deriv.1 hg1
    obtain ⟨Q', hQ', hQ'bound⟩ := ih hg'
    obtain ⟨R, hR, hRQ⟩ := exists_derivative_eq hQ'
    set Q := R + C (g u - polyFun R u)
    have hQ : Q ∈ degreeLT ℂ (r + 1) := by
      refine Submodule.add_mem _ hR ?_
      rw [mem_degreeLT]
      exact (degree_C_le).trans_lt (by exact_mod_cast Nat.succ_pos r)
    refine ⟨Q, hQ, ?_⟩
    rw [iteratedDeriv_succ']
    rcases huv.eq_or_lt with rfl | huv'
    · simp
    set h := fun x => g x - polyFun Q x
    set h' := fun x => deriv g x - polyFun Q' x
    have hderiv : ∀ x, HasDerivAt h (h' x) x := fun x => by
      have hQd : polyFun (derivative Q) x = polyFun Q' x := by
        simp [Q, derivative_add, derivative_C, hRQ]
      have := (hdiff x).hasDerivAt.sub (hasDerivAt_polyFun Q x)
      rwa [hQd] at this
    have hcont : Continuous h' :=
      hg'.continuous.sub (continuous_polyFun Q')
    have hu : h u = 0 := by simp [h, Q, polyFun]
    set μ := volume.restrict (Icc u v)
    set M := eLpNorm h' p μ * volume (Icc u v) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal)
    have hpt : ∀ x ∈ Icc u v, ‖h x‖ₑ ≤ M := fun x hx => by
      have hftc : ∫ t in u..x, h' t = h x - h u :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
          (hcont.intervalIntegrable _ _)
      rw [hu, sub_zero] at hftc
      rw [← hftc, intervalIntegral.integral_of_le hx.1]
      calc ‖∫ t in Ioc u x, h' t‖ₑ ≤ ∫⁻ t in Ioc u x, ‖h' t‖ₑ := eNorm_integral_le_lintegral_eNorm _
        _ ≤ ∫⁻ t in Icc u v, ‖h' t‖ₑ :=
            lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hx.2))
        _ = eLpNorm h' 1 μ := (eLpNorm_one_eq_lintegral_eNorm hcont.aestronglyMeasurable).symm
        _ ≤ M := by
            have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (p := 1) (q := p) hp
              hcont.aestronglyMeasurable
            rwa [Measure.restrict_apply_univ] at this
    have hbound := eLpNorm_le_of_ae_eNorm_bound (p := p) (μ := μ)
      ((hdiff.continuous.sub (continuous_polyFun Q)).aestronglyMeasurable)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using hpt x hx)
    rw [Measure.restrict_apply_univ, Real.volume_Icc] at hbound
    have hL0 : ENNReal.ofReal (v - u) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hexp : ENNReal.ofReal (v - u) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) *
        ENNReal.ofReal (v - u) ^ p.toReal⁻¹ = ENNReal.ofReal (v - u) := by
      rw [← ENNReal.rpow_add _ _ hL0 ENNReal.ofReal_ne_top, ENNReal.toReal_one, div_one,
        one_div, sub_add_cancel, ENNReal.rpow_one]
    calc eLpNorm h p μ ≤ M • ENNReal.ofReal (v - u) ^ p.toReal⁻¹ := hbound
      _ = eLpNorm h' p μ * ENNReal.ofReal (v - u) := by
          rw [smul_eq_mul, mul_assoc, Real.volume_Icc, hexp]
      _ ≤ ENNReal.ofReal (v - u) ^ r * eLpNorm (iteratedDeriv r (deriv g)) p μ *
            ENNReal.ofReal (v - u) := by gcongr
      _ = _ := by ring

end Interval

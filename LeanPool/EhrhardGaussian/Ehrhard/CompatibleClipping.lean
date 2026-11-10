/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Weight-dependent clipping of input and output quantiles preserves a strict linear constraint. -/

public section

namespace EhrhardGaussian.Ehrhard

/-- Clipping the two input quantiles from below and the output on both sides
preserves a prescribed strict gap. The cutoff conditions are explicit. -/
theorem compatible_quantile_clipping
    {p q s U V L H Lf Lg η u v w : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 < s)
    (hu : u ≤ U) (hv : v ≤ V) (horiginal : p * u + q * v ≤ s * w)
    (hLfU : -Lf ≤ U) (hLgV : -Lg ≤ V)
    (hH : p * U + q * V + η ≤ s * H)
    (hLf : q * V + s * L + η ≤ p * Lf)
    (hLg : p * U + s * L + η ≤ q * Lg) :
    p * max u (-Lf) + q * max v (-Lg) -
      s * min (max (w + η / s) (-L)) H ≤ -η := by
  have hu' : max u (-Lf) ≤ U := max_le hu hLfU
  have hv' : max v (-Lg) ≤ V := max_le hv hLgV
  by_cases hout : H ≤ max (w + η / s) (-L)
  · rw [min_eq_right hout]
    have h1 := mul_le_mul_of_nonneg_left hu' hp
    have h2 := mul_le_mul_of_nonneg_left hv' hq
    linarith only [h1, h2, hH]
  · rw [min_eq_left (le_of_not_ge hout)]
    have hw := mul_le_mul_of_nonneg_left (le_max_right (w + η / s) (-L)) hs.le
    by_cases huf : u ≤ -Lf
    · rw [max_eq_right huf]
      have h2 := mul_le_mul_of_nonneg_left hv' hq
      linarith only [h2, hw, hLf]
    · rw [max_eq_left (le_of_not_ge huf)]
      by_cases hvg : v ≤ -Lg
      · rw [max_eq_right hvg]
        have h1 := mul_le_mul_of_nonneg_left hu hp
        linarith only [h1, hw, hLg]
      · rw [max_eq_left (le_of_not_ge hvg)]
        have hw' := mul_le_mul_of_nonneg_left (le_max_left (w + η / s) (-L)) hs.le
        have hcancel : s * (w + η / s) = s * w + η := by
          rw [mul_add, mul_div_cancel₀ _ hs.ne']
        rw [hcancel] at hw'
        linarith only [horiginal, hw']

/-- The compatible cutoffs exist for every positive pair of weights and output
scale. Including a common lower bound `M` allows all cutoffs to tend to infinity. -/
theorem exists_compatible_quantile_cutoffs {p q s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (U V L η M : ℝ) :
    ∃ H Lf Lg : ℝ, M ≤ H ∧ M ≤ Lf ∧ M ≤ Lg ∧ -Lf ≤ U ∧ -Lg ≤ V ∧
      p * U + q * V + η ≤ s * H ∧
      q * V + s * L + η ≤ p * Lf ∧
      p * U + s * L + η ≤ q * Lg := by
  let H := max M ((p * U + q * V + η) / s)
  let Lf := max (max M (-U)) ((q * V + s * L + η) / p)
  let Lg := max (max M (-V)) ((p * U + s * L + η) / q)
  have hH : (p * U + q * V + η) / s ≤ H := le_max_right _ _
  have hLf : (q * V + s * L + η) / p ≤ Lf := le_max_right _ _
  have hLg : (p * U + s * L + η) / q ≤ Lg := le_max_right _ _
  refine ⟨H, Lf, Lg, le_max_left _ _,
    (le_max_left M (-U)).trans (le_max_left _ _),
    (le_max_left M (-V)).trans (le_max_left _ _), ?_, ?_, ?_, ?_, ?_⟩
  · have h := (le_max_right M (-U)).trans (le_max_left (max M (-U))
      ((q * V + s * L + η) / p))
    linarith only [h]
  · have h := (le_max_right M (-V)).trans (le_max_left (max M (-V))
      ((p * U + s * L + η) / q))
    linarith only [h]
  · exact (div_le_iff₀ hs).mp hH |>.trans_eq (mul_comm H s)
  · exact (div_le_iff₀ hp).mp hLf |>.trans_eq (mul_comm Lf p)
  · exact (div_le_iff₀ hq).mp hLg |>.trans_eq (mul_comm Lg q)

end EhrhardGaussian.Ehrhard

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleySquarefreeRankin

/-! # Finite squarefree Hooley sums with a free moment order

For every eligible `q`, the reciprocal sum is bounded by a constant times
`(Kq)^q (log x)^(2^t−t+t/q)`. The cutoff and constants are independent of `q`.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem exists_squarefreeHooleyRootSum_power_bound {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t : ℝ} (ht : 1 ≤ t) :
    ∃ K x₀ : ℝ, 1 ≤ K ∧ 1 < x₀ ∧ ∀ q : ℕ, 2 < q → 2 * t ≤ q →
      ∀ x : ℝ, x₀ < x → squarefreeHooleyRootSum Q t x ≤
        ((2 : ℝ) ^ t * Real.exp 1) * ((K * q) ^ q * (Real.log x) ^ ((2 : ℝ) ^ t - t + t / q)) := by
  obtain ⟨K, b, hK, hb, _, hbound⟩ := exists_irreducible_hooleyDirichlet_power_bound hQ hirr ht
  have hd : 0 < b - 1 := by linarith
  let x₀ := Real.exp (1 / (b - 1) + 1)
  have hx₀ : 1 < x₀ := Real.one_lt_exp_iff.mpr (by positivity)
  refine ⟨K, x₀, hK, hx₀, fun q hq hqt x hx => ?_⟩
  have hx₁ : 1 < x := hx₀.trans hx
  have hl : 0 < Real.log x := Real.log_pos hx₁
  have hlbig : 1 / (b - 1) + 1 < Real.log x := by
    have H := Real.log_lt_log (Real.exp_pos (1 / (b - 1) + 1)) hx
    rwa [Real.log_exp] at H
  have hσ : 1 < 1 + 1 / Real.log x := by linarith [one_div_pos.mpr hl]
  have hσb : 1 + 1 / Real.log x ≤ b := by
    have H : 1 / (b - 1) ≤ Real.log x := by linarith
    have H' := (div_le_iff₀ hd).mp H
    have H'' := (div_le_iff₀ hl).mpr (show 1 ≤ (b - 1) * Real.log x by nlinarith)
    linarith
  have H := hbound q hq hqt (1 + 1 / Real.log x) hσ hσb
  have Hpow (e : ℝ) : ((1 + 1 / Real.log x) - 1) ^ (-e) = (Real.log x) ^ e := by
    rw [add_sub_cancel_left, one_div, Real.inv_rpow hl.le, ← Real.rpow_neg hl.le, neg_neg]
  rw [Hpow] at H
  apply (squarefreeHooleyRootSum_le_log_dirichlet (q := q) hQ (by linarith) (by omega) hx₁).trans
  exact mul_le_mul_of_nonneg_left H (by positivity)

end NairTenenbaum

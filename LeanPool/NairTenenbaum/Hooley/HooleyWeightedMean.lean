/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyPowerfulComparison

/-! # The sharp weighted reciprocal Hooley mean

For an irreducible integer polynomial without a fixed prime divisor, the
reciprocal mean has logarithmic exponent `2^t−t` and exponential coefficient
`sqrt(2t)+o(1)`. The bound includes all positive integers.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial Filter
open scoped Topology

/-- The subexponential factor used in the sharp weighted Hooley bound. -/
noncomputable def hooleySubexponential (η x : ℝ) : ℝ :=
  Real.exp (η * Real.sqrt (Real.log (Real.log x) * Real.log (Real.log (Real.log x))))

theorem hooleySubexponential_pos (η x : ℝ) : 0 < hooleySubexponential η x := Real.exp_pos _

theorem exists_hooleyRootSum_sharp_bound {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t η : ℝ} (ht : 1 ≤ t)
    (hη : Real.sqrt (2 * t) < η) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x : ℝ, x₀ < x →
      hooleyRootSum Q t x ≤ C * ((Real.log x) ^ ((2 : ℝ) ^ t - t) * hooleySubexponential η x) := by
  obtain ⟨x₀, C, hx₀, hC, H⟩ := exists_squarefreeHooleyRootSum_sharp_bound hQ hirr ht hη
  let A := ∑' n : {n : ℕ // Powerful n}, powerfulRootWeight Q t n
  have hA : 0 ≤ A := tsum_nonneg (powerfulRootWeight_nonneg Q t)
  refine ⟨x₀, (1 + A) * C, hx₀, mul_pos (by linarith) hC, fun x hx => ?_⟩
  have HM : 0 ≤ (Real.log x) ^ ((2 : ℝ) ^ t - t) * hooleySubexponential η x :=
    mul_nonneg (Real.rpow_nonneg (Real.log_pos (hx₀.trans hx)).le _) (hooleySubexponential_pos η
        x).le
  calc
    _ ≤ A * squarefreeHooleyRootSum Q t x := hooleyRootSum_le_powerful_mul_squarefree hQ hirr (by
      linarith) x
    _ ≤ A * (C * ((Real.log x) ^ ((2 : ℝ) ^ t - t) * hooleySubexponential η x)) :=
      mul_le_mul_of_nonneg_left (H x hx) hA
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A) (mul_nonneg hC.le HM)

theorem exists_hooleyRootSum_X_sharp_bound {η : ℝ} (hη : Real.sqrt 2 < η) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x : ℝ, x₀ < x →
      hooleyRootSum (X : ℤ[X]) 1 x ≤ C * (Real.log x * hooleySubexponential η x) := by
  have HI : Irreducible ((X : ℤ[X]).map (Int.castRingHom ℚ)) := by
    simpa only [Polynomial.map_X] using (Polynomial.irreducible_X : Irreducible (X : ℚ[X]))
  obtain ⟨x₀, C, hx₀, hC, H⟩ := exists_hooleyRootSum_sharp_bound noFixedPrimeDivisor_X HI
    (t := 1) (by norm_num) (by simpa using hη)
  refine ⟨x₀, C, hx₀, hC, fun x hx => ?_⟩
  simpa only [Real.rpow_one, show (2 : ℝ) - 1 = 1 by norm_num] using H x hx

end NairTenenbaum

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.ConvolutionPowerError
public import LeanPool.NairTenenbaum.NumberFields.LogWeightedSummatoryBound
public import LeanPool.NairTenenbaum.NumberFields.PrimeRootMangoldtBound

/-! # The Mertens upper bound reduced to quantitative ideal counting

A power-saving error in the ideal count implies a bounded error in its weighted
von Mangoldt sum. The quantitative ideal-count hypothesis is explicit here;
this module does not assert that it follows from the qualitative mean theorem.
-/

@[expose] public section

namespace NairTenenbaum

open Finset ArithmeticFunction NumberField Polynomial

theorem reciprocal_logDerivative_le_of_power_error {a v : ArithmeticFunction ℝ}
    (ha : ∀ n, 0 ≤ a n) (hv : ∀ n, 0 ≤ v n)
    (hconv : v * a = arithmeticLogWeight a) {κ E C θ x : ℝ}
    (hκ : 0 < κ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (herror : ∀ t : ℝ, 1 ≤ t → |arithmeticSummatory a t - κ * t| ≤ E * t ^ θ)
    (hbound : ∀ t : ℝ, 1 ≤ t → arithmeticSummatory v t ≤ C * t)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hx : 1 ≤ x) :
    arithmeticSummatory (fun n => v n / n) x ≤
      Real.log x + E * (C + 1) / (κ * (1 - θ)) := by
  have HE := arithmeticSummatory_convolution_power_error hv hE hC herror hbound hθ hθ1 hx
  rw [hconv] at HE
  have HA : arithmeticSummatory a x ≤ κ * x + E * x ^ θ := by
    have H := (abs_le.mp (herror x hx)).2
    linarith
  have HL := arithmeticSummatory_log_le_of_power_error a.map_zero ha hE HA hθ1 hx
  have HLeq : arithmeticSummatory (arithmeticLogWeight a) x =
      arithmeticSummatory (fun n => a n * Real.log n) x := rfl
  rw [HLeq] at HE
  have HE' := (abs_le.mp HE).1
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  apply (mul_le_mul_iff_right₀ (mul_pos hκ hx0)).mp
  have hconst : κ * x * (Real.log x + E * (C + 1) / (κ * (1 - θ))) =
      κ * x * Real.log x + E / (1 - θ) * x + E * C / (1 - θ) * x := by
    field_simp [hκ.ne', (show 1 - θ ≠ 0 by linarith)]
    ring
  rw [hconst]
  nlinarith

variable (K : Type*) [Field K] [NumberField K]

theorem idealMangoldtReciprocalSum_le_of_power_error {E θ : ℝ} (hE : 0 ≤ E)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (herror : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory (idealNormArithmetic K) t - dedekindZeta_residue K * t| ≤ E * t ^ θ)
    {x : ℝ} (hx : 1 ≤ x) :
    idealMangoldtReciprocalSum K x ≤ Real.log x +
      E * ((Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) + 1) /
        (dedekindZeta_residue K * (1 - θ)) := by
  apply reciprocal_logDerivative_le_of_power_error
    (a := idealNormArithmetic K) (v := idealVonMangoldt K)
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    · rw [idealNormArithmetic_apply_pos K (Nat.pos_of_ne_zero hn)]
      exact Nat.cast_nonneg _
  · exact idealVonMangoldt_nonneg K
  · rw [mul_comm]
    exact idealVonMangoldt_convolution K
  · exact dedekindZeta_residue_pos K
  · exact hE
  · positivity
  · exact herror
  · intro t ht
    exact idealVonMangoldt_summatory_le K (by linarith)
  · exact hθ
  · exact hθ1
  · exact hx

theorem exists_primeRootLogSum_mertens_bound_of_power_error {Q : ℤ[X]} (N : ℕ)
    (hmatch : ∀ p : ℕ, p.Prime → N < p → rootCount Q p = idealNormCount K p)
    {E θ : ℝ} (hE : 0 ≤ E) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (herror : ∀ t : ℝ, 1 ≤ t →
      |arithmeticSummatory (idealNormArithmetic K) t - dedekindZeta_residue K * t| ≤ E * t ^ θ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → primeRootLogSum Q x ≤ Real.log x + B := by
  obtain ⟨C, hC, HC⟩ := exists_primeRootLogSum_idealMangoldt_bound K N hmatch
  let D := E * ((Module.finrank ℚ K : ℝ) * (Real.log 4 + 4) + 1) /
    (dedekindZeta_residue K * (1 - θ))
  refine ⟨max (D + C) 0, le_max_right _ _, fun x hx => ?_⟩
  have H := idealMangoldtReciprocalSum_le_of_power_error K hE hθ hθ1 herror hx
  have HCx := HC x
  have Hmax := le_max_left (D + C) 0
  dsimp [D] at Hmax
  linarith

end NairTenenbaum

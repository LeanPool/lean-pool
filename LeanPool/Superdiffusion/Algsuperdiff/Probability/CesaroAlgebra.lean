/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.CesaroWindow

/-!
# CesaroAlgebra

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Elementary algebra of the Cesàro window average

`Algsuperdiff/Probability/CesaroWindow.lean` defines the §4.2 window average
  `cesaroAvg f n m = (m − n + 1)⁻¹ · ∑_{k ∈ [n, m]} f k`

(`avsum_{k=n}^m` in ABK26, §4.2) together with the `rpow` bookkeeping and the
`Γ_σ` centering layer, but proves nothing about the average as a linear
functional.  This module supplies that basic API: additivity, constants, scalar
multiples, monotonicity, and a four-term convenience form
matching the `D₁ + D₂ + D₃ + const` shape of the `l.minimal.scale.sep`
decomposition.

Everything here assumes `n ≤ m`, which is exactly the condition making the window
nonempty and the normalizing factor `(m − n + 1 : ℝ)` positive.

`cesaroAvg_denom_pos` and `cesaroAvg_card` are the `cesaroAvg`-facing names for
the window facts already proved in `CesaroWindow.lean` (`window_pos`,
`natCast_card_Icc_int`); they delegate rather than duplicate the proofs.

## Main results

* `Algsuperdiff.Probability.cesaroAvg_add`
* `Algsuperdiff.Probability.cesaroAvg_const_mul`
* `Algsuperdiff.Probability.cesaroAvg_mono`
* `Algsuperdiff.Probability.cesaroAvg_add4`

## References

* ABK26, `l.minimal.scale.sep` for the window average.
-/

namespace Algsuperdiff.Probability

open scoped BigOperators

noncomputable section

variable {f g : ℤ → ℝ} {n m : ℤ}

/-- The window normalizer `(m − n + 1 : ℝ)` is positive on a nonempty window. -/
theorem cesaroAvg_denom_pos (hnm : n ≤ m) : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) :=
  window_pos hnm

/-- The window `[n, m]` has exactly `m − n + 1` elements. -/
theorem cesaroAvg_card (hnm : n ≤ m) :
    ((Finset.Icc n m).card : ℝ) = ((m - n + 1 : ℤ) : ℝ) :=
  natCast_card_Icc_int hnm

/-- `cesaroAvg` is additive in its integrand. -/
theorem cesaroAvg_add (f g : ℤ → ℝ) (n m : ℤ) :
    cesaroAvg (fun k => f k + g k) n m = cesaroAvg f n m + cesaroAvg g n m := by
  simp only [cesaroAvg, Finset.sum_add_distrib, mul_add]

/-- `cesaroAvg` commutes with scalar multiplication of the integrand. -/
theorem cesaroAvg_const_mul (c : ℝ) (f : ℤ → ℝ) (n m : ℤ) :
    cesaroAvg (fun k => c * f k) n m = c * cesaroAvg f n m := by
  simp only [cesaroAvg, ← Finset.mul_sum]
  ring

/-- The average of a constant over a nonempty window is that constant. -/
theorem cesaroAvg_const (hnm : n ≤ m) (c : ℝ) :
    cesaroAvg (fun _ => c) n m = c := by
  have hne : ((m - n + 1 : ℤ) : ℝ) ≠ 0 := ne_of_gt (cesaroAvg_denom_pos hnm)
  simp only [cesaroAvg, Finset.sum_const, nsmul_eq_mul, cesaroAvg_card hnm]
  field_simp

/-- `cesaroAvg` is monotone in the integrand on the window. -/
theorem cesaroAvg_mono (hnm : n ≤ m) (h : ∀ k ∈ Finset.Icc n m, f k ≤ g k) :
    cesaroAvg f n m ≤ cesaroAvg g n m := by
  have hpos := cesaroAvg_denom_pos hnm
  simp only [cesaroAvg]
  have hinv : (0 : ℝ) ≤ 1 / ((m - n + 1 : ℤ) : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) hinv

/-- Three summands plus an additive constant — the shape produced by the
`D₁ + D₂ + D₃` decomposition of `l.minimal.scale.sep`. -/
theorem cesaroAvg_add4 (hnm : n ≤ m) (f₁ f₂ f₃ : ℤ → ℝ) (c : ℝ) :
    cesaroAvg (fun k => f₁ k + f₂ k + f₃ k + c) n m =
      cesaroAvg f₁ n m + cesaroAvg f₂ n m + cesaroAvg f₃ n m + c := by
  rw [show (fun k => f₁ k + f₂ k + f₃ k + c)
        = (fun k => (fun k' => f₁ k' + f₂ k' + f₃ k') k + (fun _ => c) k) from rfl,
    cesaroAvg_add, cesaroAvg_const hnm,
    show (fun k => f₁ k + f₂ k + f₃ k)
        = (fun k => (fun k' => f₁ k' + f₂ k') k + f₃ k) from rfl,
    cesaroAvg_add, cesaroAvg_add]

end

end Algsuperdiff.Probability

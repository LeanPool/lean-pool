/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimePowerLogExpansion
public import LeanPool.NairTenenbaum.DivisorSums.ScalarRoughLogMass
public import LeanPool.NairTenenbaum.Polynomials.PolynomialLogMassLength

/-! # Canonical smooth and rough logarithmic masses of polynomial values

At a zero polynomial value the positive representative is one. This does
not change the logarithm, and eventual nonvanishing removes this convention
from applications to the product of the original values.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset Real

/-- The positive absolute polynomial value used in the logarithmic decomposition. -/
noncomputable def positivePolynomialValue (Q : ℤ[X]) (n : ℕ) : ℕ+ :=
  ⟨max 1 (Q.eval (n : ℤ)).natAbs, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩

theorem positivePolynomialValue_eq {Q : ℤ[X]} {n : ℕ} (hn : Q.eval (n : ℤ) ≠ 0) :
    (positivePolynomialValue Q n : ℕ) = (Q.eval (n : ℤ)).natAbs := by
  change max 1 (Q.eval (n : ℤ)).natAbs = _
  exact max_eq_right (Int.natAbs_pos.mpr hn)

theorem log_positivePolynomialValue (Q : ℤ[X]) (n : ℕ) :
    Real.log (positivePolynomialValue Q n : ℕ) = Real.log ((Q.eval (n : ℤ)).natAbs : ℝ) := by
  by_cases hn : Q.eval (n : ℤ) = 0
  · simp [positivePolynomialValue, hn]
  · rw [positivePolynomialValue_eq hn]

/-- The contribution of smooth prime factors to the logarithmic polynomial mass. -/
noncomputable def polynomialSmoothLogMass (Q : ℤ[X]) (x y z : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, Real.log (smoothPart (positivePolynomialValue Q n) z : ℕ)

/-- The contribution of rough prime factors to the logarithmic polynomial mass. -/
noncomputable def polynomialRoughLogMass (Q : ℤ[X]) (x y z : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, Real.log (roughPart (positivePolynomialValue Q n) z : ℕ)

theorem polynomialRoughLogMass_eq (Q : ℤ[X]) (x y z : ℝ) :
    polynomialRoughLogMass Q x y z = polynomialLogMass Q x y - polynomialSmoothLogMass Q x y z := by
  unfold polynomialRoughLogMass polynomialSmoothLogMass polynomialLogMass
  rw [sum_log_roughPart]
  simp only [log_positivePolynomialValue]

theorem polynomialSmoothLogMass_eq_primePower_counts (Q : ℤ[X]) (x y : ℝ) {z : ℝ}
    (hz : 0 ≤ z) (L : ℕ → ℕ)
    (hL : ∀ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, ∀ n ∈ shortInterval x y,
      (positivePolynomialValue Q n : ℕ).factorization p ≤ L p) :
    polynomialSmoothLogMass Q x y z =
      ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime,
        (∑ ν ∈ Icc 1 (L p), (((shortInterval x y).filter
          (fun n => p ^ ν ∣ (positivePolynomialValue Q n : ℕ))).card : ℝ)) * Real.log p :=
  sum_log_smoothPart_eq_primePower_counts _ _ hz L hL

/-- Only the upper bound for the small-prime mass remains to obtain a
quantitative lower bound for the rough mass. -/
theorem exists_polynomialRoughLogMass_lower_of_smooth_upper {Q : ℤ[X]} (hQ : Q ≠ 0)
    {β : ℝ} (hβ : 0 < β) :
    ∃ x₀ B : ℝ, 1 < x₀ ∧ 0 ≤ B ∧ ∀ x y z E : ℝ, x₀ < x → x ^ β ≤ y →
      polynomialSmoothLogMass Q x y z ≤ y * Real.log y + E →
        (Q.natDegree : ℝ) * y * Real.log x - y * Real.log y - (B * y + E) ≤
          polynomialRoughLogMass Q x y z := by
  obtain ⟨x₀, B, hx₀, hB, H⟩ := exists_polynomialLogMass_linear_error hQ hβ
  refine ⟨x₀, B, hx₀, hB, fun x y z E hx hy hs => ?_⟩
  rw [polynomialRoughLogMass_eq]
  linarith [H x y hx hy]

end NairTenenbaum

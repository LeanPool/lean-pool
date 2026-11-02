/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.SmoothValueScales

/-! # Small-value and bounded-smoothness errors at the Corollary 6 scales -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem smoothShortSum_mono {k : ℕ} (Q : Fin k → ℤ[X]) {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) (j : Fin k) (x y : ℝ) {z w : ℝ} (hzw : z ≤ w) :
    smoothShortSum Q F j x y z ≤ smoothShortSum Q F j x y w := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hnS, hns⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hnS, Nat.factoredNumbers_mono ?_ hns⟩
    exact Icc_subset_Icc le_rfl (Nat.floor_mono hzw)
  · exact fun n _ _ => extendArithmeticMap_nonneg hF _

theorem PolynomialSystem.smallValues_sum_power_bound {k r g : ℕ} (P : PolynomialSystem k r)
    (hdeg : P.total.natDegree = g) {A B σ : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    (j : Fin k) (hj : 0 < (P.Q j).natDegree) (S : Finset ℕ) {x c q : ℝ}
    (hx : 1 ≤ x) (hq : 0 ≤ q) (hmargin : c * σ ≤ 3 * q / 4)
    (hvalue : ∀ n ∈ S, ((P.total.eval (n : ℤ)).natAbs : ℝ) ≤ x ^ c) :
    (∑ n ∈ S.filter (fun n : ℕ => (((P.Q j).eval (n : ℤ)).natAbs : ℝ) ≤ x ^ (q / 8)),
      extendArithmeticMap F (fun i => ((P.Q i).eval (n : ℤ)).natAbs)) ≤
      (4 * (g : ℝ) * B) * x ^ (7 * q / 8) * F 1 := by
  have hx₀ : 0 < x := by linarith
  have HT : 1 ≤ x ^ (q / 8) := Real.one_le_rpow hx (by positivity)
  have H := P.smallValues_sum_le hF hB hσ j hj S hx₀.le
    (Real.rpow_nonneg hx₀.le (q / 8)) hvalue
  rw [hdeg] at H
  have Hcount : 2 * (g : ℝ) * (x ^ (q / 8) + 1) ≤ 4 * (g : ℝ) * x ^ (q / 8) := by
    nlinarith [mul_le_mul_of_nonneg_left HT (by positivity : (0 : ℝ) ≤ 2 * g)]
  have Hweight : B * x ^ (c * σ) * F 1 ≤ B * x ^ (3 * q / 4) * F 1 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx hmargin) hB) (hF.nonneg 1)
  have H' := H.trans (mul_le_mul Hcount Hweight
    (by positivity [hF.nonneg 1]) (by positivity : 0 ≤ 4 * (g : ℝ) * x ^ (q / 8)))
  apply H'.trans_eq
  calc
    _ = (4 * (g : ℝ) * B) * (x ^ (q / 8) * x ^ (3 * q / 4)) * F 1 := by ring
    _ = _ := by rw [← Real.rpow_add hx₀, show q / 8 + 3 * q / 4 = 7 * q / 8 by ring]

theorem PolynomialSystem.fixedSmooth_sum_power_bound {k r g : ℕ} (P : PolynomialSystem k r)
    (hdeg : P.total.natDegree = g) {A B σ : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    (j : Fin k) (hj : 0 < (P.Q j).natDegree) (S s : Finset ℕ) {x c q : ℝ}
    (hx : 1 ≤ x) (hc : 0 < c) (hq : 0 < q) (hmargin : c * σ ≤ 3 * q / 4)
    (hvalue : ∀ n ∈ S, ((P.total.eval (n : ℤ)).natAbs : ℝ) ≤ x ^ c) :
    (∑ n ∈ S.filter (fun n : ℕ => ((P.Q j).eval (n : ℤ)).natAbs ∈ Nat.factoredNumbers s),
      extendArithmeticMap F (fun i => ((P.Q i).eval (n : ℤ)).natAbs)) ≤
      (2 * (g : ℝ) * B * fixedSmoothCountBound s (q / (8 * c))) * x ^ (7 * q / 8) * F 1 := by
  have hx₀ : 0 < x := by linarith
  have hη : 0 < q / (8 * c) := by positivity
  have H := P.fixedSmooth_sum_le hF hB hσ j hj S s hx₀.le hη hvalue
  rw [hdeg, show c * (q / (8 * c)) = q / 8 by field_simp] at H
  have Hweight : B * x ^ (c * σ) * F 1 ≤ B * x ^ (3 * q / 4) * F 1 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx hmargin) hB) (hF.nonneg 1)
  have H' := H.trans (mul_le_mul_of_nonneg_left Hweight
    (mul_nonneg (mul_nonneg (by positivity) (fixedSmoothCountBound_pos s hη).le)
      (Real.rpow_nonneg hx₀.le _)))
  apply H'.trans_eq
  calc
    _ = (2 * (g : ℝ) * B * fixedSmoothCountBound s (q / (8 * c))) *
        (x ^ (q / 8) * x ^ (3 * q / 4)) * F 1 := by ring
    _ = _ := by rw [← Real.rpow_add hx₀, show q / 8 + 3 * q / 4 = 7 * q / 8 by ring]

end NairTenenbaum

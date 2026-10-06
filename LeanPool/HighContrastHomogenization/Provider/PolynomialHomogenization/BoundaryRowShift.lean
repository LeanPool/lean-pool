/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AdaptedCellExcessBoundary

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.BoundaryRowShift

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Shifting a geometric boundary row

Enlarging the containing cube shifts the spatial excess row by a fixed number
of generations.  The sharper boundary kernel is summable against any
nonnegative row controlled by the shifted fractional kernel.
-/

namespace HCPolySupport
namespace HighContrast

open scoped BigOperators

noncomputable section

private theorem boundary_weight_le_fractional_weight {rho : ℝ}
    (hrho1 : rho ≤ 1) (n : ℕ) :
    (3 : ℝ) ^ (-(n : ℤ)) ≤ (3 : ℝ) ^ (-rho * (n : ℝ)) := by
  rw [← Real.rpow_intCast]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  push_cast
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith only [hrho1, hn]

private theorem shifted_row_term_eq {rho : ℝ} (G n : ℕ) (k : ℤ)
    (B : ℤ → ℝ) :
    (3 : ℝ) ^ (rho * (G : ℝ)) *
        ((3 : ℝ) ^ (-rho * ((n + G : ℕ) : ℝ)) *
          B ((k + (G : ℕ)) - ((n + G : ℕ) : ℤ))) =
      (3 : ℝ) ^ (-rho * (n : ℝ)) * B (k - (n : ℤ)) := by
  have hindex : (k + (G : ℕ)) - ((n + G : ℕ) : ℤ) = k - (n : ℤ) := by
    push_cast
    omega
  rw [hindex, ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 2
  push_cast
  ring

/-- A shifted fractional row controls the sharper integer boundary row.  The
fixed shift appears only as its geometric prefactor. -/
theorem summable_boundary_row_and_tsum_le_shifted_row
    {rho : ℝ} (hrho1 : rho ≤ 1)
    (G : ℕ) (k : ℤ) (B : ℤ → ℝ) (hB0 : ∀ r, 0 ≤ B r)
    (hrow : Summable (fun n : ℕ =>
      (3 : ℝ) ^ (-rho * (n : ℝ)) *
        B ((k + (G : ℕ)) - (n : ℤ)))) :
    Summable (fun n : ℕ =>
      (3 : ℝ) ^ (-(n : ℤ)) * B (k - (n : ℤ))) ∧
      (∑' n : ℕ, (3 : ℝ) ^ (-(n : ℤ)) * B (k - (n : ℤ))) ≤
        (3 : ℝ) ^ (rho * (G : ℝ)) *
          ∑' n : ℕ, (3 : ℝ) ^ (-rho * (n : ℝ)) *
            B ((k + (G : ℕ)) - (n : ℤ)) := by
  let f : ℕ → ℝ := fun n =>
    (3 : ℝ) ^ (-(n : ℤ)) * B (k - (n : ℤ))
  let R : ℕ → ℝ := fun n =>
    (3 : ℝ) ^ (-rho * (n : ℝ)) *
      B ((k + (G : ℕ)) - (n : ℤ))
  let C : ℝ := (3 : ℝ) ^ (rho * (G : ℝ))
  have hC0 : 0 ≤ C := Real.rpow_nonneg (by norm_num) _
  have hf0 : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (by positivity) (hB0 (k - (n : ℤ)))
  have hR0 : ∀ n, 0 ≤ R n := fun n =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (hB0 ((k + (G : ℕ)) - (n : ℤ)))
  have htail : Summable (fun n => R (n + G)) :=
    hrow.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hpoint : ∀ n, f n ≤ C * R (n + G) := by
    intro n
    have hweight := boundary_weight_le_fractional_weight hrho1 n
    have hmul := mul_le_mul_of_nonneg_right hweight (hB0 (k - (n : ℤ)))
    simp only [f, R, C]
    rw [shifted_row_term_eq (rho := rho) G n k B]
    exact hmul
  have hmajor : Summable (fun n => C * R (n + G)) := htail.mul_left C
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hpoint hmajor
  refine ⟨hf, (hf.tsum_le_tsum hpoint hmajor).trans ?_⟩
  rw [tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ hC0
  have hsplit :
      (∑' n : ℕ, R n) =
        (∑ n ∈ Finset.range G, R n) + ∑' n : ℕ, R (n + G) := by
    exact (htail.sum_add_tsum_nat_add' (k := G)).symm
  rw [hsplit]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun n _ => hR0 n)

end

end HighContrast
end HCPolySupport

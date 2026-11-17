/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Algebra.Order.Star.Real

/-! # Finite sums encoded by independent geometric exponents -/

@[expose] public section

namespace NairTenenbaum

open Finset

theorem finite_sum_geometric_product_le {α ι : Type*} [Fintype ι]
    (T : Finset α) (e : α → ι → ℕ) (he : Set.InjOn e T)
    (w : ι → ℝ) (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∀ i, w i < 1) :
    (∑ a ∈ T, ∏ i, w i ^ e a i) ≤ ∏ i, (1 - w i)⁻¹ := by
  classical
  let N := T.sup (fun a => univ.sup (e a))
  let B := Fintype.piFinset (fun _ : ι => range (N + 1))
  have hmem (a : α) (ha : a ∈ T) : e a ∈ B := by
    apply Fintype.mem_piFinset.mpr
    intro i
    apply mem_range.mpr
    exact Nat.lt_succ_of_le ((le_sup (f := e a) (mem_univ i)).trans (le_sup (f := fun a =>
        univ.sup (e a)) ha))
  calc
    _ = ∑ f ∈ T.image e, ∏ i, w i ^ f i := (sum_image he).symm
    _ ≤ ∑ f ∈ B, ∏ i, w i ^ f i := sum_le_sum_of_subset_of_nonneg
      (by rintro f hf; obtain ⟨a, ha, rfl⟩ := mem_image.mp hf; exact hmem a ha)
      (fun f _ _ => prod_nonneg (fun i _ => pow_nonneg (hw₀ i) _))
    _ = ∏ i, ∑ k ∈ range (N + 1), w i ^ k := by exact sum_prod_piFinset _ _
    _ ≤ _ := by
      apply prod_le_prod₀ (fun i _ => sum_nonneg (fun k _ => pow_nonneg (hw₀ i) k))
      intro i _
      have H := (summable_geometric_of_lt_one (hw₀ i) (hw₁ i)).sum_le_tsum (range (N + 1))
        (fun k _ => pow_nonneg (hw₀ i) k)
      simpa only [tsum_geometric_of_lt_one (hw₀ i) (hw₁ i), one_div] using H

theorem one_sub_inv_le_exp_quadratic {t : ℝ} (ht₁ : t ≤ 1 / 2) :
    (1 - t)⁻¹ ≤ Real.exp (t + 2 * t ^ 2) := by
  have hd : 0 < 1 - t := by linarith
  have H : t / (1 - t) ≤ t + 2 * t ^ 2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - 2 * t by linarith)]
  calc
    _ = t / (1 - t) + 1 := by field_simp; ring
    _ ≤ Real.exp (t / (1 - t)) := Real.add_one_le_exp _
    _ ≤ _ := Real.exp_le_exp.mpr H

end NairTenenbaum

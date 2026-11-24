/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.CoprimePhase
public import LeanPool.ShellsortMean.ProductVariance

/-! Bounds on source residual variance from independent threshold bits. -/

@[expose] public section

namespace Shellsort
open scoped BigOperators

/-- Real-valued interval bound for the actual arithmetic-progression count. -/
theorem exists_source_residual_interval_real (h g j s : ℕ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hj : j < g) :
    ∃ a : ℝ, ∀ y : ℕ,
      a ≤ (g : ℝ) * sourcePrefixCount h g j s y - y ∧
      (g : ℝ) * sourcePrefixCount h g j s y - y ≤ a + (g - 1) := by
  obtain ⟨a, _, ha⟩ := exists_source_residual_interval h g j s hg hc hj
  refine ⟨-(a : ℝ), fun y => ?_⟩
  have hlo : -(a : ℝ) ≤ (g : ℝ) * sourcePrefixCount h g j s y - y := by
    exact_mod_cast (ha y).1
  have hup : (g : ℝ) * sourcePrefixCount h g j s y - y ≤ (g : ℝ) - 1 - a := by
    exact_mod_cast (ha y).2
  constructor
  · exact hlo
  · linarith

/-- For independent source counts, the variance bound holds for their genuine
modular residuals, with no bound on those counts and no assumed variance. -/
theorem source_product_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (count : ∀ i, β i → ℕ) (source : ι → ℕ)
    (hw0 : ∀ i y, 0 ≤ w i y) (hw1 : ∀ i, ∑ y, w i y = 1)
    (h g j : ℕ) (hg : 0 < g) (hc : Nat.Coprime h g) (hj : j < g) (c : ℝ) :
    centeredSecond (productWeight w) (fun x => c + ∑ i,
      ((g : ℝ) * sourcePrefixCount h g j (source i) (count i (x i)) - count i (x i))) ≤
      (Fintype.card ι : ℝ) * (g - 1) ^ 2 / 4 := by
  classical
  choose a ha using fun i => exists_source_residual_interval_real h g j (source i) hg hc hj
  have hv := productWeight_variance_le_ranges w
    (fun i y => (g : ℝ) * sourcePrefixCount h g j (source i) (count i y) - count i y)
    hw0 hw1 a (fun i => a i + (g - 1)) (fun i y => ha i (count i y)) c
  have he : (∑ i, (a i + ((g : ℝ) - 1) - a i) ^ 2 / 4) =
      (Fintype.card ι : ℝ) * (g - 1) ^ 2 / 4 := by
    simp only [add_sub_cancel_left, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  exact he ▸ hv

end Shellsort

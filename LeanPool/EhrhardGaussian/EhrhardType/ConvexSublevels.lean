/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.Basic
import Mathlib.Analysis.Convex.Deriv

/-! # Strict sublevels of finite convex functions

A nonconstant convex function is unbounded above. Under a probability measure
charging every nonempty open set, its strict sublevels therefore have mass below one.
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace EhrhardGaussian.EhrhardType

/-- A finite convex function with two different values is unbounded above. -/
theorem exists_lt_convex_of_nonconstant {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F : E → ℝ} (hF : ConvexOn ℝ univ F) (hn : ¬ ∀ x, F x = F 0) (M : ℝ) :
    ∃ x, M < F x := by
  obtain ⟨x, hx⟩ := not_forall.mp hn
  obtain ⟨x, y, hxy⟩ : ∃ x y, F x < F y := by
    rcases lt_or_gt_of_ne hx with h | h
    · exact ⟨x, 0, h⟩
    · exact ⟨0, x, h⟩
  let g : ℝ → ℝ := F ∘ AffineMap.lineMap x y
  have hg : ConvexOn ℝ univ g := by
    simpa only [preimage_univ] using hF.comp_affineMap (AffineMap.lineMap x y)
  have hg01 : g 0 < g 1 := by simpa [g] using hxy
  let m := g 1 - g 0
  have hm : 0 < m := sub_pos.mpr hg01
  let z := max 2 ((M - g 0 + 1) / m)
  have hz : 1 < z := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hs := hg.secant_mono_aux2 (x := 0) (y := 1) (z := z) (mem_univ _) (mem_univ _) (by norm_num)
    hz
  simp only [sub_zero, div_one] at hs
  have hs' : m * z ≤ g z - g 0 := (le_div_iff₀ (by linarith : 0 < z)).mp hs
  have hlarge : M - g 0 + 1 ≤ z * m :=
    (div_le_iff₀ hm).mp (le_max_right _ _)
  exact ⟨AffineMap.lineMap x y z, by change M < g z; nlinarith only [hs', hlarge]⟩

/-- The full-support nonconstant case cannot have an upper-endpoint atom of full mass. -/
theorem strict_sublevel_measure_lt_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] [IsOpenPosMeasure μ]
    {F : E → ℝ} (hF : ConvexOn ℝ univ F) (hcont : Continuous F)
    (hn : ¬ ∀ x, F x = F 0) (a : ℝ) : μ {x | F x < a} < 1 := by
  obtain ⟨x, hx⟩ := exists_lt_convex_of_nonconstant hF hn a
  have hpos : 0 < μ {x | a < F x} :=
    (isOpen_lt continuous_const hcont).measure_pos μ ⟨x, hx⟩
  have hcompl : 0 < μ {x | F x < a}ᶜ := hpos.trans_le (measure_mono (by
    intro y hy
    change a < F y at hy
    exact not_lt.mpr hy.le))
  apply lt_of_le_of_ne prob_le_one
  intro heq
  have hzero : μ {x | F x < a}ᶜ = 0 := by
    rw [measure_compl (isOpen_lt hcont continuous_const).measurableSet (measure_ne_top _ _),
      heq, measure_univ, tsub_self]
  exact hcompl.ne' hzero

end EhrhardGaussian.EhrhardType

end

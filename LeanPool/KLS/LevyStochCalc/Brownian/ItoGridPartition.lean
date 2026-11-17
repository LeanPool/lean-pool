/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFormulaGrid

/-!
# The uniform grid partitions the time axis

The cells `(tᵢ, tᵢ₊₁]` of the uniform grid on `[0, T]` are pairwise disjoint with union
`(0, T]`, so a lower integral over `[0, T]` is the sum of the lower integrals over the cells.

## Main statements

* `LevyStochCalc.Brownian.Ito.unifGrid_iUnion_Ioc` — the cells cover `(0, T]`.
* `LevyStochCalc.Brownian.Ito.lintegral_Icc_eq_sum_unifGrid` — the cellwise decomposition of a
  lower integral.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

/-- The cells of the uniform grid cover `(0, T]`. -/
theorem unifGrid_iUnion_Ioc {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    (⋃ i ∈ Finset.range m, Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)))
      = Set.Ioc (0 : ℝ) T := by
  ext s
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_Ioc, exists_prop]
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    refine ⟨lt_of_le_of_lt (by simpa using unifGrid_nonneg hT.le m i) hlo, ?_⟩
    exact hhi.trans (unifGrid_le hT.le (by omega) hm0)
  · rintro ⟨hs0, hsT⟩
    obtain ⟨i, hi, hlo, hhi⟩ := exists_unifGrid_cell hT hm0 hs0 hsT
    exact ⟨i, hi, hlo, hhi⟩

/-- The cells of the uniform grid are pairwise disjoint. -/
theorem unifGrid_pairwiseDisjoint {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    (Finset.range m : Set ℕ).PairwiseDisjoint
      fun i => Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)) := by
  have hmono : StrictMono (unifGrid T m) :=
    strictMono_nat_of_lt_succ fun i => unifGrid_lt_succ hT hm0 i
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine Set.disjoint_left.mpr fun s hs hs' => ?_
    exact absurd (hs.2.trans_lt (lt_of_le_of_lt (hmono.monotone hlt) hs'.1)) (lt_irrefl _)
  · refine Set.disjoint_left.mpr fun s hs hs' => ?_
    exact absurd (hs'.2.trans_lt (lt_of_le_of_lt (hmono.monotone hlt) hs.1)) (lt_irrefl _)

/-- A lower integral over `[0, T]` is the sum of the lower integrals over the grid cells. -/
theorem lintegral_Icc_eq_sum_unifGrid {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (f : ℝ → ℝ≥0∞) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, f s ∂volume
      = ∑ i ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), f s ∂volume := by
  rw [← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc,
    ← unifGrid_iUnion_Ioc hT hm0,
    MeasureTheory.lintegral_biUnion_finset (unifGrid_pairwiseDisjoint hT hm0)
      (fun i _ => measurableSet_Ioc) f]

end LevyStochCalc.Brownian.Ito

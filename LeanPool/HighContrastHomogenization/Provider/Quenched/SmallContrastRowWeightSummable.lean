/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitTsum

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRowWeightSummable

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Row weights: summability and the partition bound together

The relative-volume bound bounds the value of the row series but says
nothing about summability — in Mathlib `∑' f ≤ 1` holds of every unsummable `f`,
since an unsummable `tsum` is `0`.  Its consumer needs both: the burn split
replaces a dominating geometric series with a partition bound, and a partition
bound is not a domination, so summability has to come from somewhere else.

It comes from the same place the bound does — nonnegativity together with
uniformly bounded partial sums — and the partial sums are bounded because a
finite subfamily of a disjoint filling has total volume at most the parent's.
Both facts are recorded here, the first at the generality the bridge uses and
the second purely arithmetically.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **A finite disjoint subfamily has total relative volume at most one.**  This
is what bounds the partial sums of the row series. -/
theorem finset_relative_volume_le_one {ι : Type*} (s : Finset ι)
    {c : ι → Set (Vec d)} {T : Set (Vec d)}
    (hmeas : ∀ i ∈ s, MeasurableSet (c i))
    (hdisj : (s : Set ι).Pairwise (Function.onFun Disjoint c))
    (hsub : ∀ i ∈ s, c i ⊆ T)
    (hT : volume T ≠ ⊤) (hT0 : volume T ≠ 0) :
    ∑ i ∈ s, (volume (c i)).toReal / (volume T).toReal ≤ 1 := by
  have hTpos : (0 : ℝ) < (volume T).toReal := ENNReal.toReal_pos hT0 hT
  have hci : ∀ i ∈ s, volume (c i) ≠ ⊤ := by
    intro i hi
    exact ne_top_of_le_ne_top hT (measure_mono (hsub i hi))
  have hunion : ∑ i ∈ s, volume (c i) = volume (⋃ i ∈ s, c i) :=
    (measure_biUnion_finset hdisj hmeas).symm
  have hle : ∑ i ∈ s, volume (c i) ≤ volume T := by
    rw [hunion]
    exact measure_mono (Set.iUnion₂_subset hsub)
  have hreal : ∑ i ∈ s, (volume (c i)).toReal ≤ (volume T).toReal := by
    rw [← ENNReal.toReal_sum hci]
    exact ENNReal.toReal_mono hT hle
  rw [← Finset.sum_div, div_le_one hTpos]
  exact hreal

/-- **Summability and the bound, from nonnegativity and bounded partial sums.**
This is the conjunction the burn split's consumer needs; the bound alone is not
enough, because an unsummable family satisfies it vacuously. -/
theorem summable_and_tsum_le_one_of_sum_range_le {w : ℕ → ℝ}
    (hw0 : ∀ u, 0 ≤ w u)
    (hpartial : ∀ N : ℕ, ∑ u ∈ Finset.range N, w u ≤ 1) :
    Summable w ∧ ∑' u : ℕ, w u ≤ 1 := by
  have hS : Summable w := summable_of_sum_range_le hw0 hpartial
  exact ⟨hS, Real.tsum_le_of_sum_range_le hw0 hpartial⟩

end

end HCPolySupport.HighContrast.Quenched

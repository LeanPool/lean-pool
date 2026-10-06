/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain

/-!
# High-contrast homogenization: Provider.Recurrence.AdaptedPartitionAverage

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Averages over a partition up to a null set

`e.fixed.geometry.parent.child` weights the cells of a partition of `U` by
`|U_i| / |U|`, and the aligned subdivision of the coarse block is a partition
only up to a null set — the adapted cubes are open, so their union omits the
interior faces.  This file records what that costs: nothing.

The integral of an integrable function over the parent is the sum of the
integrals over the cells, because the parent and the union of the cells differ by
a null set and the cells are pairwise disjoint measurable sets; the same argument
with the constant function one gives `|U| = Σ |U_i|`, so the weights `|U_i| / |U|`
sum to one and the average over the parent is the weighted average of the
averages over the cells.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Integrals over a partition up to a null set -/

/-- The parent set and the union of the cells of a partition up to a null set
agree almost everywhere. -/
theorem ae_eq_iUnion_of_aePartition {ι : Type*} {U : Set (Vec d)} {Z : Finset ι}
    {c : ι → Set (Vec d)} (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hnull : volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) = 0) :
    U =ᵐ[volume] ⋃ i ∈ (↑Z : Set ι), c i := by
  refine ae_eq_set.mpr ⟨hnull, ?_⟩
  have hV : (⋃ i ∈ (↑Z : Set ι), c i) ⊆ U :=
    Set.iUnion₂_subset fun i hi => hsub i (Finset.mem_coe.mp hi)
  rw [Set.sdiff_eq_empty.mpr hV, measure_empty]

/-- **The integral over the parent is the sum of the integrals over the cells**,
for a finite family of pairwise disjoint measurable subsets covering the parent
up to a null set. -/
theorem setIntegral_eq_sum_of_aePartition {ι : Type*} {U : Set (Vec d)} {Z : Finset ι}
    {c : ι → Set (Vec d)} {g : Vec d → ℝ}
    (hmeas : ∀ i ∈ Z, MeasurableSet (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c)
    (hnull : volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) = 0)
    (hint : IntegrableOn g U volume) :
    ∫ x in U, g x = ∑ i ∈ Z, ∫ x in c i, g x := by
  have hrestrict : volume.restrict U = volume.restrict (⋃ i ∈ (↑Z : Set ι), c i) :=
    Measure.restrict_congr_set (ae_eq_iUnion_of_aePartition hsub hnull)
  have hcoe : (⋃ i ∈ (↑Z : Set ι), c i) = ⋃ i ∈ Z, c i := Finset.set_biUnion_coe Z c
  calc ∫ x in U, g x
      = ∫ x in ⋃ i ∈ Z, c i, g x := by rw [hrestrict, hcoe]
    _ = ∑ i ∈ Z, ∫ x in c i, g x :=
        integral_biUnion_finset Z hmeas hdisj fun i hi => hint.mono_set (hsub i hi)

/-- **The volume of the parent is the sum of the volumes of the cells.** -/
theorem measure_eq_sum_of_aePartition {ι : Type*} {U : Set (Vec d)} {Z : Finset ι}
    {c : ι → Set (Vec d)}
    (hmeas : ∀ i ∈ Z, MeasurableSet (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c)
    (hnull : volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) = 0) :
    volume U = ∑ i ∈ Z, volume (c i) := by
  have hcoe : (⋃ i ∈ (↑Z : Set ι), c i) = ⋃ i ∈ Z, c i := Finset.set_biUnion_coe Z c
  calc volume U
      = volume (⋃ i ∈ Z, c i) := by
        rw [← hcoe]
        exact measure_congr (ae_eq_iUnion_of_aePartition hsub hnull)
    _ = ∑ i ∈ Z, volume (c i) := measure_biUnion_finset hdisj hmeas

/-! ## Averages over a partition -/

/-- The cells of a partition of a set of finite volume have finite volume. -/
theorem measure_cell_ne_top_of_subset {U : Set (Vec d)} {V : Set (Vec d)}
    (hUtop : volume U ≠ ⊤) (hsub : V ⊆ U) : volume V ≠ ⊤ :=
  ne_top_of_le_ne_top hUtop (measure_mono hsub)

/-- **The weights `|U_i| / |U|` of `e.fixed.geometry.parent.child` sum to
one.** -/
theorem sum_weight_eq_one_of_aePartition {ι : Type*} {U : Set (Vec d)} {Z : Finset ι}
    {c : ι → Set (Vec d)}
    (hmeas : ∀ i ∈ Z, MeasurableSet (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c)
    (hnull : volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) = 0)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ⊤) :
    ∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal = 1 := by
  have htoReal : (volume U).toReal = ∑ i ∈ Z, (volume (c i)).toReal := by
    rw [measure_eq_sum_of_aePartition hmeas hsub hdisj hnull,
      ENNReal.toReal_sum fun i hi => measure_cell_ne_top_of_subset hUtop (hsub i hi)]
  rw [← Finset.sum_div, ← htoReal, div_self (ENNReal.toReal_pos hU0 hUtop).ne']

/-- **The average over the parent is the weighted average of the averages over
the cells**, with the weights `|U_i| / |U|` of
`e.fixed.geometry.parent.child`. -/
theorem volumeAverage_eq_sum_weight_of_aePartition {ι : Type*} {U : Set (Vec d)}
    {Z : Finset ι} {c : ι → Set (Vec d)} {g : Vec d → ℝ}
    (hmeas : ∀ i ∈ Z, MeasurableSet (c i)) (hsub : ∀ i ∈ Z, c i ⊆ U)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint c)
    (hnull : volume (U \ ⋃ i ∈ (↑Z : Set ι), c i) = 0)
    (hint : IntegrableOn g U volume)
    (hcell0 : ∀ i ∈ Z, volume (c i) ≠ 0) (hUtop : volume U ≠ ⊤) :
    volumeAverage U g =
      ∑ i ∈ Z, (volume (c i)).toReal / (volume U).toReal * volumeAverage (c i) g := by
  have hcellR : ∀ i ∈ Z,
      ∫ x in c i, g x = (volume (c i)).toReal * volumeAverage (c i) g := by
    intro i hi
    have hpos : (0 : ℝ) < (volume (c i)).toReal :=
      ENNReal.toReal_pos (hcell0 i hi) (measure_cell_ne_top_of_subset hUtop (hsub i hi))
    rw [volumeAverage, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  rw [volumeAverage, setIntegral_eq_sum_of_aePartition hmeas hsub hdisj hnull hint,
    Finset.sum_congr rfl hcellR, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end

end Recurrence
end HighContrast
end HCPolySupport

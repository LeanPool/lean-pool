/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationIndex
public import LeanPool.HighContrastHomogenization.Provider.Response.RowCellEnergyBound

/-!
# High-contrast homogenization: Provider.Response.NestedAlignedGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Nested aligned-cell geometry

Aligned cells subdivide in two stages by the mixed-radix label obtained from a
parent label and a centred residual label.  This gives both containment of the
nested label in the terminal index and an exact reindexing of normalized cell
averages.
-/

namespace HCPolySupport.HighContrast.Response

noncomputable section

variable {d : ℕ}

open scoped BigOperators

/-- **A two-stage aligned label remains aligned with the terminal cell.** -/
theorem nestedLabel_mem_alignedIndex {q : Mat d} (hq : q.PosDef)
    {k s t : ℤ} (hks : k ≤ s) (hst : s ≤ t)
    {w z : Fin d → ℤ} (hw : w ∈ alignedIndex q k s)
    (hz : z ∈ alignedIndex q s t) :
    nestedLabel k s z w ∈ alignedIndex q k t := by
  have hwCenter : adaptedCellCenter q k w ∈ adaptedCell q s :=
    (mem_alignedIndex_iff hq hks).mp hw
  have hzSubset : adaptedCellAt q s z ⊆ adaptedCell q t :=
    adaptedCellAt_subset_of_mem_alignedIndex hq hst hz
  have hsplit :
      adaptedCellCenter q k (nestedLabel k s z w) =
        adaptedCellCenter q s z + adaptedCellCenter q k w := by
    apply PortableHistory.adaptedCellCenter_split q hks
    intro i
    simp only [nestedLabel]
    ring
  apply (mem_alignedIndex_iff hq (hks.trans hst)).mpr
  apply hzSubset
  rw [Recurrence.adaptedCellAt_eq_translateSet, hsplit, mem_translateSet_iff_sub_mem]
  simpa only [add_sub_cancel_left] using hwCenter

private theorem sum_nestedLabel_alignedIndex {q : Mat d} (hq : q.PosDef)
    {k s t : ℤ} (hks : k ≤ s) (hst : s ≤ t)
    (f : (Fin d → ℤ) → ℝ) :
    ∑ w ∈ alignedIndex q k s, ∑ z ∈ alignedIndex q s t,
        f (nestedLabel k s z w) =
      ∑ v ∈ alignedIndex q k t, f v := by
  classical
  let source := (alignedIndex q k s).product (alignedIndex q s t)
  let target := alignedIndex q k t
  let embed : (Fin d → ℤ) × (Fin d → ℤ) → (Fin d → ℤ) :=
    fun wz ↦ nestedLabel k s wz.2 wz.1
  have hmaps : Set.MapsTo embed (↑source : Set ((Fin d → ℤ) × (Fin d → ℤ)))
      (↑target : Set (Fin d → ℤ)) := by
    intro wz hwz
    have hwz' := Finset.mem_product.mp hwz
    exact nestedLabel_mem_alignedIndex hq hks hst hwz'.1 hwz'.2
  have hsurj : Set.SurjOn embed
      (↑source : Set ((Fin d → ℤ) × (Fin d → ℤ)))
      (↑target : Set (Fin d → ℤ)) := by
    intro v hv
    have hvCenter : adaptedCellCenter q k v ∈ adaptedCell q t :=
      (mem_alignedIndex_iff hq (hks.trans hst)).mp hv
    obtain ⟨z, w, hz, hw, hlabel⟩ := PortableHistory.exists_index_split hq hks hst hvCenter
    refine ⟨(w, z), Finset.mem_product.mpr
      ⟨(mem_alignedIndex_iff hq hks).mpr hw,
        (mem_alignedIndex_iff hq hst).mpr hz⟩, ?_⟩
    funext i
    simp only [embed, nestedLabel]
    rw [hlabel i]
    ring
  have hscale : (t - k).toNat = (s - k).toNat + (t - s).toNat := by
    omega
  have hcard : source.card = target.card := by
    calc
      source.card =
          (alignedIndex q k s).card * (alignedIndex q s t).card := by
        exact Finset.card_product _ _
      _ = target.card := by
        dsimp only [target]
        rw [card_alignedIndex hq hks, card_alignedIndex hq hst,
          card_alignedIndex hq (hks.trans hst), hscale, Nat.mul_add, pow_add]
  have hinj : Set.InjOn embed
      (↑source : Set ((Fin d → ℤ) × (Fin d → ℤ))) :=
    Finset.injOn_of_surjOn_of_card_le embed hmaps hsurj hcard.le
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun wz _ ↦ embed wz) ?_ ?_ ?_ ?_
  · intro wz hwz
    exact hmaps hwz
  · intro wz hwz wz' hwz' heq
    exact hinj hwz hwz' heq
  · intro v hv
    obtain ⟨wz, hwz, heq⟩ := hsurj hv
    exact ⟨wz, hwz, heq⟩
  · intro wz _
    rfl

/-- **Two-stage normalized aligned-cell averaging is exact.** -/
theorem avsum_nestedLabel_alignedIndex {q : Mat d} (hq : q.PosDef)
    {k s t : ℤ} (hks : k ≤ s) (hst : s ≤ t)
    (f : (Fin d → ℤ) → ℝ) :
    avsum (alignedIndex q k s) (fun w ↦
        avsum (alignedIndex q s t) (fun z ↦ f (nestedLabel k s z w))) =
      avsum (alignedIndex q k t) f := by
  have hscale : (t - k).toNat = (s - k).toNat + (t - s).toNat := by
    omega
  have hcardNat :
      (alignedIndex q k s).card * (alignedIndex q s t).card =
        (alignedIndex q k t).card := by
    rw [card_alignedIndex hq hks, card_alignedIndex hq hst,
      card_alignedIndex hq (hks.trans hst), hscale, Nat.mul_add, pow_add]
  have hcardReal :
      ((alignedIndex q k s).card : ℝ) * ((alignedIndex q s t).card : ℝ) =
        ((alignedIndex q k t).card : ℝ) := by
    exact_mod_cast hcardNat
  simp only [avsum_eq]
  rw [← Finset.mul_sum, sum_nestedLabel_alignedIndex hq hks hst f,
    ← hcardReal, mul_inv]
  ring

end

end HCPolySupport.HighContrast.Response

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryPatch
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# The entry condition for a spoke in the entering sector

In the omitted assertion on XII page 243, a spoke in the same local
corner as the incoming curve has the required entry homotopy. Shrink
the sector patch, follow the spoke only until it leaves the patch, and
apply the common-patch criterion. This isolates the selection of the
spoke from the homotopy argument.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- A spoke entering the same sector as the approaching path satisfies
the entry homotopy condition of XII, page 243. The paths are read in the
region with its boundary vertex added. -/
theorem exists_sector_entry_neighbourhood {S : Type*} [TopologicalSpace S]
    {D W r Z : Set S} {v : Z}
    (hD : IsClosedDisc D) (hv : v.val ∈ discBd D)
    (hW : IsOpen W) (hvW : v.val ∈ W)
    (hlocal : ((D \ discBd D) ∩ W) ∪ {v.val} ⊆ Z)
    (hregion : (D \ discBd D) ∩ W ⊆ r) :
    ∃ N : Set S, IsOpen N ∧ v.val ∈ N ∧
      ∀ {a b : Z} (p : Path a v) (β : Path v b),
        a ≠ v →
        (∀ t, (p t).val ∈ ((N ∩ D) \ discBd D) ∪ {v.val}) →
        (∀ t, 0 < t → (β t).val ∈ r) →
        (∃ ε : unitInterval, 0 < ε ∧
          ∀ t, 0 < t → t ≤ ε → (β t).val ∈ D \ discBd D) →
        ∃ ρ : Path a b, (∀ t, (ρ t).val ∈ r) ∧ (p.trans β).Homotopic ρ := by
  obtain ⟨N, X, hN, hvN, hvX, hX, hXlocal, hnear, hpuncture⟩ :=
    exists_simplyConnected_sector_patch_with_puncture hD hv hW hvW
  refine ⟨N, hN, hvN, ?_⟩
  intro a b p β hav hp hβr hgerm
  obtain ⟨ε, hε, hεD⟩ := hgerm
  have hβN : (β 0).val ∈ N := by rw [β.source]; exact hvN
  obtain ⟨s, hs, hsε, hsN⟩ := GM11.exists_pos_le
    (continuous_subtype_val.comp β.continuous) hN hβN hε
  have hXsub : X ⊆ Z := fun _ hx => hlocal (hXlocal hx)
  have hXR : ∀ z : Z, z.val ∈ X \ {v.val} → z.val ∈ r := by
    intro z hz
    rcases hXlocal hz.1 with hzlocal | hzv
    · exact hregion hzlocal
    · exact (hz.2 hzv).elim
  have hpX : ∀ t, (p t).val ∈ X := by
    intro t
    rcases hp t with ht | ht
    · exact hnear ht
    · exact mem_singleton_iff.mp ht ▸ hvX
  have haX : a.val ∈ X \ {v.val} := by
    refine ⟨p.source ▸ hpX 0, ?_⟩
    intro hav'
    exact hav (Subtype.ext (mem_singleton_iff.mp hav'))
  have hsX : (β s).val ∈ X \ {v.val} := by
    have hsD := hεD s hs hsε
    refine ⟨hnear ⟨⟨hsN s le_rfl, hsD.1⟩, hsD.2⟩, ?_⟩
    intro hsv
    exact hsD.2 (mem_singleton_iff.mp hsv ▸ hv)
  have hprefix : ∀ t, ((β.subpath 0 s) t).val ∈ X := by
    intro t
    change (β (Icc.convexComb 0 s t)).val ∈ X
    have hle : Icc.convexComb 0 s t ≤ s := by
      change (1 - t.val) * 0 + t.val * s.val ≤ s.val
      simp only [mul_zero, zero_add]
      exact mul_le_of_le_one_left s.property.1 t.property.2
    by_cases ht0 : Icc.convexComb 0 s t = 0
    · rw [ht0, β.source]
      exact hvX
    · have hpos := unitInterval.pos_iff_ne_zero.mpr ht0
      have hmem := hεD _ hpos (hle.trans hsε)
      exact hnear ⟨⟨hsN _ hle, hmem.1⟩, hmem.2⟩
  have htail : ∀ t, ((β.subpath s 1) t).val ∈ r := by
    intro t
    apply hβr
    change (0 : ℝ) < (1 - t.val) * s.val + t.val * 1
    have hle : s.val ≤ (1 - t.val) * s.val + t.val * 1 := by
      nlinarith [t.property.1, s.property.2]
    exact lt_of_lt_of_le hs hle
  exact entry_homotopy_of_ambient_patch (R := Subtype.val ⁻¹' r)
    hX hXsub hpuncture hXR p β hpX haX s hsX hprefix htail

end GraphMinor.GM12

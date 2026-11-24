/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryPatch
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Comparing entries inside a normal patch

For the omitted entry lemma on XII page 243, shorten the approaching
path until it lies in the patch. Shorten the beginning of a spoke in
the same way. Both pieces lie in the simply connected patch and have
ends in its path-connected puncture. Replace their concatenation by
a path in that puncture, then append the rest of the spoke in the
region. This gives the entry comparison without a sector assumption.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 unitInterval

/-- A normal patch at a vertex compares any incoming region path
with any spoke leaving through that region, after shortening the
incoming path. -/
theorem entry_comparison_from_normal_patch
    {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {r N X : Set S} (hr : r ∈ Γ.R) {v : S}
    (hv : v ∈ Γ.V) (hN : IsOpen N) (hvN : v ∈ N) (hvX : v ∈ X)
    (hX : IsSimplyConnectedSet X) (hpuncture : IsPathConnected (X \ {v}))
    (hXZ : X ⊆ r ∪ {v}) (hcover : N \ Γ.U ⊆ X)
    {a : (r ∪ {v} : Set S)} {b : (r ∪ {v} : Set S)}
    (F : Path a (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S))) (β : Path (F 1) b)
    (hF : ∀ t, t < 1 → (F t).val ∈ r)
    (hβ : ∀ t, 0 < t → (β t).val ∈ r) :
    ∃ t : I, t < 1 ∧ ∃ ρ : Path (F t) b,
      (∀ s, (ρ s).val ∈ r) ∧ ((F.subpath t 1).trans β).Homotopic ρ := by
  have hvr : v ∉ r := fun h => region_subset hr h (Γ.V_subset_U hv)
  have hF1 : (F 1).val = v := congrArg Subtype.val F.target
  obtain ⟨δ, hδ, _, hδN⟩ := exists_pos_le
    (continuous_subtype_val.comp F.symm.continuous) hN
    (by simpa only [Function.comp_apply, Path.symm_apply, symm_zero, hF1] using hvN)
    (show (0 : I) < 1 from zero_lt_one)
  let t : I := σ δ
  have ht : t < 1 := by change (1 - δ.val : ℝ) < 1; exact sub_lt_self _ hδ
  have hterminal : ∀ u : I, t ≤ u → (F u).val ∈ N := by
    intro u htu
    have hback : σ u ≤ δ := by
      change 1 - u.val ≤ δ.val
      have htu' : 1 - δ.val ≤ u.val := htu
      linarith
    have hm := hδN (σ u) hback
    simpa only [Function.comp_apply, Path.symm_apply, symm_symm] using hm
  have hpX : ∀ s : I, ((F.subpath t 1) s).val ∈ X := by
    intro s
    let u := Icc.convexComb t 1 s
    change (F u).val ∈ X
    by_cases hu : u = 1
    · rw [hu, hF1]
      exact hvX
    · exact hcover ⟨hterminal u (Icc.le_convexComb (le_one t) s),
        region_subset hr (hF u (lt_of_le_of_ne u.property.2 hu))⟩
  have haX : (F t).val ∈ X \ {(F 1).val} := by
    refine ⟨?_, ?_⟩
    · exact (congrArg Subtype.val (F.subpath t 1).source) ▸ hpX 0
    · intro he
      have hm := hF t ht
      rw [mem_singleton_iff.mp he, hF1] at hm
      exact hvr hm
  obtain ⟨s, hs, _, hsN⟩ := exists_pos_le
    (continuous_subtype_val.comp β.continuous) hN
    (by change (β 0).val ∈ N; rw [β.source, hF1]; exact hvN)
    (show (0 : I) < 1 from zero_lt_one)
  have hβX : ∀ u : I, u ≤ s → (β u).val ∈ X := by
    intro u hus
    by_cases hu : u = 0
    · rw [hu, β.source, hF1]
      exact hvX
    · exact hcover ⟨hsN u hus, region_subset hr (hβ u (pos_iff_ne_zero.mpr hu))⟩
  have hsX : (β s).val ∈ X \ {(F 1).val} := by
    refine ⟨hβX s le_rfl, ?_⟩
    intro he
    have hm := hβ s hs
    rw [mem_singleton_iff.mp he, hF1] at hm
    exact hvr hm
  have hprefix : ∀ u : I, ((β.subpath 0 s) u).val ∈ X :=
    fun u => hβX _ (Icc.convexComb_le (nonneg s) u)
  have htail : ∀ u : I, ((β.subpath s 1) u).val ∈ r :=
    fun u => hβ _ (hs.trans_le (Icc.le_convexComb (le_one s) u))
  have hpuncture' : IsPathConnected (X \ {(F 1).val}) := by rwa [hF1]
  have hXR : ∀ z : (r ∪ {v} : Set S), z.val ∈ X \ {(F 1).val} → z.val ∈ r := by
    intro z hz
    rcases hXZ hz.1 with hzr | hzv
    · exact hzr
    · exact (hz.2 (hF1.symm ▸ hzv)).elim
  obtain ⟨ρ, hρ, hhom⟩ := entry_homotopy_of_ambient_patch (R := Subtype.val ⁻¹' r)
    hX hXZ hpuncture' hXR
    (F.subpath t 1) β hpX haX s hsX hprefix htail
  exact ⟨t, ht, ρ, hρ, hhom⟩

end GraphMinor.GM12

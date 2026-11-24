/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Corners
import LeanPool.GraphMinor.GM11.RadialCap
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# Small discs in corners for the local diversion in XII (7.2)

A corner between two half-edges has a small closed disc whose boundary
contains an initial part of each half-edge. The disc meets the drawing
only in those two initial parts. These discs allow a diversion near the
boundary vertex while keeping the outside drawing fixed.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
private theorem exists_small_parameter {f : I → S} (hf : Continuous f)
    {O : Set S} (hO : IsOpen O) (h0 : f 0 ∈ O) {τ : I} (hτ : 0 < τ) :
    ∃ t : I, 0 < t ∧ t < 1 ∧ t ≤ τ ∧ ∀ u, u ≤ t → f u ∈ O := by
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (hO.preimage hf) 0 h0
  let r : ℝ := min (ε / 2) (min τ.1 (1 / 2))
  have hr : 0 < r := by
    apply lt_min (by linarith)
    exact lt_min hτ (by norm_num)
  have hrτ : r ≤ τ.1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrhalf : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hrε : r ≤ ε / 2 := min_le_left _ _
  refine ⟨⟨r, hr.le, by linarith⟩, hr, by change r < 1; linarith, hrτ, ?_⟩
  intro u hu
  apply hb
  rw [Metric.mem_ball, Subtype.dist_eq]
  simp only [Set.Icc.coe_zero, Real.dist_eq, sub_zero]
  rw [abs_of_nonneg u.2.1]
  have hu' : u.1 ≤ r := hu
  linarith

/-- A small cap of a corner, used for the local diversion at the vertex in
XII (7.2), page 260. Its only points on the drawing are on its two spokes. -/
theorem exists_corner_cap (hS : IsClosedSurface S)
    {H : Drawing S} {γ : Set S → I → S} (hγ : EdgePar H γ)
    {v : S} {next : halfEdges H γ v → halfEdges H γ v}
    {ρ P Q : halfEdges H γ v → Set S} {W : Set S}
    {τ : halfEdges H γ v → I}
    (hsec : IsSectors H γ v next ρ P W Q τ) (k : halfEdges H γ v) :
    ∃ (t₀ t₁ : I) (D : Set S), 0 < t₀ ∧ t₀ < 1 ∧ 0 < t₁ ∧ t₁ < 1 ∧
      IsClosedDisc D ∧ D ⊆ W ∧ D ⊆ Q k ∧
      spoke γ k.1 '' Icc 0 t₀ ∪ spoke γ (next k).1 '' Icc 0 t₁ ⊆ discBd D ∧
      D ∩ H.U ⊆ spoke γ k.1 '' Icc 0 t₀ ∪ spoke γ (next k).1 '' Icc 0 t₁ := by
  have hz : ∀ i : halfEdges H γ v, spoke γ i.1 0 = v := fun i => (spoke_zero γ i.1).trans i.2.2
  obtain ⟨W', hW'o, hvW', hcap⟩ := exists_cap hS (hsec.disc k) (hsec.bd k) hsec.isOpen hsec.mem
  obtain ⟨t₀, ht₀, ht₀1, ht₀τ, ht₀W⟩ := exists_small_parameter (continuous_spoke hγ k.2.1) hW'o
    (by rw [hz]; exact hvW') (hsec.pos k)
  obtain ⟨t₁, ht₁, ht₁1, ht₁τ, ht₁W⟩ := exists_small_parameter (continuous_spoke hγ
    (next k).2.1) hW'o
    (by rw [hz]; exact hvW') (hsec.pos (next k))
  let A := spoke γ k.1 '' Icc 0 t₀
  let B := spoke γ (next k).1 '' Icc 0 t₁
  let a := spoke γ k.1 t₀
  let b := spoke γ (next k).1 t₁
  have hA : IsLineWithEnds A v a := by
    have h := isLine_spoke_piece hγ k.2.1 ht₀
    rwa [hz] at h
  have hB : IsLineWithEnds B v b := by
    have h := isLine_spoke_piece hγ (next k).2.1 ht₁
    rwa [hz] at h
  have hvA : v ∈ A := ⟨0, ⟨le_rfl, ht₀.le⟩, hz k⟩
  have hvB : v ∈ B := ⟨0, ⟨le_rfl, ht₁.le⟩, hz (next k)⟩
  have hAB : A ∩ B = {v} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hvA, hvB⟩)
    rintro x ⟨⟨s, hs, rfl⟩, t, ht, hts⟩
    by_cases hs0 : s = 0
    · exact mem_singleton_iff.mpr (by rw [hs0, hz])
    · have hspos : 0 < s := unitInterval.pos_iff_ne_zero.mpr hs0
      by_cases ht0 : t = 0
      · rw [ht0, hz] at hts
        exact mem_singleton_iff.mpr hts.symm
      · have htpos : 0 < t := unitInterval.pos_iff_ne_zero.mpr ht0
        have hne : k.1 ≠ (next k).1 := fun he => hsec.next_ne k (Subtype.ext he.symm)
        have hs1 := (spoke_eq_of_ne hγ k.2.1 (next k).2.1 hne hspos htpos hts.symm).1
        exact ((hs.2.trans_lt ht₀1).ne hs1).elim
  have hline : IsLineWithEnds (A ∪ B) a b := IsLineWithEnds.union hA hB hAB
  have hab : a ≠ b := by
    intro he
    have hmem : a ∈ A ∩ B :=
      ⟨⟨t₀, ⟨bot_le, le_rfl⟩, rfl⟩, t₁, ⟨bot_le, le_rfl⟩, he.symm⟩
    have hav : a = v := mem_singleton_iff.mp (hAB ▸ hmem)
    have h₀ := spoke_injective hγ k.2.1 (hav.trans (hz k).symm)
    exact ht₀.ne' h₀
  have hTbd : A ∪ B ⊆ discBd (Q k) := by
    rintro x (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact hsec.left k s (hs.2.trans ht₀τ)
    · exact hsec.right k s (hs.2.trans ht₁τ)
  have hTW : A ∪ B ⊆ W' := by
    rintro x (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ht₀W s hs.2
    · exact ht₁W s hs.2
  have hva : v ≠ a := by
    intro he
    have h₀ := spoke_injective hγ k.2.1 (he.symm.trans (hz k).symm)
    exact ht₀.ne' h₀
  have hvb : v ≠ b := by
    intro he
    have h₁ := spoke_injective hγ (next k).2.1 (he.symm.trans (hz (next k)).symm)
    exact ht₁.ne' h₁
  obtain ⟨C, D, _, _, _, _, hD, hDW, hDQ, hDb, hDbd⟩ :=
    hcap a b (A ∪ B) hab hline hTbd hTW (Or.inl hvA) hva hvb
  refine ⟨t₀, t₁, D, ht₀, ht₀1, ht₁, ht₁1, hD, hDW, hDQ, ?_, ?_⟩
  · rw [hDb]
    exact subset_union_left
  · rintro x ⟨hxD, hxH⟩
    have hxQ : x ∈ discBd (Q k) := by
      by_contra hxnot
      have hxP := hsec.inside k ⟨⟨hDW hxD, hDQ hxD⟩, hxnot⟩
      exact region_subset (hsec.corners.region k) (hsec.sub k hxP) hxH
    exact hDbd ⟨hxD, hxQ⟩

end GraphMinor.GM12

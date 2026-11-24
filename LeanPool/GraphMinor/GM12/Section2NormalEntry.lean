/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryExistence
import LeanPool.GraphMinor.GM12.Section2SectorCover

/-!
# An entering edge for a normal approach at a vertex of degree at least two

For the omitted entry lemma on XII page 243, a normal approach stays in
one sector near its endpoint. Normalize the approach in reverse, use
the closed sector cover and connectedness to choose the sector, then
apply the entry-edge existence theorem for that sector.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The entry edge exists at a vertex with at least two half-edges.
This proves that case of the omitted assertion in XII's trace definition,
page 243, directly from a normal approach and radial maximality. -/
theorem exists_entersLike_of_two_halfEdges {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) (h2 : 2 ≤ Nat.card (halfEdges Γ γ v))
    {r : Set S} (hr : r ∈ Γ.R) {w : S} (hw : w ∈ r) (hwV : w ∈ K.V)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c) (hfc : f c = v)
    (hinside : ∀ t ∈ Ioo a c, f t ∈ r) :
    ∃ e ∈ K.E, EntersLike f a c e r v w := by
  obtain ⟨next, ρ, P, W, Q, τ, hsec, hcover⟩ :=
    exists_sectors_with_cover hS Γ hγ hv h2
  let h₀ := (a + c) / 2
  have hh₀ : h₀ ∈ Ioo a c := ⟨by dsimp [h₀]; linarith, by dsimp [h₀]; linarith⟩
  have hpos : 0 < c - h₀ := sub_pos.mpr hh₀.2
  let g : unitInterval → S := fun t => f (c - t.val * (c - h₀))
  have hg : Continuous g := hf.comp (by fun_prop)
  have hg0 : g 0 = v := by simpa only [g, Icc.coe_zero, zero_mul, sub_zero] using hfc
  have hginside : ∀ t, 0 < t → g t ∈ r := by
    intro t ht
    apply hinside
    constructor
    · have hle := mul_le_of_le_one_left hpos.le t.property.2
      linarith [hh₀.1]
    · have hp := mul_pos (show (0 : ℝ) < t.val from ht) hpos
      linarith
  have hgoff : ∀ t, 0 < t → g t ∉ Γ.U := fun t ht => region_subset hr (hginside t ht)
  obtain ⟨k, ε, hε, hεQ, hερ⟩ := initially_in_given_corner hsec hcover hg hg0 hgoff
  obtain ⟨δ, hδ, hδε, hδW⟩ := GM11.exists_pos_le hg hsec.isOpen
    (hg0.symm ▸ hsec.mem) hε
  have hρr : ρ k = r := region_eq_of_mem (hsec.corners.region k) hr
    (hερ δ hδ hδε) (hginside δ hδ)
  let h := c - δ.val * (c - h₀)
  have hh : h ∈ Ioo a c := by
    constructor
    · have hle := mul_le_of_le_one_left hpos.le δ.property.2
      dsimp only [h]
      linarith [hh₀.1]
    · have hp := mul_pos (show (0 : ℝ) < δ.val from hδ) hpos
      dsimp only [h]
      linarith
  have hlocal : ∀ t ∈ Ico h c, f t ∈ ρ k ∩ (Q k \ discBd (Q k)) := by
    intro t ht
    let s : unitInterval := ⟨(c - t) / (c - h₀),
      div_nonneg (sub_nonneg.mpr ht.2.le) hpos.le, by
        apply (div_le_one hpos).mpr
        have hle := mul_le_of_le_one_left hpos.le δ.property.2
        dsimp only [h] at ht
        linarith [ht.1]⟩
    have hs : 0 < s := div_pos (sub_pos.mpr ht.2) hpos
    have hsδ : s ≤ δ := by
      change (c - t) / (c - h₀) ≤ δ.val
      apply (div_le_iff₀ hpos).mpr
      dsimp only [h] at ht
      linarith [ht.1]
    have hgs : g s = f t := by
      change f (c - (c - t) / (c - h₀) * (c - h₀)) = f t
      congr 1
      field_simp [ne_of_gt hpos]
      ring
    have hQ : g s ∈ Q k := hεQ s (hsδ.trans hδε)
    have hnot : g s ∉ discBd (Q k) := fun hbd =>
      hgoff s hs (hsec.bdU k ⟨hδW s hsδ, hbd⟩)
    rw [← hgs]
    exact ⟨hερ s hs (hsδ.trans hδε), hQ, hnot⟩
  have hwρ : w ∈ ρ k := hρr.symm ▸ hw
  obtain ⟨e, he, hentry⟩ := exists_entersLike_of_sector hS hrad hmax hE hv hsec hcover k hwρ hwV
    hh hf.continuousOn hfc hlocal
  exact ⟨e, he, hρr ▸ hentry⟩

end GraphMinor.GM12

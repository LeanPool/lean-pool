/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2Corners
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# The terminal sector of a real normal approach

For trace restriction in XII (2.1), pages 243--244, fix one sector
system at the common vertex. Every incoming or reversed outgoing
approach stays in one of these sectors near that vertex. Normalize
the approach backwards and apply the connected-sector selection
lemma, retaining a terminal real interval in the sector interior.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A continuous normal approach has a terminal interval in one
of the prescribed sector interiors and in that corner's region. -/
theorem exists_terminal_sector_of_approach
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    {γ : Set S → unitInterval → S} {v : S}
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ P Q : halfEdges Γ γ v → Set S} {W : Set S}
    {τ : halfEdges Γ γ v → unitInterval}
    (hsec : IsSectors Γ γ v next ρ P W Q τ)
    (hcover : W \ Γ.U ⊆ ⋃ k, Q k)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c) (hfc : f c = v)
    (hoff : ∀ t ∈ Ioo a c, f t ∉ Γ.U) :
    ∃ (k : halfEdges Γ γ v) (h : ℝ), h ∈ Ioo a c ∧
      ∀ t ∈ Ico h c, f t ∈ ρ k ∩ (Q k \ discBd (Q k)) := by
  let h₀ := (a + c) / 2
  have hh₀ : h₀ ∈ Ioo a c := ⟨by dsimp [h₀]; linarith, by dsimp [h₀]; linarith⟩
  have hpos : 0 < c - h₀ := sub_pos.mpr hh₀.2
  let g : unitInterval → S := fun t => f (c - t.val * (c - h₀))
  have hg : Continuous g := hf.comp (by fun_prop)
  have hg0 : g 0 = v := by simpa only [g, Icc.coe_zero, zero_mul, sub_zero] using hfc
  have hgoff : ∀ t, 0 < t → g t ∉ Γ.U := by
    intro t ht
    apply hoff
    constructor
    · have hle := mul_le_of_le_one_left hpos.le t.property.2
      linarith [hh₀.1]
    · have hp := mul_pos (show (0 : ℝ) < t.val from ht) hpos
      linarith
  obtain ⟨k, ε, hε, hεQ, hερ⟩ := initially_in_given_corner hsec hcover hg hg0 hgoff
  obtain ⟨δ, hδ, hδε, hδW⟩ := GM11.exists_pos_le hg hsec.isOpen
    (hg0.symm ▸ hsec.mem) hε
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
  exact ⟨k, h, hh, hlocal⟩

end GraphMinor.GM12

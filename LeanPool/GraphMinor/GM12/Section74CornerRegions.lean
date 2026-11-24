/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Corners
public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM12.Section74NoParallel
import LeanPool.GraphMinor.GM11.RadialFaces
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM07.Section3

/-!
# Distinct corner regions in the base case of XII (7.4)

The no-selected-disc case on pages 262--263 implies that the
corner regions at the vertex are distinct. Otherwise two paths
in different sectors join inside the same region and make a
normal circle through the vertex. Respectfulness selects its
disc. With no edge inside, the disc lies in the old region with
the vertex restored. A small connected set on its interior side
would then lie in both sectors, contrary to their intersection
being in the drawing. This is the sector argument used for XI's
radial corner lemma, now with the selected disc at the old vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 unitInterval

/-- In the no-selected-edge case of XII (7.4), distinct sectors
at the vertex belong to distinct regions of the drawing. -/
theorem corner_regions_injective_in_theorem_7_4_base
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    {c : S} (hv : c ∈ Γ.V)
    (hno : ∀ D F : Set S, IsClosedDisc D → IsOArc F → subBd D = F →
      (PaintingOrDrawing.drawing Γ).IsNormal F → F ∩ Γ.V = {c} →
      ((PaintingOrDrawing.drawing Γ).inter D, (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      ∀ e ∈ Γ.E, ¬ e ⊆ D)
    {γ : Set S → I → S}
    {next : halfEdges Γ γ c → halfEdges Γ γ c}
    {ρ P Q : halfEdges Γ γ c → Set S} {W : Set S} {τ : halfEdges Γ γ c → I}
    (hsec : IsSectors Γ γ c next ρ P W Q τ) : Function.Injective ρ := by
  intro k k' hρ
  by_contra hkk
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hcor := IsSectors.corners hsec
  have hpR : ρ k ∈ Γ.R := IsCorners.region hcor k
  have hcp : c ∉ ρ k := fun h => region_subset hpR h (Γ.V_subset_U hv)
  have hppath : IsPathConnected (ρ k) :=
    isPathConnected_of_isOpen hS (region_isOpen hpR) (region_isPreconnected hpR)
      (region_nonempty hpR)
  obtain ⟨g₁, hg₁, hi₁, h₁0, h₁⟩ := exists_path_into_disc (IsSectors.disc hsec k)
    (IsSectors.bd hsec k) (IsSectors.isOpen hsec) (IsSectors.mem hsec)
  obtain ⟨g₂, hg₂, hi₂, h₂0, h₂⟩ := exists_path_into_disc (IsSectors.disc hsec k')
    (IsSectors.bd hsec k') (IsSectors.isOpen hsec) (IsSectors.mem hsec)
  have hg₁p : ∀ t, 0 < t → g₁ t ∈ ρ k := fun t ht => by
    obtain ⟨a, b, d⟩ := h₁ t ht
    exact IsSectors.sub hsec k (IsSectors.inside hsec k ⟨⟨a, b⟩, d⟩)
  have hg₂p : ∀ t, 0 < t → g₂ t ∈ ρ k := fun t ht => by
    obtain ⟨a, b, d⟩ := h₂ t ht
    rw [hρ]
    exact IsSectors.sub hsec k' (IsSectors.inside hsec k' ⟨⟨a, b⟩, d⟩)
  obtain ⟨e, he, hei, he0, he1, hep, O, hO, hcO, hOr⟩ :=
    exists_chord_to_point hppath hcp (hg₂p 1 one_pos) hg₁ h₁0 hg₁p
  -- The first time after `0` at which `e` meets `g₂`.
  have hsame : ∀ t, t ≠ 0 → e t ∈ O → e t ∉ range g₂ := by
    rintro t ht htO ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hOr t htO
    have hne : e t ≠ c := fun h => hcp (h ▸ hep t ht)
    have ha0 : 0 < a := unitInterval.pos_iff_ne_zero.mpr fun h => hne (by rw [← ha, h, h₁0])
    have hb0 : 0 < b := unitInterval.pos_iff_ne_zero.mpr fun h => hne (by rw [← hb, h, h₂0])
    have hmem : e t ∈ Q k ∩ Q k' := ⟨ha ▸ (h₁ a ha0).2.1, hb ▸ (h₂ b hb0).2.1⟩
    exact region_subset hpR (hep t ht) (IsSectors.inter hsec k k' hkk hmem)
  obtain ⟨δ, hδ, hδa, hδO⟩ := exists_pos_le he hO (he0 ▸ hcO) (a := 1) one_pos
  let Z : Set I := Icc δ 1 ∩ e ⁻¹' range g₂
  have hZc : IsCompact Z := isCompact_Icc.inter_right
    ((isCompact_range hg₂).isClosed.preimage he)
  have hZne : Z.Nonempty := ⟨1, ⟨hδa, le_rfl⟩, ⟨1, he1.symm⟩⟩
  obtain ⟨t₀, ⟨ht₀I, s₀, hs₀⟩, ht₀min⟩ := hZc.exists_isLeast hZne
  have ht₀ : 0 < t₀ := hδ.trans_le ht₀I.1
  have hne₀ : e t₀ ≠ c := fun h => ht₀.ne' (hei (h.trans he0.symm))
  have hs₀0 : 0 < s₀ := unitInterval.pos_iff_ne_zero.mpr fun h => hne₀ (by rw [← hs₀, h, h₂0])
  have hl₁ : IsLineWithEnds (e '' Icc 0 t₀) c (e t₀) := he0 ▸ isLine_piece he hei ht₀
  have hl₂ : IsLineWithEnds (g₂ '' Icc 0 s₀) c (e t₀) := by
    have := isLine_piece hg₂ hi₂ hs₀0
    rwa [h₂0, hs₀] at this
  have hmeet : e '' Icc 0 t₀ ∩ g₂ '' Icc 0 s₀ ⊆ {c, e t₀} := by
    rintro y ⟨⟨a, ha, rfl⟩, b, -, hb⟩
    by_cases ha0 : a = 0
    · exact Or.inl (by rw [ha0, he0])
    · refine Or.inr ?_
      have hle : t₀ ≤ a := by
        by_cases hδa' : δ ≤ a
        · exact ht₀min ⟨⟨hδa', unitInterval.le_one _⟩, ⟨b, hb⟩⟩
        · have hal : a ≤ δ := (not_le.mp hδa').le
          exact (hsame a ha0 (hδO a hal) ⟨b, hb⟩).elim
      have : a = t₀ := le_antisymm ha.2 hle
      change e a = e t₀
      rw [this]
  have hJ : IsOArc (e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀) := isOArc_union hl₁ hl₂ hmeet
  have hJp : ∀ y ∈ e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀, y = c ∨ y ∈ ρ k := by
    rintro _ (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩)
    · by_cases ha : a = 0
      · exact Or.inl (by rw [ha, he0])
      · exact Or.inr (hep a ha)
    · by_cases ha : a = 0
      · exact Or.inl (by rw [ha, h₂0])
      · exact Or.inr (hg₂p a (unitInterval.pos_iff_ne_zero.mpr ha))
  let J := e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀
  have hvJ : c ∈ J := Or.inl ⟨0, ⟨le_rfl, ht₀.le⟩, he0⟩
  have hn : (PaintingOrDrawing.drawing Γ).IsNormal J := by
    intro x hx
    rcases hJp x hx.1 with hxc | hxr
    · exact hxc ▸ hv
    · exact (region_subset hpR hxr hx.2).elim
  have hJV : J ∩ Γ.V = {c} := by
    apply Subset.antisymm
    · intro x hx
      exact (hJp x hx.1).resolve_right (fun hxr => region_subset hpR hxr (Γ.V_subset_U hx.2))
    · exact singleton_subset_iff.mpr ⟨hvJ, hv⟩
  obtain ⟨Δ, hΔ, hbd, hm⟩ := hT.2.2.2 J hJ hn
    (by change (J ∩ Γ.V).ncard < θ; rw [hJV, ncard_singleton]; omega)
  have hNo := hno Δ J hΔ hJ hbd hn hJV hm
  obtain ⟨K, hK⟩ := exists_radialDrawing hS hT.1
  have hE : Γ.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hT.2.1 hθ
  have hVD := vertices_in_normal_vertex_disc_of_no_edges hS ⟨hT.1, hK.2.1⟩ hE hΔ hbd hn hJV hNo
  have hb : discBd Δ = J := (IsClosedDisc.frontier_eq_discBd hS hΔ).symm.trans
    ((subBd_eq_frontier Δ).symm.trans hbd)
  have hcb : c ∈ discBd Δ := hb.symm ▸ hvJ
  have hΔr : Δ ⊆ ρ k ∪ {c} := disc_subset_region_vertex_of_no_edges hS hΔ hb hvJ hn hVD hpR
    (fun x hx => (hJp x hx.1).resolve_left hx.2) hNo
  have hfree : Disjoint (Δ \ discBd Δ) Γ.U := by
    apply disjoint_left.mpr
    intro x hx hxG
    rcases hΔr hx.1 with hxr | hxc
    · exact region_subset hpR hxr hxG
    · exact hx.2 (hxc.symm ▸ hcb)
  obtain ⟨A, W₀, hW₀, hcW₀, hAc, hAΔ, hAb, hAX, -, hclA⟩ :=
    exists_half_nbhd hΔ (IsSectors.isOpen hsec).isClosed_compl hcb
      (fun h' => h' (IsSectors.mem hsec))
  have hAW : ∀ y ∈ A, y ∈ W := fun y hy => by
    by_contra hn
    exact disjoint_left.mp hAX hy hn
  have hAU : ∀ y ∈ A, y ∉ Γ.U := fun y hy hyU =>
    disjoint_left.mp hfree ⟨hAΔ hy, disjoint_left.mp hAb hy⟩ hyU
  -- A connected set off `H` near `c`, with a point of a sector interior in its closure, lies in the
  -- closed disc of that sector.
  have hinQ : ∀ j, ∀ z, z ∈ closure A → z ∈ Q j → z ∉ discBd (Q j) → A ⊆ Q j := by
    intro j z hzA hzQ hzb
    have hQd := IsSectors.disc hsec j
    have hAfr : Disjoint A (frontier (Q j)) := by
      rw [IsClosedDisc.frontier_eq_discBd hS hQd]
      exact disjoint_left.mpr fun y hy hyb => hAU y hy (IsSectors.bdU hsec j ⟨hAW y hy, hyb⟩)
    have hzint : z ∈ interior (Q j) := by
      have hnf : z ∉ frontier (Q j) := by
        rwa [IsClosedDisc.frontier_eq_discBd hS hQd]
      by_contra hni
      exact hnf ⟨subset_closure hzQ, hni⟩
    rcases subset_or_disjoint_of_frontier hQd.isClosed hAc hAfr with h' | h'
    · exact h'
    · obtain ⟨y, hyI, hyA⟩ := mem_closure_iff.mp hzA _ isOpen_interior hzint
      exact (disjoint_left.mp h' hyA (interior_subset hyI)).elim
  obtain ⟨t, ht, htt₀, htN⟩ := exists_pos_le he (hW₀.inter hO) (by rw [he0]; exact ⟨hcW₀, hcO⟩) ht₀
  obtain ⟨s, hs, hss₀, hsN⟩ := exists_pos_le hg₂ hW₀ (by rw [h₂0]; exact hcW₀) hs₀0
  have hzt : e t ∈ closure A := hclA ⟨(htN t le_rfl).1, hb ▸ Or.inl ⟨t, ⟨ht.le, htt₀⟩, rfl⟩⟩
  have hzs : g₂ s ∈ closure A := hclA ⟨hsN s le_rfl, hb ▸ Or.inr ⟨s, ⟨hs.le, hss₀⟩, rfl⟩⟩
  obtain ⟨a, ha⟩ := hOr t (htN t le_rfl).2
  have ha0 : 0 < a := unitInterval.pos_iff_ne_zero.mpr fun h =>
    ht.ne' (hei ((ha.symm.trans (by rw [h, h₁0])).trans he0.symm))
  have hA₁ : A ⊆ Q k := hinQ k _ hzt (ha ▸ (h₁ a ha0).2.1) (ha ▸ (h₁ a ha0).2.2)
  have hA₂ : A ⊆ Q k' := hinQ k' _ hzs (h₂ s hs).2.1 (h₂ s hs).2.2
  obtain ⟨y, -, hyA⟩ := mem_closure_iff.mp hzs _ isOpen_univ (mem_univ _)
  exact hAU y hyA (IsSectors.inter hsec k k' hkk ⟨hA₁ hyA, hA₂ hyA⟩)

end GraphMinor.GM12

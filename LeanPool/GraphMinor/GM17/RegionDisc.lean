/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section8
public import LeanPool.GraphMinor.Surface.CutRetract
public import LeanPool.GraphMinor.Surface.OpenDisc
public import LeanPool.GraphMinor.Surface.Disc

/-!
# Regions of a painting are open discs

We prove `RegionOpenDiscCriterionStatement`, the surface fact behind (8.1) of Graph Minors XVII
(page 181). Cap all cuffs, so that we
are in a surface without boundary, and apply Graph Minors VII, (4.2) (`open_disc`) to the region. A
region misses `bd(Σ)`, so it stays
open after capping.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

/-- (8.1) of Graph Minors XVII, the surface part: every region is an open disc when every `O`-arc
off `U(Γ)` bounds a disc off
`U(Γ)`. -/
theorem regionOpenDiscCriterion : RegionOpenDiscCriterionStatement := by
  unfold RegionOpenDiscCriterionStatement
  intro S _ hconn hS Γ hne hF r hr
  have hcS : CompactSpace S := hS.1
  have ht2 : T2Space S := hS.2.1
  obtain ⟨T, tT, j, K, hT, hj, hK, hu, hi, hconnT⟩ := exists_capAll S hS
  have hcT : ConnectedSpace T := hconnT hconn
  have ht2T : T2Space T := hT.2.1
  have hrsub : ∀ x ∈ r, x ∉ Γ.U := fun x hx => (arcComponentsIn_subset hr hx).2
  have hrpc := arcComponentsIn_isPathConnected hr
  have hint : ∀ x ∈ r, IsInteriorPoint x := fun x hx => by
    by_contra h
    exact hrsub x hx (Γ.bd_subset h)
  have hUc : IsOpen Γ.Uᶜ := Γ.isClosed_U.isOpen_compl
  have hro : IsOpen r := by
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    obtain ⟨V, hV, hxV, hsub, ⟨e⟩⟩ := (hint x hx).exists_subset hUc (hrsub x hx)
    have hVp : IsPathConnected V := by
      have h1 := isPathConnected_iff_pathConnectedSpace.mp isPathConnected_openUnitDisc
      exact isPathConnected_iff_pathConnectedSpace.mpr (e.symm.surjective.pathConnectedSpace
        e.symm.continuous)
    have h3 : V ⊆ r := subset_arcComponent_of_isPathConnected hr (fun y hy
      => ⟨mem_univ _, hsub hy⟩) hVp ⟨x, hxV, hx⟩
    exact Filter.mem_of_superset (hV.mem_nhds hxV) h3
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨s, cs, hs⟩ := (haveI : Nonempty S := ⟨x₀⟩; exists_sec hj.continuous hj.injective)
  have hYK : ∀ x ∈ r, j x ∉ K := fun x hx h => by
    have h1 : j x ∈ range j ∩ K := ⟨mem_range_self x, h⟩
    rw [hi] at h1
    obtain ⟨y, hy, he⟩ := h1
    exact (hj.injective he ▸ hy) (hint x hx)
  have hYo : IsOpen (j '' r) := by
    have hcl : IsClosed (K ∪ j '' rᶜ) := hK.union (hj.isClosedMap _ hro.isClosed_compl)
    convert hcl.isOpen_compl using 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ (h | ⟨x', hx', he⟩)
      · exact hYK x hx h
      · exact hx' (hj.injective he ▸ hx)
    · intro h
      have hy : y ∈ range j ∪ K := hu ▸ mem_univ y
      rcases hy with ⟨x, rfl⟩ | hy
      · by_contra h3
        exact h (.inr ⟨x, fun hx => h3 ⟨x, hx, rfl⟩, rfl⟩)
      · exact absurd (.inl hy) h
  have hYc : IsConnected (j '' r) := hrpc.isConnected.image _ hj.continuous.continuousOn
  have hYF : ∀ F : Set T, F ⊆ j '' r → IsOArc F → ∃ Δ : Set T, Δ ⊆ j '' r ∧ IsClosedDisc Δ
    ∧ discBd Δ = F := by
    intro F hFr hO
    have hFj : F ⊆ range j := fun y hy => image_subset_range _ _ (hFr hy)
    have hs' : ∀ y ∈ F, j (s y) = y := fun y hy => by
      obtain ⟨x, rfl⟩ := hFj hy
      rw [hs]
    have hO' : IsOArc (s '' F) := hO.image (cs.mono hFj) (hj.continuous.continuousOn) fun y hy
      => hs' y hy
    have hsr : s '' F ⊆ r := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hFr hy
      rwa [hs]
    obtain ⟨Δ, hΔ, hb, hd⟩ := hF _ hO' (disjoint_left.mpr fun x hx => hrsub x (hsr hx))
    have hΔr : Δ ⊆ r := by
      refine subset_arcComponent_of_isPathConnected hr (fun y hy => ⟨mem_univ _,
        disjoint_left.mp hd hy⟩)
        (isPathConnected_of_isClosedDisc_finite_diff hΔ Subset.rfl (by simp)) ?_
      obtain ⟨φ⟩ := hO'
      obtain ⟨x, h5⟩ := φ 1
      have h6 : x ∈ discBd Δ := hb ▸ h5
      obtain ⟨z, -, hz⟩ := h6
      exact ⟨x, hz ▸ z.2, hsr h5⟩
    obtain ⟨h1, h2⟩ := hΔ.image (f := j) (f' := s) hj.continuous.continuousOn (cs.mono
      (image_subset_range _ _)) fun x _ => hs x
    refine ⟨_, image_mono hΔr, h1, ?_⟩
    rw [h2, hb, image_image]
    exact (image_congr hs').trans (image_id' F)
  rcases open_disc T (j '' r) hT hcT hYc hYo hYF with ⟨-, h⟩ | ⟨-, ⟨e⟩⟩
  · obtain ⟨x, hx, he⟩ := h ▸ mem_univ (j x₀)
    exact (hrsub x hx (hj.injective he ▸ hx₀)).elim
  · exact ⟨hro, ⟨e.trans (hj.isEmbedding.homeomorphImage r).symm⟩⟩

end GraphMinor.GM17

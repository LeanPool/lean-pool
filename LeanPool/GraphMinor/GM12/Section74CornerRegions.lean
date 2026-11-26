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
  refine corner_regions_ne_of_free_disc hS (Γ.V_subset_U hv) hsec hkk ?_ hρ
  intro J hJ hvJ hJp
  have hpR : ρ k ∈ Γ.R := IsCorners.region (IsSectors.corners hsec) k
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
  exact ⟨Δ, hΔ, hb, hfree⟩

end GraphMinor.GM12

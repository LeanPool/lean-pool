/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CircleFibreParameters
public import LeanPool.GraphMinor.GM12.Section73CollapseHomotopy
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section2InsideHomotopy
import LeanPool.GraphMinor.GM12.Section2NormalNoncover
import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.GM11.Regions

/-!
# Comparing selected discs outside the merged region

For XII (7.3), Claim (1), page 262, the old circuit collapses
onto the new one. Its intersection with the star is one point
or one arc. Parameterize both circles and use the disc-supported
homotopy to compare them away from the merged region. The tangle
supplies a drawing point outside both selected discs. For any
other point outside the region, homotopy in the surface punctured
at these two points determines which side of each circle it lies
on. The selected discs therefore agree outside the region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 Hypergraph

/-- Selected discs bounded by a circle and its star-collapse
image agree outside the merged region. This is the topological
inside comparison in XII (7.3), Claim (1), page 262. The fibre
shape describes the two old circuit alternatives. -/
theorem selected_discs_agree_outside_collapsed_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle (PaintingOrDrawing.drawing Γ).toHypergraph θ T)
    {r : Set S} (hr : r ∈ Γ.R)
    {D E B F G A : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hB : IsClosedDisc B) (hBr : B ⊆ r) (hAB : A ⊆ discInt B)
    (hbdD : subBd D = F) (hbdE : subBd E = G)
    (hnF : Γ.IsNormal F) (hnG : Γ.IsNormal G)
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hmE : ((PaintingOrDrawing.drawing Γ).inter E,
      (PaintingOrDrawing.drawing Γ).interOutside E) ∈ T)
    (hF : IsOArc F)
    (hshape : (F ∩ A).Subsingleton ∨ ∃ p q, IsLineWithEnds (F ∩ A) p q)
    (f : C(S, S)) (hfixB : ∀ x ∉ discInt B, f x = x)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (himage : f '' F = G) : D \ r = E \ r := by
  have hFD : F ⊆ D := by
    rw [← hbdD, subBd_eq_frontier]
    exact hD.isClosed.frontier_subset
  have hGE : G ⊆ E := by
    rw [← hbdE, subBd_eq_frontier]
    exact hE.isClosed.frontier_subset
  have hnD : (PaintingOrDrawing.drawing Γ).IsNormal (frontier D) := by
    rw [← subBd_eq_frontier, hbdD]
    exact hnF
  have hnE : (PaintingOrDrawing.drawing Γ).IsNormal (frontier E) := by
    rw [← subBd_eq_frontier, hbdE]
    exact hnG
  obtain ⟨q, hqΓ, hqD, hqE⟩ := exists_support_point_outside_two_small_sides hT
    hD.isClosed hE.isClosed hnD hnE hmD hmE
  have hqr : q ∉ r := fun hqr => region_subset hr hqr hqΓ
  have hAr : A ⊆ r := hAB.trans ((Surface.discInt_subset B).trans hBr)
  have hfix : ∀ x ∉ r, f x = x := fun x hxr => hfixB x
    (fun hxB => hxr (hBr (Surface.discInt_subset B hxB)))
  have hmem : ∀ x ∉ r, x ∈ D ↔ x ∈ E := by
    intro x hxr
    by_cases hxF : x ∈ F
    · have hxG : x ∈ G := himage ▸ ⟨x, hxF, hfix x hxr⟩
      exact iff_of_true (hFD hxF) (hGE hxG)
    have hxG : x ∉ G := by
      intro hxG
      obtain ⟨y, hyF, hfy⟩ := himage.symm ▸ hxG
      rcases (hfibre y x).mp (hfy.trans (hfix x hxr).symm) with hyx | hA
      · exact hxF (hyx ▸ hyF)
      · exact hxr (hAr hA.2)
    let Z : Set S := ({x, q} : Set S)ᶜ
    have hFZ : F ⊆ Z := by
      intro y hy hpair
      rcases hpair with hyx | hyq
      · exact hxF (hyx ▸ hy)
      · exact hqD (hFD (hyq ▸ hy))
    have hGZ : G ⊆ Z := by
      intro y hy hpair
      rcases hpair with hyx | hyq
      · exact hxG (hyx ▸ hy)
      · exact hqE (hGE (hyq ▸ hy))
    have hBZ : B ⊆ Z := by
      intro y hy hpair
      rcases hpair with hyx | hyq
      · exact hxr (hBr (hyx ▸ hy))
      · exact hqr (hBr (hyq ▸ hy))
    obtain ⟨φ, ψ, hφ, hψ, hφrange, hψrange, hcollapse⟩ :=
      exists_circle_parameters_of_fibre_shape hF hshape f hfibre (himage.symm ▸ hGZ)
    have hψrange' : range ψ = G := hψrange.trans himage
    have hφZ : range φ ⊆ Z := hφrange.symm ▸ hFZ
    have hdeform := closedCurve_homotopic_under_disc_collapse hS hB hAB f hfixB hfibre φ hφZ hBZ
    exact mem_disc_iff_of_boundary_homotopy hS hφ hψ hD hE
      (hbdD.trans hφrange.symm) (hbdE.trans hψrange'.symm) hqD hqE (hdeform.trans hcollapse)
  ext x
  exact and_congr_left (fun hx => hmem x hx)

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73ProperArcCircle
public import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.Surface.Jordan
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM12.Section72RadialDeletion

/-!
# An added spoke splits an old disc face

For maximality in XII (7.3), page 261, compare the cleaned drawing
with a radial extension having the same vertices. Any added edge
lies in one old disc face and has its ends on the old drawing.
Compactify that face. The added edge becomes a circle in a sphere,
whose two Jordan sides give distinct regions of the extension inside
the old face. This will contradict uniqueness of surviving drawing
edges in each old face.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 OnePoint

/-- An added edge with distinct ends splits a face of a two-cell
spanning subdrawing into at least two regions. This is the face
refinement used for maximality in XII (7.3), page 261. -/
theorem exists_two_regions_in_old_face
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H K : Drawing S} (hHK : H.IsSubdrawing K)
    (hV : H.V = K.V) (hH : (PaintingOrDrawing.drawing H).IsTwoCell)
    {g : Set S} (hg : g ∈ K.E) (hgn : g ∉ H.E)
    {a b : S} (hline : IsLineWithEnds (closure g) a b)
    (hcap : closure g ∩ K.V = {a, b}) :
    ∃ A ∈ H.R, ∃ p ∈ K.R, ∃ q ∈ K.R, p ≠ q ∧ p ⊆ A ∧ q ⊆ A := by
  let : CompactSpace S := hS.1
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hgdis : Disjoint g H.U := disjoint_left.mpr fun x hxg hxH =>
    hgn (edge_mem_of_meets_subdrawing hHK hg ⟨x, hxg, hxH⟩)
  obtain ⟨x, hxg⟩ := hg.1
  obtain ⟨A, hA, hxA⟩ := exists_region_of_notMem (disjoint_left.mp hgdis hxg)
  have hgA : g ⊆ A := subset_region hA hg.2.2.1.isConnected.isPreconnected hgdis hxg hxA
  have haV : a ∈ H.V := hV.symm ▸ (hcap.superset (Or.inl rfl)).2
  have hbV : b ∈ H.V := hV.symm ▸ (hcap.superset (Or.inr rfl)).2
  have han : a ∉ A := fun haA => region_subset hA haA (H.V_subset_U haV)
  have hbn : b ∉ A := fun hbA => region_subset hA hbA (H.V_subset_U hbV)
  have hinside : closure g \ {a, b} ⊆ A := by
    rintro y ⟨hyg, hyn⟩
    apply hgA
    exact (K.closure_diff_V hg).subset ⟨hyg, fun hyV => hyn (hcap.subset ⟨hyg, hyV⟩)⟩
  let F : Set (OnePoint A) := collapse A '' closure g
  have hF : IsOArc F := isOArc_collapse_proper_line (hH.2 A hA) hline han hbn hinside
  have hinfF : (∞ : OnePoint A) ∈ F := ⟨a, (hcap.superset (Or.inl rfl)).1, collapse_of_notMem han⟩
  have hsphere := isSphere_onePoint (hH.2 A hA)
  obtain ⟨hSA, hconnA⟩ := IsSphere.isClosedSurface hsphere
  let : T2Space (OnePoint A) := hSA.2.1
  let : ConnectedSpace (OnePoint A) := hconnA
  let : LocallyConnectedSpace (OnePoint A) := IsClosedSurface.locallyConnectedSpace hSA
  obtain ⟨C, hCU, _⟩ := exists_loop_drawing hF hinfF
  obtain ⟨B₁, B₂, hsplit⟩ := jordan_sphere hsphere hF
  have hB₁ : B₁ ∈ C.R := by
    change B₁ ∈ componentsIn (univ \ C.U)
    rw [hCU, hsplit.2.1]
    exact Or.inl rfl
  have hB₂ : B₂ ∈ C.R := by
    change B₂ ∈ componentsIn (univ \ C.U)
    rw [hCU, hsplit.2.1]
    exact Or.inr rfl
  have hc : Continuous (collapse A) := continuous_collapse (hH.2 A hA).1
  have hpreinside : ∀ B ∈ C.R, collapse A ⁻¹' B ⊆ A := by
    intro B hB y hyB
    by_contra hyn
    have hyinf : collapse A y = ∞ := collapse_of_notMem hyn
    exact region_subset hB hyB (hyinf.symm ▸ (hCU.symm ▸ hinfF))
  have hprene : ∀ B ∈ C.R, (collapse A ⁻¹' B).Nonempty := by
    intro B hB
    obtain ⟨z, hzB⟩ := region_nonempty hB
    induction z using OnePoint.rec with
    | infty => exact False.elim (region_subset hB hzB (hCU.symm ▸ hinfF))
    | coe z =>
      refine ⟨z.val, ?_⟩
      change collapse A z.val ∈ B
      rw [collapse_of_mem z.property]
      exact hzB
  obtain ⟨y₁, hy₁, hy₁K⟩ := exists_notMem_U (Γ := K) hS
    ((region_isOpen hB₁).preimage hc) (hprene B₁ hB₁)
  obtain ⟨y₂, hy₂, hy₂K⟩ := exists_notMem_U (Γ := K) hS
    ((region_isOpen hB₂).preimage hc) (hprene B₂ hB₂)
  obtain ⟨p, hp, hy₁p⟩ := exists_region_of_notMem hy₁K
  obtain ⟨q, hq, hy₂q⟩ := exists_region_of_notMem hy₂K
  have hpA : p ⊆ A := subset_region hA (region_isPreconnected hp)
    (disjoint_left.mpr fun z hzp hzH => region_subset hp hzp (hHK.U_subset hzH))
    hy₁p (hpreinside B₁ hB₁ hy₁)
  have hqA : q ⊆ A := subset_region hA (region_isPreconnected hq)
    (disjoint_left.mpr fun z hzq hzH => region_subset hq hzq (hHK.U_subset hzH))
    hy₂q (hpreinside B₂ hB₂ hy₂)
  refine ⟨A, hA, p, hp, q, hq, ?_, hpA, hqA⟩
  intro hpq
  have hy₂p : y₂ ∈ p := hpq.symm ▸ hy₂q
  have hpavoid : ∀ z ∈ p, collapse A z ∉ C.U := by
    intro z hzp hzC
    have hzA := hpA hzp
    have hzfinite : collapse A z ≠ ∞ := collapse_ne_infty_iff.mpr hzA
    rw [hCU] at hzC
    obtain ⟨w, hwg, hwz⟩ := hzC
    have hwA : w ∈ A := collapse_ne_infty_iff.mp (fun hwinf => hzfinite (hwz.symm.trans hwinf))
    have hwz' : w = z := collapse_injOn A hwA hzA hwz
    exact region_subset hp hzp (K.closure_subset_U hg (hwz' ▸ hwg))
  have hpcover : p ⊆ (collapse A ⁻¹' B₁) ∪ (collapse A ⁻¹' B₂) := by
    intro z hzp
    obtain ⟨B, hB, hzB⟩ := exists_region_of_notMem (hpavoid z hzp)
    have hBB : B = B₁ ∨ B = B₂ := by
      change B ∈ componentsIn (univ \ C.U) at hB
      rw [hCU, hsplit.2.1] at hB
      exact hB
    rcases hBB with rfl | rfl
    · exact Or.inl hzB
    · exact Or.inr hzB
  have hBdis : Disjoint B₁ B₂ := disjoint_left.mpr fun z hz₁ hz₂ =>
    hsplit.1 (region_eq_of_mem hB₁ hB₂ hz₁ hz₂)
  rcases (region_isPreconnected hp).subset_or_subset
      ((region_isOpen hB₁).preimage hc) ((region_isOpen hB₂).preimage hc)
      (hBdis.preimage (collapse A)) hpcover with hin₁ | hin₂
  · exact disjoint_left.mp hBdis (hin₁ hy₂p) hy₂
  · exact disjoint_left.mp hBdis hy₁ (hin₂ hy₁p)

end GraphMinor.GM12

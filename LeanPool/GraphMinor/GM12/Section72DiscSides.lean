/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72Regions
public import LeanPool.GraphMinor.GM11.GlueDiscs
import LeanPool.GraphMinor.GM11.PerimeterExists

/-!
# The two sides of the boundary circle inside its region

In XII (7.2), the boundary of the removed disc lies in an open-disc
region except at one vertex. Collapse the complement of that region.
The circle is still embedded in the resulting sphere. Its two sides
are the two Jordan discs there. This identifies the part of the old
region inside the removed disc with the interior of one of those discs.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 OnePoint

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The two open sides of a circle partitioning a sphere cannot be split
further by an open set whose frontier lies on that circle. -/
private theorem eq_discInt_of_two_sides
    {X : Type*} [TopologicalSpace X]
    {B C O T : Set X} (hB : IsClosedDisc B) (hC : IsClosedDisc C)
    (hbB : discBd B = O) (hbC : discBd C = O)
    (hu : B ∪ C = univ) (_hi : B ∩ C = O)
    (hTo : IsOpen T) (hclT : closure T ⊆ T ∪ O) (hdis : Disjoint T O)
    (hne : T.Nonempty) (hout : ∃ z, z ∉ O ∧ z ∉ T) :
    T = discInt B ∨ T = discInt C := by
  have cover : ∀ {z}, z ∉ O → z ∈ discInt B ∨ z ∈ discInt C := by
    intro z hz
    rcases hu ▸ mem_univ z with hzB | hzC
    · exact Or.inl ⟨hzB, hbB.symm ▸ hz⟩
    · exact Or.inr ⟨hzC, hbC.symm ▸ hz⟩
  have fill : ∀ {D : Set X}, IsClosedDisc D → discBd D = O →
      (discInt D ∩ T).Nonempty → discInt D ⊆ T := by
    intro D hD hb hmeet
    refine hD.isPreconnected_discInt.subset_of_closure_inter_subset hTo hmeet ?_
    rintro z ⟨hzcl, hzD⟩
    exact (hclT hzcl).resolve_right (hb ▸ hzD.2)
  have key : ∀ {D E : Set X}, IsClosedDisc D → IsClosedDisc E →
      discBd D = O → discBd E = O →
      (∀ {z}, z ∉ O → z ∈ discInt D ∨ z ∈ discInt E) →
      (discInt D ∩ T).Nonempty → T = discInt D := by
    intro D E hD hE hbD hbE hcover hmeet
    have hDT := fill hD hbD hmeet
    apply Subset.antisymm _ hDT
    intro z hzT
    rcases hcover (disjoint_left.mp hdis hzT) with hzD | hzE
    · exact hzD
    · have hET := fill hE hbE ⟨z, hzE, hzT⟩
      obtain ⟨p, hpO, hpT⟩ := hout
      rcases hcover hpO with hpD | hpE
      · exact (hpT (hDT hpD)).elim
      · exact (hpT (hET hpE)).elim
  obtain ⟨z, hzT⟩ := hne
  rcases cover (disjoint_left.mp hdis hzT) with hzB | hzC
  · exact Or.inl (key hB hC hbB hbC (fun hz => cover hz) ⟨z, hzB, hzT⟩)
  · exact Or.inr (key hC hB hbC hbB (fun hz => (cover hz).symm) ⟨z, hzC, hzT⟩)

/-- In XII (7.2), page 260, the boundary circle meets its old region in
all but the one vertex. On compactifying the region, the part inside the
removed disc is exactly one Jordan-disc interior. -/
theorem theorem_7_2_disc_side (hS : IsClosedSurface S)
    {r Δ : Set S} {v : S} (hr : IsOpenDisc r) (hΔ : IsClosedDisc Δ)
    (hv : v ∈ discBd Δ) (hvr : v ∉ r) (hbr : discBd Δ \ {v} ⊆ r) :
    ∃ B : Set (OnePoint r), IsClosedDisc B ∧
      discBd B = collapse r '' discBd Δ ∧
      collapse r '' (discInt Δ ∩ r) = discInt B := by
  have : CompactSpace S := hS.1
  have : T2Space (OnePoint r) := by
    obtain ⟨e⟩ := isSphere_onePoint hr
    exact e.symm.t2Space
  have hc : Continuous (collapse r) := continuous_collapse hr.1
  have hinj : InjOn (collapse r) r := by
    intro x hx y hy hxy
    rw [collapse_of_mem hx, collapse_of_mem hy] at hxy
    exact congrArg Subtype.val (OnePoint.coe_injective hxy)
  have hfinite : ∀ {x : S}, collapse r x ≠ ∞ → x ∈ r := by
    intro x hx
    by_contra hxr
    exact hx (collapse_of_notMem hxr)
  have hFb : ∀ {x}, x ∈ discBd Δ → x ∉ r → x = v := by
    intro x hxb hxr
    by_contra hxv
    exact hxr (hbr ⟨hxb, by simpa only [mem_singleton_iff] using hxv⟩)
  have hF_inj : InjOn (collapse r) (discBd Δ) := by
    intro x hx y hy hxy
    by_cases hxr : x ∈ r
    · have hyr : y ∈ r := hfinite (by
        rw [← hxy, collapse_of_mem hxr]
        exact OnePoint.coe_ne_infty _)
      exact hinj hxr hyr hxy
    · have hyr : y ∉ r := by
        intro hyr
        rw [collapse_of_notMem hxr, collapse_of_mem hyr] at hxy
        exact OnePoint.coe_ne_infty _ hxy.symm
      exact (hFb hx hxr).trans (hFb hy hyr).symm
  let O := collapse r '' discBd Δ
  have hO : IsOArc O := isOArc_image hΔ.isOArc_discBd hc.continuousOn hF_inj
  have hInf : (∞ : OnePoint r) ∈ O :=
    ⟨v, hv, collapse_of_notMem hvr⟩
  have hO_in : ∀ {x : S}, x ∈ r → collapse r x ∈ O → x ∈ discBd Δ := by
    rintro x hxr ⟨y, hy, hyx⟩
    have hyr : y ∈ r := hfinite (by rw [hyx, collapse_of_mem hxr]; exact OnePoint.coe_ne_infty _)
    exact hinj hyr hxr hyx ▸ hy
  let T := collapse r '' (discInt Δ ∩ r)
  have hTo : IsOpen T := by
    have hop : IsOpen (discInt Δ ∩ r) :=
      (hΔ.isOpen_discInt (fun x => (hS.2.2 x).isManifoldPoint)).inter hr.1
    have heq : T = ((↑) : r → OnePoint r) '' (Subtype.val ⁻¹' (discInt Δ ∩ r)) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx.2⟩, hx, (collapse_of_mem hx.2).symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.1, hx, collapse_of_mem x.2⟩
    rw [heq]
    exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (hop.preimage continuous_subtype_val)
  have hdis : Disjoint T O := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ hzO
    exact hx.1.2 (hO_in hx.2 hzO)
  have hclT : closure T ⊆ T ∪ O := by
    have hcompact : IsClosed (collapse r '' Δ) := (hΔ.isCompact.image hc).isClosed
    have hsub : T ⊆ collapse r '' Δ := image_mono (fun _ hx => hx.1.1)
    refine (closure_minimal hsub hcompact).trans ?_
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxr : x ∈ r
    · by_cases hxb : x ∈ discBd Δ
      · exact Or.inr ⟨x, hxb, rfl⟩
      · exact Or.inl ⟨x, ⟨⟨hx, hxb⟩, hxr⟩, rfl⟩
    · rw [collapse_of_notMem hxr]
      exact Or.inr hInf
  obtain ⟨w, hwb, hwv⟩ := (infinite_of_isOArc hΔ.isOArc_discBd).exists_notMem_finite
    (finite_singleton v)
  have hwr : w ∈ r := hbr ⟨hwb, hwv⟩
  obtain ⟨y, hyr, hyD⟩ := mem_closure_iff.mp (hΔ.subset_closure_discInt
    (Surface.discBd_subset Δ hwb))
    r hr.1 hwr
  have hne : T.Nonempty := ⟨collapse r y, y, ⟨hyD, hyr⟩, rfl⟩
  have hwout : w ∈ closure (univ \ Δ) := by
    have hwfr : w ∈ frontier Δ := (IsClosedDisc.frontier_eq_discBd hS hΔ).symm ▸ hwb
    rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff] at hwfr
    exact hwfr.2
  obtain ⟨p, hpr, hpD⟩ := mem_closure_iff.mp hwout r hr.1 hwr
  have hout : ∃ z : OnePoint r, z ∉ O ∧ z ∉ T := by
    refine ⟨collapse r p, ?_, ?_⟩
    · exact fun hpO => hpD.2 (Surface.discBd_subset Δ (hO_in hpr hpO))
    · rintro ⟨x, hx, hxp⟩
      exact hpD.2 (hinj hx.2 hpr hxp ▸ hx.1.1)
  obtain ⟨B, C, _, hB, hC, hbB, hbC, hu, hi, _, _⟩ :=
    sphere_disc (OnePoint r) (isSphere_onePoint hr) O hO
  rcases eq_discInt_of_two_sides hB hC hbB hbC hu hi hTo hclT hdis hne hout with h | h
  · exact ⟨B, hB, hbB, h⟩
  · exact ⟨C, hC, hbC, h⟩

end GraphMinor.GM12

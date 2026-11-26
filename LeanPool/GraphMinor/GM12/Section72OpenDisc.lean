/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72DiscSides
import LeanPool.GraphMinor.GM12.Section72DiscMap
import LeanPool.GraphMinor.GM11.PerimeterPull
import Mathlib.Topology.Piecewise

/-!
# The open disc obtained by filling one side of a region

For XII (7.2), page 260, replace the removed disc by its Jordan disc
in the compactification of the old region. The prescribed boundary
map extends across the discs. Paste it with the collapse map outside
the removed disc. This gives a homeomorphism from the merged region
to the old open disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 OnePoint

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Filling a disc attached along all its boundary except one point to an
open disc gives an open disc. This is the open-disc assertion in XII (7.2),
page 260. The one missing boundary point stays outside the union. -/
theorem isOpenDisc_union_disc_sdiff_point (hS : IsClosedSurface S)
    {r Δ : Set S} {v : S} (hr : IsOpenDisc r) (hΔ : IsClosedDisc Δ)
    (hv : v ∈ discBd Δ) (hvr : v ∉ r) (hbr : discBd Δ \ {v} ⊆ r) :
    IsOpenDisc (r ∪ (Δ \ {v})) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space (OnePoint r) := by
    obtain ⟨e⟩ := isSphere_onePoint hr
    exact e.symm.t2Space
  obtain ⟨B, hB, hbB, hside⟩ := theorem_7_2_disc_side hS hr hΔ hv hvr hbr
  have hc : Continuous (collapse r) := continuous_collapse hr.1
  have hk : InjOn (collapse r) r := by
    intro x hx y hy hxy
    rw [collapse_of_mem hx, collapse_of_mem hy] at hxy
    exact congrArg Subtype.val (OnePoint.coe_injective hxy)
  have hfinite : ∀ {x : S}, collapse r x ≠ ∞ → x ∈ r := by
    intro x hx
    by_contra hxr
    exact hx (collapse_of_notMem hxr)
  have hboundary : ∀ {x : S}, x ∈ discBd Δ → x ∉ r → x = v := by
    intro x hxb hxr
    by_contra hxv
    exact hxr (hbr ⟨hxb, by simpa only [mem_singleton_iff] using hxv⟩)
  have hki : InjOn (collapse r) (discBd Δ) := by
    intro x hx y hy hxy
    by_cases hxr : x ∈ r
    · have hyr := hfinite (by rw [← hxy, collapse_of_mem hxr]; exact OnePoint.coe_ne_infty _)
      exact hk hxr hyr hxy
    · have hyr : y ∉ r := by
        intro hyr
        rw [collapse_of_notMem hxr, collapse_of_mem hyr] at hxy
        exact OnePoint.coe_ne_infty _ hxy.symm
      exact (hboundary hx hxr).trans (hboundary hy hyr).symm
  obtain ⟨g, hgc, hgi, hgB, hgbd⟩ := exists_disc_boundary_extension hΔ hB (collapse r)
    hc.continuousOn hki hbB.symm
  have hg_mem : MapsTo g Δ B := fun x hx => hgB ▸ mem_image_of_mem g hx
  have hgv : g v = ∞ := (hgbd hv).trans (collapse_of_notMem hvr)
  have hκB : ∀ {x : S}, x ∈ r → (collapse r x ∈ B ↔ x ∈ Δ) := by
    intro x hxr
    constructor
    · intro hxB
      by_cases hxb : collapse r x ∈ discBd B
      · rw [hbB] at hxb
        obtain ⟨y, hy, hyx⟩ := hxb
        have hyr := hfinite (by rw [hyx, collapse_of_mem hxr]; exact OnePoint.coe_ne_infty _)
        exact hk hyr hxr hyx ▸ Surface.discBd_subset Δ hy
      · have hxint : collapse r x ∈ discInt B := ⟨hxB, hxb⟩
        rw [← hside] at hxint
        obtain ⟨y, hy, hyx⟩ := hxint
        exact hk hy.2 hxr hyx ▸ hy.1.1
    · intro hxD
      by_cases hxb : x ∈ discBd Δ
      · exact Surface.discBd_subset B (hbB ▸ mem_image_of_mem (collapse r) hxb)
      · have hxint : collapse r x ∈ discInt B := hside ▸ mem_image_of_mem
          (collapse r) ⟨⟨hxD, hxb⟩, hxr⟩
        exact hxint.1
  let Y := r ∪ (Δ \ {v})
  have hYeq : Y = r ∪ interior Δ := by
    apply Subset.antisymm
    · rintro x (hx | ⟨hxD, hxv⟩)
      · exact Or.inl hx
      · by_cases hxi : x ∈ interior Δ
        · exact Or.inr hxi
        · have hxb : x ∈ discBd Δ := (IsClosedDisc.frontier_eq_discBd hS hΔ) ▸ ⟨subset_closure hxD,
            hxi⟩
          exact Or.inl (hbr ⟨hxb, hxv⟩)
    · rintro x (hx | hxi)
      · exact Or.inl hx
      · refine Or.inr ⟨interior_subset hxi, ?_⟩
        intro hxv
        have hvi : v ∈ interior Δ := mem_singleton_iff.mp hxv ▸ hxi
        exact ((IsClosedDisc.frontier_eq_discBd hS hΔ).symm ▸ hv).2 hvi
  have hYo : IsOpen Y := hYeq ▸ hr.1.union isOpen_interior
  have hYv : ∀ {x}, x ∈ Y → x ≠ v := by
    rintro x (hx | hx) rfl
    · exact hvr hx
    · exact hx.2 rfl
  have hYout : ∀ {x}, x ∈ Y → x ∉ Δ → x ∈ r := by
    rintro x (hx | hx) hxD
    · exact hx
    · exact (hxD hx.1).elim
  let L : S → OnePoint r := Δ.piecewise g (collapse r)
  have hLc : ContinuousOn L Y := by
    refine ContinuousOn.piecewise ?_ ?_ (hc.continuousOn.mono inter_subset_left)
    · rintro x ⟨_, hxf⟩
      exact hgbd ((IsClosedDisc.frontier_eq_discBd hS hΔ) ▸ hxf)
    · exact hgc.mono (by rw [hΔ.isClosed.closure_eq]; exact inter_subset_right)
  have hL_mem : ∀ {x}, x ∈ Y → (L x ∈ B ↔ x ∈ Δ) := by
    intro x hx
    by_cases hxD : x ∈ Δ
    · simp only [L, piecewise, hxD, ↓reduceIte, iff_true]
      exact hg_mem hxD
    · simp only [L, piecewise, hxD, ↓reduceIte, iff_false]
      exact fun h => hxD ((hκB (hYout hx hxD)).mp h)
  have hLi : InjOn L Y := by
    intro x hx y hy hxy
    by_cases hxD : x ∈ Δ
    · have hyD : y ∈ Δ := (hL_mem hy).mp (hxy ▸ (hL_mem hx).mpr hxD)
      exact hgi hxD hyD (by simpa only [L, piecewise, hxD, hyD, ↓reduceIte] using hxy)
    · have hyD : y ∉ Δ := fun hyD => hxD ((hL_mem hx).mp (hxy.symm ▸ (hL_mem hy).mpr hyD))
      exact hk (hYout hx hxD) (hYout hy hyD)
        (by simpa only [L, piecewise, hxD, hyD, ↓reduceIte] using hxy)
  let N : Set (OnePoint r) := {z | z ≠ ∞}
  have hLN : MapsTo L Y N := by
    intro x hx
    by_cases hxD : x ∈ Δ
    · change L x ≠ ∞
      rw [show L x = g x from by simp [L, hxD]]
      exact fun h => hYv hx (hgi hxD (Surface.discBd_subset Δ hv) (h.trans hgv.symm))
    · rw [show L x = collapse r x from by simp [L, hxD], collapse_of_mem (hYout hx hxD)]
      exact OnePoint.coe_ne_infty _
  have hLs : ∀ z ∈ N, ∃ x ∈ Y, L x = z := by
    intro z hz
    by_cases hzB : z ∈ B
    · obtain ⟨x, hxD, hxg⟩ := hgB.symm ▸ hzB
      have hxv : x ≠ v := fun h => hz (by rw [← hxg, h, hgv])
      exact ⟨x, Or.inr ⟨hxD, by simpa only [mem_singleton_iff] using hxv⟩, by simp [L, hxD, hxg]⟩
    · obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hz
      have hxD : x.1 ∉ Δ := fun h => hzB (by rw [← collapse_of_mem x.2]; exact (hκB x.2).mpr h)
      exact ⟨x.1, Or.inl x.2, by simp [L, hxD, collapse_of_mem x.2]⟩
  let j : Δ → B := fun x => ⟨g x, hg_mem x.2⟩
  have hjc : Continuous j := hgc.domRestrict.subtype_mk _
  have hjb : Function.Bijective j := by
    refine ⟨fun x y h => Subtype.ext (hgi x.2 y.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := hgB.symm ▸ hz
    exact ⟨⟨x, hx⟩, rfl⟩
  have : CompactSpace Δ := isCompact_iff_compactSpace.mp hΔ.isCompact
  let H : Δ ≃ₜ B := hjc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j hjb)
  let k : OnePoint r → S := fun z => if hz : z ∈ B then (H.symm ⟨z, hz⟩).1 else v
  have hkB : ContinuousOn k B := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : B.domRestrict k = fun z : B => (H.symm z).1 := by
      ext z
      simp [k, domRestrict, z.2]
    rw [heq]
    exact continuous_subtype_val.comp H.symm.continuous
  have hkg : ∀ x ∈ Δ, k (g x) = x := by
    intro x hx
    change (if hz : g x ∈ B then (H.symm ⟨g x, hz⟩).1 else v) = x
    rw [dite_eq_left (hg_mem hx)]
    exact congrArg Subtype.val (H.symm_apply_apply ⟨x, hx⟩)
  have hunc : ∀ x ∈ r, uncollapse v (collapse r x) = x := by
    intro x hx
    rw [collapse_of_mem hx, uncollapse_coe]
  have hkbd : EqOn k (uncollapse v) (discBd B) := by
    intro z hz
    rw [hbB] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [← hgbd hx, hkg x (Surface.discBd_subset Δ hx), hgbd hx]
    by_cases hxr : x ∈ r
    · exact (hunc x hxr).symm
    · rw [collapse_of_notMem hxr]
      exact hboundary hx hxr
  have huc : ContinuousOn (uncollapse (A := r) v) N := by
    intro z hz
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hz
    exact (continuousAt_uncollapse v x).continuousWithinAt
  let M := B.piecewise k (uncollapse v)
  have hMc : ContinuousOn M N := by
    refine ContinuousOn.piecewise ?_ ?_ (huc.mono inter_subset_left)
    · intro z hz
      exact hkbd ((IsClosedDisc.frontier_eq_discBd (GM11.IsSphere.isClosedSurface
        (isSphere_onePoint hr)).1 hB) ▸ hz.2)
    · exact hkB.mono (by rw [hB.isClosed.closure_eq]; exact inter_subset_right)
  have hML : ∀ x ∈ Y, M (L x) = x := by
    intro x hx
    by_cases hxD : x ∈ Δ
    · rw [show L x = g x from by simp [L, hxD]]
      simp only [M, piecewise, hg_mem hxD, ↓reduceIte]
      exact hkg x hxD
    · have hxB : L x ∉ B := fun h => hxD ((hL_mem hx).mp h)
      simp only [M, piecewise, hxB, ↓reduceIte]
      rw [show L x = collapse r x from by simp [L, hxD]]
      exact hunc x (hYout hx hxD)
  let f : Y → N := fun x => ⟨L x, hLN x.2⟩
  have hfc : Continuous f := hLc.domRestrict.subtype_mk _
  have hfb : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (hLi x.2 y.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, hLx⟩ := hLs z hz
    exact ⟨⟨x, hx⟩, Subtype.ext hLx⟩
  let e := Equiv.ofBijective f hfb
  have hInv : ∀ z : N, M z = (e.symm z).1 := by
    intro z
    have he : L (e.symm z).1 = z.1 := congrArg Subtype.val (e.apply_symm_apply z)
    rw [← he]
    exact hML _ (e.symm z).2
  let E : Y ≃ₜ N :=
    { toEquiv := e
      continuous_toFun := hfc
      continuous_invFun := (hMc.domRestrict.congr hInv).subtype_mk _ }
  have hN : range ((↑) : r → OnePoint r) = N := by
    ext z
    exact OnePoint.ne_infty_iff_exists.symm
  let R : r ≃ₜ N := OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hN)
  obtain ⟨φ⟩ := hr.2
  exact ⟨hYo, ⟨(φ.trans R).trans E.symm⟩⟩

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.NetSwapBasic
import LeanPool.GraphMinor.GM07.Section26Edges
import LeanPool.GraphMinor.GM07.Section26Path
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.Section2MinVal
import LeanPool.GraphMinor.GM07.Section46JPlus
import LeanPool.GraphMinor.GM07.MinimalNet
import LeanPool.GraphMinor.GM11.GlueDiscs
import LeanPool.GraphMinor.GM11.DrawingOps
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Graph Minors VII, the shortcut O-arc

For (2.6), page 218, first handle coincident endpoint images.
The cutting line already maps to an O-arc in that case: its
inner points have singleton fibers and only its ends are
identified. Its contact count includes at most one endpoint.
For distinct endpoint images, their line image meets the seam
only at its ends. Joining it to a seam path gives the required
normal O-arc, and only the inner line contacts are added.

The main result is `minimalNetShortcutOArc`, which is (2.6). It follows the proof in the text, with
one
change. The inequality the text prints for an edge of type (ii) is false, so we use the one from the
exact count (`Net.edge_contacts_le`), and sum it along the path of (2.5) (`walk_contacts_le`). See
the correction to the proof of (2.6) in `corrections/GM07.md`.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- The coincident-endpoint case of VII (2.6), page 218. The image
of the proper cutting line is already a normal O-arc, with at most
one graph contact in addition to its inner contacts. -/
theorem lemma_2_6_of_equal_endpoint_images
    {S : Type*} [TopologicalSpace S] [T2Space S] (N : Net S)
    {G : Drawing S} {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    {F : Set N.D} {s t : N.D} (hF : IsLineWithEnds F s t)
    (hFbd : F ∩ bd N.D = {s, t}) (hNormal : G_D.IsNormal F)
    (hst : N.φ s = N.φ t) :
    G.IsNormal (N.φ '' F) ∧ IsOArc (N.φ '' F) ∧
      (N.φ '' F ∩ G.V).ncard ≤ (N.φ '' (F \ {s, t}) ∩ G.V).ncard + 1 := by
  obtain ⟨k, hk, hkF, hk0, hk1⟩ := hF.exists_arc
  have hinner : ∀ r ∈ Ioo (0 : unitInterval) 1, k r ∉ bd N.D := by
    intro r hr hbd
    have hends := hFbd.subset ⟨hkF ▸ mem_range_self r, hbd⟩
    rcases hends with hrs | hrt
    · exact hr.1.ne' (hk.2 (hrs.trans hk0.symm))
    · exact hr.2.ne (hk.2 ((mem_singleton_iff.mp hrt).trans hk1.symm))
  have hRange : range (N.φ ∘ k) = N.φ '' F := by rw [range_comp, hkF]
  have hArc : IsOArc (range (N.φ ∘ k)) := by
    apply GM11.isOArc_of_loop (N.quotientMap_φ.continuous.comp hk.1)
    · exact (congrArg N.φ hk0).trans (hst.trans (congrArg N.φ hk1).symm)
    · intro r hr q hq heq
      exact hk.2 (N.interior_inj (k r) (hinner r hr) (k q) heq)
    · intro r hr heq
      have hkr := N.interior_inj (k r) (hinner r hr) (k 0) heq
      exact hr.1.ne' (hk.2 hkr)
  have hImage : N.φ '' F = N.φ '' (F \ {s, t}) ∪ {N.φ s} := by
    apply Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      by_cases hxe : x ∈ ({s, t} : Set N.D)
      · rcases hxe with hxs | hxt
        · exact Or.inr (congrArg N.φ hxs)
        · exact Or.inr ((congrArg N.φ (mem_singleton_iff.mp hxt)).trans hst.symm)
      · exact Or.inl ⟨x, ⟨hx, hxe⟩, rfl⟩
    · rintro z (⟨x, hx, rfl⟩ | hzs)
      · exact ⟨x, hx.1, rfl⟩
      · exact ⟨s, hF.left_mem, (mem_singleton_iff.mp hzs).symm⟩
  refine ⟨N.normal_image_of_pullback hPull hNormal, hRange ▸ hArc, ?_⟩
  rw [hImage, union_inter_distrib_right]
  have h := ncard_union_le (N.φ '' (F \ {s, t}) ∩ G.V) ({N.φ s} ∩ G.V)
  have hEnd : ({N.φ s} ∩ G.V).ncard ≤ 1 := by
    exact (ncard_inter_le_ncard_left _ _ (finite_singleton _)).trans_eq (ncard_singleton _)
  exact h.trans (Nat.add_le_add_left hEnd _)

/-- With distinct endpoint images, the image of the proper cutting
line is a line between them. Interior injectivity excludes every
identification involving an inner point. This is the line used in
the last step of VII (2.6), page 218. -/
theorem lemma_2_6_image_line
    {S : Type*} [TopologicalSpace S] [T2Space S] (N : Net S)
    {F : Set N.D} {s t : N.D} (hF : IsLineWithEnds F s t)
    (hFbd : F ∩ bd N.D = {s, t}) (hst : N.φ s ≠ N.φ t) :
    IsLineWithEnds (N.φ '' F) (N.φ s) (N.φ t) := by
  have hi : InjOn N.φ F := by
    intro x hx y hy hxy
    by_cases hxbd : x ∈ bd N.D
    · by_cases hybd : y ∈ bd N.D
      · have hxe : x = s ∨ x = t := hFbd.subset ⟨hx, hxbd⟩
        have hye : y = s ∨ y = t := hFbd.subset ⟨hy, hybd⟩
        rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
        · rfl
        · exact (hst hxy).elim
        · exact (hst hxy.symm).elim
        · rfl
      · exact (N.interior_inj y hybd x hxy.symm).symm
    · exact N.interior_inj x hxbd y hxy
  obtain ⟨k, hk, hkF, hk0, hk1⟩ := hF.exists_arc
  have hki : Function.Injective (N.φ ∘ k) := by
    intro r q heq
    exact hk.2 (hi (hkF ▸ mem_range_self r) (hkF ▸ mem_range_self q) heq)
  have h := GM11.isLine_range (N.quotientMap_φ.continuous.comp hk.1) hki
  have hRange : range (N.φ ∘ k) = N.φ '' F := by rw [range_comp, hkF]
  simpa only [hRange, Function.comp_apply, hk0, hk1] using h

/-- The image of the proper cutting line meets the seam precisely
at its endpoint images. In particular its open image misses every
path in the refined seam graph. This is used in VII (2.6), page 218. -/
theorem lemma_2_6_image_inter_seam
    {S : Type*} [TopologicalSpace S] (N : Net S)
    {F : Set N.D} {s t : N.D} (hF : IsLineWithEnds F s t)
    (hFbd : F ∩ bd N.D = {s, t}) :
    N.φ '' F ∩ N.seamU = {N.φ s, N.φ t} := by
  apply Subset.antisymm
  · rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
    have hxbd : x ∈ bd N.D := by
      by_contra h
      exact h ((N.interior_inj x h y hyx.symm).symm ▸ hy)
    rcases hFbd.subset ⟨hx, hxbd⟩ with hxs | hxt
    · exact Or.inl (congrArg N.φ hxs)
    · exact Or.inr (congrArg N.φ (mem_singleton_iff.mp hxt))
  · rintro z (rfl | hzt)
    · have hsbd : s ∈ bd N.D := (hFbd.symm.subset (show s ∈ ({s, t} : Set N.D) from Or.inl rfl)).2
      exact ⟨⟨s, hF.left_mem, rfl⟩, ⟨s, hsbd, rfl⟩⟩
    · have htbd : t ∈ bd N.D := (hFbd.symm.subset (show t ∈ ({s, t} : Set N.D) from Or.inr rfl)).2
      rw [mem_singleton_iff] at hzt
      subst z
      exact ⟨⟨t, hF.right_mem, rfl⟩, ⟨t, htbd, rfl⟩⟩

/-- Combining the seam path with the cutting-line image gives the
normal O-arc in the last step of VII (2.6), page 218. The endpoints
are already on the path, so only inner cutting-line contacts need
be added to the path's contacts. -/
theorem lemma_2_6_union_path
    {S : Type*} [TopologicalSpace S] [T2Space S] (N : Net S)
    {G J P : Drawing S} {F : Set N.D} {s t : N.D}
    (hN : N.IsNormalFor G) (hJ : N.IsSeamGraphFor J)
    (hP : P.IsPathBetween (N.φ s) (N.φ t)) (hPJ : P.U ⊆ J.U)
    (hF : IsLineWithEnds F s t)
    (hFbd : F ∩ bd N.D = {s, t}) (hst : N.φ s ≠ N.φ t)
    {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    (hNormal : G_D.IsNormal F) :
    G.IsNormal (N.φ '' F ∪ P.U) ∧ IsOArc (N.φ '' F ∪ P.U) ∧
      ((N.φ '' F ∪ P.U) ∩ G.V).ncard ≤
        (N.φ '' (F \ {s, t}) ∩ G.V).ncard + (P.U ∩ G.V).ncard ∧
      N.φ '' F ⊆ N.φ '' F ∪ P.U ∧ N.φ '' F ∪ P.U ⊆ N.φ '' F ∪ J.U := by
  have hPline := GM11.isLine_of_isPathBetween hP hst
  have hLine := lemma_2_6_image_line N hF hFbd hst
  have hPU : P.U ⊆ N.seamU := hPJ.trans hJ.2.1.subset
  have hMeet : N.φ '' F ∩ P.U ⊆ {N.φ s, N.φ t} :=
    fun z hz => (lemma_2_6_image_inter_seam N hF hFbd).subset ⟨hz.1, hPU hz.2⟩
  have hArc := GM11.isOArc_union hLine hPline hMeet
  obtain ⟨K, hK, hNormK⟩ := hN
  have hNormP : G.IsNormal P.U := by
    intro z hz
    exact hNormK ⟨hK.2.1.symm ▸ hPU hz.1, hz.2⟩
  have hNormF := N.normal_image_of_pullback hPull hNormal
  have hNorm : G.IsNormal (N.φ '' F ∪ P.U) := by
    rintro z ⟨(hzF | hzP), hzG⟩
    · exact hNormF ⟨hzF, hzG⟩
    · exact hNormP ⟨hzP, hzG⟩
  have hUnion : N.φ '' F ∪ P.U = N.φ '' (F \ {s, t}) ∪ P.U := by
    apply Subset.antisymm
    · rintro z (⟨x, hx, rfl⟩ | hzP)
      · by_cases hxe : x ∈ ({s, t} : Set N.D)
        · rcases hxe with hxs | hxt
          · exact Or.inr ((congrArg N.φ hxs).symm ▸ hPline.left_mem)
          · exact Or.inr ((congrArg N.φ (mem_singleton_iff.mp hxt)).symm ▸ hPline.right_mem)
        · exact Or.inl ⟨x, ⟨hx, hxe⟩, rfl⟩
      · exact Or.inr hzP
    · rintro z (⟨x, hx, rfl⟩ | hzP)
      · exact Or.inl ⟨x, hx.1, rfl⟩
      · exact Or.inr hzP
  refine ⟨hNorm, hArc, ?_, subset_union_left, union_subset_union_right _ hPJ⟩
  rw [hUnion, union_inter_distrib_right]
  exact ncard_union_le _ _

universe u

/-- The bound for `P`. Let `k = |φ(F*) ∩ V(G)|` and `m = |E(P)|`. Then `|U(P) ∩ V(G)| ≤ mk + m + 1 +
|bd(Σ) ∩ V(G)|`. With `m + 1 = |V(P)|` this is the display in the proof of VII (2.6), page 218. -/
theorem path_contacts_le {S : Type u} [TopologicalSpace S] {G P : Drawing S} {x y : S}
    (W : GraphWalk P.toGraph x y) (hW : W.IsSimple) (hPV : P.V = {z | z ∈ W.support})
    (hPE : P.E = {e | e ∈ W.edges}) (k : ℕ)
    (hedge : ∀ e a b, e ∈ W.edges → P.toGraph.IsLink e a b → a ≠ b →
      (e ∩ G.V ⊆ bd S ∧ a ∉ G.V \ bd S ∧ b ∉ G.V \ bd S) ∨
        2 * (e ∩ G.V).ncard + ({a} ∩ G.V).ncard + ({b} ∩ G.V).ncard ≤
          2 * k + ({x} ∩ G.V).ncard + ({y} ∩ G.V).ncard) :
    (P.U ∩ G.V).ncard ≤ W.edges.length * k + W.edges.length + 1 + (bd S ∩ G.V).ncard := by
  have hle : ∀ z : S, ({z} ∩ G.V).ncard ≤ 1 := fun z =>
    (ncard_inter_le_ncard_left _ _ (finite_singleton _)).trans_eq (ncard_singleton _)
  have hle₀ : ∀ z : S, ({z} ∩ (G.V \ bd S)).ncard ≤ ({z} ∩ G.V).ncard := fun z =>
    ncard_le_ncard (fun w hw => ⟨hw.1, hw.2.1⟩) (G.finite_V.subset inter_subset_right)
  have hsum := walk_contacts_le G.finite_V _ W hW hedge
  have hsub : P.U ∩ G.V ⊆ (walkPoints W ∩ (G.V \ bd S)) ∪ (bd S ∩ G.V) := by
    rintro z ⟨hz, hzV⟩
    by_cases hb : z ∈ bd S
    · exact Or.inr ⟨hb, hzV⟩
    · refine Or.inl ⟨?_, hzV, hb⟩
      by_cases hzP : z ∈ P.V
      · exact Or.inl (hPV ▸ hzP : z ∈ {z | z ∈ W.support})
      · obtain ⟨e, he, hze⟩ := P.exists_edge_of_mem hz hzP
        exact Or.inr (mem_biUnion (hPE ▸ he : e ∈ {e | e ∈ W.edges}) hze)
  have hfin : (walkPoints W ∩ (G.V \ bd S)).Finite := G.finite_V.subset fun z hz => hz.2.1
  have hc := (ncard_le_ncard hsub (hfin.union (G.finite_V.subset inter_subset_right))).trans
    (ncard_union_le _ _)
  have h₁ := hle x
  have h₂ := hle y
  have h₃ := hle₀ x
  have h₄ := hle₀ y
  have hm : W.edges.length * (2 * k + ({x} ∩ G.V).ncard + ({y} ∩ G.V).ncard) ≤
      2 * (W.edges.length * k) + 2 * W.edges.length := by
    calc W.edges.length * (2 * k + ({x} ∩ G.V).ncard + ({y} ∩ G.V).ncard)
        ≤ W.edges.length * (2 * k + 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (W.edges.length * k) + 2 * W.edges.length := by ring
  omega

/-- Graph Minors VII, (2.6), page 218, with the bounds of (2.4) as hypotheses. See the module
docstring. -/
theorem minimalNetShortcutOArc : ∀ (S : Type u) [TopologicalSpace S] [T1Space S], IsSurface S →
    ∀ a b c : ℕ, 2 * a + b + c > 1 → Nonempty (S ≃ₜ SurfaceModel a b c) →
    ∀ (G J : Drawing S) (N : Net S),
      G.IsProper → N.IsMinimalFor G → N.IsSeamGraphFor J →
      J.V.ncard ≤ 2 * (2 * a + b + c - 1) →
      J.E.ncard ≤ 3 * (2 * a + b + c - 1) →
      ∀ (G_D : Drawing N.D), IsPullbackDrawing N.φ G G_D →
      ∀ (F : Set N.D) (s t : N.D),
        G_D.IsNormal F → IsProperIArc F → IsLineWithEnds F s t →
        ∃ A : Set S, G.IsNormal A ∧ IsOArc A ∧
          (A ∩ G.V).ncard ≤
            2 * (2 * a + b + c) * ((N.φ '' (F \ {s, t}) ∩ G.V).ncard + 1) +
              (bd S ∩ G.V).ncard ∧
          N.φ '' F ⊆ A ∧ A ⊆ N.φ '' F ∪ J.U := by
  intro S _ _ hS a b c habc _ G J N _ hMin hSeam hV _ G_D hPull F s t hNorm hProper hEnds
  have : T2Space S := hS.2.1
  have : T2Space N.D := N.isSurface_D.2.1
  obtain ⟨u, v, huv, hbdF, hFuv⟩ := hProper
  have hst : s ≠ t := by
    rcases seam_line_end_mem hEnds hFuv with rfl | rfl <;> rcases seam_line_end_mem hEnds.symm hFuv
      with h | h
    · obtain ⟨g, g0, g1⟩ := hEnds
      rintro rfl
      exact zero_ne_one (g.injective (Subtype.ext (g0.trans g1.symm)))
    · exact h ▸ huv
    · exact fun h' => huv (h.symm.trans h'.symm)
    · obtain ⟨g, g0, g1⟩ := hEnds
      rintro rfl
      exact zero_ne_one (g.injective (Subtype.ext (g0.trans g1.symm)))
  have hFbd : F ∩ bd N.D = {s, t} := by
    rw [hbdF]
    rcases seam_line_end_mem hEnds hFuv with h | h <;>
      rcases seam_line_end_mem hEnds.symm hFuv with h' | h'
    · exact absurd (h.trans h'.symm) hst
    · rw [h, h']
    · rw [h, h', pair_comm]
    · exact absurd (h.trans h'.symm) hst
  set k := (N.φ '' (F \ {s, t}) ∩ G.V).ncard with hk
  have hn : 2 ≤ 2 * a + b + c := habc
  by_cases heq : N.φ s = N.φ t
  · obtain ⟨h₁, h₂, h₃⟩ := lemma_2_6_of_equal_endpoint_images N hPull hEnds hFbd hNorm heq
    refine ⟨N.φ '' F, h₁, h₂, ?_, Subset.rfl, subset_union_left⟩
    have : 1 * (k + 1) ≤ 2 * (2 * a + b + c) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨M, e, hr, hmap, hU, hV₁, hV₂, hcount, hs, ht⟩ := N.exists_refine_ends s t
  have hφ : ∀ z, M.φ (e z) = N.φ z := fun z => congrFun hmap z
  have hrpos : 0 < M.r := lt_of_lt_of_le hSeam.1 hr
  have hNnorm : G.IsNormal N.seamU := ((N.isNormalFor_iff hS G).mp hMin.1).2
  have hMnorm : M.IsNormalFor G := (M.isNormalFor_iff hS G).mpr ⟨hrpos, hU.symm ▸ hNnorm⟩
  have hmin : ∀ M' : Net S, M'.IsNormalFor G →
      M.bdVertexPreimageCard G ≤ M'.bdVertexPreimageCard G := fun M' h' => by
    rw [hcount]
    exact hMin.2.1 M' h'
  have : T2Space M.D := M.isSurface_D.2.1
  have hebd : e '' bd N.D = bd M.D := image_bd_homeomorph e
  have hsbd : s ∈ bd N.D := (hFbd.symm.subset (Or.inl rfl)).2
  have htbd : t ∈ bd N.D := (hFbd.symm.subset (Or.inr rfl)).2
  have hsbd' : e s ∈ bd M.D := hebd ▸ mem_image_of_mem e hsbd
  have htbd' : e t ∈ bd M.D := hebd ▸ mem_image_of_mem e htbd
  have hst' : e s ≠ e t := e.injective.ne hst
  have hF' : IsLineWithEnds (e '' F) (e s) (e t) := by
    obtain ⟨g, hg, hgr, hg0, hg1⟩ := hEnds.exists_arc
    have harc : IsArcMap (e ∘ g) := ⟨e.continuous.comp hg.1, e.injective.comp hg.2⟩
    have := harc.isLineWithEnds
    rwa [range_comp, hgr, Function.comp_apply, Function.comp_apply, hg0, hg1] at this
  have hFbd' : e '' F ∩ bd M.D = {e s, e t} := by
    rw [← hebd, ← image_inter e.injective, hFbd, image_pair]
  have himF : M.φ '' (e '' F) = N.φ '' F := by
    rw [← image_comp, hmap]
  have hNormal : G.IsNormal (M.φ '' (e '' F)) := by
    rw [himF]
    exact N.normal_image_of_pullback hPull hNorm
  have himF' : M.φ '' ((e '' F) \ {e s, e t}) = N.φ '' (F \ {s, t}) := by
    rw [← image_pair, ← image_sdiff e.injective, ← image_comp, hmap]
  obtain ⟨A, B, C₁, C₂, hA, hB, hAB, hI, hAd, hBd, hcomp, hC12, hAC, hBC⟩ :=
    M.exists_cut_pieces hF' hst' hFbd'
  obtain ⟨JM, hJM⟩ := M.exists_isSeamGraphFor hS hrpos
  have hJU : JM.U = N.seamU := hJM.2.1.trans hU
  have hJV : JM.V = M.seamV := hJM.2.2
  have hAfin : (JM.V ∪ {N.φ s, N.φ t}).Finite := JM.finite_V.union (by simp)
  have hAU : JM.V ∪ {N.φ s, N.φ t} ⊆ JM.U := by
    refine union_subset JM.V_subset_U ?_
    rintro z (rfl | hz)
    · exact hJU ▸ ⟨s, hsbd, rfl⟩
    · obtain rfl : z = N.φ t := hz
      exact hJU ▸ ⟨t, htbd, rfl⟩
  obtain ⟨J', hJ'U, hJ'V⟩ := exists_drawing_with_more_vertices JM hAfin subset_union_left hAU
  have hsV : M.φ (e s) = N.φ s := hφ s
  have htV : M.φ (e t) = N.φ t := hφ t
  obtain ⟨P, hPJ, hPath, hPtype⟩ := exists_path_no_type3_type4 hS M JM J' hJM hsbd' htbd' hst'
    hcomp hC12 hJ'U (by rw [hJ'V, hsV, htV])
  rw [hsV, htV] at hPath
  have hU' : J'.U = M.seamU := hJ'U.trans hJM.2.1
  have hV' : M.seamV ⊆ J'.V := by
    rw [hJ'V, hJV]
    exact subset_union_left
  have hPUJ : P.U ⊆ J.U := by
    refine hPJ.U_subset.trans ?_
    rw [hJ'U, hJU, hSeam.2.1]
  have havoid : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → M.φ (M.f j r) ∉ J'.V := by
    intro j r hr'
    rw [hJ'V, hJV]
    rintro (h | h | h)
    · exact M.notMem_seamV_of_mem_Ioo j hr' h
    · have hmem : e s ∈ M.φ ⁻¹' {M.φ (M.f j r)} := by
        change M.φ (e s) = _
        rw [hsV, h]
      rw [M.fiber_eq_pair_of_mem_Ioo j hr'] at hmem
      rcases hmem with h' | h'
      · exact (hs j r hr').1 h'.symm
      · exact (hs j r hr').2 (mem_singleton_iff.mp h').symm
    · have hmem : e t ∈ M.φ ⁻¹' {M.φ (M.f j r)} := by
        change M.φ (e t) = _
        rw [htV, mem_singleton_iff.mp h]
      rw [M.fiber_eq_pair_of_mem_Ioo j hr'] at hmem
      rcases hmem with h' | h'
      · exact (ht j r hr').1 h'.symm
      · exact (ht j r hr').2 (mem_singleton_iff.mp h').symm
  obtain ⟨W, hWs, hWV, hWE⟩ := hPath
  have hedge : ∀ g a b, g ∈ W.edges → P.toGraph.IsLink g a b → a ≠ b →
      (g ∩ G.V ⊆ bd S ∧ a ∉ G.V \ bd S ∧ b ∉ G.V \ bd S) ∨
        2 * (g ∩ G.V).ncard + ({a} ∩ G.V).ncard + ({b} ∩ G.V).ncard ≤
          2 * k + ({N.φ s} ∩ G.V).ncard + ({N.φ t} ∩ G.V).ncard := by
    intro g a b hg hlink hab
    have hgP : g ∈ P.E := hWE ▸ hg
    have hlink' : J'.toGraph.IsLink g a b := (hPJ.isLink_iff hgP).mp hlink
    rcases M.edge_cases hU' hV' havoid (hPJ.2 hgP) with hb | ⟨i, hi⟩
    · refine Or.inl ⟨fun z hz => hb hz.1, ?_, ?_⟩
      · have ha : a ∈ closure g ∩ J'.V := by rw [hlink'.2.2.2]; simp
        exact fun h' => h'.2 ((isClosed_bd S).closure_subset_iff.mpr hb ha.1)
      · have ha : b ∈ closure g ∩ J'.V := by rw [hlink'.2.2.2]; simp
        exact fun h' => h'.2 ((isClosed_bd S).closure_subset_iff.mpr hb ha.1)
    · refine Or.inr ?_
      have := M.edge_contacts_le hS hMnorm hmin hF' hst' hFbd' hs ht hA hB hAB hI hAd hBd hAC hBC
        hNormal hU' hV' havoid hab hlink' i hi (hPtype g hgP).1 (hPtype g hgP).2
      rwa [himF', hsV, htV] at this
  have hcontacts := path_contacts_le W hWs hWV hWE k hedge
  obtain ⟨hA₁, hA₂, hA₃, hA₄, hA₅⟩ := lemma_2_6_union_path N hMin.1 hSeam ⟨W, hWs, hWV, hWE⟩ hPUJ
    hEnds
    hFbd heq hPull hNorm
  refine ⟨_, hA₁, hA₂, ?_, hA₄, hA₅⟩
  -- The count of vertices of `P`.
  have hlen : W.edges.length + 1 ≤ 2 * (2 * a + b + c) := by
    classical
    have h₁ : P.V.ncard = W.support.length := by
      have : P.V = ↑W.support.toFinset := by
        rw [hWV]
        ext z
        simp
      rw [this, ncard_coe_finset, List.toFinset_card_of_nodup hWs]
    have h₂ : W.support.length = W.edges.length + 1 := GM11.length_support W
    have h₃ : P.V ⊆ J.V ∪ {N.φ s, N.φ t} := by
      refine hPJ.1.trans ?_
      rw [hJ'V, hJV, hSeam.2.2]
      exact union_subset (hV₂.trans Subset.rfl) subset_union_right
    have h₄ := ncard_le_ncard h₃ (J.finite_V.union (by simp))
    have h₅ := ncard_union_le J.V ({N.φ s, N.φ t} : Set S)
    have h₆ : ({N.φ s, N.φ t} : Set S).ncard ≤ 2 := ncard_insert_le _ _ |>.trans (by simp)
    omega
  have hprod : (W.edges.length + 1) * (k + 1) ≤ 2 * (2 * a + b + c) * (k + 1) :=
    Nat.mul_le_mul_right _ hlen
  have hexpand : (W.edges.length + 1) * (k + 1) =
      W.edges.length * k + W.edges.length + k + 1 := by ring
  omega

end GraphMinor.GM07

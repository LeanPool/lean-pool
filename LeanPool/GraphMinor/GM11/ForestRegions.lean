/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.LeafNbhd
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A drawing without circuits has one region

This file proves `isPreconnected_compl_of_noCircuit`: the complement of a drawing without circuits
in
a connected closed surface is connected. Graph Minors XI uses this in the proof of (4.4) with the
words "(since `Σ` is connected)".

We first remove finitely many points, since a punctured small disc is connected. Then we add the
edges of the drawing, in the reverse of the order in which leaves can be deleted. By
`isPreconnected_sdiff_of_local`, it is enough to see that a region that reaches a new edge, or its
free end `v`, contains a fixed point near `v`. This follows from the two sides of the edge
(`exists_edge_sides`) and the neighbourhood of a leaf (`exists_leaf_nbhd`).
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A punctured round ball in the plane is connected. -/
theorem isPreconnected_ball_sdiff (c : EuclideanPlane) {δ : ℝ} (_hδ : 0 < δ) :
    IsPreconnected (Metric.ball c δ \ {c}) := by
  have hrank : 1 < Module.rank ℝ EuclideanPlane := by
    apply Module.lt_rank_of_lt_finrank
    simp
  have hsph : IsPreconnected (Metric.sphere (0 : EuclideanPlane) 1) := isPreconnected_sphere hrank
    0 1
  have hprod : IsPreconnected (Ioo (0 : ℝ) δ ×ˢ Metric.sphere (0 : EuclideanPlane) 1) :=
    isPreconnected_Ioo.prod hsph
  have hEq : Metric.ball c δ \ {c} =
      (fun q : ℝ × EuclideanPlane => c + q.1 • q.2) ''
        (Ioo (0 : ℝ) δ ×ˢ Metric.sphere (0 : EuclideanPlane) 1) := by
    ext x
    constructor
    · rintro ⟨hx, hxc⟩
      have hd : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
      refine ⟨(‖x - c‖, ‖x - c‖⁻¹ • (x - c)), ⟨⟨hd, ?_⟩, ?_⟩, ?_⟩
      · simpa [dist_eq_norm] using hx
      · simp [norm_smul, hd.ne']
      · simp [smul_smul, hd.ne']
    · rintro ⟨⟨r, w⟩, ⟨⟨hr₀, hr₁⟩, hw⟩, rfl⟩
      have hw' : ‖w‖ = 1 := by simpa using hw
      refine ⟨?_, ?_⟩
      · simp [dist_eq_norm, norm_smul, hw', abs_of_pos hr₀, hr₁]
      · intro h
        have h₁ : r • w = 0 := by simpa using h
        rcases smul_eq_zero.mp h₁ with h₂ | h₂
        · exact hr₀.ne' h₂
        · simp [h₂] at hw'
  rw [hEq]
  exact hprod.image _ (by fun_prop)

/-- Small punctured neighbourhoods in a closed surface. -/
theorem exists_punctured_nbhd (hS : IsClosedSurface S) {O : Set S} (hO : IsOpen O) {x : S}
    (hx : x ∈ O) :
    ∃ Z : Set S, IsOpen Z ∧ x ∈ Z ∧ Z ⊆ O ∧ IsPreconnected (Z \ {x}) ∧ x ∈ closure (Z \ {x}) := by
  obtain ⟨V, hV, hxV, ⟨h⟩⟩ := hS.2.2 x
  let T : OpenUnitDisc → S := fun y => (h.symm y).1
  have hT : Continuous T := continuous_subtype_val.comp h.symm.continuous
  have hTinj : Function.Injective T := fun p q hpq => h.symm.injective (Subtype.ext hpq)
  have hTopen : IsOpenMap T := hV.isOpenEmbedding_subtypeVal.isOpenMap.comp h.symm.isOpenMap
  let c : OpenUnitDisc := h ⟨x, hxV⟩
  have hTc : T c = x := by simp [T, c]
  let P : Set OpenUnitDisc := T ⁻¹' O
  have hP : IsOpen P := hO.preimage hT
  have hP' : IsOpen (Subtype.val '' P : Set EuclideanPlane) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap _ hP
  have hcP : (c : EuclideanPlane) ∈ (Subtype.val '' P : Set EuclideanPlane) :=
    ⟨c, by simpa [P, hTc] using hx, rfl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hP' _ hcP
  have hsub : Metric.ball (c : EuclideanPlane) δ ⊆ OpenUnitDisc := by
    intro y hy
    obtain ⟨z, -, rfl⟩ := hball hy
    exact z.2
  let B : Set OpenUnitDisc := Subtype.val ⁻¹' Metric.ball (c : EuclideanPlane) δ
  have hdiff : T '' B \ {x} = T '' (Subtype.val ⁻¹' (Metric.ball (c : EuclideanPlane) δ \ {(c :
    EuclideanPlane)})) := by
    ext q
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hne⟩
      refine ⟨y, ⟨hy, fun hyc => hne ?_⟩, rfl⟩
      have : y = c := Subtype.ext hyc
      rw [this, hTc]
      rfl
    · rintro ⟨y, ⟨hy, hne⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, fun hq => hne ?_⟩
      have : y = c := hTinj (hq.trans hTc.symm)
      rw [this]
      rfl
  refine ⟨T '' B, hTopen _ (Metric.isOpen_ball.preimage continuous_subtype_val),
    ⟨c, by simp [B, hδ], hTc⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hball hy
    have : z = y := Subtype.ext hzy
    exact this ▸ hz
  · rw [hdiff]
    refine IsPreconnected.image ?_ _ hT.continuousOn
    refine (IsInducing.subtypeVal :
      IsInducing (Subtype.val : OpenUnitDisc → EuclideanPlane)).isPreconnected_image.mp ?_
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (sdiff_subset.trans hsub)]
    exact isPreconnected_ball_sdiff _ hδ
  · rw [hdiff, ← hTc]
    refine image_closure_subset_closure_image hT ⟨c, ?_, rfl⟩
    rw [closure_subtype, Subtype.image_preimage_coe, inter_eq_right.mpr (sdiff_subset.trans hsub)]
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    have hr : 0 < min ε δ / 2 := by positivity
    obtain ⟨b, hb⟩ := (NormedSpace.sphere_nonempty (x := (c : EuclideanPlane))).mpr hr.le
    have hbd : dist b (c : EuclideanPlane) = min ε δ / 2 := hb
    have hlt₁ : min ε δ / 2 < δ := by
      have := min_le_right ε δ
      linarith
    have hlt₂ : min ε δ / 2 < ε := by
      have := min_le_left ε δ
      linarith
    refine ⟨b, ⟨by simpa [Metric.mem_ball, hbd] using hlt₁, ?_⟩, ?_⟩
    · intro hbc
      rw [mem_singleton_iff.mp hbc, dist_self] at hbd
      linarith
    · rw [dist_comm, hbd]
      exact hlt₂

/-- The complement of a finite set in a connected closed surface is connected. -/
theorem isPreconnected_compl_finite (hS : IsClosedSurface S) [PreconnectedSpace S] {F : Set S}
    (hF : F.Finite) : IsPreconnected Fᶜ := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    rw [compl_empty]
    exact isPreconnected_univ
  | @insert x F hxF hF ih =>
    have hG : IsOpen Fᶜ := hF.isClosed.isOpen_compl
    have hxG : x ∈ Fᶜ := hxF
    obtain ⟨Z, hZ, hxZ, hZG, hZc, hZcl⟩ := exists_punctured_nbhd hS hG hxG
    obtain ⟨a, haZ⟩ : (Z \ {x}).Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty] at hcon
      rw [hcon, closure_empty] at hZcl
      exact hZcl
    have hEq : (insert x F)ᶜ = Fᶜ \ {x} := by
      ext y
      simp [not_or, and_comm]
    rw [hEq]
    have hcl : IsClosed (Fᶜᶜ ∪ {x}) := by
      rw [compl_compl]
      exact hF.isClosed.union isClosed_singleton
    refine isPreconnected_sdiff_of_local hG ih hcl ⟨x, hxG, rfl⟩ ⟨hZG haZ.1, haZ.2⟩ ?_
    rintro y hy ⟨t, ⟨-, ht⟩, htc⟩
    obtain rfl : t = x := ht
    have hopen : IsOpen (Fᶜ \ {t}) := hG.sdiff isClosed_singleton
    obtain ⟨b, hbZ, hbC⟩ := mem_closure_iff.mp htc Z hZ hxZ
    have hbne : b ≠ t := (connectedComponentIn_subset _ _ hbC).2
    rw [connectedComponentIn_eq hbC]
    refine hZc.subset_connectedComponentIn ⟨hbZ, hbne⟩ ?_ haZ
    exact fun q hq => ⟨hZG hq.1, hq.2⟩

/-- One step of the induction: adding a leaf edge keeps the complement connected. -/
private theorem isPreconnected_compl_of_leaf (hS : IsClosedSurface S)
    (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) {u v : S} (huv : u ≠ v)
    (hcap : closure e ∩ Γ.V = {u, v}) (hL : IsLineWithEnds (closure e) u v)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f) (hc : IsPreconnected (Γ.U \ e)ᶜ) :
    IsPreconnected Γ.Uᶜ := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hvV : v ∈ Γ.V := by
    have : v ∈ closure e ∩ Γ.V := by rw [hcap]; simp
    exact this.2
  have hve : v ∈ closure e := by
    have : v ∈ closure e ∩ Γ.V := by rw [hcap]; simp
    exact this.1
  have hvnot : v ∉ e := fun h => (he.2.1 h).2 hvV
  -- `Bad` is `U(Γ) - e` without `v`.
  let Bad : Set S := (Γ.V \ {v}) ∪ ⋃ g ∈ Γ.E \ {e}, closure g
  have hBad : IsClosed Bad :=
    (Γ.finite_V.subset sdiff_subset).isClosed.union
      ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
  have hBadeq : (Γ.U \ e) \ {v} = Bad := by
    rw [← deleteEdge_U Γ he, Drawing.U_eq, deleteEdge_E]
    have hV : (Γ.deleteEdge e).V = Γ.V := by
      apply subset_antisymm (Drawing.span_isSubdrawing Γ _ _).1
      intro x hx
      exact Or.inl ⟨hx, hx⟩
    rw [hV]
    ext x
    constructor
    · rintro ⟨hx | hx, hxv⟩
      · exact Or.inl ⟨hx, hxv⟩
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨Or.inl hx.1, hx.2⟩
      · refine ⟨Or.inr hx, ?_⟩
        obtain ⟨g, ⟨hg, hge⟩, hxg⟩ := mem_iUnion₂.mp hx
        rintro rfl
        exact hleaf g hg hge hxg
  have hvBad : v ∉ Bad := by
    rw [← hBadeq]
    exact fun h => h.2 rfl
  -- `G` is the complement of `Bad`, and `T` is `e` with its end `v`.
  have hBadU : ∀ x ∈ Bad, x ∈ Γ.U ∧ x ∉ e := by
    intro x hx
    rw [← hBadeq] at hx
    exact hx.1
  obtain ⟨Z₁, hZ₁, hvZ₁, hZ₁B, -, hZ₁cl⟩ := exists_punctured_nbhd hS hBad.isOpen_compl hvBad
  have hG : IsPreconnected Badᶜ := by
    refine hc.subset_closure ?_ ?_
    · intro x hx hxB
      exact hx (hBadU x hxB)
    · intro x hx
      by_cases hxv : x = v
      · rw [hxv]
        refine closure_mono ?_ hZ₁cl
        rintro y ⟨hyZ, hyv⟩ hyU
        exact hZ₁B hyZ (by rw [← hBadeq]; exact ⟨hyU, hyv⟩)
      · refine subset_closure fun hxU => hx ?_
        rw [← hBadeq]
        exact ⟨hxU, hxv⟩
  let T : Set S := e ∪ {v}
  have hGT : Badᶜ \ T = univ \ Γ.U := by
    ext x
    constructor
    · rintro ⟨hxB, hxT⟩
      refine ⟨mem_univ _, fun hxU => hxB ?_⟩
      rw [← hBadeq]
      exact ⟨⟨hxU, fun hxe => hxT (Or.inl hxe)⟩, fun hxv => hxT (Or.inr hxv)⟩
    · rintro ⟨-, hxU⟩
      refine ⟨fun hxB => hxU (hBadU x hxB).1, ?_⟩
      rintro (hxe | hxv)
      · exact hxU (he.2.1 hxe).1
      · exact hxU (Γ.V_subset_U (by rw [mem_singleton_iff.mp hxv]; exact hvV))
  have hclosed : IsClosed (Badᶜᶜ ∪ T) := by
    have : Badᶜᶜ ∪ T = Γ.U := by
      rw [compl_compl]
      ext x
      constructor
      · rintro (hx | hx | hx)
        · exact (hBadU x hx).1
        · exact (he.2.1 hx).1
        · exact Γ.V_subset_U (by rw [mem_singleton_iff.mp hx]; exact hvV)
      · intro hx
        by_cases hxe : x ∈ e
        · exact Or.inr (Or.inl hxe)
        by_cases hxv : x = v
        · exact Or.inr (Or.inr hxv)
        · refine Or.inl ?_
          rw [← hBadeq]
          exact ⟨⟨hx, hxe⟩, hxv⟩
    rw [this]
    exact Γ.isClosed_U
  -- A point `p` of `e` near `v`, and points `a₁, a₂` on its two sides near `v`.
  obtain ⟨Z, hZ, hvZ, hZpts⟩ := exists_leaf_nbhd hS Γ he huv hcap hL hleaf isOpen_univ (mem_univ v)
  obtain ⟨p, hpZ, hpe⟩ := mem_closure_iff.mp hve Z hZ hvZ
  obtain ⟨W, A₁, A₂, hW, hpW, -, hsub, h₁, h₂, d₁, d₂, c₁, c₂⟩ := exists_edge_sides hS Γ he hpe
  have hWZ : IsOpen (W ∩ Z) := hW.inter hZ
  have hpWZ : p ∈ W ∩ Z := ⟨hpW, hpZ⟩
  obtain ⟨a₁, ha₁WZ, ha₁⟩ := mem_closure_iff.mp (c₁ ⟨hpe, hpW⟩) _ hWZ hpWZ
  obtain ⟨a₂, ha₂WZ, ha₂⟩ := mem_closure_iff.mp (c₂ ⟨hpe, hpW⟩) _ hWZ hpWZ
  have ha₁U : a₁ ∉ Γ.U := disjoint_left.mp d₁ ha₁
  have ha₂U : a₂ ∉ Γ.U := disjoint_left.mp d₂ ha₂
  have hcomp : IsPreconnected (univ \ Γ.U) → IsPreconnected Γ.Uᶜ := by
    intro h
    rwa [← compl_eq_univ_sdiff] at h
  apply hcomp
  rw [← hGT]
  refine isPreconnected_sdiff_of_local hBad.isOpen_compl hG hclosed
    ⟨v, hvBad, Or.inr rfl⟩ (a := a₁) (by rw [hGT]; exact ⟨mem_univ _, ha₁U⟩) ?_
  rw [hGT]
  rintro x hx ⟨t, ⟨-, ht⟩, htc⟩
  have hreg : connectedComponentIn (univ \ Γ.U) x ∈ Γ.R := (mem_R_iff Γ).mpr ⟨x, hx.2, rfl⟩
  set C := connectedComponentIn (univ \ Γ.U) x with hC
  have hCo : IsOpen C := region_isOpen hreg
  -- Two points of `Z` off `U(Γ)`, one of them in `C`: the other one is in `C` as well.
  have hjoin : ∀ b ∈ C, b ∈ Z → ∀ a ∈ Z, a ∉ Γ.U → a ∈ C := by
    intro b hbC hbZ a haZ haU
    obtain ⟨A, hA, hAd, hbA, haA⟩ := hZpts b hbZ (region_subset hreg hbC) a haZ haU
    exact subset_region hreg hA hAd hbA hbC haA.1
  rcases ht with hte | htv
  · have hpc : p ∈ closure C := edge_subset_closure_of_incident hS he hreg ⟨t, hte, htc⟩ hpe
    obtain ⟨b, hbWZ, hbC⟩ := mem_closure_iff.mp hpc _ hWZ hpWZ
    rcases hsub ⟨hbWZ.1, region_subset hreg hbC⟩ with hb | hb
    · exact subset_region hreg h₁ d₁ hb hbC ha₁
    · have ha₂C : a₂ ∈ C := subset_region hreg h₂ d₂ hb hbC ha₂
      exact hjoin a₂ ha₂C ha₂WZ.2 a₁ ha₁WZ.2 ha₁U
  · obtain rfl : t = v := htv
    obtain ⟨b, hbZ, hbC⟩ := mem_closure_iff.mp htc Z hZ hvZ
    exact hjoin b hbC hbZ a₁ ha₁WZ.2 ha₁U

/-- The complement of a drawing without circuits in a connected closed surface is connected. So the
drawing has only one region, which Graph Minors XI uses in the proof of (4.4), page 80. -/
theorem isPreconnected_compl_of_noCircuit (hS : IsClosedSurface S) [PreconnectedSpace S]
    (Γ : Drawing S)
    (hno : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ → False) : IsPreconnected Γ.Uᶜ := by
  have : T2Space S := hS.2.1
  induction hn : Γ.E.ncard using Nat.strong_induction_on generalizing Γ with
  | _ n ih =>
    by_cases hE : Γ.E.Nonempty
    · obtain ⟨e, he, u, v, huv, hcap, hL, hleaf⟩ := exists_leaf hno hE
      refine isPreconnected_compl_of_leaf hS Γ he huv hcap hL hleaf ?_
      rw [← deleteEdge_U Γ he]
      have hlt : (Γ.deleteEdge e).E.ncard < n := by
        rw [deleteEdge_E, ← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem he Γ.finite_edges
      exact ih _ hlt (Γ.deleteEdge e)
        (fun C hC hCs => hno C hC (hCs.trans (deleteEdge_isSubdrawing Γ e))) rfl
    · have hU : Γ.U = Γ.V := by
        rw [Γ.U_eq]
        have hemp : Γ.E = ∅ := not_nonempty_iff_eq_empty.mp hE
        rw [hemp]
        simp
      rw [hU]
      exact isPreconnected_compl_finite hS Γ.finite_V

/-- A drawing without circuits has at most one region. -/
theorem region_eq_of_noCircuit (hS : IsClosedSurface S) [PreconnectedSpace S]
    {Γ : Drawing S}
    (hno : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ → False) {r₁ r₂ : Set S}
    (h₁ : r₁ ∈ Γ.R) (h₂ : r₂ ∈ Γ.R) : r₁ = r₂ := by
  have hc := isPreconnected_compl_of_noCircuit hS Γ hno
  obtain ⟨x, hx⟩ := region_nonempty h₁
  obtain ⟨y, hy⟩ := region_nonempty h₂
  have hy₁ : y ∈ r₁ := by
    obtain ⟨z, -, rfl⟩ := (mem_R_iff Γ).mp h₁
    rw [connectedComponentIn_eq hx]
    refine (compl_eq_univ_sdiff Γ.U ▸ hc).subset_connectedComponentIn
      (connectedComponentIn_subset _ _ hx) subset_rfl ?_
    exact ⟨mem_univ _, region_subset h₂ hy⟩
  exact region_eq_of_mem h₁ h₂ hy₁ hy

end GraphMinor.GM11

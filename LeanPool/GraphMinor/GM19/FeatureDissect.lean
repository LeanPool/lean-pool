/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureAccess
public import LeanPool.GraphMinor.Surface.CutGraph

/-!
# A dissection of a surface that contains a given graph

We want to cut a surface along a graph, so we want a dissection into discs whose graph contains the
given graph. The theorem
`exists_dissection` for closed surfaces asks that the graph hangs well on any graph that stays
connected when a point is removed. A
vertex of degree one does not hang well. So first we add `O`-arcs, one through each vertex that is
not on the boundary. At a vertex of
degree at least two, a small curve around the vertex meets two edges, and these close up to an
`O`-arc. At a vertex of degree one, the
arc given by `exists_chord` closes up the end of the edge (`exists_arcs_through`). Every edge then
has both ends on the `O`-arcs, and
this is all the proof for closed surfaces needs (`exists_dissection_graph`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function Metric GraphMinor.Surface

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The part of a line from its end `v` to the first point outside the open set `O`. The set `R`
holds the rest of the line. -/
theorem exists_piece [T2Space S] {e : Set S} {v w : S} (hl : IsLineWithEnds e v w) {O : Set S}
  (hO : IsOpen O) (hv : v ∈ O)
    (hw : w ∉ O) :
    ∃ ℓ : 𝕀 → S, IsArcMap ℓ ∧ ℓ 0 = v ∧ range ℓ ⊆ e ∧ ℓ 1 ∉ O ∧ ℓ 1 ∈ closure O ∧ (∀ t, t ≠ 1
      → ℓ t ∈ O) ∧
      ∃ R, IsClosed R ∧ v ∉ R ∧ e ⊆ range ℓ ∪ R := by
  obtain ⟨b, hb, rfl, rfl, rfl⟩ := hl.exists_arc
  have hK : IsCompact (b ⁻¹' Oᶜ) := (hO.isClosed_compl.preimage hb.1).isCompact
  obtain ⟨τ, ⟨hτ, hmin⟩⟩ := hK.exists_isLeast ⟨1, hw⟩
  have hτ0 : τ ≠ 0 := fun h ↦ hτ (h ▸ hv)
  have hpos : (0 : 𝕀) < τ := lt_of_le_of_ne unitInterval.nonneg' hτ0.symm
  have hin : ∀ t, t < τ → b t ∈ O := fun t ht ↦ by
    by_contra h
    exact absurd (hmin h) (not_le.mpr ht)
  have hcl : b τ ∈ closure O := by
    have h1 : τ ∈ closure (Iio τ) := by
      rw [closure_Iio' (a := τ) ⟨0, hpos⟩]
      exact mem_Iic.mpr le_rfl
    exact map_mem_closure hb.1 h1 hin
  have hne : (0 : 𝕀) ≠ τ := hτ0.symm
  have hr := range_subArc b hpos.le
  refine ⟨subArc b 0 τ, hb.sub hne, subArc_zero _ _ _, range_subArc_subset _ _ _, ?_, ?_, ?_,
    b '' Icc τ 1,
    (isCompact_Icc.image hb.1).isClosed, ?_, ?_⟩
  · rw [subArc_one]
    exact hτ
  · rw [subArc_one]
    exact hcl
  · intro t ht
    have hm : subArc b 0 τ t ∈ b '' Icc 0 τ := hr ▸ mem_range_self t
    obtain ⟨x, hx, hxe⟩ := hm
    rw [← hxe]
    refine hin x (lt_of_le_of_ne hx.2 fun h ↦ ht ?_)
    apply (hb.sub hne).2
    rw [subArc_one, ← hxe, h]
  · rintro ⟨x, hx, hxe⟩
    have : x = 0 := hb.2 hxe
    rw [this] at hx
    exact absurd hx.1 (not_le.mpr hpos)
  · rintro _ ⟨x, rfl⟩
    rcases le_total x τ with h | h
    · exact .inl (hr ▸ ⟨x, ⟨unitInterval.nonneg', h⟩, rfl⟩)
    · exact .inr ⟨x, ⟨h, unitInterval.le_one'⟩, rfl⟩

/-- An edge through a vertex `v` is a line from `v` to another vertex. -/
theorem exists_other {V : Set S} {E : Set (Set S)} (hg : IsGraph V E) {e : Set S}
  (he : e ∈ E) {v : S} (hv : v ∈ V)
    (hve : v ∈ e) : ∃ w, w ∈ V ∧ w ≠ v ∧ IsLineWithEnds e v w := by
  obtain ⟨a, b, hab, hl, hi⟩ := hg.edge e he
  have h1 : v ∈ e ∩ V := ⟨hve, hv⟩
  have h2 : a ∈ e ∩ V := hi ▸ .inl rfl
  have h3 : b ∈ e ∩ V := hi ▸ .inr rfl
  rw [hi] at h1
  rcases h1 with rfl | rfl
  · exact ⟨b, h3.2, hab.symm, hl⟩
  · exact ⟨a, h2.2, hab, hl.symm⟩

/-- A vertex of degree one that is not on the boundary lies on an `O`-arc that we can add to the
graph. -/
theorem exists_leaf_loop [T2Space S] {V : Set S} {E : Set (Set S)} (hg : IsGraph V E)
  (hVE : V ⊆ ⋃₀ E) {v : S} {e : Set S}
    (hvi : IsInteriorPoint v) (hv : v ∈ V) (he : e ∈ E) (hve : v ∈ e) (huniq : ∀ f ∈ E, v ∈ f → f
      = e) :
    ∃ V' E' C, IsGraph V' E' ∧ V ⊆ V' ∧ V' ⊆ ⋃₀ E' ∧ ⋃₀ E' = ⋃₀ E ∪ C ∧ IsOArc C ∧ v ∈ C := by
  classical
  obtain ⟨w, hwV, hwv, hl⟩ := exists_other hg he hv hve
  let Z : Set S := (V \ {v}) ∪ ⋃₀ (E \ {e})
  have hZc : IsClosed Z := by
    refine ((hg.fin.subset sdiff_subset).isClosed).union ((hg.fine.subset
      sdiff_subset).isClosed_sUnion ?_)
    rintro f ⟨hf, -⟩
    obtain ⟨_, _, -, hl', -⟩ := hg.edge f hf
    exact hl'.isCompact.isClosed
  have hvZ : v ∉ Z := by
    rintro (⟨-, h⟩ | ⟨f, ⟨hf, hfe⟩, hvf⟩)
    · exact h rfl
    · exact hfe (huniq f hf hvf)
  obtain ⟨U, h, g, c, hUW, hg0⟩ := hvi.exists_ballChart hZc.isOpen_compl hvZ (R := 2) (by norm_num)
  have hb12 : ball (0 : ℂ) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  have hh0 : h v = 0 := by
    have := c.hg (mem_ball_self (by norm_num : (0 : ℝ) < 2))
    rwa [hg0] at this
  have hO : IsOpen (g '' ball 0 1) := c.isOpen_image isOpen_ball hb12
  have hvO : v ∈ g '' ball 0 1 := ⟨0, mem_ball_self one_pos, hg0⟩
  have hgU : ∀ z ∈ ball (0 : ℂ) 2, g z ∈ U := fun z hz ↦ c.gm hz
  have hwO : w ∉ g '' ball 0 1 := by
    rintro ⟨z, hz, rfl⟩
    exact hUW (hgU z (hb12 hz)) (.inl ⟨hwV, hwv⟩)
  obtain ⟨ℓ, hℓ, hℓ0, hℓe, hℓ1, hℓc, hℓi, R, hRc, hvR, heR⟩ := exists_piece hl hO hvO hwO
  have hT : IsClosed (g '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn (c.gc.mono hcb)).isClosed
  have hclT : closure (g '' ball 0 1) ⊆ g '' closedBall 0 1 := closure_minimal
    (image_mono ball_subset_closedBall) hT
  have hℓU : ∀ t, ℓ t ∈ U := fun t ↦ by
    by_cases ht : t = 1
    · obtain ⟨z, hz, hzv⟩ := hclT hℓc
      rw [ht, ← hzv]
      exact hgU z (hcb hz)
    · obtain ⟨z, hz, hzv⟩ := hℓi t ht
      rw [← hzv]
      exact hgU z (hb12 hz)
  let a : 𝕀 → ℂ := fun t ↦ h (ℓ t)
  have ha : IsArcMap a := ⟨c.hc.comp_continuous hℓ.1 hℓU, fun x y hxy ↦ hℓ.2 (by
    rw [← c.gh (hℓU x), ← c.gh (hℓU y)]
    exact congrArg g hxy)⟩
  have ha0 : a 0 = 0 := by simp only [a, hℓ0, hh0]
  have ha1 : ‖a 1‖ = 1 := by
    obtain ⟨z, hz, hzv⟩ := hclT hℓc
    have hne : ¬ ‖z‖ < 1 := fun hlt ↦ hℓ1 ⟨z, mem_ball_zero_iff.mpr hlt, hzv⟩
    have e1 : a 1 = z := by
      simp only [a]
      rw [← hzv, c.hg (hcb hz)]
    rw [e1]
    exact le_antisymm (mem_closedBall_zero_iff.mp hz) (not_lt.mp hne)
  have halt : ∀ t, t ≠ 1 → ‖a t‖ < 1 := fun t ht ↦ by
    obtain ⟨z, hz, hzv⟩ := hℓi t ht
    have e1 : a t = z := by
      simp only [a]
      rw [← hzv, c.hg (hb12 hz)]
    rw [e1]
    exact mem_ball_zero_iff.mp hz
  have hnh : g ⁻¹' Rᶜ ∈ 𝓝 (0 : ℂ) := by
    have hcont : ContinuousAt g 0 := c.gc.continuousAt (ball_mem_nhds 0 (by norm_num))
    refine hcont.preimage_mem_nhds (hRc.isOpen_compl.mem_nhds ?_)
    rw [hg0]
    exact hvR
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp hnh
  have hε : 0 < min ε₀ 1 := lt_min hε₀ one_pos
  obtain ⟨s, hs0, -, q, hq, hq0, hq1, hqb, hqoff⟩ := exists_chord ha ha0 ha1 halt hε
  have hq2 : ∀ t, q t ∈ ball (0 : ℂ) 2 := fun t ↦ by
    have := mem_ball_zero_iff.mp (hqb (mem_range_self t))
    exact mem_ball_zero_iff.mpr (by linarith [min_le_right ε₀ (1 : ℝ)])
  have hqR : ∀ t, g (q t) ∉ R := fun t ↦ by
    have := mem_ball_zero_iff.mp (hqb (mem_range_self t))
    exact hball (mem_ball_zero_iff.mpr (by linarith [min_le_left ε₀ (1 : ℝ)]))
  let A' : 𝕀 → S := fun t ↦ g (q t)
  have hA' : IsArcMap A' := ⟨c.gc.comp_continuous hq.1 hq2, fun x y hxy ↦ hq.2 (by
    rw [← c.hg (hq2 x), ← c.hg (hq2 y)]
    exact congrArg h hxy)⟩
  have hA0 : A' 0 = v := by simp only [A', hq0, hg0]
  have hA1 : A' 1 = ℓ s := by
    simp only [A', hq1, a]
    exact c.gh (hℓU s)
  have hlA := hA'.isLineWithEnds
  rw [hA0, hA1] at hlA
  have hgr : gr V E = ⋃₀ E := union_eq_right.mpr hVE
  have hps : ℓ s ∈ e := hℓe (mem_range_self s)
  have hps' : ℓ s ∈ ⋃₀ E := ⟨e, he, hps⟩
  have hmeet : range A' ∩ gr V E = {v, ℓ s} := by
    rw [hgr]
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, f, hf, hxf⟩
      by_cases ht0 : t = 0
      · exact .inl (by rw [ht0, hA0])
      by_cases ht1 : t = 1
      · exact .inr (by rw [ht1, hA1]; rfl)
      exfalso
      have hxU : A' t ∈ U := hgU _ (hq2 t)
      have hfe : f = e := by
        by_contra hne
        exact hUW hxU (.inr ⟨f, ⟨hf, hne⟩, hxf⟩)
      rcases heR (hfe ▸ hxf) with ⟨y, hy⟩ | hR
      · apply hqoff t ht0 ht1
        refine ⟨y, ?_⟩
        simp only [a]
        rw [hy]
        exact c.hg (hq2 t)
      · exact hqR t hR
    · rintro (rfl | rfl)
      · exact ⟨⟨0, hA0⟩, hVE hv⟩
      · exact ⟨⟨1, hA1⟩, hps'⟩
  have hvp : v ≠ ℓ s := fun h' ↦ hs0 (hℓ.2 (hℓ0.trans h').symm)
  obtain ⟨E₁, hg1, hgr1, hsub1⟩ := hg.add_point (ℓ s)
  have hV1 : insert (ℓ s) V ⊆ ⋃₀ E₁ := by
    rintro x (rfl | hx)
    · exact hsub1 hps'
    · exact hsub1 (hVE hx)
  have hE1 : gr (insert (ℓ s) V) E₁ = ⋃₀ E := by
    rw [hgr1, hgr, insert_eq_of_mem hps']
  have hE1' : ⋃₀ E₁ = ⋃₀ E := by rw [← hE1]; exact (union_eq_right.mpr hV1).symm
  have hA : range A' ∩ gr (insert (ℓ s) V) E₁ = {v, ℓ s} := by rw [hE1, ← hgr, hmeet]
  obtain ⟨hg2, -⟩ := hg1.add_arc hvp hlA (.inr hv) (.inl rfl) hA
  have hB := (hℓ.sub hs0.symm).isLineWithEnds
  rw [subArc_zero, subArc_one, hℓ0] at hB
  have hBsub : range (subArc ℓ 0 s) ⊆ ⋃₀ E := fun x hx ↦ ⟨e, he, hℓe (range_subArc_subset _ _ _ hx)⟩
  have hi : range A' ∩ range (subArc ℓ 0 s) = {v, ℓ s} := by
    apply Subset.antisymm
    · rw [← hmeet, hgr]
      exact inter_subset_inter_right _ hBsub
    · rintro x (rfl | rfl)
      · exact ⟨⟨0, hA0⟩, hB.left_mem⟩
      · exact ⟨⟨1, hA1⟩, hB.right_mem⟩
  refine ⟨insert (ℓ s) V, insert (range A') E₁, range A' ∪ range (subArc ℓ 0 s), hg2,
    subset_insert _ _, ?_, ?_,
    oArc_of_lines hlA hB hi, .inl ⟨0, hA0⟩⟩
  · rw [sUnion_insert]
    exact hV1.trans subset_union_right
  · rw [sUnion_insert, hE1', union_comm]
    ext x
    constructor
    · rintro (h' | h')
      · exact .inl h'
      · exact .inr (.inl h')
    · rintro (h' | h' | h')
      · exact .inl h'
      · exact .inr h'
      · exact .inl (hBsub h')

/-- A vertex with two edges that is not on the boundary lies on an `O`-arc. We add a small curve
around it, and with this curve
also an `O`-arc made of two pieces of edges and a part of the curve. -/
theorem exists_two_loop [CompactSpace S] [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {V : Set
  S} {E : Set (Set S)}
    (hg : IsGraph V E) (hVE : V ⊆ ⋃₀ E) {v : S} {e₁ e₂ : Set S} (hvi : IsInteriorPoint v)
      (hv : v ∈ V) (he₁ : e₁ ∈ E)
    (he₂ : e₂ ∈ E) (hne : e₁ ≠ e₂) (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂) :
    ∃ V' E' 𝓑, IsGraph V' E' ∧ V ⊆ V' ∧ V' ⊆ ⋃₀ E' ∧ ⋃₀ E' = ⋃₀ E ∪ ⋃₀ 𝓑 ∧ 𝓑.Finite ∧
      (∀ C ∈ 𝓑, IsOArc C) ∧ v ∈ ⋃₀ 𝓑 := by
  classical
  obtain ⟨w₁, hw₁V, hw₁v, hl₁⟩ := exists_other hg he₁ hv hv₁
  obtain ⟨w₂, hw₂V, hw₂v, hl₂⟩ := exists_other hg he₂ hv hv₂
  have hZc : IsClosed (V \ {v}) := (hg.fin.subset sdiff_subset).isClosed
  obtain ⟨U, h, g, c, hUW, hg0⟩ := hvi.exists_ballChart hZc.isOpen_compl (by simp) (R := 3)
    (by norm_num)
  obtain ⟨L, hL, hLu⟩ := hg.exists_list
  obtain ⟨P, D, hPO, hPt, hD, hbd, hgD, hDU, hdis⟩ := exists_tame_curve' hman c L hL
  have hgr : gr V E = ⋃₀ E := union_eq_right.mpr hVE
  rw [hLu, ← hgr] at hPt
  obtain ⟨V1, E1, hV1, hg1, hgr1, hno1⟩ := hg.add_curve hPO hPt
  have hO := hD.isOpen_discInt hman
  have hvg : v ∈ g '' closedBall 0 2 := ⟨0, mem_closedBall_self (by norm_num), hg0⟩
  have hvP : v ∉ P := fun h' ↦ Set.disjoint_left.mp hdis h' hvg
  have hvO : v ∈ discInt D := ⟨hgD hvg, by rwa [hbd]⟩
  have hOD : discInt D ⊆ D := sdiff_subset
  have hwO : ∀ w, w ∈ V → w ≠ v → w ∉ discInt D := fun w hw hne' hin ↦
    hUW (hDU (hOD hin)) ⟨hw, hne'⟩
  obtain ⟨ℓ₁, hℓ₁, h10, h1e, h1n, h1c, h1i, -⟩ := exists_piece hl₁ hO hvO (hwO w₁ hw₁V hw₁v)
  obtain ⟨ℓ₂, hℓ₂, h20, h2e, h2n, h2c, h2i, -⟩ := exists_piece hl₂ hO hvO (hwO w₂ hw₂V hw₂v)
  have hDc : IsClosed D := hD.isCompact.isClosed
  have hclD : closure (discInt D) ⊆ D := closure_minimal hOD hDc
  have hend : ∀ x, x ∈ closure (discInt D) → x ∉ discInt D → x ∈ P := fun x h1 h2 ↦ by
    by_contra h3
    exact h2 ⟨hclD h1, by rwa [hbd]⟩
  have hx₁ := hend _ h1c h1n
  have hx₂ := hend _ h2c h2n
  have hsubD : ∀ ℓ : 𝕀 → S, ℓ 1 ∈ closure (discInt D) → (∀ t, t ≠ 1 → ℓ t ∈ discInt D)
    → range ℓ ⊆ D := by
    rintro ℓ h1 h2 _ ⟨t, rfl⟩
    by_cases ht : t = 1
    · rw [ht]
      exact hclD h1
    · exact hOD (h2 t ht)
  have hin : range ℓ₁ ∩ range ℓ₂ = {v} := by
    apply Subset.antisymm
    · rintro x ⟨hx1, hx2⟩
      have hxV := hg.disj _ he₁ _ he₂ hne ⟨h1e hx1, h2e hx2⟩
      by_contra hxv
      exact hUW (hDU (hsubD _ h1c h1i hx1)) ⟨hxV, hxv⟩
    · rintro x rfl
      exact ⟨⟨0, h10⟩, ⟨0, h20⟩⟩
  have hl1 := hℓ₁.isLineWithEnds
  have hl2 := hℓ₂.isLineWithEnds
  rw [h10] at hl1
  rw [h20] at hl2
  have hM := hl1.symm.union hl2 hin
  have hxne : ℓ₁ 1 ≠ ℓ₂ 1 := fun h' ↦ by
    have : ℓ₁ 1 ∈ range ℓ₁ ∩ range ℓ₂ := ⟨⟨1, rfl⟩, ⟨1, h'.symm⟩⟩
    rw [hin] at this
    exact hvP (this ▸ hx₁)
  obtain ⟨A, B, hA, hB, hAB, -⟩ := hPO.lines hx₁ hx₂ hxne
  have hAP : A ⊆ P := hAB ▸ subset_union_left
  have hoff : ∀ x, x ∈ P → x ∉ discInt D := fun x hx h' ↦ h'.2 (hbd ▸ hx)
  have hi : (range ℓ₁ ∪ range ℓ₂) ∩ A = {ℓ₁ 1, ℓ₂ 1} := by
    apply Subset.antisymm
    · rintro x ⟨⟨t, rfl⟩ | ⟨t, rfl⟩, hxA⟩
      · by_cases ht : t = 1
        · exact .inl (by rw [ht])
        · exact absurd (h1i t ht) (hoff _ (hAP hxA))
      · by_cases ht : t = 1
        · exact .inr (by rw [ht]; rfl)
        · exact absurd (h2i t ht) (hoff _ (hAP hxA))
    · rintro x (rfl | rfl)
      · exact ⟨hM.left_mem, hA.left_mem⟩
      · exact ⟨hM.right_mem, hA.right_mem⟩
  have hC := oArc_of_lines hM hA hi
  have hgrV1 : gr V1 E1 = ⋃₀ E1 := union_eq_right.mpr (hno1 hVE)
  have hMsub : range ℓ₁ ∪ range ℓ₂ ⊆ ⋃₀ E := by
    rintro x (hx | hx)
    · exact ⟨e₁, he₁, h1e hx⟩
    · exact ⟨e₂, he₂, h2e hx⟩
  refine ⟨V1, E1, {(range ℓ₁ ∪ range ℓ₂) ∪ A, P}, hg1, hV1, hno1 hVE, ?_, by simp, ?_, ?_⟩
  · rw [← hgrV1, hgr1, hgr]
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact .inl hx
      · exact .inr ⟨P, .inr rfl, hx⟩
    · rintro x (hx | ⟨C, rfl | rfl, hx⟩)
      · exact .inl hx
      · rcases hx with hx | hx
        · exact .inl (hMsub hx)
        · exact .inr (hAP hx)
      · exact .inr hx
  · rintro C (rfl | rfl)
    · exact hC
    · exact hPO
  · exact ⟨_, .inl rfl, .inl (.inl ⟨0, h10⟩)⟩

/-- We can enlarge a graph that contains the boundary, by `O`-arcs, so that every chosen vertex is
on one of the `O`-arcs. -/
theorem exists_arcs_through (hS : IsSurface S) {V₀ : Set S} {E₀ : Set (Set S)} (hg : IsGraph V₀ E₀)
  (hV₀ : V₀ ⊆ ⋃₀ E₀)
    (hbd : bd S ⊆ ⋃₀ E₀) {W : Set S} (hW : W.Finite) (hWV : W ⊆ V₀) :
    ∃ V E 𝓐, IsGraph V E ∧ V₀ ⊆ V ∧ V ⊆ ⋃₀ E ∧ ⋃₀ E = ⋃₀ E₀ ∪ ⋃₀ 𝓐 ∧ 𝓐.Finite ∧ (∀ C ∈ 𝓐, IsOArc C)
      ∧ cuffs S ⊆ 𝓐 ∧
      W ⊆ ⋃₀ 𝓐 := by
  classical
  obtain ⟨hcpt, ht2, hman⟩ := id hS
  induction W, hW using Set.Finite.induction_on with
  | empty =>
    have hc := cuff_statement.{u} S hS
    refine ⟨V₀, E₀, cuffs S, hg, subset_rfl, hV₀, ?_, hc.2.1, hc.2.2, subset_rfl, empty_subset _⟩
    rw [sUnion_cuffs]
    exact (union_eq_left.mpr hbd).symm
  | @insert v W _ _ ih =>
    obtain ⟨V, E, 𝓐, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih fun x hx ↦ hWV (mem_insert_of_mem _ hx)
    have hvV₀ : v ∈ V₀ := hWV (mem_insert _ _)
    by_cases hv : v ∈ ⋃₀ 𝓐
    · refine ⟨V, E, 𝓐, h1, h2, h3, h4, h5, h6, h7, ?_⟩
      rintro x (rfl | hx)
      · exact hv
      · exact h8 hx
    have hvi : IsInteriorPoint v := by
      by_contra h'
      exact hv (sUnion_mono h7 (sUnion_cuffs (S := S) ▸ h'))
    obtain ⟨e, he, hve⟩ := h3 (h2 hvV₀)
    have hstep : ∃ V' E' 𝓑, IsGraph V' E' ∧ V ⊆ V' ∧ V' ⊆ ⋃₀ E' ∧ ⋃₀ E' = ⋃₀ E ∪ ⋃₀ 𝓑 ∧ 𝓑.Finite ∧
        (∀ C ∈ 𝓑, IsOArc C) ∧ v ∈ ⋃₀ 𝓑 := by
      by_cases hsec : ∃ f ∈ E, v ∈ f ∧ f ≠ e
      · obtain ⟨f, hf, hvf, hfe⟩ := hsec
        exact exists_two_loop hman h1 h3 hvi (h2 hvV₀) he hf hfe.symm hve hvf
      · push Not at hsec
        obtain ⟨V', E', C, a1, a2, a3, a4, a5, a6⟩ := exists_leaf_loop h1 h3 hvi
          (h2 hvV₀) he hve hsec
        exact ⟨V', E', {C}, a1, a2, a3, by simpa using a4, by simp, by simpa using a5,
          by simpa using a6⟩
    obtain ⟨V', E', 𝓑, a1, a2, a3, a4, a5, a6, a7⟩ := hstep
    refine ⟨V', E', 𝓐 ∪ 𝓑, a1, h2.trans a2, a3, ?_, h5.union a5, ?_,
      subset_union_of_subset_left h7 _, ?_⟩
    · rw [a4, h4, sUnion_union, union_assoc]
    · rintro C (hC | hC)
      · exact h6 C hC
      · exact a6 C hC
    · rintro x (rfl | hx)
      · exact sUnion_mono subset_union_right a7
      · exact sUnion_mono subset_union_left (h8 hx)

/-- Adding finitely many lines with distinct ends in a set keeps it connected after removing a
point. -/
theorem twoConn_add_lines {G : Set S} (hG : TwoConn G) {𝓛 : Set (Set S)} (h𝓛 : 𝓛.Finite)
    (hl : ∀ L ∈ 𝓛, ∃ s t, IsLineWithEnds L s t ∧ s ≠ t ∧ s ∈ G ∧ t ∈ G) : TwoConn (G ∪ ⋃₀ 𝓛) := by
  induction 𝓛, h𝓛 using Set.Finite.induction_on with
  | empty => simpa using hG
  | @insert L 𝓛 _ _ ih =>
    have h1 := ih fun L' hL' ↦ hl L' (mem_insert_of_mem _ hL')
    obtain ⟨s, t, hL, hne, hs, ht⟩ := hl L (mem_insert _ _)
    have h2 := h1.add_line hL (.inl hs) (.inl ht) hne
    rwa [sUnion_insert, union_comm L, ← union_assoc]

/-- **A dissection of a connected surface whose graph contains a given graph.** The given graph has
to contain the boundary. -/
theorem exists_dissection_graph (hS : IsSurface S) [ConnectedSpace S] {V₀ : Set S} {E₀ : Set
  (Set S)} (hg₀ : IsGraph V₀ E₀)
    (hV₀ : V₀ ⊆ ⋃₀ E₀) (hbd : bd S ⊆ ⋃₀ E₀) :
    ∃ (V : Set S) (E 𝓕 : Set (Set S)), IsDissection V E 𝓕 ∧ V₀ ⊆ V ∧ ⋃₀ E₀ ⊆ gr V E := by
  classical
  obtain ⟨V₁, E₁, 𝓐, hg, hV₀₁, hV₁, hE₁, h𝓐, hO𝓐, hcu, hW⟩ := exists_arcs_through hS hg₀ hV₀ hbd
    hg₀.fin subset_rfl
  obtain ⟨hcpt, ht2, hman⟩ := id hS
  obtain ⟨T, _, j, K, hT, hj, hK, hu, hi, hconn⟩ := exists_capAll S hS
  have := hconn inferInstance
  have : T2Space T := hT.2.1
  have hgT := hg.map hj.isEmbedding
  have hsU : ⋃₀ ((fun e => j '' e) '' E₁) = j '' ⋃₀ E₁ := by
    rw [sUnion_image, sUnion_eq_biUnion, image_iUnion₂]
  have hsU₀ : ⋃₀ ((fun e => j '' e) '' E₀) = j '' ⋃₀ E₀ := by
    rw [sUnion_image, sUnion_eq_biUnion, image_iUnion₂]
  have hsA : ⋃₀ ((fun C => j '' C) '' 𝓐) = j '' ⋃₀ 𝓐 := by
    rw [sUnion_image, sUnion_eq_biUnion, image_iUnion₂]
  obtain ⟨ρ, hρ, hl⟩ := exists_inv_of_compactOn (isCompact_univ (X := S)) hj.continuous.continuousOn
    hj.injective.injOn
  have hOT : ∀ C ∈ 𝓐, IsOArc (j '' C) := fun C hC =>
    (hO𝓐 C hC).image hj.continuous.continuousOn (hρ.mono (image_mono (subset_univ _)))
      (fun x _ => hl (mem_univ x))
  obtain ⟨V, E, 𝓕, hVV, hsub, hd⟩ := exists_dissection hT hgT (image_mono hV₁ |>.trans (by
      rintro _ ⟨y, ⟨e, he, hy⟩, rfl⟩
      exact ⟨_, ⟨e, he, rfl⟩, mem_image_of_mem j hy⟩)) (𝓒c := (fun C => j '' C) '' 𝓐) (h𝓐.image _)
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact (hOT C hC).twoConn)
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact (hOT C hC).exists_three)
    (by
      intro G hG hm
      have h1 := hG.sUnion_add (h𝓐.image _) (by
        rintro _ ⟨C, hC, rfl⟩
        exact (hOT C hC).twoConn) hm
      have h2 := twoConn_add_lines h1 (hg₀.fine.image fun e => j '' e) (by
        rintro _ ⟨e, he, rfl⟩
        obtain ⟨u, v, hne, hl', hie⟩ := hg₀.edge e he
        have hu' : u ∈ V₀ := (show u ∈ e ∩ V₀ from hie ▸ .inl rfl).2
        have hv' : v ∈ V₀ := (show v ∈ e ∩ V₀ from hie ▸ .inr rfl).2
        refine ⟨j u, j v, hl'.map_of_embedding hj.isEmbedding, hj.injective.ne hne, .inr ?_,
          .inr ?_⟩
        · rw [hsA]
          exact mem_image_of_mem j (hW hu')
        · rw [hsA]
          exact mem_image_of_mem j (hW hv'))
      have e : G ∪ ⋃₀ ((fun e => j '' e) '' E₁) =
          G ∪ ⋃₀ ((fun C => j '' C) '' 𝓐) ∪ ⋃₀ ((fun e => j '' e) '' E₀) := by
        rw [hsU, hE₁, image_union, hsU₀, hsA, union_assoc, union_comm (j '' ⋃₀ E₀)]
      rw [e]
      exact h2)
  rw [hsU] at hsub
  have hbdA : bd S ⊆ ⋃₀ 𝓐 := by
    rw [← sUnion_cuffs]
    exact sUnion_mono hcu
  have hsub2 : ⋃₀ 𝓐 ⊆ ⋃₀ E₁ := hE₁ ▸ subset_union_right
  have hb0 : j '' bd S ⊆ ⋃₀ E := (image_mono (hbdA.trans hsub2)).trans hsub
  have hb1 : j '' bd S ⊆ ⋃₀ {e ∈ E | e ⊆ range j} := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ ⋃₀ cuffs S := sUnion_cuffs (S := S) ▸ hx
    obtain ⟨C, hC, hxC⟩ := hx'
    have hne : Nonempty T := ⟨j x⟩
    have hC' := hOT C (hcu hC)
    have hsubC : j '' C ⊆ ⋃₀ E := (image_mono (subset_sUnion_of_mem (hcu hC) |>.trans hsub2)).trans
      hsub
    obtain ⟨e, he, hxe⟩ := hd.graph.subset_edges hC' hsubC (mem_image_of_mem j hxC)
    exact ⟨e, ⟨he.1, he.2.trans (image_subset_range _ _)⟩, hxe⟩
  refine ⟨_, _, _, pull_dissection hman hj hK hu hi hd hb0, ?_, ?_⟩
  · intro x hx
    exact hVV (mem_image_of_mem j (hV₀₁ hx))
  · intro x hx
    refine mem_pull_gr hj hK hu hi hd hb1 (.inr (hsub (mem_image_of_mem j ?_)))
    rw [hE₁]
    exact .inl hx

end GraphMinor.GM19

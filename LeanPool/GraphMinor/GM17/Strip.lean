/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Bigon
public import LeanPool.GraphMinor.Surface.DiscRemove

/-!
# A thin strip along a side of a cell

We use the disc on the far side of a side of a cell. In a closed surface we remove the inside of the
closure of the cell, and we take a thin disc along the side with `exists_wedge`
(`exists_strip`). This pushes a side of a cell off the cell: the proofs of (8.2) to (8.8) of Graph
Minors XVII (pages 181 to 183) use it.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- A closed disc is a neighbourhood of the inner points of the line in which it meets the boundary
of the surface. -/
theorem disc_nhds {Y : Type} [TopologicalSpace Y] (hY : IsSurface Y) {D K : Set Y} {u v x : Y}
    (hD : IsClosedDisc D) (hK : IsLineWithEnds K u v) (hKD : K ⊆ discBd D)
    (hDb : D ∩ bd Y = K) (hx : x ∈ K)
    (hxu : x ≠ u) (hxv : x ≠ v) : D ∈ 𝓝 x := by
  have ht2 : T2Space Y := hY.2.1
  have hxb : x ∈ bd Y := (hDb ▸ hx : x ∈ D ∩ bd Y).2
  have hC : connectedComponentIn (bd Y) x ∈ cuffs Y := ⟨x, hxb, rfl⟩
  set C := connectedComponentIn (bd Y) x with hCdef
  have hKb : K ⊆ bd Y := hDb ▸ inter_subset_right
  have hKC : K ⊆ C := (isPreconnected_line hK).subset_connectedComponentIn hx hKb
  have hCb : C ⊆ bd Y := connectedComponentIn_subset _ _
  obtain ⟨T, tT, ι, E, hT, hι, hE, hun, hmeet, hbdE, hbdT⟩ := paste_disc.{0} Y C hY hC
  have ht2T : T2Space T := hT.2.1
  have hDC : D ∩ C = K := subset_antisymm (fun y hy => hDb ▸ ⟨hy.1, hCb hy.2⟩) (subset_inter
    (hKD.trans (discBd_subset D)) hKC)
  have hD' : IsClosedDisc (ι '' D) := by
    obtain ⟨φ⟩ := hD
    exact ⟨φ.trans (hι.isEmbedding.homeomorphImage D)⟩
  have hbD' : discBd (ι '' D) = ι '' discBd D := by
    have h := image_bd_homeomorph (hι.isEmbedding.homeomorphImage D)
    rw [discBd, discBd, ← h, image_image, image_image]
    rfl
  have hl : IsLineWithEnds (ι '' K) (ι u) (ι v) := hK.map_of_embedding hι.isEmbedding
  have hin : ι '' D ∩ E = ι '' K := by
    apply subset_antisymm
    · rintro _ ⟨⟨y, hy, rfl⟩, hyE⟩
      obtain ⟨z, hz, he⟩ := (hmeet ▸ ⟨⟨y, rfl⟩, hyE⟩ : ι y ∈ ι '' C)
      obtain rfl := hι.injective he
      exact ⟨z, hDC ▸ ⟨hy, hz⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨mem_image_of_mem _ (discBd_subset D (hKD hy)), discBd_subset E
        (hbdE ▸ mem_image_of_mem _ (hKC hy))⟩
  obtain ⟨h1, h2⟩ := disc_union _ _ _ _ _ hD' hE hl hin (hbD' ▸ image_mono hKD)
    (hbdE ▸ image_mono hKC)
  have hopen := h1.isOpen_discInt hT.2.2
  have hxint : ι x ∈ discInt (ι '' D ∪ E) := by
    refine ⟨.inl (mem_image_of_mem _ (discBd_subset D (hKD hx))), fun hmem => ?_⟩
    rw [h2] at hmem
    refine hmem.2 ⟨mem_image_of_mem _ hx, ?_⟩
    rintro (h | h)
    · exact hxu (hι.injective h)
    · exact hxv (hι.injective h)
  have hOC : IsOArc C := (cuff_statement.{0} Y hY).2.2 C hC
  obtain ⟨L', hL', hu', hi'⟩ := oarc_split hOC hK hKC
  have hxL' : x ∉ L' := fun h => by
    rcases (hi' ▸ ⟨hx, h⟩ : x ∈ ({u, v} : Set Y)) with h | h
    · exact hxu h
    · exact hxv h
  have hO : ι ⁻¹' discInt (ι '' D ∪ E) ∩ L'ᶜ ∈ 𝓝 x :=
    ((hopen.preimage hι.continuous).inter hL'.isCompact.isClosed.isOpen_compl).mem_nhds ⟨hxint,
      hxL'⟩
  refine Filter.mem_of_superset hO fun y hy => ?_
  rcases hy.1.1 with ⟨z, hz, he⟩ | hE'
  · exact hι.injective he ▸ hz
  · obtain ⟨z, hz, he⟩ := (hmeet ▸ ⟨⟨y, rfl⟩, hE'⟩ : ι y ∈ ι '' C)
    obtain rfl := hι.injective he
    have h3 : z ∈ K ∪ L' := hu'.symm ▸ hz
    exact discBd_subset D (hKD (h3.resolve_right hy.2))


theorem closure_eq_cell {Γ : Painting S} {c : Set S} (hc : c ∈ Γ.C) {x : S}
  (hx : x ∈ closure c) (hn : x ∉ Γ.N) : x ∈ c := by
  by_contra h
  exact hn (Γ.tilde_subset_N hc ⟨hx, h⟩)

theorem closure_inter_closure {Γ : Painting S} {c d : Set S} (hc : c ∈ Γ.C)
  (hd : d ∈ Γ.C) (hne : c ≠ d) : closure c ∩ closure d ⊆ Γ.N := by
  rintro x ⟨h1, h2⟩
  by_contra hn
  exact hne (arcComponentsIn_eq_of_mem hc hd (closure_eq_cell hc h1 hn) (closure_eq_cell hd h2 hn))

/-- A thin disc along a line of the boundary of a disc in a closed surface, off a closed set that
meets the line at most in its ends. -/
theorem disc_strip {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T) {B L Z : Set T} {u v :
  T} (hB : IsClosedDisc B) (hL : IsLineWithEnds L u v) (hLb : L ⊆ discBd B) (hZ : IsClosed Z)
    (hZL : Z ∩ L ⊆ {u, v}) :
    ∃ St γ, IsClosedDisc St ∧ IsLineWithEnds γ u v ∧ discBd St = L ∪ γ ∧ L ∩ γ = {u, v} ∧ St ∩ B
      = L ∧ St ∩ Z ⊆ {u, v} ∧ ∀ x ∈ L, x ≠ u → x ≠ v → B ∪ St ∈ 𝓝 x := by
  classical
  have hcT : CompactSpace T := hT.1
  have ht2T : T2Space T := hT.2.1
  have hTs : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  have hLcl : L ⊆ B := hLb.trans (discBd_subset _)
  have hint : ∀ x ∈ discBd B, IsInteriorPoint x := fun x _ => hT.2.2 x
  obtain ⟨hcl, hY, hbdY⟩ := remove_disc hTs hB hint
  have hv : IsClosedEmbedding (Subtype.val : ↥(discInt B)ᶜ → T) := hcl.isClosedEmbedding_subtypeVal
  have hrv : range (Subtype.val : ↥(discInt B)ᶜ → T) = (discInt B)ᶜ := Subtype.range_val
  have hsv : ∀ {P : Set T}, P ⊆ discBd B → P ⊆ range (Subtype.val : ↥(discInt B)ᶜ → T)
    := fun {P} hP x hx => by
    rw [hrv]
    exact fun h => h.2 (hP hx)
  obtain ⟨u', v', hu', hv', hK⟩ := hL.pull hv.isEmbedding (hsv hLb)
  have hKb : (Subtype.val ⁻¹' L : Set ↥(discInt B)ᶜ) ⊆ bd _ := fun y hy => hbdY ▸ Or.inr (hLb hy)
  have hZK : (Subtype.val ⁻¹' Z : Set ↥(discInt B)ᶜ) ∩ Subtype.val ⁻¹' L ⊆ {u', v'} := by
    rintro y ⟨hy, hyL⟩
    rcases hZL ⟨hy, hyL⟩ with h | h
    · exact .inl (Subtype.ext (h.trans hu'.symm))
    · exact .inr (Subtype.ext (h.trans hv'.symm))
  obtain ⟨D, hD, hKD, hDZ, hDb⟩ := exists_wedge hY hK hKb (hZ.preimage continuous_subtype_val) hZK
  have hDt : IsClosedDisc (Subtype.val '' D) := image_emb_disc hv.isEmbedding hD
  have hDtb : discBd (Subtype.val '' D) = Subtype.val '' discBd D := discBd_image hv.isEmbedding D
  have hDB : Subtype.val '' D ∩ B = L := by
    apply subset_antisymm
    · rintro _ ⟨⟨y, hy, rfl⟩, hyB⟩
      have h1 : y.1 ∈ discBd B := by
        by_contra h
        exact y.2 ⟨hyB, h⟩
      have h2 : y ∈ bd _ := hbdY ▸ Or.inr h1
      exact (hDb ▸ ⟨hy, h2⟩ : y ∈ Subtype.val ⁻¹' L)
    · intro x hx
      obtain ⟨y, hy⟩ := hsv hLb hx
      have hyL : y ∈ Subtype.val ⁻¹' L := by rwa [mem_preimage, hy]
      exact ⟨⟨y, discBd_subset D (hKD hyL), hy⟩, hLcl hx⟩
  obtain ⟨K', hK', hun, hin⟩ := oarc_split hD.isOArc_discBd hK hKD
  have hK'D : K' ⊆ D := (hun ▸ subset_union_right).trans (discBd_subset D)
  have hl' := hK'.map_of_embedding hv.isEmbedding
  rw [hu', hv'] at hl'
  have hjK : Subtype.val '' (Subtype.val ⁻¹' L : Set ↥(discInt B)ᶜ) = L
    := image_preimage_eq_of_subset (hsv hLb)
  refine ⟨_, _, hDt, hl', ?_, ?_, hDB, ?_, ?_⟩
  · rw [hDtb, ← hun, image_union, hjK]
  · apply subset_antisymm
    · rintro _ ⟨hx, y, hy, rfl⟩
      have h1 : y ∈ (Subtype.val ⁻¹' L : Set ↥(discInt B)ᶜ) ∩ K' := ⟨hx, hy⟩
      rw [hin] at h1
      rcases h1 with rfl | rfl
      · exact .inl hu'
      · exact .inr hv'
    · rintro x (rfl | rfl)
      · exact ⟨hL.left_mem, hl'.left_mem⟩
      · exact ⟨hL.right_mem, hl'.right_mem⟩
  · rintro _ ⟨⟨y, hy, rfl⟩, hz⟩
    rcases hDZ ⟨hy, hz⟩ with rfl | rfl
    · exact .inl hu'
    · exact .inr hv'
  · intro x hx hxu hxv
    have hul : L ⊆ discBd (Subtype.val '' D) := by
      rw [hDtb]
      refine fun y hy => ?_
      obtain ⟨y', hy', rfl⟩ := (hjK ▸ hy : y ∈ Subtype.val '' _)
      exact mem_image_of_mem _ (hKD hy')
    obtain ⟨h1, h2⟩ := disc_union _ _ _ _ _ hB hDt hL (by rw [inter_comm]; exact hDB) hLb hul
    have hop := h1.isOpen_discInt (fun y => (hT.2.2 y).isManifoldPoint)
    have hxint : x ∈ discInt (B ∪ Subtype.val '' D) := by
      refine ⟨.inl (hLcl hx), fun hmem => ?_⟩
      rw [h2] at hmem
      refine hmem.2 ⟨hx, ?_⟩
      rintro (h | h)
      · exact hxu h
      · exact hxv h
    exact Filter.mem_of_superset (hop.mem_nhds hxint) fun y hy => hy.1

/-- A thin disc on the far side of a side of a cell. -/
theorem exists_strip [CompactSpace S] [T2Space S] [ConnectedSpace S] (hS : IsSurface S) {Γ :
  Painting S} {c L A : Set S} {u v : S} (hc : c ∈ Γ.C) (hL : IsLineWithEnds L u v)
    (hLb : L ⊆ discBd (closure c)) (hLbd : ∀ x ∈ L, x ≠ u → x ≠ v → x ∉ bd S) (hLN : ∀ x ∈ L, x ≠ u
      → x ≠ v → x ∉ Γ.N) (hA : IsClosed A) (hAL : A ∩ L ⊆ {u, v}) :
    ∃ St γ, IsClosedDisc St ∧ IsLineWithEnds γ u v ∧ discBd St = L ∪ γ ∧ L ∩ γ = {u, v}
      ∧ St ∩ closure c = L ∧ St ∩ A ⊆ {u, v} ∧ St ∩ Γ.U ⊆ L ∧
      ∀ x ∈ L, x ≠ u → x ≠ v → closure c ∪ St ∈ 𝓝 x := by
  classical
  obtain ⟨T, tT, j, cap, hT, hTc, hj, hcap, hcov⟩ := exists_cap_discs _ S hS rfl
  have ht2T : T2Space T := hT.2.1
  obtain ⟨hdisc, -, -, -⟩ := Γ.cell_disc c hc
  have hB : IsClosedDisc (j '' closure c) := image_emb_disc hj.isEmbedding hdisc
  have hbB : discBd (j '' closure c) = j '' discBd (closure c) := discBd_image hj.isEmbedding _
  have hLcl : L ⊆ closure c := hLb.trans (discBd_subset _)
  have hfinC := (cuff_statement.{0} S hS).2.1
  let Z : Set T := j '' (A ∪ Γ.N ∪ ⋃ d ∈ Γ.C \ {c}, closure d) ∪ ⋃ C ∈ cuffs S, cap C
  have hZc : IsClosed Z := (hj.isClosedMap _ ((hA.union Γ.finite_N.isClosed).union
    ((Γ.finite_cells.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure))).union
    (hfinC.isClosed_biUnion fun C hC => (hcap C hC).1.isClosed)
  have hbC : ∀ {C : Set S}, C ∈ cuffs S → C ⊆ bd S := fun {C} hC => by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hZj : ∀ {x}, j x ∈ Z → x ∈ A ∨ x ∈ Γ.N ∨ (∃ d ∈ Γ.C, d ≠ c ∧ x ∈ closure d) ∨ x ∈ bd S := by
    intro x hx
    rcases hx with ⟨y, hy, he⟩ | hx
    · obtain rfl := hj.injective he
      rcases hy with (h | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · obtain ⟨d, hd, h⟩ := mem_iUnion₂.mp h
        exact .inr (.inr (.inl ⟨d, hd.1, hd.2, h⟩))
    · obtain ⟨C, hC, hw⟩ := mem_iUnion₂.mp hx
      obtain ⟨y, hy, he⟩ := ((hcap C hC).2.2 ▸ ⟨⟨x, rfl⟩, hw⟩ : j x ∈ j '' C)
      obtain rfl := hj.injective he
      exact .inr (.inr (.inr (hbC hC hy)))
  have hZends : Z ∩ j '' L ⊆ {j u, j v} := by
    rintro _ ⟨hZx, x, hx, rfl⟩
    by_contra hcon
    have hcu : x ≠ u := fun h => hcon (.inl (congrArg j h))
    have hcv : x ≠ v := fun h => hcon (.inr (congrArg j h))
    rcases hZj hZx with h | h | ⟨d, hd, hne, h⟩ | h
    · rcases hAL ⟨h, hx⟩ with h | h
      · exact hcu h
      · exact hcv h
    · exact hLN x hx hcu hcv h
    · exact hLN x hx hcu hcv (closure_inter_closure hc hd hne.symm ⟨hLcl hx, h⟩)
    · exact hLbd x hx hcu hcv h
  have hl : IsLineWithEnds (j '' L) (j u) (j v) := hL.map_of_embedding hj.isEmbedding
  have hjLb : j '' L ⊆ discBd (j '' closure c) := hbB ▸ image_mono hLb
  obtain ⟨D, γ, hDt, hγ, hDtb, hin, hDB, hDZ', hnb⟩ := disc_strip hT hB hl hjLb hZc hZends
  have hDr : D ⊆ range j := by
    intro z hz
    rcases (hcov ▸ mem_univ z : z ∈ range j ∪ ⋃ C ∈ cuffs S, cap C) with h | h
    · exact h
    · rcases hDZ' ⟨hz, .inr h⟩ with h1 | h1
      · rw [h1]
        exact mem_range_self _
      · rw [h1]
        exact mem_range_self _
  obtain ⟨hSt, hStb⟩ := isClosedDisc_preimage hj hDt hDr
  have hγD : γ ⊆ D := (hDtb ▸ subset_union_right).trans (discBd_subset D)
  obtain ⟨u₁, v₁, hu₁, hv₁, hγ'⟩ := hγ.pull hj.isEmbedding (hγD.trans hDr)
  obtain rfl : u₁ = u := hj.injective hu₁
  obtain rfl : v₁ = v := hj.injective hv₁
  refine ⟨_, _, hSt, hγ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hStb, hDtb, preimage_union, preimage_image_eq _ hj.injective]
  · have h1 : j ⁻¹' (j '' L ∩ γ) = L ∩ j ⁻¹' γ := by
      rw [preimage_inter, preimage_image_eq _ hj.injective]
    rw [← h1, hin]
    ext x
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, hj.injective.eq_iff]
  · have h1 : j ⁻¹' (D ∩ j '' closure c) = j ⁻¹' D ∩ closure c := by
      rw [preimage_inter, preimage_image_eq _ hj.injective]
    rw [← h1, hDB, preimage_image_eq _ hj.injective]
  · rintro x ⟨hx, hxA⟩
    rcases hDZ' ⟨hx, .inl ⟨x, .inl (.inl hxA), rfl⟩⟩ with h | h
    · exact .inl (hj.injective h)
    · exact .inr (hj.injective h)
  · rintro x ⟨hx, hxU⟩
    have hends : j x ∈ Z → x ∈ L := fun hz => by
      rcases hDZ' ⟨hx, hz⟩ with h | h
      · rw [hj.injective h]
        exact hL.left_mem
      · rw [hj.injective h]
        exact hL.right_mem
    by_cases hxN : x ∈ Γ.N
    · exact hends (.inl ⟨x, .inl (.inr hxN), rfl⟩)
    obtain ⟨d, hd, hxd⟩ := exists_mem_arcComponentsIn (F := Γ.U \ Γ.N) (x := x) ⟨hxU, hxN⟩
    by_cases hdc : d = c
    · subst hdc
      have h1 : j x ∈ D ∩ j '' closure d := ⟨hx, mem_image_of_mem _ (subset_closure hxd)⟩
      rw [hDB] at h1
      exact hj.injective.mem_set_image.mp h1
    · exact hends (.inl ⟨x, .inr (mem_iUnion₂.mpr ⟨d, ⟨hd, hdc⟩, subset_closure hxd⟩), rfl⟩)
  · intro x hx hxu hxv
    have h1 := hnb (j x) (mem_image_of_mem _ hx) (fun h => hxu (hj.injective h)) (fun h => hxv
      (hj.injective h))
    refine Filter.mem_of_superset (hj.continuous.continuousAt h1) fun y hy => ?_
    rcases hy with h | h
    · exact .inl (hj.injective.mem_set_image.mp h)
    · exact .inr h

end GraphMinor.GM17

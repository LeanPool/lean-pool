/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentOuter
import LeanPool.GraphMinor.GM19.Section6Cuff

/-!
# The three shapes of a distance flaw

We apply `exists_outer_fragment` to each of the three shapes of `IsOuterShape`. In the first shape
the cell is one closed disc. In the
second it is a disc and a pasted disc, joined by a line or touching in a point. In the third it is
two discs, joined by a line or
touching in a point.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

variable {S Shat Y : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  [TopologicalSpace Y]
  [T2Space Y] {ψ : Y → S} {K : Drawing S}

omit [T2Space S] in
/-- A pasted disc that meets a closed disc with boundary in `S` lies in that disc. -/
theorem IsCappedSurface.subset_of_meet (hS : IsSurface S) (cap : IsCappedSurface S Shat) {D : Set
  Shat} (hD : IsClosedDisc D)
    (h : discBd D ⊆ range cap.emb) {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hm :
      (cap.cuffDisc Θ ∩ D).Nonempty) :
    closure (cap.cuffDisc Θ) ⊆ D := by
  obtain ⟨x, hx, hxD⟩ := hm
  rcases cap.side hS hD h hΘ with h' | h'
  · exact h'
  · exfalso
    refine disjoint_left.1 h' (subset_closure hx) ⟨hxD, fun hb ↦ ?_⟩
    exact cap.notMem_range hΘ hx (h hb)

omit [T2Space S] [T2Space Shat] in
theorem IsCappedSurface.bd_of_mem (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Θ : Set S}
  (hΘ : Θ ∈ cuffs S) {z : S}
    (hz : cap.emb z ∈ closure (cap.cuffDisc Θ)) : z ∈ bd S :=
  cuff_subset_bd ⟨Θ, hΘ⟩ (cap.mem_of_emb_mem hS hΘ hz)

omit [T2Space S] [T2Space Shat] in
theorem IsCappedSurface.mem_closure_emb (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Θ : Set
  S} (hΘ : Θ ∈ cuffs S) {z : S}
    (hz : z ∈ Θ) : cap.emb z ∈ closure (cap.cuffDisc Θ) := by
  rw [cap.closure_cuffDisc hS hΘ]
  exact Or.inr (mem_image_of_mem _ hz)

omit [T2Space Y] in
/-- The cell is one closed disc `D`. -/
theorem outer_disc (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hY : IsSurface Y)
  (hψ : IsCutMap ψ K.U) {D : Set Shat}
    (hD : IsClosedDisc D) (hr : discBd D ⊆ range cap.emb) (hK : cap.emb '' K.U ⊆ discBd D)
    (hrest : discBd D ⊆ cap.discs ∪ cap.emb '' K.U)
    (hm : ∀ Θ ∈ cuffs S, ¬ closure (cap.cuffDisc Θ) ⊆ D → (closure (cap.cuffDisc Θ) ∩ discBd
      D).Subsingleton)
    {Θ₁ Θ₂ : Set S} (h₁ : Θ₁ ∈ cuffs S) (h₂ : Θ₂ ∈ cuffs S) (hne : Θ₁ ≠ Θ₂) (hZ₁ : closure
      (cap.cuffDisc Θ₁) ⊆ D)
    (hZ₂ : closure (cap.cuffDisc Θ₂) ⊆ D) : IsOuterFragment cap ψ (cap.emb ⁻¹' (discInt D)ᶜ) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hbd : D \ discInt D ⊆ discBd D := by
    rintro x ⟨hx, hn⟩
    by_contra hb
    exact hn ⟨hx, hb⟩
  refine exists_outer_fragment hS cap hY hψ hD.isClosed (hD.isOpen_discInt hman) (discInt_subset D)
    (fun c hc ↦ ?_)
    (hK.trans (Surface.discBd_subset D)) (hbd.trans hrest) (hbd.trans
      (discBd_subset_closure_compl hT hD)) ?_ h₁ h₂ hne hZ₁ hZ₂
  · exact isCell_disc hT (isClosedDisc_image_injOn hD c.continuous.continuousOn hc).1
  · intro Θ hΘ hn x hx y hy
    have key : ∀ {x}, x ∈ closure (cap.cuffDisc Θ) ∩ D → x ∈ closure (cap.cuffDisc Θ) ∩ discBd D
      := by
      rintro x ⟨hxE, hxD⟩
      refine ⟨hxE, ?_⟩
      rcases cap.side hS hD hr hΘ with h | h
      · exact absurd h hn
      · by_contra hb
        exact disjoint_left.1 h hxE ⟨hxD, hb⟩
    exact hm Θ hΘ hn (key hx) (key hy)

omit [T2Space Y] in
/-- The first shape: one closed disc. Its boundary may run through a pasted disc. -/
theorem outer_shape1 (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hY : IsSurface Y)
  (hψ : IsCutMap ψ K.U) {Δ : Set Shat}
    (hΔ : IsClosedDisc Δ) (hf : IsCutFormOf cap K (discBd Δ)) {Θ₁ Θ₂ : Set S} (h₁ : Θ₁ ∈ cuffs S)
      (h₂ : Θ₂ ∈ cuffs S) (hne : Θ₁ ≠ Θ₂)
    (m₁ : (cap.cuffDisc Θ₁ ∩ Δ).Nonempty) (m₂ : (cap.cuffDisc Θ₂ ∩ Δ).Nonempty) :
    IsOuterFragment cap ψ (cap.emb ⁻¹' (discInt Δ)ᶜ) := by
  rcases hf with ⟨hF, -, hsing⟩ | ⟨s, t, Θ, hΘ, hst, hs, ht, hKb, hl, hsub, hrest⟩
  · have hr : discBd Δ ⊆ range cap.emb := hF.le.trans (image_subset_range _ _)
    refine outer_disc hS cap hY hψ hΔ hr hF.ge (hF.le.trans subset_union_right) ?_ h₁ h₂ hne
      (cap.subset_of_meet hS hΔ hr h₁ m₁) (cap.subset_of_meet hS hΔ hr h₂ m₂)
    rintro Θ' hΘ' - x ⟨hxE, hx⟩ y ⟨hyE, hy⟩
    rw [hF] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [hsing ⟨ha, cap.bd_of_mem hS hΘ' hxE⟩ ⟨hb, cap.bd_of_mem hS hΘ' hyE⟩]
  · obtain ⟨-, Δ₂, -, hd₂, -, hK₂, -, hr₂, -, hs₂, -, hE₂, hΔΔ₂, -, hpre⟩ :=
      exists_form_discs hS cap hΔ hΘ hst hs ht hKb hl hsub hrest
    have hres := outer_disc (ψ := ψ) hS cap hY hψ hd₂ hr₂ hK₂ (fun x hx ↦ ?_) ?_ h₁ h₂ hne
      (cap.subset_of_meet hS hd₂ hr₂ h₁ (m₁.mono (inter_subset_inter_right _ hΔΔ₂)))
      (cap.subset_of_meet hS hd₂ hr₂ h₂ (m₂.mono (inter_subset_inter_right _ hΔΔ₂)))
    · rwa [preimage_compl, hpre, ← preimage_compl] at hres
    · rcases hs₂ hx with h | ⟨z, hz, rfl⟩
      · exact Or.inr h
      · exact Or.inl (mem_biUnion hΘ (cap.mem_closure_emb hS hΘ hz))
    · rintro Θ' hΘ' hn x ⟨hxE, hx⟩
      exfalso
      have hne' : Θ' ≠ Θ := fun he ↦ hn (he ▸ hE₂)
      rcases hs₂ hx with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · have hzΘ := cap.mem_of_emb_mem hS hΘ' hxE
        have hzb : z ∈ K.U ∩ bd S := ⟨hz, cuff_subset_bd ⟨Θ', hΘ'⟩ hzΘ⟩
        rw [hKb] at hzb
        rcases hzb with rfl | h'
        · exact hne' (cuffs_eq_of_mem hΘ' hΘ hzΘ hs)
        · exact hne' (cuffs_eq_of_mem hΘ' hΘ hzΘ (mem_singleton_iff.1 h' ▸ ht))
      · exact hne' (cuffs_eq_of_mem hΘ' hΘ (cap.mem_of_emb_mem hS hΘ' hxE) hz)

omit [T2Space Shat] in
omit [T2Space S] in
theorem IsCappedSurface.preimage_compl_discInt (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Θ
  : Set S} (hΘ : Θ ∈ cuffs S)
    (G : Set Shat) : cap.emb ⁻¹' (G ∪ discInt (closure (cap.cuffDisc Θ)))ᶜ = cap.emb ⁻¹' Gᶜ := by
  ext z
  simp only [mem_preimage, mem_compl_iff, mem_union, not_or]
  rw [← cap.cuffDisc_eq_discInt hS hΘ]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ cap.notMem_range hΘ h' (mem_range_self z)⟩⟩

theorem isPreconnected_of_line {T : Type} [TopologicalSpace T] {L : Set T} {a b : T}
  (hl : IsLineWithEnds L a b) : IsPreconnected L := by
  obtain ⟨f, -, -⟩ := hl
  have : L = range fun t ↦ (f t).1 := by
    ext x
    constructor
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, by simp⟩
    · rintro ⟨t, rfl⟩
      exact (f t).2
  rw [this]
  exact isPreconnected_range (continuous_subtype_val.comp f.continuous)

theorem ends_of_line {T : Type} [TopologicalSpace T] {L : Set T} {a b : T}
  (hl : IsLineWithEnds L a b) : a ∈ L ∧ b ∈ L ∧ a ≠ b := by
  obtain ⟨f, h0, h1⟩ := hl
  refine ⟨h0 ▸ (f 0).2, h1 ▸ (f 1).2, fun h ↦ ?_⟩
  have : (0 : unitInterval) = 1 := f.injective (Subtype.ext (h0.trans (h.trans h1.symm)))
  exact zero_ne_one this

omit [T2Space Y] in
/-- The second shape: a path from a cuff to a circuit. The cell is the pasted disc, the path, and
the disc of the circuit. -/
theorem outer_shape2 (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hY : IsSurface Y)
  (hψ : IsCutMap ψ K.U) {Δ : Set Shat}
    {L : Set S} {s u : S} {Θ Θ' : Set S} (hΔ : IsClosedDisc Δ) (hr : discBd Δ ⊆ range cap.emb)
      (hΘ : Θ ∈ cuffs S) (hΘ' : Θ' ∈ cuffs S)
    (hne : Θ ≠ Θ') (hs : s ∈ Θ) (hL : (L = {u} ∧ s = u) ∨ IsLineWithEnds L s u)
      (hK : cap.emb '' K.U = discBd Δ ∪ cap.emb '' L)
    (hLΔ : cap.emb '' L ∩ Δ = {cap.emb u}) (hLb : L ∩ bd S ⊆ {s}) (hbd : discBd Δ ∩ cap.emb '' bd S
      ⊆ {cap.emb u})
    (hdj : Disjoint (cap.cuffDisc Θ) Δ) (hmeet : (cap.cuffDisc Θ' ∩ Δ).Nonempty) :
    IsOuterFragment cap ψ (cap.emb ⁻¹' (discInt Δ)ᶜ) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  set E := closure (cap.cuffDisc Θ) with hEdef
  have hE : IsClosedDisc E := cap.cuffDisc_closedDisc Θ hΘ
  have hbE : discBd E = cap.emb '' Θ := cap.cuffDisc_bd Θ hΘ
  have hnot : ¬ E ⊆ Δ := by
    obtain ⟨x, hx⟩ := hE.nonempty_discInt
    rw [← cap.cuffDisc_eq_discInt hS hΘ] at hx
    exact fun h ↦ disjoint_left.1 hdj hx (h (subset_closure hx))
  have hEi : Disjoint E (discInt Δ) := (cap.side hS hΔ hr hΘ).resolve_left hnot
  have hbdmem : ∀ {Θ₂}, Θ₂ ∈ cuffs S → Disjoint (closure (cap.cuffDisc Θ₂)) (discInt Δ) →
      ∀ {x}, x ∈ closure (cap.cuffDisc Θ₂) → x ∈ Δ → x = cap.emb u := by
    intro Θ₂ h₂ hd x hxE hxD
    have hb : x ∈ discBd Δ := by
      by_contra hb
      exact disjoint_left.1 hd hxE ⟨hxD, hb⟩
    obtain ⟨z, rfl⟩ := hr hb
    exact hbd ⟨hb, mem_image_of_mem _ (cap.bd_of_mem hS h₂ hxE)⟩
  have hEΔ : ∀ {x}, x ∈ E → x ∈ Δ → x = cap.emb u := fun h h' ↦ hbdmem hΘ hEi h h'
  have hLs : ∀ {Θ₂}, Θ₂ ∈ cuffs S → ∀ {z}, z ∈ L → cap.emb z ∈ closure (cap.cuffDisc Θ₂) → z = s
    := by
    intro Θ₂ h₂ z hz hzE
    exact hLb ⟨hz, cap.bd_of_mem hS h₂ hzE⟩
  have huL : cap.emb u ∈ cap.emb '' L ∩ Δ := by rw [hLΔ]; rfl
  have hE'Δ : closure (cap.cuffDisc Θ') ⊆ Δ := cap.subset_of_meet hS hΔ hr hΘ' hmeet
  have hmO : ∀ Θ₂ ∈ cuffs S, Θ₂ ≠ Θ → ¬ closure (cap.cuffDisc Θ₂) ⊆ Δ → ∀ {x}, x ∈ closure
    (cap.cuffDisc Θ₂) →
      (x ∈ Δ ∨ x ∈ cap.emb '' L) → x = cap.emb u := by
    rintro Θ₂ h₂ hn₂ hn x hx (h | ⟨z, hz, rfl⟩)
    · exact hbdmem h₂ ((cap.side hS hΔ hr h₂).resolve_left hn) hx h
    · have hzs := hLs h₂ hz hx
      subst hzs
      exact absurd (cuffs_eq_of_mem h₂ hΘ (cap.mem_of_emb_mem hS h₂ hx) hs) hn₂
  have hEd : ∀ Θ₂ ∈ cuffs S, Θ₂ ≠ Θ → Disjoint (closure (cap.cuffDisc Θ₂)) E
    := fun Θ₂ h₂ hn ↦ cap.cuffDisc_disjoint Θ₂ h₂ Θ hΘ hn
  have hrestK : ∀ {x}, x ∈ discBd Δ ∨ x ∈ cap.emb '' L ∨ x ∈ E → x ∈ cap.discs ∪ cap.emb '' K.U
    := by
    rintro x (h | h | h)
    · exact Or.inr (hK ▸ Or.inl h)
    · exact Or.inr (hK ▸ Or.inr h)
    · exact Or.inl (mem_biUnion hΘ h)
  rcases hL with ⟨rfl, rfl⟩ | hl
  · have hsE : cap.emb s ∈ E := cap.mem_closure_emb hS hΘ hs
    have hsimp : cap.emb '' {s} = {cap.emb s} := image_singleton
    have ht : Δ ∩ E = {cap.emb s} := by
      ext x
      constructor
      · rintro ⟨h, h'⟩
        exact hEΔ h' h
      · rintro rfl
        exact ⟨huL.2, hsE⟩
    have hres := exists_outer_fragment (ψ := ψ) (Z := Δ ∪ E) (G := discInt Δ ∪ discInt E) hS cap hY
      hψ
      (hΔ.isClosed.union hE.isClosed) ((hΔ.isOpen_discInt hman).union (hE.isOpen_discInt hman))
      (union_subset_union (discInt_subset Δ) (discInt_subset E)) (fun c hc ↦ isCell_touch_image hT
        hΔ hE ht c hc)
      (by
        rw [hK]
        rintro x (h | h)
        · exact Or.inl (Surface.discBd_subset _ h)
        · rw [hsimp] at h
          exact Or.inl (mem_singleton_iff.1 h ▸ huL.2))
      (by
        rintro x ⟨h | h, hn⟩
        · exact hrestK (Or.inl (by
            by_contra hb
            exact hn (Or.inl ⟨h, hb⟩)))
        · exact hrestK (Or.inr (Or.inr h)))
      (frontier_touch hT hΔ hE ht)
      (by
        intro Θ₂ h₂ hn x hx y hy
        have hn₂ : Θ₂ ≠ Θ := fun he ↦ hn (he ▸ subset_union_right)
        have hn₃ : ¬ closure (cap.cuffDisc Θ₂) ⊆ Δ := fun h ↦ hn (h.trans subset_union_left)
        have key : ∀ {x}, x ∈ closure (cap.cuffDisc Θ₂) ∩ (Δ ∪ E) → x = cap.emb s := by
          rintro x ⟨hxE, h | h⟩
          · exact hmO Θ₂ h₂ hn₂ hn₃ hxE (Or.inl h)
          · exact absurd h (disjoint_left.1 (hEd Θ₂ h₂ hn₂) hxE)
        rw [key hx, key hy])
      hΘ hΘ' hne subset_union_right (hE'Δ.trans subset_union_left)
    rwa [cap.preimage_compl_discInt hS hΘ] at hres
  · obtain ⟨hsL, huL', hsu⟩ := ends_of_line hl
    have hline := hl.map_of_embedding cap.isEmbedding
    have hLE : cap.emb '' L ∩ E = {cap.emb s} := by
      ext x
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, h⟩
        rw [hLs hΘ hz h]
        rfl
      · rintro rfl
        exact ⟨mem_image_of_mem _ hsL, cap.mem_closure_emb hS hΘ hs⟩
    have hdE : Disjoint E Δ := disjoint_left.2 fun x hx hxΔ ↦ by
      have hxu := hEΔ hx hxΔ
      have : cap.emb u ∈ cap.emb '' L ∩ E := ⟨huL.1, hxu ▸ hx⟩
      rw [hLE] at this
      exact hsu (cap.isEmbedding.injective this).symm
    have hsE : cap.emb s ∈ discBd E := by
      rw [hbE]
      exact mem_image_of_mem _ hs
    have huB : cap.emb u ∈ discBd Δ := mem_discBd_of_cross hT hΔ (isPreconnected_of_line hline)
      (mem_image_of_mem _ hsL)
      (disjoint_left.1 hdE (Surface.discBd_subset _ hsE)) huL.1 hLΔ
    have hres := exists_outer_fragment (ψ := ψ) (Z := E ∪ cap.emb '' L ∪ Δ) (G
      := discInt E ∪ discInt Δ) hS cap hY hψ
      ((hE.isClosed.union (isClosed_of_cuffLine hline)).union hΔ.isClosed)
        ((hE.isOpen_discInt hman).union (hΔ.isOpen_discInt hman))
      (union_subset_union (discInt_subset E |>.trans subset_union_left) (discInt_subset Δ))
      (fun c hc ↦ isCell_bridge_image hT hE hΔ hdE hsE huB hline hLE hLΔ c hc)
      (by
        rw [hK]
        rintro x (h | h)
        · exact Or.inr (Surface.discBd_subset _ h)
        · exact Or.inl (Or.inr h))
      (by
        rintro x ⟨(h | h) | h, hn⟩
        · exact hrestK (Or.inr (Or.inr h))
        · exact hrestK (Or.inr (Or.inl h))
        · exact hrestK (Or.inl (by
            by_contra hb
            exact hn (Or.inr ⟨h, hb⟩))))
      (frontier_bridge hT hE hΔ hdE hsE huB hline hLE hLΔ)
      (by
        intro Θ₂ h₂ hn x hx y hy
        have hn₂ : Θ₂ ≠ Θ := fun he ↦ hn (he ▸ subset_union_left.trans subset_union_left)
        have hn₃ : ¬ closure (cap.cuffDisc Θ₂) ⊆ Δ := fun h ↦ hn (h.trans subset_union_right)
        have key : ∀ {x}, x ∈ closure (cap.cuffDisc Θ₂) ∩ (E ∪ cap.emb '' L ∪ Δ) → x = cap.emb u
          := by
          rintro x ⟨hxE, (h | h) | h⟩
          · exact absurd h (disjoint_left.1 (hEd Θ₂ h₂ hn₂) hxE)
          · exact hmO Θ₂ h₂ hn₂ hn₃ hxE (Or.inr h)
          · exact hmO Θ₂ h₂ hn₂ hn₃ hxE (Or.inl h)
        rw [key hx, key hy])
      hΘ hΘ' hne (subset_union_left.trans subset_union_left) (hE'Δ.trans subset_union_right)
    rwa [union_comm, cap.preimage_compl_discInt hS hΘ] at hres

omit [T2Space Y] in
/-- The third shape: two circuits with a path between them. The cell is the two discs and the path.
-/
theorem outer_shape3 (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hY : IsSurface Y)
  (hψ : IsCutMap ψ K.U) {Δ₁ Δ₂ : Set Shat}
    {L : Set S} {a b : S} {Θ₁ Θ₂ : Set S} (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂)
      (hr₁ : discBd Δ₁ ⊆ range cap.emb)
    (hr₂ : discBd Δ₂ ⊆ range cap.emb) (hL : (L = {a} ∧ a = b) ∨ IsLineWithEnds L a b)
    (hK : cap.emb '' K.U = discBd Δ₁ ∪ discBd Δ₂ ∪ cap.emb '' L) (hL₁ : cap.emb '' L ∩ Δ₁
      = {cap.emb a})
    (hL₂ : cap.emb '' L ∩ Δ₂ = {cap.emb b}) (hdb : Disjoint (cap.emb '' bd S)
      (discBd Δ₁ ∪ cap.emb '' L))
    (hsing : (discBd Δ₂ ∩ cap.emb '' bd S).Subsingleton) (hmeet : Δ₁ ∩ Δ₂ ⊆ {cap.emb a})
      (h₁ : Θ₁ ∈ cuffs S) (h₂ : Θ₂ ∈ cuffs S)
    (hne : Θ₁ ≠ Θ₂) (m₁ : (cap.cuffDisc Θ₁ ∩ Δ₁).Nonempty) (m₂ : (cap.cuffDisc Θ₂ ∩ Δ₂).Nonempty) :
    IsOuterFragment cap ψ (cap.emb ⁻¹' (discInt Δ₁ ∪ discInt Δ₂)ᶜ) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hE₁ := cap.subset_of_meet hS hΔ₁ hr₁ h₁ m₁
  have hE₂ := cap.subset_of_meet hS hΔ₂ hr₂ h₂ m₂
  have hG : IsOpen (discInt Δ₁ ∪ discInt Δ₂) := (hΔ₁.isOpen_discInt hman).union
    (hΔ₂.isOpen_discInt hman)
  have haL : cap.emb a ∈ cap.emb '' L ∩ Δ₁ := by rw [hL₁]; rfl
  have hbL : cap.emb b ∈ cap.emb '' L ∩ Δ₂ := by rw [hL₂]; rfl
  have hbound : ∀ {D}, IsClosedDisc D → (D = Δ₁ ∨ D = Δ₂) → ∀ {Θ}, Θ ∈ cuffs S → ¬ closure
    (cap.cuffDisc Θ) ⊆ D → ∀ {x},
      x ∈ closure (cap.cuffDisc Θ) → x ∈ D → x ∈ discBd D := by
    rintro D hD hc Θ hΘ hn x hx hxD
    have hr : discBd D ⊆ range cap.emb := by
      rcases hc with rfl | rfl
      · exact hr₁
      · exact hr₂
    by_contra hb
    exact disjoint_left.1 ((cap.side hS hD hr hΘ).resolve_left hn) hx ⟨hxD, hb⟩
  have hEb : ∀ {Θ}, Θ ∈ cuffs S → ∀ {z}, cap.emb z ∈ closure (cap.cuffDisc Θ)
    → cap.emb z ∈ cap.emb '' bd S := fun hΘ _ hz ↦
    mem_image_of_mem _ (cap.bd_of_mem hS hΘ hz)
  have hrange : ∀ {D}, (D = Δ₁ ∨ D = Δ₂) → discBd D ⊆ range cap.emb := by
    rintro D (rfl | rfl)
    · exact hr₁
    · exact hr₂
  have hm₃ : ∀ {Θ}, Θ ∈ cuffs S → ¬ closure (cap.cuffDisc Θ) ⊆ Δ₁ → ¬ closure (cap.cuffDisc Θ) ⊆ Δ₂
    → ∀ {x},
      x ∈ closure (cap.cuffDisc Θ) → x ∈ Δ₁ ∪ cap.emb '' L ∪ Δ₂ → x ∈ discBd Δ₂ ∩ cap.emb '' bd S
        := by
    rintro Θ hΘ hn₁ hn₂ x hx ((h | h) | h)
    · exfalso
      have hb := hbound hΔ₁ (Or.inl rfl) hΘ hn₁ hx h
      obtain ⟨z, rfl⟩ := hr₁ hb
      exact disjoint_left.1 hdb (hEb hΘ hx) (Or.inl hb)
    · exfalso
      obtain ⟨z, hz, rfl⟩ := h
      exact disjoint_left.1 hdb (hEb hΘ hx) (Or.inr (mem_image_of_mem _ hz))
    · have hb := hbound hΔ₂ (Or.inr rfl) hΘ hn₂ hx h
      obtain ⟨z, rfl⟩ := hr₂ hb
      exact ⟨hb, hEb hΘ hx⟩
  rcases hL with ⟨rfl, rfl⟩ | hl
  · have hsimp : cap.emb '' {a} = {cap.emb a} := image_singleton
    have ht : Δ₁ ∩ Δ₂ = {cap.emb a} := by
      refine Subset.antisymm hmeet ?_
      rintro _ rfl
      exact ⟨haL.2, hbL.2⟩
    exact exists_outer_fragment (ψ := ψ) (Z := Δ₁ ∪ Δ₂) hS cap hY hψ (hΔ₁.isClosed.union
      hΔ₂.isClosed) hG
      (union_subset_union (discInt_subset Δ₁) (discInt_subset Δ₂)) (fun c hc ↦ isCell_touch_image
        hT hΔ₁ hΔ₂ ht c hc)
      (by
        rw [hK]
        rintro x ((h | h) | h)
        · exact Or.inl (Surface.discBd_subset _ h)
        · exact Or.inr (Surface.discBd_subset _ h)
        · rw [hsimp] at h
          exact Or.inl (mem_singleton_iff.1 h ▸ haL.2))
      (by
        rintro x ⟨h | h, hn⟩
        · refine Or.inr (hK ▸ Or.inl (Or.inl ?_))
          by_contra hb
          exact hn (Or.inl ⟨h, hb⟩)
        · refine Or.inr (hK ▸ Or.inl (Or.inr ?_))
          by_contra hb
          exact hn (Or.inr ⟨h, hb⟩))
      (frontier_touch hT hΔ₁ hΔ₂ ht)
      (by
        intro Θ hΘ hn x hx y hy
        have hn₁ : ¬ closure (cap.cuffDisc Θ) ⊆ Δ₁ := fun h ↦ hn (h.trans subset_union_left)
        have hn₂ : ¬ closure (cap.cuffDisc Θ) ⊆ Δ₂ := fun h ↦ hn (h.trans subset_union_right)
        have key : ∀ {x}, x ∈ closure (cap.cuffDisc Θ) ∩ (Δ₁ ∪ Δ₂) → x ∈ discBd Δ₂ ∩ cap.emb '' bd
          S := by
          rintro x ⟨hxE, h | h⟩
          · exact hm₃ hΘ hn₁ hn₂ hxE (Or.inl (Or.inl h))
          · exact hm₃ hΘ hn₁ hn₂ hxE (Or.inr h)
        exact hsing (key hx) (key hy))
      h₁ h₂ hne (hE₁.trans subset_union_left) (hE₂.trans subset_union_right)
  · obtain ⟨haL', hbL', hab⟩ := ends_of_line hl
    have hline := hl.map_of_embedding cap.isEmbedding
    have hb₁ : cap.emb b ∉ Δ₁ := fun h ↦ by
      have : cap.emb b ∈ cap.emb '' L ∩ Δ₁ := ⟨hbL.1, h⟩
      rw [hL₁] at this
      exact hab (cap.isEmbedding.injective this).symm
    have ha₂ : cap.emb a ∉ Δ₂ := fun h ↦ by
      have : cap.emb a ∈ cap.emb '' L ∩ Δ₂ := ⟨haL.1, h⟩
      rw [hL₂] at this
      exact hab (cap.isEmbedding.injective this)
    have hd : Disjoint Δ₁ Δ₂ := disjoint_left.2 fun x hx hx' ↦ by
      have hxa := hmeet ⟨hx, hx'⟩
      exact ha₂ (mem_singleton_iff.1 hxa ▸ hx')
    have ha : cap.emb a ∈ discBd Δ₁ := mem_discBd_of_cross hT hΔ₁ (isPreconnected_of_line hline)
      hbL.1 hb₁ haL.1 hL₁
    have hb : cap.emb b ∈ discBd Δ₂ := mem_discBd_of_cross hT hΔ₂ (isPreconnected_of_line hline)
      haL.1 ha₂ hbL.1 hL₂
    exact exists_outer_fragment (ψ := ψ) (Z := Δ₁ ∪ cap.emb '' L ∪ Δ₂) hS cap hY hψ
      ((hΔ₁.isClosed.union (isClosed_of_cuffLine hline)).union hΔ₂.isClosed) hG
      (union_subset_union ((discInt_subset Δ₁).trans subset_union_left) (discInt_subset Δ₂))
      (fun c hc ↦ isCell_bridge_image hT hΔ₁ hΔ₂ hd ha hb hline hL₁ hL₂ c hc)
      (by
        rw [hK]
        rintro x ((h | h) | h)
        · exact Or.inl (Or.inl (Surface.discBd_subset _ h))
        · exact Or.inr (Surface.discBd_subset _ h)
        · exact Or.inl (Or.inr h))
      (by
        rintro x ⟨(h | h) | h, hn⟩
        · refine Or.inr (hK ▸ Or.inl (Or.inl ?_))
          by_contra hb'
          exact hn (Or.inl ⟨h, hb'⟩)
        · exact Or.inr (hK ▸ Or.inr h)
        · refine Or.inr (hK ▸ Or.inl (Or.inr ?_))
          by_contra hb'
          exact hn (Or.inr ⟨h, hb'⟩))
      (frontier_bridge hT hΔ₁ hΔ₂ hd ha hb hline hL₁ hL₂)
      (by
        intro Θ hΘ hn x hx y hy
        have hn₁ : ¬ closure (cap.cuffDisc Θ) ⊆ Δ₁ := fun h ↦ hn (h.trans
          (subset_union_left.trans subset_union_left))
        have hn₂ : ¬ closure (cap.cuffDisc Θ) ⊆ Δ₂ := fun h ↦ hn (h.trans subset_union_right)
        exact hsing (hm₃ hΘ hn₁ hn₂ hx.1 hx.2) (hm₃ hΘ hn₁ hn₂ hy.1 hy.2))
      h₁ h₂ hne (hE₁.trans (subset_union_left.trans subset_union_left))
        (hE₂.trans subset_union_right)

omit [T2Space Y] in
/-- The fragment of the proof of (10.4), for each shape of a distance flaw. -/
theorem outer_shape (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hY : IsSurface Y)
  (hψ : IsCutMap ψ K.U) {𝓓 : Set (Set Shat)}
    (h : IsOuterShape cap K 𝓓) : IsOuterFragment cap ψ (⋂ Δ ∈ 𝓓, cap.emb ⁻¹' closure Δᶜ) := by
  have hT := cap.isClosedSurface
  rcases h with ⟨Δ, rfl, hΔ, hf, Θ₁, h₁, Θ₂, h₂, hne, m₁, m₂⟩ | ⟨Δ, L, s, u, Θ, Θ', rfl, hΔ, hr,
    hΘ, hΘ', hne, hs, hL, hK, hLΔ, hLb, hbd,
    hdj, hmeet⟩ | ⟨Δ₁, Δ₂, L, a, b, Θ₁, Θ₂, rfl, -, hΔ₁, hΔ₂, hr₁, hr₂, hL, hK, hL₁, hL₂, hdb,
      hsing, hmeet, h₁, h₂, hne, m₁, m₂⟩
  · simp only [mem_singleton_iff, iInter_iInter_eq_left]
    rw [closure_compl_disc hT hΔ]
    exact outer_shape1 hS cap hY hψ hΔ hf h₁ h₂ hne m₁ m₂
  · simp only [mem_singleton_iff, iInter_iInter_eq_left]
    rw [closure_compl_disc hT hΔ]
    exact outer_shape2 hS cap hY hψ hΔ hr hΘ hΘ' hne hs hL hK hLΔ hLb hbd hdj hmeet
  · have := outer_shape3 (ψ := ψ) hS cap hY hψ hΔ₁ hΔ₂ hr₁ hr₂ hL hK hL₁ hL₂ hdb
      hsing hmeet h₁ h₂ hne m₁ m₂
    have he : (⋂ Δ ∈ ({Δ₁, Δ₂} : Set (Set Shat)), cap.emb ⁻¹' closure Δᶜ) = cap.emb ⁻¹'
      (discInt Δ₁ ∪ discInt Δ₂)ᶜ := by
      simp only [mem_insert_iff, mem_singleton_iff, iInter_iInter_eq_or_left, iInter_iInter_eq_left]
      rw [closure_compl_disc hT hΔ₁, closure_compl_disc hT hΔ₂, compl_union, preimage_inter]
    rwa [he]

end GraphMinor.GM19

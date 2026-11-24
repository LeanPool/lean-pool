/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section8
public import LeanPool.GraphMinor.Surface.PasteModel
public import LeanPool.GraphMinor.Surface.PasteDisc

/-!
# Pasting a disc on a cuff of a painted surface

We prove `PasteCuffPaintingStatement`, the surface fact behind (5.1) of Graph Minors XVII (page
171). A painting moves along a closed
embedding of surfaces (`Painting.pushClosed`), as long as the boundary of the new surface is in the
image of `U(Γ)`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S'] {ι : S → S'}

theorem arcComps_image (hι : IsEmbedding ι) (W : Set S) :
    arcComponentsIn (ι '' W) = (fun c => ι '' c) '' arcComponentsIn W := by
  have himg : ∀ c ∈ arcComponentsIn W, ι '' c ∈ arcComponentsIn (ι '' W) := fun c hc => by
    refine ⟨hc.1.image _, image_mono hc.2.1, hc.2.2.1.image hι.continuous, fun D hDF hD hsub => ?_⟩
    have hDr : ι '' (ι ⁻¹' D) = D := image_preimage_eq_of_subset (hDF.trans
      (image_subset_range _ _))
    have hpc : IsPathConnected (ι ⁻¹' D) := by
      rw [hι.isInducing.isPathConnected_iff, hDr]
      exact hD
    have hsub' : ι ⁻¹' D ⊆ W := fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hDF hx
      exact hι.injective hyx ▸ hy
    have := hc.2.2.2 (ι ⁻¹' D) hsub' hpc fun x hx => hsub (mem_image_of_mem _ hx)
    rw [← hDr, this]
  ext d
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := hd.1
    obtain ⟨y, hy, rfl⟩ := hd.2.1 hx
    obtain ⟨c, hc, hyc⟩ := exists_mem_arcComponentsIn hy
    refine ⟨c, hc, ?_⟩
    exact arcComponentsIn_eq_of_mem (himg c hc) hd (mem_image_of_mem _ hyc) hx
  · rintro ⟨c, hc, rfl⟩
    exact himg c hc

theorem discBd_image (hι : IsEmbedding ι) (Δ : Set S) : discBd (ι '' Δ) = ι '' discBd Δ := by
  have h := image_bd_homeomorph (hι.homeomorphImage Δ)
  rw [discBd, discBd, ← h, image_image, image_image]
  rfl

theorem image_emb_disc (hι : IsEmbedding ι) {Δ : Set S} (h : IsClosedDisc Δ) : IsClosedDisc
  (ι '' Δ) := by
  obtain ⟨φ⟩ := h
  exact ⟨φ.trans (hι.homeomorphImage Δ)⟩

theorem tilde_image_emb (hι : IsClosedEmbedding ι) (c : Set S) : tilde (ι '' c) = ι '' tilde c := by
  rw [tilde, tilde, hι.closure_image_eq, image_sdiff hι.injective]

theorem isLine_image (hι : IsEmbedding ι) {L : Set S} (h : IsLine L) : IsLine (ι '' L) := by
  obtain ⟨f⟩ := h
  exact ⟨f.trans (hι.homeomorphImage L)⟩

theorem lineEnds_image (hι : IsEmbedding ι) {L : Set S} : lineEnds (ι '' L) = ι '' lineEnds L := by
  ext x
  constructor
  · rintro ⟨y, f, h1, h2⟩
    let f' := f.trans (hι.homeomorphImage L).symm
    have hf : ∀ t, ι (f' t).1 = (f t).1 := fun t => by
      have h3 := (hι.homeomorphImage L).apply_symm_apply (f t)
      exact congrArg Subtype.val h3
    exact ⟨(f' 0).1, ⟨(f' 1).1, f', rfl, rfl⟩, (hf 0).trans h1⟩
  · rintro ⟨_, ⟨y, f, rfl, rfl⟩, rfl⟩
    exact ⟨ι (f 1).1, f.trans (hι.homeomorphImage L), rfl, rfl⟩

/-- A painting moves along a closed embedding, if the boundary of the new surface lies in the image
of `U(Γ)` and the border cells of the
image come from border cells with the same boundary. -/
noncomputable def Painting.pushClosed (Γ : Painting S) (hι : IsClosedEmbedding ι)
  (hb : bd S' ⊆ ι '' Γ.U)
    (hbord : ∀ c ∈ Γ.C, (ι '' c ∩ bd S').Nonempty → (c ∩ bd S).Nonempty ∧ closure (ι '' c) ∩ bd S'
      = ι '' (closure c ∩ bd S)) : Painting S' where
  U := ι '' Γ.U
  N := ι '' Γ.N
  isClosed_U := hι.isClosedMap _ Γ.isClosed_U
  N_subset := image_mono Γ.N_subset
  finite_N := Γ.finite_N.image _
  finite_cells := by
    rw [← image_sdiff hι.injective, arcComps_image hι.isEmbedding]
    exact Γ.finite_cells.image _
  cell_disc := by
    rw [← image_sdiff hι.injective, arcComps_image hι.isEmbedding]
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := Γ.cell_disc c hc
    simp only
    rw [tilde_image_emb hι, hι.closure_image_eq, discBd_image hι.isEmbedding,
      ncard_image_of_injective _ hι.injective]
    exact ⟨image_emb_disc hι.isEmbedding h1, image_mono h2, h3.image _, h4⟩
  bd_subset := hb
  border_cell := by
    rw [← image_sdiff hι.injective, arcComps_image hι.isEmbedding]
    rintro _ ⟨c, hc, rfl⟩ h
    obtain ⟨h0, h5⟩ := hbord c hc h
    obtain ⟨h1, h2, h3, h4⟩ := Γ.border_cell c hc h0
    simp only
    rw [tilde_image_emb hι, h5, ncard_image_of_injective _ hι.injective,
      lineEnds_image hι.isEmbedding, h4]
    exact ⟨h1, h2.image _, isLine_image hι.isEmbedding h3, rfl⟩

theorem Painting.pushClosed_C (Γ : Painting S) (hι : IsClosedEmbedding ι) (hb) (hbord) :
    (Γ.pushClosed hι hb hbord).C = (fun c => ι '' c) '' Γ.C := by
  change arcComponentsIn (ι '' Γ.U \ ι '' Γ.N) = _
  rw [← image_sdiff hι.injective, arcComps_image hι.isEmbedding]
  rfl

theorem cuffs_disjoint_eq {C C' : Set S} (h : C ∈ cuffs S) (h' : C' ∈ cuffs S) {x : S} (hx : x ∈ C)
  (hx' : x ∈ C') : C = C' := by
  by_contra hne
  exact disjoint_left.mp (cuffs_disjoint h h' hne) hx hx'

/-- (5.1) of Graph Minors XVII, the surface part. -/
theorem pasteCuffPainting : PasteCuffPaintingStatement := by
  unfold PasteCuffPaintingStatement
  intro S _ hcS ht2 hconn hS Γ Θ hΘ
  obtain ⟨S', tS', ι, Δ, hS', hι, hΔ, hcov, hmeet, hΔb, hbdS⟩ := paste_disc.{0} S Θ hS hΘ
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{0} S hS hconn
  obtain ⟨hc0, ⟨e'⟩⟩ := paste_model hS hΘ hS' hι hΔ hcov hmeet hΔb e
  have hcS' : CompactSpace S' := hS'.1
  have ht2' : T2Space S' := hS'.2.1
  have hconn' : ConnectedSpace S' := by
    have := (isSurface_model a b (c - 1)).2
    exact e'.symm.surjective.connectedSpace e'.symm.continuous
  have hbsub : bd S ⊆ Γ.U := Γ.bd_subset
  have hcuffΘ : Θ ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have hb : bd S' ⊆ ι '' Γ.U := by
    rw [hbdS]
    exact image_mono (sdiff_subset.trans hbsub)
  have hbord : ∀ c ∈ Γ.C, (ι '' c ∩ bd S').Nonempty → (c ∩ bd S).Nonempty ∧ closure
    (ι '' c) ∩ bd S' = ι '' (closure c ∩ bd S) := by
    rintro c hc ⟨_, ⟨x, hx, rfl⟩, hxb⟩
    rw [hbdS] at hxb
    obtain ⟨y, ⟨hy, hyΘ⟩, he⟩ := hxb
    obtain rfl := hι.injective he
    refine ⟨⟨y, hx, hy⟩, ?_⟩
    have hΘ₂ : connectedComponentIn (bd S) y ∈ cuffs S := ⟨y, hy, rfl⟩
    have hne : connectedComponentIn (bd S) y ≠ Θ := fun h => hyΘ (h ▸ mem_connectedComponentIn hy)
    have h1 := (Γ.border_cell_subset_cuff hc hΘ₂ ⟨y, hx, mem_connectedComponentIn hy⟩).1
    have h2 := cuffs_disjoint hΘ₂ hΘ hne
    rw [hι.closure_image_eq, hbdS, ← image_inter hι.injective]
    congr 1
    ext z
    constructor
    · rintro ⟨h3, h4, -⟩
      exact ⟨h3, h4⟩
    · intro h3
      exact ⟨h3.1, h3.2, disjoint_left.mp h2 (h1 h3)⟩
  have hcomp : ∀ y ∈ bd S \ Θ, connectedComponentIn (bd S') (ι y) = ι '' connectedComponentIn
    (bd S) y := by
    rintro y ⟨hy, hyΘ⟩
    have hΘ₂ : connectedComponentIn (bd S) y ∈ cuffs S := ⟨y, hy, rfl⟩
    have hne : connectedComponentIn (bd S) y ≠ Θ := fun h => hyΘ (h ▸ mem_connectedComponentIn hy)
    have h2 := cuffs_disjoint hΘ₂ hΘ hne
    have hyb : ι y ∈ bd S' := hbdS ▸ ⟨y, ⟨hy, hyΘ⟩, rfl⟩
    apply subset_antisymm
    · have hQ := connectedComponentIn_subset (bd S') (ι y)
      have hQr : connectedComponentIn (bd S') (ι y) ⊆ range ι := by
        rw [hbdS] at hQ ⊢
        exact hQ.trans (image_subset_range _ _)
      have h3 : ι '' (ι ⁻¹' connectedComponentIn (bd S') (ι y)) = connectedComponentIn (bd S')
        (ι y) := image_preimage_eq_of_subset hQr
      have h4 : IsPreconnected (ι ⁻¹' connectedComponentIn (bd S') (ι y)) := by
        rw [← hι.isEmbedding.isInducing.isPreconnected_image, h3]
        exact isPreconnected_connectedComponentIn
      have h5 : ι ⁻¹' connectedComponentIn (bd S') (ι y) ⊆ bd S := fun z hz => by
        have h6 := hQ hz
        rw [hbdS] at h6
        obtain ⟨w, hw, he⟩ := h6
        exact hι.injective he ▸ hw.1
      have h7 := h4.subset_connectedComponentIn (mem_connectedComponentIn hyb) h5
      rw [← h3]
      exact image_mono h7
    · refine IsPreconnected.subset_connectedComponentIn (isPreconnected_connectedComponentIn.image
      _ hι.continuous.continuousOn)
        ⟨y, mem_connectedComponentIn hy, rfl⟩ ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [hbdS]
      exact ⟨z, ⟨connectedComponentIn_subset _ _ hz, fun h => disjoint_left.mp h2 hz h⟩, rfl⟩
  have hcuffs : cuffs S' = (fun Θ' => ι '' Θ') '' (cuffs S \ {Θ}) := by
    ext P
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := hx
      rw [hbdS] at hx'
      obtain ⟨y, hy, rfl⟩ := hx'
      refine ⟨connectedComponentIn (bd S) y, ⟨⟨y, hy.1, rfl⟩, fun h => hy.2 ?_⟩, (hcomp y hy).symm⟩
      have h1 : connectedComponentIn (bd S) y = Θ := h
      exact h1 ▸ mem_connectedComponentIn hy.1
    · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hne⟩, rfl⟩
      have hyΘ : y ∉ Θ := fun h => hne (cuffs_disjoint_eq hΘ ⟨y, hy, rfl⟩ h
        (mem_connectedComponentIn hy)).symm
      exact ⟨ι y, hbdS ▸ ⟨y, ⟨hy, hyΘ⟩, rfl⟩, hcomp y ⟨hy, hyΘ⟩⟩
  refine ⟨S', tS', hcS', ht2', hconn', hS', ⟨a, b, c - 1, a, b, c, ⟨e'⟩, ⟨e⟩, le_rfl, le_rfl,
    by omega⟩, ι, Γ.pushClosed hι hb hbord, hι.injective, rfl,
    Γ.pushClosed_C hι hb hbord, hbdS, hcuffs, fun c _ => tilde_image_emb hι c, ?_⟩
  rintro Θ' hΘ' hne n₁ h₁ n₂ h₂ n₃ h₃ n₄ h₄ ⟨f, t₁, t₂, t₃, t₄, h12, h23, h34, h41, e1, e2, e3, e4⟩
  let f' := f.trans (hι.isEmbedding.homeomorphImage Θ').symm
  have hf : ∀ t, ι (GM19.cuffPoint f' t) = GM19.cuffPoint f t := fun t => by
    have h3 := (hι.isEmbedding.homeomorphImage Θ').apply_symm_apply (f (Circle.exp t))
    exact congrArg Subtype.val h3
  exact ⟨f', t₁, t₂, t₃, t₄, h12, h23, h34, h41, hι.injective ((hf _).trans e1),
    hι.injective ((hf _).trans e2),
    hι.injective ((hf _).trans e3), hι.injective ((hf _).trans e4)⟩

end GraphMinor.GM17

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM12.Section3HomeoWalks
public import LeanPool.GraphMinor.GM11.Walks
public import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# Spans under a homeomorphism

A homeomorphism `ψ` from a surface `S` to a surface `Z` carries a `Σ`-span in `S` to a `Σ`-span of
the same order in `Z` (`IsSigmaSpan.transport`). The surface tower of `Section4.lean` has one
surface for each homeomorphism class, and this is how a span in any surface reaches the tower.

We map drawings with `mapDrawingHomeo`, and hypergraphs on points and sets of points with `mapH`.
Then we go through the parts of a span in turn: separations, tangles, 2-cell drawings, respectful
tangles, rigid drawings and the control of `T` by `T*`.
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology
open Hypergraph
open GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12
  GraphMinor.GM14 GraphMinor.GM15

universe u v w

variable {S Z : Type w} [TopologicalSpace S] [TopologicalSpace Z]

/-- The image of a hypergraph on points and sets of points under a homeomorphism. -/
def mapH (ψ : S ≃ₜ Z) (A : Hypergraph S (Set S)) : Hypergraph Z (Set Z) where
  vertexSet := ψ '' A.vertexSet
  edgeSet := image ψ '' A.edgeSet
  Inc e v := A.Inc (ψ.symm '' e) (ψ.symm v)
  vertex_mem_of_inc _ v h := ⟨ψ.symm v, A.vertex_mem_of_inc h, by simp⟩
  edge_mem_of_inc e _ h := ⟨ψ.symm '' e, A.edge_mem_of_inc h, by simp [image_image]⟩
  vertexSet_finite := A.vertexSet_finite.image _
  edgeSet_finite := A.edgeSet_finite.image _

theorem symm_image_image (ψ : S ≃ₜ Z) (e : Set S) : ψ.symm '' (ψ '' e) = e := by
  simp [image_image]

theorem image_symm_image (ψ : S ≃ₜ Z) (e : Set Z) : ψ '' (ψ.symm '' e) = e := by
  simp [image_image]

theorem mapH_symm (ψ : S ≃ₜ Z) (A : Hypergraph S (Set S)) : mapH ψ.symm (mapH ψ A) = A := by
  apply Hypergraph.ext
  · exact symm_image_image ψ _
  · change image ψ.symm '' (image ψ '' A.edgeSet) = A.edgeSet
    rw [image_image]
    simp [symm_image_image]
  · funext e v
    change A.Inc (ψ.symm '' (ψ '' e)) (ψ.symm (ψ v)) = A.Inc e v
    rw [symm_image_image, ψ.symm_apply_apply]

theorem mapH_symm' (ψ : S ≃ₜ Z) (A : Hypergraph Z (Set Z)) : mapH ψ (mapH ψ.symm A) = A :=
  mapH_symm ψ.symm A

theorem mapH_union (ψ : S ≃ₜ Z) (A B : Hypergraph S (Set S)) : mapH ψ (A ∪ B) = mapH ψ A ∪ mapH ψ B
  := by
  apply Hypergraph.ext
  · exact image_union _ _ _
  · exact image_union _ _ _
  · rfl

theorem mapH_inter (ψ : S ≃ₜ Z) (A B : Hypergraph S (Set S)) : mapH ψ (A ∩ B) = mapH ψ A ∩ mapH ψ B
  := by
  apply Hypergraph.ext
  · exact image_inter ψ.injective
  · exact image_inter (image_injective.mpr ψ.injective)
  · rfl

theorem mapH_le (ψ : S ≃ₜ Z) {A B : Hypergraph S (Set S)} (h : A ≤ B) : mapH ψ A ≤ mapH ψ B := by
  have h' : IsSubhypergraph A B := h
  refine ⟨image_mono h'.vertexSet_subset, image_mono h'.edgeSet_subset, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  ext v
  have h1 := h'.ends_eq e he
  change B.Inc (ψ.symm '' (ψ '' e)) (ψ.symm v) ↔ A.Inc (ψ.symm '' (ψ '' e)) (ψ.symm v)
  rw [symm_image_image]
  exact Set.ext_iff.mp h1 _

theorem isSeparation_mapH (ψ : S ≃ₜ Z) {G A B : Hypergraph S (Set S)} (h : G.IsSeparation A B) :
  (mapH ψ G).IsSeparation (mapH ψ A) (mapH ψ B) := by
  refine ⟨mapH_le ψ h.left_le, mapH_le ψ h.right_le, ?_, ?_⟩
  · rw [← mapH_union, h.union_eq]
  · rw [← mapH_inter]
    change image ψ '' (A ∩ B).edgeSet = ∅
    rw [h.edgeSet_inter_eq, image_empty]

theorem separationOrder_mapH (ψ : S ≃ₜ Z) (A B : Hypergraph S (Set S)) : separationOrder (mapH ψ A)
  (mapH ψ B) = separationOrder A B := by
  rw [separationOrder, ← mapH_inter]
  exact ncard_image_of_injective _ ψ.injective

/-- The image of a set of separations under a homeomorphism. -/
def mapT (ψ : S ≃ₜ Z) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) : Set (Hypergraph Z
  (Set Z) × Hypergraph Z (Set Z)) :=
  (fun p => (mapH ψ p.1, mapH ψ p.2)) '' T

theorem mem_mapT (ψ : S ≃ₜ Z) {T : Set (Hypergraph S (Set S) × Hypergraph S
  (Set S))} {A B : Hypergraph S (Set S)} : (mapH ψ A, mapH ψ B) ∈ mapT ψ T ↔ (A, B) ∈ T := by
  constructor
  · rintro ⟨⟨A', B'⟩, h, he⟩
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp he
    have h3 : A' = A := by
      have := congrArg (mapH ψ.symm) h1
      simpa [mapH_symm] using this
    have h4 : B' = B := by
      have := congrArg (mapH ψ.symm) h2
      simpa [mapH_symm] using this
    rwa [← h3, ← h4]
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_mapT' (ψ : S ≃ₜ Z) {T : Set (Hypergraph S (Set S) × Hypergraph S
  (Set S))} {A B : Hypergraph Z (Set Z)} : (A, B) ∈ mapT ψ T ↔ (mapH ψ.symm A, mapH ψ.symm B) ∈ T
    := by
  rw [← mem_mapT ψ, mapH_symm', mapH_symm']

theorem isTangle_mapT (ψ : S ≃ₜ Z) {G : Hypergraph S (Set S)} {θ : ℕ} {T : Set (Hypergraph S
  (Set S) × Hypergraph S (Set S))} (h : IsTangle G θ T) :
    IsTangle (mapH ψ G) θ (mapT ψ T) := by
  refine ⟨h.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨⟨A, B⟩, hp, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp he
    exact isSeparation_mapH ψ (h.isSeparation hp)
  · rintro _ _ ⟨⟨A, B⟩, hp, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp he
    change separationOrder (mapH ψ A) (mapH ψ B) < θ
    rw [separationOrder_mapH]
    exact h.order_lt hp
  · intro A B hs ho
    have h1 := isSeparation_mapH ψ.symm hs
    rw [mapH_symm] at h1
    have h2 : separationOrder (mapH ψ.symm A) (mapH ψ.symm B) < θ := by
      rw [separationOrder_mapH]
      exact ho
    rcases h.axiom1 h1 h2 with h3 | h3
    · exact .inl ((mem_mapT' ψ).mpr h3)
    · exact .inr ((mem_mapT' ψ).mpr h3)
  · rintro _ B₁ _ B₂ _ B₃ ⟨⟨A₁, C₁⟩, h1, he₁⟩ ⟨⟨A₂, C₂⟩, h2, he₂⟩ ⟨⟨A₃, C₃⟩, h3, he₃⟩ he
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp he₁
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp he₂
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp he₃
    apply h.axiom2 h1 h2 h3
    have := congrArg (mapH ψ.symm) he
    simp only at this
    rw [← mapH_union, ← mapH_union, mapH_symm, mapH_symm] at this
    exact this
  · rintro _ _ ⟨⟨A, B⟩, hp, he⟩ hv
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp he
    exact h.axiom3 hp (ψ.injective.image_injective hv)

/-! ## Drawings -/

theorem toHypergraph_map (ψ : S ≃ₜ Z) (H : Drawing S) : (mapDrawingHomeo ψ H).toHypergraph
  = mapH ψ H.toHypergraph := by
  apply Hypergraph.ext
  · rfl
  · exact mapDrawingHomeo_edges ψ H
  · funext e v
    apply propext
    change (e ∈ (mapDrawingHomeo ψ H).E ∧ v ∈ ψ '' H.V ∧ v ∈ closure e) ↔ (ψ.symm '' e ∈ H.E
      ∧ ψ.symm v ∈ H.V ∧ ψ.symm v ∈ closure (ψ.symm '' e))
    rw [mapDrawingHomeo_edges]
    constructor
    · rintro ⟨⟨e', he, rfl⟩, ⟨v', hv, rfl⟩, h⟩
      refine ⟨by rwa [symm_image_image], by simpa using hv, ?_⟩
      rw [← ψ.symm.image_closure]
      exact ⟨_, h, rfl⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨_, h1, image_symm_image ψ e⟩, ⟨_, h2, by simp⟩, ?_⟩
      rw [← ψ.symm.image_closure] at h3
      obtain ⟨w, hw, he⟩ := h3
      rwa [ψ.symm.injective he] at hw

theorem map_R (ψ : S ≃ₜ Z) (H : Drawing S) : (mapDrawingHomeo ψ H).R = image ψ '' H.R := by
  change componentsIn (univ \ ψ '' H.U) = image ψ '' componentsIn (univ \ H.U)
  have h1 : univ \ ψ '' H.U = ψ '' (univ \ H.U) := by
    rw [image_sdiff ψ.injective, image_univ_of_surjective ψ.surjective]
  rw [h1]
  exact (image_componentsIn ψ _).symm

theorem isOpenDisc_image (ψ : S ≃ₜ Z) {Λ : Set S} (h : IsOpenDisc Λ) : IsOpenDisc (ψ '' Λ) := by
  obtain ⟨h1, ⟨φ⟩⟩ := h
  exact ⟨ψ.isOpenMap _ h1, ⟨φ.trans (ψ.image Λ)⟩⟩

theorem isClosedDisc_image (ψ : S ≃ₜ Z) {Δ : Set S} (h : IsClosedDisc Δ) : IsClosedDisc (ψ '' Δ)
  := by
  obtain ⟨φ⟩ := h
  exact ⟨φ.trans (ψ.image Δ)⟩

theorem isOArc_homeo_image (ψ : S ≃ₜ Z) {F : Set S} (h : IsOArc F) : IsOArc (ψ '' F) := by
  obtain ⟨φ⟩ := h
  exact ⟨φ.trans (ψ.image F)⟩

theorem subBd_image (ψ : S ≃ₜ Z) (Δ : Set S) : subBd (ψ '' Δ) = ψ '' subBd Δ := by
  have h1 : univ \ ψ '' Δ = ψ '' (univ \ Δ) := by
    rw [image_sdiff ψ.injective, image_univ_of_surjective ψ.surjective]
  rw [subBd, subBd, h1, image_inter ψ.injective, ψ.image_closure, ψ.image_closure]

theorem map_U (ψ : S ≃ₜ Z) (H : Drawing S) : (mapDrawingHomeo ψ H).U = ψ '' H.U := rfl

theorem map_V (ψ : S ≃ₜ Z) (H : Drawing S) : (mapDrawingHomeo ψ H).V = ψ '' H.V := rfl

theorem image_inter_symm (ψ : S ≃ₜ Z) (F : Set Z) (A : Set S) : ψ '' (ψ.symm '' F ∩ A) = F ∩ ψ '' A
  := by
  rw [image_inter ψ.injective, image_symm_image]

theorem ncard_symm (ψ : S ≃ₜ Z) (F : Set Z) (A : Set S) : (F ∩ ψ '' A).ncard =
  (ψ.symm '' F ∩ A).ncard := by
  rw [← image_inter_symm]
  exact ncard_image_of_injective _ ψ.injective

theorem normal_symm (ψ : S ≃ₜ Z) {F : Set Z} {U V : Set S} (h : F ∩ ψ '' U ⊆ ψ '' V) : ψ.symm '' F
  ∩ U ⊆ V := by
  intro x hx
  have h1 : ψ x ∈ ψ '' (ψ.symm '' F ∩ U) := ⟨x, hx, rfl⟩
  rw [image_inter_symm] at h1
  obtain ⟨y, hy, he⟩ := h h1
  exact ψ.injective he ▸ hy

/-- A connected space stays connected under a homeomorphism. -/
theorem connected_homeo (ψ : S ≃ₜ Z) (h : ConnectedSpace S) : ConnectedSpace Z :=
  ψ.surjective.connectedSpace ψ.continuous

theorem isTwoCell_map (ψ : S ≃ₜ Z) {H : Drawing S} (h : (PaintingOrDrawing.drawing H).IsTwoCell) :
  (PaintingOrDrawing.drawing (mapDrawingHomeo ψ H)).IsTwoCell := by
  refine ⟨connected_homeo ψ h.1, ?_⟩
  intro r hr
  have hr' : r ∈ (mapDrawingHomeo ψ H).R := hr
  rw [map_R] at hr'
  obtain ⟨r₀, h0, rfl⟩ := hr'
  exact isOpenDisc_image ψ (h.2 r₀ h0)

section inter

variable [T1Space S] [T1Space Z]

omit [T1Space S] [T1Space Z] in
theorem inter_map (ψ : S ≃ₜ Z) (H : Drawing S) (Δ : Set S) :
    (PaintingOrDrawing.drawing (mapDrawingHomeo ψ H)).inter (ψ '' Δ) = mapH ψ
      ((PaintingOrDrawing.drawing H).inter Δ) := by
  apply Hypergraph.ext
  · exact (image_inter ψ.injective).symm
  · change {e | e ∈ (mapDrawingHomeo ψ H).E ∧ e ⊆ ψ '' Δ} = image ψ '' {e | e ∈ H.E ∧ e ⊆ Δ}
    rw [mapDrawingHomeo_edges]
    ext e
    constructor
    · rintro ⟨⟨e₀, h0, rfl⟩, h1⟩
      exact ⟨e₀, ⟨h0, (image_subset_image_iff ψ.injective).mp h1⟩, rfl⟩
    · rintro ⟨e₀, ⟨h0, h1⟩, rfl⟩
      exact ⟨⟨e₀, h0, rfl⟩, image_mono h1⟩
  · funext e v
    apply propext
    change ((mapDrawingHomeo ψ H).toHypergraph.Inc e v ∧ e ⊆ ψ '' Δ ∧ v ∈ ψ '' Δ) ↔
      (H.toHypergraph.Inc (ψ.symm '' e) (ψ.symm v) ∧ ψ.symm '' e ⊆ Δ ∧ ψ.symm v ∈ Δ)
    rw [toHypergraph_map]
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · rw [← image_subset_image_iff ψ.injective, image_symm_image]
    · constructor
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
      · intro h
        exact ⟨_, h, by simp⟩

omit [T1Space S] [T1Space Z] in
theorem closure_compl_image (ψ : S ≃ₜ Z) (Δ : Set S) : closure (univ \ ψ '' Δ) = ψ '' closure
  (univ \ Δ) := by
  rw [ψ.image_closure, image_sdiff ψ.injective, image_univ_of_surjective ψ.surjective]

omit [T1Space S] [T1Space Z] in
theorem interOutside_map (ψ : S ≃ₜ Z) (H : Drawing S) (Δ : Set S) :
    (PaintingOrDrawing.drawing (mapDrawingHomeo ψ H)).interOutside (ψ '' Δ) = mapH ψ
      ((PaintingOrDrawing.drawing H).interOutside Δ) := by
  rw [PaintingOrDrawing.interOutside, PaintingOrDrawing.interOutside, closure_compl_image,
    inter_map]

omit [T1Space S] [T1Space Z] in
theorem isRespectful_map (ψ : S ≃ₜ Z) {H : Drawing S} {θ : ℕ} {T : Set (Hypergraph S
  (Set S) × Hypergraph S (Set S))}
    (h : (PaintingOrDrawing.drawing H).IsRespectful θ T) : (PaintingOrDrawing.drawing
      (mapDrawingHomeo ψ H)).IsRespectful θ (mapT ψ T) := by
  refine ⟨connected_homeo ψ h.1, fun F hF hN hc => ?_⟩
  have hN' : ψ.symm '' F ∩ H.U ⊆ H.V := normal_symm ψ hN
  have hc' : (ψ.symm '' F ∩ H.V).ncard < θ := by
    rw [← ncard_symm]
    exact hc
  obtain ⟨Δ, hΔ, hb, hm⟩ := h.2 (ψ.symm '' F) (isOArc_homeo_image ψ.symm hF) hN' hc'
  refine ⟨ψ '' Δ, isClosedDisc_image ψ hΔ, ?_, ?_⟩
  · rw [subBd_image, hb, image_symm_image]
  · rw [inter_map, interOutside_map]
    exact (mem_mapT ψ).mpr hm

/-- The path inside a closed set of a drawing maps to the corresponding path of the image. -/
theorem interSet_map (ψ : S ≃ₜ Z) (H : Drawing S) (Δ : Set S) :
    (mapDrawingHomeo ψ H).interSet (ψ '' Δ) = mapDrawingHomeo ψ (H.interSet Δ) := by
  have hE : {e | e ∈ (mapDrawingHomeo ψ H).E ∧ e ⊆ ψ '' Δ} = image ψ '' {e | e ∈ H.E ∧ e ⊆ Δ} := by
    rw [mapDrawingHomeo_edges]
    ext e
    constructor
    · rintro ⟨⟨e₀, h0, rfl⟩, h1⟩
      exact ⟨e₀, ⟨h0, (image_subset_image_iff ψ.injective).mp h1⟩, rfl⟩
    · rintro ⟨e₀, ⟨h0, h1⟩, rfl⟩
      exact ⟨⟨e₀, h0, rfl⟩, image_mono h1⟩
  apply Drawing.ext_of_V_E
  · change (mapDrawingHomeo ψ H).spanV ((mapDrawingHomeo ψ H).V ∩ ψ '' Δ) {e | e ∈
    (mapDrawingHomeo ψ H).E ∧ e ⊆ ψ '' Δ} = ψ '' H.spanV (H.V ∩ Δ) {e | e ∈ H.E ∧ e ⊆ Δ}
    rw [hE]
    ext z
    constructor
    · rintro (⟨⟨⟨v, hv, rfl⟩, ⟨w, hw, he⟩⟩, -⟩ | h)
      · exact ⟨v, .inl ⟨⟨hv, ψ.injective he ▸ hw⟩, hv⟩, rfl⟩
      · obtain ⟨e, ⟨⟨e₀, h0, rfl⟩, -⟩, hz⟩ := mem_iUnion₂.mp h
        rw [← ψ.image_closure, map_V, ← image_inter ψ.injective] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        exact ⟨y, .inr (mem_iUnion₂.mpr ⟨e₀, ⟨h0, h0.1⟩, hy⟩), rfl⟩
    · rintro ⟨y, (⟨⟨h1, h2⟩, -⟩ | h), rfl⟩
      · exact .inl ⟨⟨⟨y, h1, rfl⟩, ⟨y, h2, rfl⟩⟩, ⟨y, h1, rfl⟩⟩
      · obtain ⟨e, ⟨h0, -⟩, hz⟩ := mem_iUnion₂.mp h
        refine .inr (mem_iUnion₂.mpr ⟨ψ '' e, ⟨⟨e, h0, rfl⟩, ?_⟩, ?_⟩)
        · rw [mapDrawingHomeo_edges]
          exact ⟨e, h0.1, rfl⟩
        · rw [← ψ.image_closure, map_V, ← image_inter ψ.injective]
          exact ⟨y, hz, rfl⟩
  · change ((mapDrawingHomeo ψ H).span _ _).E = (mapDrawingHomeo ψ (H.span _ _)).E
    rw [Drawing.span_E, hE, mapDrawingHomeo_edges ψ (H.span _ _), Drawing.span_E,
      mapDrawingHomeo_edges ψ H, image_inter (image_injective.mpr ψ.injective)]

end inter

/-- A walk maps to a walk of the image drawing, with the images of its vertices and its edges. -/
theorem exists_walk_map (ψ : S ≃ₜ Z) (H : Drawing S) {x y : S} (W : GraphWalk H.toGraph x y) :
    ∃ W' : GraphWalk (mapDrawingHomeo ψ H).toGraph (ψ x) (ψ y), W'.support = W.support.map ψ
      ∧ W'.edges = W.edges.map (image ψ) := by
  induction W with
  | nil hx => exact ⟨.nil ⟨_, hx, rfl⟩, rfl, rfl⟩
  | cons hl rest ih =>
    obtain ⟨R, h1, h2⟩ := ih
    exact ⟨.cons (isLink_mapDrawingHomeo ψ H hl) R, congrArg (List.cons _) h1,
      congrArg (List.cons _) h2⟩

theorem isPathBetween_map (ψ : S ≃ₜ Z) {H : Drawing S} {a b : S} (h : H.IsPathBetween a b) :
  (mapDrawingHomeo ψ H).IsPathBetween (ψ a) (ψ b) := by
  obtain ⟨W, h1, h2, h3⟩ := h
  obtain ⟨W', h4, h5⟩ := exists_walk_map ψ H W
  refine ⟨W', ?_, ?_, ?_⟩
  · change W'.support.Nodup
    rw [h4]
    exact h1.map ψ.injective
  · change ψ '' H.V = _
    rw [h2]
    ext z
    simp [h4]
  · rw [mapDrawingHomeo_edges, h3]
    ext z
    simp [h5]

theorem isRigid_map [T1Space S] [T1Space Z] (ψ : S ≃ₜ Z) {H : Drawing S} (h : IsRigid H) : IsRigid
  (mapDrawingHomeo ψ H) := by
  intro F hF hN hc
  have hN' : ψ.symm '' F ∩ H.U ⊆ H.V := normal_symm ψ hN
  have hc' : (ψ.symm '' F ∩ H.V).ncard ≤ 2 := by
    rw [← ncard_symm]
    exact hc
  obtain ⟨Δ, hΔ, hb, hd⟩ := h (ψ.symm '' F) (isOArc_homeo_image ψ.symm hF) hN' hc'
  refine ⟨ψ '' Δ, isClosedDisc_image ψ hΔ, by rw [subBd_image, hb, image_symm_image], ?_⟩
  rcases hd with hd | ⟨u, v, huv, h1, h2⟩
  · left
    have h3 : ψ '' (Δ ∩ H.U) ⊆ F := by
      refine (image_mono hd).trans ?_
      rw [image_symm_image]
    rwa [image_inter ψ.injective] at h3
  · right
    refine ⟨ψ u, ψ v, fun he => huv (ψ.injective he), ?_, ?_⟩
    · have h3 : ψ '' (ψ.symm '' F ∩ H.V) = {ψ u, ψ v} := by
        rw [h1, image_pair]
      rwa [image_inter_symm] at h3
    · rw [interSet_map]
      exact isPathBetween_map ψ h2

/-- A span embedding of a drawing gives one of its image. -/
def SpanEmbedding.mapHomeo {α : Type u} {β : Type v} {G : Graph α β} (ψ : S ≃ₜ Z) {H : Drawing S}
  (η : SpanEmbedding H G) : SpanEmbedding (mapDrawingHomeo ψ H) G where
  imageGraph := η.imageGraph
  vMap := η.vMap ∘ ψ.symm
  eMap := η.eMap ∘ image ψ.symm
  imageGraph_le := η.imageGraph_le
  bijOn_v := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      simpa using η.bijOn_v.mapsTo hv
    · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ he
      simp only [comp_apply, ψ.symm_apply_apply] at he
      rw [η.bijOn_v.injOn hv hw he]
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := η.bijOn_v.surjOn hx
      exact ⟨ψ v, ⟨v, hv, rfl⟩, by simp⟩
  bijOn_e := by
    rw [mapDrawingHomeo_edges]
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      simp only [comp_apply, symm_image_image]
      exact η.bijOn_e.mapsTo he
    · rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ h
      simp only [comp_apply, symm_image_image] at h
      rw [η.bijOn_e.injOn he hf h]
    · intro x hx
      obtain ⟨e, he, rfl⟩ := η.bijOn_e.surjOn hx
      exact ⟨ψ '' e, ⟨e, he, rfl⟩, by simp only [comp_apply, symm_image_image]⟩
  inc_iff := by
    intro e he v hv
    rw [mapDrawingHomeo_edges] at he
    obtain ⟨e, he, rfl⟩ := he
    obtain ⟨v, hv, rfl⟩ := hv
    simp only [comp_apply, symm_image_image, ψ.symm_apply_apply]
    rw [η.inc_iff e he v hv, ← ψ.image_closure]
    exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨w, hw, h⟩ => ψ.injective h ▸ hw⟩

/-- A homeomorphism carries a span to a span of the same order. -/
theorem IsSigmaSpan.transport [T2Space S] [T2Space Z] {α : Type u} {β : Type v}
  (ψ : S ≃ₜ Z) {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G} {θ_star θ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)} {T : Set (Hypergraph S (Set S) × Hypergraph S
      (Set S))} (h : IsSigmaSpan G H η θ_star θ T_star T) :
    IsSigmaSpan G (mapDrawingHomeo ψ H) (SpanEmbedding.mapHomeo ψ η) θ_star θ T_star (mapT ψ T)
      := by
  have hT : IsTangle (mapDrawingHomeo ψ H).toHypergraph θ (mapT ψ T) := by
    rw [toHypergraph_map]
    exact isTangle_mapT ψ h.isControlling.isTangle_H
  refine ⟨?_, connected_homeo ψ h.isConnected, ?_, isRigid_map ψ h.isRigid,
    ⟨isTwoCell_map ψ h.isRespectful.1, hT, isRespectful_map ψ h.isRespectful.2.2⟩, ?_⟩
  · have hS := h.isSurface
    have : CompactSpace S := hS.1
    refine ⟨ψ.surjective.compactSpace ψ.continuous, inferInstance, fun x => ?_⟩
    simpa using isManifoldPoint_of_isOpenEmbedding ψ.isOpenEmbedding (hS.2.2 (ψ.symm x))
  · rw [← image_bd_homeomorph ψ, h.bd_empty, image_empty]
  · refine ⟨h.isControlling.theta_le, h.isControlling.isTangle_star, hT, ?_⟩
    intro A B hs ho A_H B_H hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hr
    have h6 : H.toHypergraph.IsSeparation (mapH ψ.symm A_H) (mapH ψ.symm B_H) := by
      have h7 := isSeparation_mapH ψ.symm h1
      rwa [toHypergraph_map, mapH_symm] at h7
    have hr' : IsRestrictedSeparation H G η A B (mapH ψ.symm A_H) (mapH ψ.symm B_H) := by
      refine ⟨h6, ?_, ?_, ?_, ?_⟩
      · refine Eq.trans ?_ h2
        change η.vMap '' (ψ.symm '' _) = (η.vMap ∘ ψ.symm) '' _
        rw [image_comp]
      · refine Eq.trans ?_ h3
        change η.eMap '' (image ψ.symm '' _) = (η.eMap ∘ image ψ.symm) '' _
        rw [image_comp]
      · refine Eq.trans ?_ h4
        change η.vMap '' (ψ.symm '' _) = (η.vMap ∘ ψ.symm) '' _
        rw [image_comp]
      · refine Eq.trans ?_ h5
        change η.eMap '' (image ψ.symm '' _) = (η.eMap ∘ image ψ.symm) '' _
        rw [image_comp]
    rw [h.isControlling.controls hs ho hr', mem_mapT']

end GraphMinor.GM16

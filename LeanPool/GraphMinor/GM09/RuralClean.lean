/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section10g

/-!
# Clean presentations and small additions to a rural neighborhood

The proof of (6.1) removes a few edges or a vertex and must add them back to a rural neighborhood.
For that we first put a presentation in a clean form, where the drawing meets `bd(Δ)` and
`bd(Δ₀)` only in the vertices of `ΩBar` and `ΩBar₀`. Then the new edge or vertex is drawn in free
space
with `GraphDrawing.glue`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-- A rural neighborhood has a presentation that meets the two boundaries only in their vertices. -/
theorem Neighborhood.IsRural.exists_clean {N : Neighborhood α β} (h : N.IsRural) :
    ∃ P : Presentation N,
      P.Γ.drawing.U ∩ subBd P.Δ = (⋃ v ∈ N.Ω.bar, graphDrawingVertexSet P.Γ v) ∧
      P.Δ₀ ∩ subBd P.Δ ⊆ (⋃ v ∈ N.Ω.bar, graphDrawingVertexSet P.Γ v) ∧
      P.Γ.drawing.U ∩ subBd P.Δ₀ ⊆ (⋃ v ∈ N.Ω₀.bar, graphDrawingVertexSet P.Γ v) := by
  obtain ⟨Γ, Δ, Δ₀, hΔ, hsub, hU, hbd, hbd₀, ⟨φ, hφ_cw, hag⟩, hinner⟩ := h
  obtain ⟨-, -, Γ', Δ₀', -, -, -, -, -, -, hΔ₀', -, hU', -, -, -, hinterU, hinterΔ₀, hbd', hbd₀',
    hag', hinner'⟩ := exists_clean_presentation_of_restrict_outer N.bar_subset Subset.rfl
      (fun _ _ _ h => h) Γ Δ Δ₀ hΔ hsub hU hbd hbd₀ φ hag hinner
  rcases hinner' with ⟨rfl, hemp⟩ | ⟨hd, φ₀, hφ₀_cw, hag₀⟩
  · refine ⟨⟨Γ', Δ, ∅, hΔ, hΔ₀', hU', hbd', hbd₀', ⟨φ, hφ_cw, hag'⟩, Or.inl ⟨rfl, hemp⟩⟩,
      hinterU, hinterΔ₀, ?_⟩
    simp [subBd]
  have hpt : ∀ v ∈ N.Ω₀.bar, ∃ q, graphDrawingVertexSet Γ' v = {q} := fun v hv =>
    ⟨_, graphDrawingVertexSet_eq_singleton Γ' (N.bar₀_subset hv)⟩
  let F : Set EuclideanPlane := ⋃ v ∈ N.Ω₀.bar, graphDrawingVertexSet Γ' v
  have hFc : IsClosed F := N.Ω₀.finite_bar.isClosed_biUnion fun v hv => by
    obtain ⟨q, hq⟩ := hpt v hv
    rw [hq]
    exact isClosed_singleton
  have hbdeq : subBd Δ₀' = discBd Δ₀' := subBd_eq_discBd_plane hd
  have hFb : F ⊆ discBd Δ₀' := by
    rw [← hbdeq]
    exact iUnion₂_subset fun v hv => (hbd₀' v (N.bar₀_subset hv)).mpr hv
  obtain ⟨Ψ, Ψ', Ψ_hom, hc, hc', hl, hinj, hsub', hfix, hint,
    hΨ_hom_cont, hΨ_hom_zero, hΨ_hom_one, hΨ_hom_inj⟩ :=
    exists_disc_shrink_map_with_homotopy hd hFc hFb
  obtain ⟨hd', hbd'eq⟩ := hd.image hc hc' hl
  let Δ₁ : Set EuclideanPlane := Ψ '' Δ₀'
  have hbd₁ : subBd Δ₁ = Ψ '' discBd Δ₀' := by
    rw [subBd_eq_discBd_plane hd', hbd'eq]
  have hint₁_eq : interior Δ₁ = Ψ '' interior Δ₀' := by
    rw [interior_eq_discInt_plane hd', interior_eq_discInt_plane hd]
    change Δ₁ \ discBd Δ₁ = Ψ '' (Δ₀' \ discBd Δ₀')
    rw [hbd'eq]
    exact (InjOn.image_sdiff_subset hinj (Surface.discBd_subset Δ₀')).symm
  have hintmono : interior Δ₁ ⊆ interior Δ₀' := interior_mono hsub'
  have hUbd : Γ'.drawing.U ∩ subBd Δ₁ ⊆ F := by
    rintro p ⟨hpU, hp⟩
    rw [hbd₁] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    by_cases hxF : x ∈ F
    · rw [hfix x hxF]
      exact hxF
    · have := hint x ⟨Surface.discBd_subset _ hx, hxF⟩
      refine absurd ?_ (hU' hpU).2
      rw [interior_eq_discInt_plane hd]
      exact this
  have hvfix : ∀ v ∈ N.Ω₀.bar, Ψ '' graphDrawingVertexSet Γ' v = graphDrawingVertexSet Γ' v := by
    intro v hv
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hfix y (mem_iUnion₂.mpr ⟨v, hv, hy⟩)]
      exact hy
    · intro hx
      exact ⟨x, hx, hfix x (mem_iUnion₂.mpr ⟨v, hv, hx⟩)⟩
  have hbd₀₁ : ∀ v ∈ V(N.G), (graphDrawingVertexSet Γ' v ⊆ subBd Δ₁ ↔ v ∈ N.Ω₀.bar) := by
    intro v hv
    constructor
    · intro hs
      rw [graphDrawingVertexSet_eq_singleton Γ' hv, singleton_subset_iff] at hs
      have hq : (Γ'.iso.vertexEquiv ⟨v, hv⟩).1 ∈ graphDrawingVertexSet Γ' v := by
        rw [graphDrawingVertexSet_eq_singleton Γ' hv]
        rfl
      have hqU : (Γ'.iso.vertexEquiv ⟨v, hv⟩).1 ∈ Γ'.drawing.U :=
        Γ'.drawing.V_subset_U (Γ'.iso.vertexEquiv ⟨v, hv⟩).2
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp (hUbd ⟨hqU, hs⟩)
      exact (graphDrawingVertexSet_inj Γ' hq hxu) ▸ hu
    · intro hvb x hx
      rw [hbd₁]
      have : x ∈ Ψ '' graphDrawingVertexSet Γ' v := (hvfix v hvb).symm ▸ hx
      obtain ⟨y, hy, rfl⟩ := this
      refine ⟨y, ?_, rfl⟩
      rw [← hbdeq]
      exact (hbd₀' v hv).mpr hvb hy
  have hbdsub : subBd Δ₀' ⊆ Δ₀' := hbdeq ▸ Surface.discBd_subset _
  obtain ⟨φ₁, hφ₁_val, hag₁⟩ := drawingAgreesWithOArcHomeo_of_image (C' := subBd Δ₁) Γ' Γ' φ₀
    (hc.mono hbdsub)
    (hc'.mono (image_mono hbdsub)) (hl.mono hbdsub) (by rw [hbd₁, hbdeq])
    (fun v hv => (hvfix v hv).symm) hag₀
  have hφ₁_cw : IsClockwiseDiscHomeo Δ₁ φ₁ :=
    isClockwiseDiscHomeo_of_homotopy hd Subset.rfl hint₁_eq rfl φ₀ φ₁ hφ₁_val
      hΨ_hom_cont hΨ_hom_zero hΨ_hom_one hΨ_hom_inj hφ₀_cw
  refine ⟨⟨Γ', Δ, Δ₁, hΔ, hsub'.trans hΔ₀', fun x hx => ⟨(hU' hx).1,
    fun hi => (hU' hx).2 (hintmono hi)⟩,
    hbd', hbd₀₁, ⟨φ, hφ_cw, hag'⟩, Or.inr ⟨hd', φ₁, hφ₁_cw, hag₁⟩⟩, hinterU, ?_, hUbd⟩
  exact (inter_subset_inter_left _ hsub').trans hinterΔ₀

/-- The point of a vertex in a drawing in the plane. -/
noncomputable def vertexPt {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) (v : α) :
    EuclideanPlane := by
  classical
  exact if h : v ∈ V(G) then (Γ.iso.vertexEquiv ⟨v, h⟩).1 else 0

theorem vertexSet_eq_vertexPt {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) {v : α}
    (h : v ∈ V(G)) : graphDrawingVertexSet Γ v = {vertexPt Γ v} := by
  rw [graphDrawingVertexSet_eq_singleton Γ h]
  simp only [vertexPt, h, ↓reduceDIte]

theorem vertexEquiv_eq_vertexPt {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) (v : V(G)) :
    (Γ.iso.vertexEquiv v).1 = vertexPt Γ v.1 := by
  simp only [vertexPt, v.2, ↓reduceDIte]

theorem vertexPt_injOn {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) :
    InjOn (vertexPt Γ) V(G) := by
  intro u hu w hw e
  refine graphDrawingVertexSet_inj Γ (x := vertexPt Γ u) ?_ ?_
  · rw [vertexSet_eq_vertexPt Γ hu]
    rfl
  · rw [vertexSet_eq_vertexPt Γ hw, e]
    rfl

theorem vertexPt_mem_U {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) {v : α}
    (h : v ∈ V(G)) : vertexPt Γ v ∈ Γ.drawing.U := by
  rw [← vertexEquiv_eq_vertexPt Γ ⟨v, h⟩]
  exact Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, h⟩).2

/-- Angles that increase along an orbit list of `Ω` show that a drawing agrees with `Ω`. -/
theorem drawingAgrees_of_angles {S : Type*} [TopologicalSpace S] {G : Graph α β}
    {Γ : GraphDrawing G S} {Ω : CyclicPerm α} {L : List α} (hL : Ω.IsOrbitList L) {θ : α → ℝ}
    (hθ : IsValidAngle L θ) {C : Set S} (φ : Circle ≃ₜ C)
    (hC : ∀ v ∈ Ω.bar, graphDrawingVertexSet Γ v ⊆ C)
    (h : ∀ v ∈ Ω.bar, (φ (Circle.exp (θ v))).1 ∈ graphDrawingVertexSet Γ v) :
    DrawingAgreesWithOArcHomeo Γ Ω C φ :=
  ⟨hC, fun _ _ _ hcw => exists_angles_of_isClockwise3 hL hθ (T := graphDrawingVertexSet Γ)
    (f := fun t => (φ (Circle.exp t)).1) (fun t => by simp only [circle_exp_add_two_pi]) h hcw⟩

/-- The set of vertices of an edgeless drawing of `ΩBar` on the boundary of the unit disc. -/
theorem exists_edgeless_presentation (Ω : CyclicPerm α) {G : Graph α β} (hV : V(G) = Ω.bar)
    (hE : E(G) = ∅) :
    ∃ Γ : GraphDrawing G EuclideanPlane, ∃ φ : Circle ≃ₜ subBd ClosedUnitDisc,
      IsClockwiseDiscHomeo ClosedUnitDisc φ ∧
      Γ.drawing.U ⊆ subBd ClosedUnitDisc ∧ DrawingAgreesWithOArcHomeo Γ Ω (subBd ClosedUnitDisc) φ
        := by
  have hfin : V(G).Finite := hV ▸ Ω.finite_bar
  let φ := circleHomeomorphSubBdClosedUnitDisc
  rcases Ω.bar.eq_empty_or_nonempty with he | ⟨w, hw⟩
  · have hinj : InjOn (fun _ : α => (0 : EuclideanPlane)) V(G) := by
      rw [hV, he]
      exact injOn_empty _
    obtain ⟨Γ, hU, -⟩ := GraphDrawing.of_edgeless hfin hE hinj
    refine ⟨Γ, φ, isClockwiseDiscHomeo_closedUnitDisc,
      by rw [hU, hV, he, image_empty]; exact empty_subset _,
      fun v hv => (he ▸ hv : v ∈ (∅ : Set α)).elim, fun v₁ _ _ h => ?_⟩
    have hv : v₁ ∈ Ω.bar := (Ω.isClockwise3_iff.mp h).2.2.2.1
    exact (he ▸ hv : v₁ ∈ (∅ : Set α)).elim
  obtain ⟨L, hL⟩ := Ω.exists_isOrbitList_of_mem hw
  obtain ⟨θ, hθ⟩ := hL.exists_isValidAngle
  let ν : α → EuclideanPlane := fun v => (φ (Circle.exp (θ v))).1
  have hinj : InjOn ν V(G) := by
    rw [hV]
    intro u hu v hv huv
    exact injOn_circle_exp_of_isValidAngle hL hθ hu hv
      (congrArg Circle.coeHom (φ.injective (Subtype.ext huv)))
  obtain ⟨Γ, hU, hν⟩ := GraphDrawing.of_edgeless hfin hE hinj
  have hset : ∀ v ∈ Ω.bar, graphDrawingVertexSet Γ v = {ν v} := fun v hv => by
    rw [graphDrawingVertexSet_eq_singleton Γ (hV ▸ hv), hν ⟨v, hV ▸ hv⟩]
  refine ⟨Γ, φ, isClockwiseDiscHomeo_closedUnitDisc, ?_, drawingAgrees_of_angles hL hθ φ ?_ ?_⟩
  · rw [hU]
    rintro _ ⟨v, -, rfl⟩
    exact (φ _).2
  · intro v hv
    rw [hset v hv, singleton_subset_iff]
    exact (φ _).2
  · intro v hv
    rw [hset v hv]
    rfl

namespace Society

variable (S : Society α β)

/-- If every transaction has at most `k` members then the sophistication is at most `k`, by the
composition of `(G, Ω)` with the rural neighborhood that has only the vertices of `ΩBar`. -/
theorem hasSophisticationLE_of_forall_le {k : ℕ}
    (h : ∀ P_set : Set (Graph α β), S.IsTransaction P_set → P_set.ncard ≤ k) :
    S.HasSophisticationLE k := by
  let H : Graph α β := (S.G.induce S.Ω.bar).restrict ∅
  have hV : V(H) = S.Ω.bar := by simp [H]
  have hE : E(H) = ∅ := by simp [H]
  have hle : H ≤ S.G := (Graph.restrict_le).trans (S.G.induce_le S.bar_subset)
  let N : Neighborhood α β :=
    ⟨H, S.Ω, S.Ω, hV ▸ S.Ω.finite_bar, by rw [hE]; exact finite_empty, hV.ge, hV.ge⟩
  refine ⟨S, N, ⟨⟨⟨le_rfl, hle, ?_, ?_, ?_⟩, hV.ge⟩, rfl, rfl, ?_⟩, ?_, h⟩
  · rw [hV]
    exact union_eq_left.mpr S.bar_subset
  · rw [hE, union_empty]
  · rw [hE]
    exact disjoint_bot_right
  · rw [hV]
    exact (inter_eq_right.mpr S.bar_subset).symm
  obtain ⟨Γ, φ, hφ_cw, hU, hag⟩ := exists_edgeless_presentation S.Ω hV hE
  have hdisc : IsClosedDisc ClosedUnitDisc := ⟨Homeomorph.refl ClosedUnitDisc⟩
  have hiff : ∀ v ∈ V(N.G), (graphDrawingVertexSet Γ v ⊆ subBd ClosedUnitDisc ↔ v ∈ S.Ω.bar) := by
    intro v hv
    refine ⟨fun _ => hV ▸ hv, fun _ x hx => hU ?_⟩
    rw [graphDrawingVertexSet_eq_singleton Γ hv] at hx
    rw [hx]
    exact Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, hv⟩).2
  refine ⟨Γ, ClosedUnitDisc, ClosedUnitDisc, hdisc, Subset.rfl, ?_, hiff, hiff, ⟨φ, hφ_cw, hag⟩,
    Or.inr ⟨hdisc, φ, hφ_cw, hag⟩⟩
  intro x hx
  have hb := hU hx
  refine ⟨hdisc.isCompact.isClosed.closure_subset hb.1, fun hi => ?_⟩
  have hc : closure (univ \ ClosedUnitDisc) = (interior ClosedUnitDisc)ᶜ := by
    rw [← compl_eq_univ_sdiff, closure_compl]
  exact (hc ▸ hb.2 : x ∈ (interior ClosedUnitDisc)ᶜ) hi

end Society

end GraphMinor.GM09

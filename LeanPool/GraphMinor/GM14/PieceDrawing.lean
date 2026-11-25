/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.FewCircuitsDrawing
public import LeanPool.GraphMinor.GM14.RigidPoints
public import LeanPool.GraphMinor.GM14.Section6
public import LeanPool.GraphMinor.Minor.Basic

/-!
# Extending a drawing inside one disc of an arrangement

"Since every graph with at most one circuit can be drawn in the plane with all its vertices incident
with the infinite region, we deduce from (2) and the rigidity of $H$ that for each $(A, \Omega) \in
\mathscr{S}$, the
drawing $H \cap A$ in the disc $\alpha(A, \Omega)$ can be extended to an embedding of $A$ in this
disc, in such a
way that each $v \in \bar{\Omega}$ is represented by the point $\alpha(v)$" (Graph Minors XIV, proof
of (8.4), page
42). We draw `A` in the disc from scratch, and then use (6.4) to move the drawing of `H ∩ A` that we
get onto the given one.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11
open GraphMinor.GM14.Whitney

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Place a boundary drawing in another disc and prescribe up to three boundary vertices. -/
theorem place_boundary_drawing {K : Graph α β} (hV : V(K).Finite)
    (Y : GraphDrawing K EuclideanPlane) {Δ : Set EuclideanPlane}
    (hΔ : IsClosedDisc Δ) (hYU : Y.drawing.U ⊆ Δ) (hYV : Y.drawing.V ⊆ subBd Δ)
    {D : Set S} (hD : IsClosedDisc D) {X : Set α}
    (hXK : X ⊆ V(K)) (hX : X.ncard ≤ 3) {g : α → S} (hg : InjOn g X)
    (hgD : MapsTo g X (discBd D)) :
    ∃ Γ : GraphDrawing K S, Γ.drawing.U ⊆ D ∧ Γ.drawing.U ∩ discBd D = g '' X ∧
      ∀ v : V(K), v.1 ∈ X → (Γ.iso.vertexEquiv v).1 = g v.1 := by
  classical
  have hpt : ∀ v (hv : v ∈ V(K)), vertexPt Y v = (Y.iso.vertexEquiv ⟨v, hv⟩).1 := fun v hv => by
    simp [vertexPt, hv]
  have hptV : ∀ v ∈ V(K), vertexPt Y v ∈ Y.drawing.V := fun v hv => by
    rw [hpt v hv]
    exact (Y.iso.vertexEquiv ⟨v, hv⟩).2
  have hptinj : InjOn (vertexPt Y) V(K) := vertexPt_injOn Y
  let F : Set EuclideanPlane := vertexPt Y '' X
  have hXf : X.Finite := hV.subset hXK
  have hFf : F.Finite := hXf.image _
  have hFbd : F ⊆ discBd Δ := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← subBd_eq_discBd_plane hΔ]
    exact hYV (hptV v (hXK hv))
  have hFc : F.ncard ≤ 3 := (ncard_image_le hXf).trans hX
  obtain ⟨Ψ, Ψ', hΨc, -, _, hΨi, hΨD, hΨF, hΨin⟩ :=
    exists_disc_shrink_map hΔ hFf.isClosed hFbd
  obtain ⟨x₀, -⟩ := hD.nonempty_discInt
  let g' : EuclideanPlane → S := fun y =>
    if h : ∃ v ∈ X, vertexPt Y v = y then g h.choose else x₀
  have hg'e : ∀ v ∈ X, g' (vertexPt Y v) = g v := by
    intro v hv
    have h : ∃ w ∈ X, vertexPt Y w = vertexPt Y v := ⟨v, hv, rfl⟩
    have hs := h.choose_spec
    change (if h : ∃ w ∈ X, vertexPt Y w = vertexPt Y v then g h.choose else x₀) = g v
    rw [dite_eq_left_of_eq_true (eq_true h), hptinj (hXK hs.1) (hXK hv) hs.2]
  have hg'i : InjOn g' F := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ h
    rw [hg'e v hv, hg'e w hw] at h
    rw [hg hv hw h]
  have hg'm : MapsTo g' F (discBd D) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hg'e v hv]
    exact hgD hv
  obtain ⟨φ, φ', hφ, hφg, -, hφb'⟩ := exists_disc_points hΔ hD hFf hFbd hFc hg'i hg'm
  let f : EuclideanPlane → S := fun x => φ (Ψ x)
  have hΨm : MapsTo Ψ Δ Δ := fun x hx => hΨD (mem_image_of_mem Ψ hx)
  have hfc : ContinuousOn f Δ := hφ.2.2.2.2.1.comp hΨc hΨm
  have hfi : InjOn f Δ := fun x hx y hy h =>
    hΨi hx hy (hφ.injOn (hΨm hx) (hΨm hy) h)
  have hUc : IsCompact Y.drawing.U := hΔ.isCompact.of_isClosed_subset Y.drawing.isClosed_U hYU
  obtain ⟨Γ, hU, -, hv, -, -, -⟩ :=
    GM09.GraphDrawing.transportOn Y hUc (hfc.mono hYU) (hfi.mono hYU)
  have hfF : ∀ v ∈ X, f (vertexPt Y v) = g v := fun v hv => by
    have hm : vertexPt Y v ∈ F := mem_image_of_mem _ hv
    change φ (Ψ _) = g v
    rw [hΨF _ hm, hφg _ hm]
    exact hg'e v hv
  refine ⟨Γ, ?_, ?_, fun v hvX => ?_⟩
  · rw [hU]
    rintro _ ⟨x, hx, rfl⟩
    exact hφ.1 (hΨm (hYU hx))
  · rw [hU]
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨⟨x, hx, rfl⟩, hb⟩
      by_cases hxF : x ∈ F
      · obtain ⟨v, hv', rfl⟩ := hxF
        exact ⟨v, hv', (hfF v hv').symm⟩
      · have hin := hΨin x ⟨hYU hx, hxF⟩
        have hb' := hφb' hb
        rw [show φ' (f x) = Ψ x from hφ.2.2.1 hin.1] at hb'
        exact (hin.2 hb').elim
    · rintro _ ⟨v, hv', rfl⟩
      refine ⟨⟨vertexPt Y v, ?_, hfF v hv'⟩, hgD hv'⟩
      exact Y.drawing.V_subset_U (hptV v (hXK hv'))
  · rw [hv v, ← hpt v.1 v.2]
    exact hfF v.1 hvX

/-- A graph with at most one circuit can be drawn in a closed disc, with at most three chosen
vertices at given points of the boundary, and with nothing else on the boundary. -/
theorem exists_disc_drawing {K : Graph α β} (hV : V(K).Finite) (hE : E(K).Finite)
    (hc : {C | IsGraphCircuit K C}.ncard ≤ 1) {D : Set S} (hD : IsClosedDisc D) {X : Set α}
    (hXK : X ⊆ V(K)) (hX : X.ncard ≤ 3) {g : α → S} (hg : InjOn g X)
    (hgD : MapsTo g X (discBd D)) :
    ∃ Γ : GraphDrawing K S, Γ.drawing.U ⊆ D ∧ Γ.drawing.U ∩ discBd D = g '' X ∧
      ∀ v : V(K), v.1 ∈ X → (Γ.iso.vertexEquiv v).1 = g v.1 := by
  classical
  obtain ⟨Y, Δ, hΔ, hYU, hYV⟩ := exists_boundary_drawing hV hE hc
  exact place_boundary_drawing hV Y hΔ hYU hYV hD hXK hX hg hgD

/-- The inverse of an isomorphism. -/
def isoSymm {α' β' α'' β'' : Type*} {G : Graph α' β'} {G' : Graph α'' β''} (ι : Iso G G') :
    Iso G' G :=
  ι.symm

/-- The composition of two isomorphisms. -/
def isoTrans {α₁ β₁ α₂ β₂ α₃ β₃ : Type*} {G₁ : Graph α₁ β₁} {G₂ : Graph α₂ β₂} {G₃ : Graph α₃ β₃}
    (ι : Iso G₁ G₂) (κ : Iso G₂ G₃) : Iso G₁ G₃ :=
  ι.trans κ

omit [T2Space S] in
/-- A `SpanEmbedding` is an isomorphism onto its image. -/
theorem SpanEmbedding.exists_iso {H : Drawing S} {G : Graph α β} (η : SpanEmbedding H G) :
    ∃ ι : Iso H.toGraph η.imageGraph, (∀ v, (ι.vertexEquiv v).1 = η.vMap v.1) ∧
      ∀ e, (ι.edgeEquiv e).1 = η.eMap e.1 := by
  classical
  let vE : V(H.toGraph) ≃ V(η.imageGraph) := η.bijOn_v.equiv η.vMap
  let eE : E(H.toGraph) ≃ E(η.imageGraph) := η.bijOn_e.equiv η.eMap
  have hlink : ∀ (e : Set S) (he : e ∈ H.E) (x y : S) (hx : x ∈ H.V) (hy : y ∈ H.V),
      H.toGraph.IsLink e x y ↔ η.imageGraph.IsLink (η.eMap e) (η.vMap x) (η.vMap y) := by
    intro e he x y hx hy
    have hends : ∀ {a b : α} {w : S}, η.imageGraph.IsLink (η.eMap e) a b → w ∈ H.V →
        w ∈ closure e → η.vMap w = a ∨ η.vMap w = b := by
      intro a b w hab hw hwe
      obtain ⟨c, hc⟩ := (η.inc_iff e he w hw).mpr hwe
      exact η.imageGraph.eq_or_eq_of_isLink_of_isLink hc hab
    constructor
    · rintro ⟨-, -, -, hcl⟩
      have hxe : x ∈ closure e := (show x ∈ ({x, y} : Set S) from Or.inl rfl) |> fun h =>
        (hcl ▸ h : x ∈ closure e ∩ H.V).1
      have hye : y ∈ closure e := (show y ∈ ({x, y} : Set S) from Or.inr rfl) |> fun h =>
        (hcl ▸ h : y ∈ closure e ∩ H.V).1
      obtain ⟨z, hz⟩ := (η.inc_iff e he x hx).mpr hxe
      obtain ⟨w, hw, rfl⟩ := η.bijOn_v.surjOn hz.right_mem
      have hwe : w ∈ closure e := (η.inc_iff e he w hw).mp ⟨_, hz.symm⟩
      have hw' : w ∈ ({x, y} : Set S) := hcl ▸ ⟨hwe, hw⟩
      rcases hw' with rfl | rfl
      · have hy' := hends hz hy hye
        have hyx : y = w := by
          rcases hy' with h | h <;> exact η.bijOn_v.injOn hy hx h
        rwa [hyx]
      · exact hz
    · intro h
      refine ⟨he, hx, hy, subset_antisymm ?_ ?_⟩
      · rintro w ⟨hwe, hw⟩
        rcases hends h hw hwe with h' | h'
        · exact Or.inl (η.bijOn_v.injOn hw hx h')
        · exact Or.inr (η.bijOn_v.injOn hw hy h')
      · rintro w (rfl | rfl)
        · exact ⟨(η.inc_iff e he w hx).mp h.inc_left, hx⟩
        · exact ⟨(η.inc_iff e he w hy).mp h.inc_right, hy⟩
  exact ⟨⟨vE, eE, fun e x y => hlink e.1 e.2 x.1 y.1 x.2 y.2⟩, fun _ => rfl, fun _ => rfl⟩

/-- Align a disc drawing of `K` with the prescribed drawing of its subgraph. -/
theorem extend_piece_drawing {H₁ : Drawing S} {K : Graph α β} (η : SpanEmbedding H₁ K)
    {D : Set S} (hD : IsClosedDisc D) (hbdD : subBd D = discBd D)
    (hH₁D : H₁.U ⊆ D) (hH₁bd : H₁.U ∩ subBd D ⊆ H₁.V)
    {X : Set α} (hXK : X ⊆ V(K)) {g : α → S} (hgD : MapsTo g X (subBd D))
    (hXH : ∀ v ∈ H₁.V, v ∈ subBd D ↔ η.vMap v ∈ X)
    (hgH : ∀ v ∈ H₁.V, η.vMap v ∈ X → g (η.vMap v) = v)
    (hrigid : ∀ F : Set S, F ⊆ D → IsOArc F → F ∩ H₁.U ⊆ H₁.V →
      (F ∩ H₁.V).ncard ≤ 2 → ∃ Δ' : Set S, Δ' ⊆ D ∧ IsDial H₁ F Δ')
    (Y : GraphDrawing K S) (hYU : Y.drawing.U ⊆ D) (hYbd : Y.drawing.U ∩ subBd D = g '' X)
    (hYg : ∀ v : V(K), v.1 ∈ X → (Y.iso.vertexEquiv v).1 = g v.1) :
    ∃ Γ : GraphDrawing K S, Γ.drawing.U ⊆ D ∧ Γ.drawing.U ∩ subBd D = g '' X ∧
      (∀ v : V(K), v.1 ∈ X → (Γ.iso.vertexEquiv v).1 = g v.1) ∧
      (∀ v ∈ H₁.V, graphDrawingVertexSet Γ (η.vMap v) = {v}) ∧
      ∀ e ∈ H₁.E, graphDrawingEdgeSet Γ (η.eMap e) = e := by
  classical
  obtain ⟨ι, hιv, hιe⟩ := η.exists_iso
  obtain ⟨Y₀, -, hY₀U, hY₀s, hY₀v, -, hY₀e, -⟩ := GM09.GraphDrawing.ofSubgraph Y η.imageGraph_le
  let φ : Iso H₁.toGraph Y₀.drawing.toGraph := isoTrans ι Y₀.iso
  have hle := η.imageGraph_le
  have hmem : ∀ v ∈ H₁.V, η.vMap v ∈ V(K) := fun v hv =>
    hle.vertexSet_mono (η.bijOn_v.mapsTo hv)
  have hφv : ∀ v : V(H₁.toGraph), (φ.vertexEquiv v).1 =
      (Y.iso.vertexEquiv ⟨η.vMap v.1, hmem v.1 v.2⟩).1 := by
    intro v
    have h1 : (φ.vertexEquiv v).1 = (Y₀.iso.vertexEquiv (ι.vertexEquiv v)).1 := rfl
    rw [h1, hY₀v]
    congr 3
    exact hιv v
  have hφe : ∀ e : E(H₁.toGraph), (φ.edgeEquiv e).1 = graphDrawingEdgeSet Y (η.eMap e.1) := by
    intro e
    have h1 : (φ.edgeEquiv e).1 = (Y₀.iso.edgeEquiv (ι.edgeEquiv e)).1 := rfl
    have hm : η.eMap e.1 ∈ E(η.imageGraph) := η.bijOn_e.mapsTo e.2
    rw [← hY₀e _ hm, graphDrawingEdgeSet_eq Y₀ hm, h1]
    congr 3
    exact Subtype.ext (hιe e)
  have hbar : ∀ v (hv : v ∈ H₁.V), v ∈ subBd D →
      (Y.iso.vertexEquiv ⟨η.vMap v, hmem v hv⟩).1 = v := by
    intro v hv hb
    have hX' := (hXH v hv).mp hb
    rw [hYg ⟨_, hmem v hv⟩ hX']
    exact hgH v hv hX'
  have hY₀V : ∀ x ∈ Y₀.drawing.V, ∃ (v : S) (hv : v ∈ H₁.V),
      x = (Y.iso.vertexEquiv ⟨η.vMap v, hmem v hv⟩).1 := by
    intro x hx
    obtain ⟨v, hv, hw⟩ := η.bijOn_v.surjOn (Y₀.iso.vertexEquiv.symm ⟨x, hx⟩).2
    refine ⟨v, hv, ?_⟩
    have h := hY₀v (Y₀.iso.vertexEquiv.symm ⟨x, hx⟩)
    rw [Equiv.apply_symm_apply] at h
    refine h.trans ?_
    congr 3
    exact hw.symm
  have hYpt : ∀ a (ha : a ∈ X), (Y.iso.vertexEquiv ⟨a, hXK ha⟩).1 = g a := fun a ha => hYg _ ha
  have hH₂bd : Y₀.drawing.U ∩ subBd D ⊆ Y₀.drawing.V := by
    rintro x ⟨hxU, hxb⟩
    by_contra hxV
    obtain ⟨e, he, hxe⟩ := Y₀.drawing.exists_edge_of_mem hxU hxV
    have heY : e ∈ Y.drawing.E := hY₀s.2 he
    have hx' : x ∈ Y.drawing.U ∩ subBd D := ⟨hY₀U hxU, hxb⟩
    rw [hYbd] at hx'
    obtain ⟨a, ha, rfl⟩ := hx'
    have hgaV : g a ∈ Y.drawing.V := hYpt a ha ▸ (Y.iso.vertexEquiv ⟨a, hXK ha⟩).2
    exact (heY.2.1 hxe).2 hgaV
  have hbdV : H₁.V ∩ subBd D = Y₀.drawing.V ∩ subBd D := by
    ext x
    constructor
    · rintro ⟨hxV, hxb⟩
      have h1 := hφv ⟨x, hxV⟩
      rw [hbar x hxV hxb] at h1
      exact ⟨h1 ▸ (φ.vertexEquiv ⟨x, hxV⟩).2, hxb⟩
    · rintro ⟨hxV, hxb⟩
      obtain ⟨v, hv, rfl⟩ := hY₀V x hxV
      have hx' : (Y.iso.vertexEquiv ⟨η.vMap v, hmem v hv⟩).1 ∈ Y.drawing.U ∩ subBd D :=
        ⟨Y.drawing.V_subset_U (Y.iso.vertexEquiv _).2, hxb⟩
      rw [hYbd] at hx'
      obtain ⟨a, ha, hax⟩ := hx'
      have hinj : (⟨a, hXK ha⟩ : V(K)) = ⟨η.vMap v, hmem v hv⟩ := by
        apply Y.iso.vertexEquiv.injective
        apply Subtype.ext
        rw [hYpt a ha, hax]
      have hav : a = η.vMap v := congrArg Subtype.val hinj
      have hvb : v ∈ subBd D := (hXH v hv).mpr (hav ▸ ha)
      rw [hbar v hv hvb]
      exact ⟨hv, hvb⟩
  have hφbd : ∀ v : V(H₁.toGraph), v.1 ∈ subBd D → (φ.vertexEquiv v).1 = v.1 := fun v hb => by
    rw [hφv v]
    exact hbar v.1 v.2 hb
  obtain ⟨ψ, hψD, hψv, hψe, -, -, -, hψbd⟩ := theorem_6_4_proof hD hbdD hH₁D
    (hY₀U.trans hYU) hH₁bd
    hH₂bd hbdV φ hφbd hrigid
  obtain ⟨x₀, -⟩ := hD.nonempty_discInt
  have hSne : Nonempty S := ⟨x₀⟩
  have hUc : IsCompact Y.drawing.U := hD.isCompact.of_isClosed_subset Y.drawing.isClosed_U hYU
  obtain ⟨Γ, hU, -, hv, hvs, hes, -⟩ := GM09.GraphDrawing.transportOn Y hUc
    ψ.symm.continuous.continuousOn ψ.symm.injective.injOn
  have hsymm : ∀ x ∈ subBd D, ψ.symm x = x := fun x hx => by
    rw [Homeomorph.symm_apply_eq]
    exact (hψbd x hx).symm
  refine ⟨Γ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    rintro _ ⟨y, hy, rfl⟩
    have : y ∈ ψ '' D := by rw [hψD]; exact hYU hy
    obtain ⟨z, hz, rfl⟩ := this
    simpa using hz
  · rw [hU, ← hYbd]
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨⟨y, hy, rfl⟩, hb⟩
      have h1 := hψbd _ hb
      rw [Homeomorph.apply_symm_apply] at h1
      rw [← h1]
      exact ⟨hy, h1 ▸ hb⟩
    · rintro y ⟨hy, hb⟩
      exact ⟨⟨y, hy, hsymm y hb⟩, hb⟩
  · intro v hvX
    rw [hv v, hYg v hvX]
    exact hsymm _ (hgD hvX)
  · intro v hvH
    have hk := hmem v hvH
    rw [hvs, graphDrawingVertexSet_eq_singleton Y hk, image_singleton, ← hφv ⟨v, hvH⟩,
      ← hψv ⟨v, hvH⟩]
    simp
  · intro e he
    rw [hes, ← hφe ⟨e, he⟩, ← hψe ⟨e, he⟩]
    simp [image_image]

/-- **The drawing of one member of the segregation.** Suppose that `H₁` is drawn in the closed disc
`D`, and that it is a subgraph `η(H₁)` of `K`. Suppose that `K = η(H₁)`, or that `K` has at most
one circuit. Then `K` has a drawing in `D` which extends the drawing `H₁`, with the vertices of `X`
at given points of the boundary, and with nothing else on the boundary. -/
theorem exists_piece_drawing {H₁ : Drawing S} {K : Graph α β} (η : SpanEmbedding H₁ K)
    (hV : V(K).Finite) (hE : E(K).Finite) {D : Set S} (hD : IsClosedDisc D)
    (hbdD : subBd D = discBd D) (hH₁D : H₁.U ⊆ D) (hH₁bd : H₁.U ∩ subBd D ⊆ H₁.V)
    {X : Set α} (hXK : X ⊆ V(K)) (hX : X.ncard ≤ 3) {g : α → S} (hg : InjOn g X)
    (hgD : MapsTo g X (subBd D)) (hXH : ∀ v ∈ H₁.V, v ∈ subBd D ↔ η.vMap v ∈ X)
    (hgH : ∀ v ∈ H₁.V, η.vMap v ∈ X → g (η.vMap v) = v)
    (hrigid : ∀ F : Set S, F ⊆ D → IsOArc F → F ∩ H₁.U ⊆ H₁.V →
      (F ∩ H₁.V).ncard ≤ 2 → ∃ Δ' : Set S, Δ' ⊆ D ∧ IsDial H₁ F Δ')
    (hc : η.imageGraph = K ∨ {C | IsGraphCircuit K C}.ncard ≤ 1) :
    ∃ Γ : GraphDrawing K S, Γ.drawing.U ⊆ D ∧ Γ.drawing.U ∩ subBd D = g '' X ∧
      (∀ v : V(K), v.1 ∈ X → (Γ.iso.vertexEquiv v).1 = g v.1) ∧
      (∀ v ∈ H₁.V, graphDrawingVertexSet Γ (η.vMap v) = {v}) ∧
      ∀ e ∈ H₁.E, graphDrawingEdgeSet Γ (η.eMap e) = e := by
  classical
  by_cases hK : η.imageGraph = K
  · -- Here `K` is `η(H₁)`, so the drawing `H₁` itself is the answer.
    have key : ∀ K' : Graph α β, η.imageGraph = K' → ∃ ι : Iso H₁.toGraph K',
        (∀ v, (ι.vertexEquiv v).1 = η.vMap v.1) ∧ ∀ e, (ι.edgeEquiv e).1 = η.eMap e.1 := by
      rintro _ rfl
      exact η.exists_iso
    obtain ⟨ι, hιv, hιe⟩ := key K hK
    let Γ : GraphDrawing K S := ⟨H₁, isoSymm ι⟩
    have hsv : ∀ (v : α) (hv : v ∈ V(K)), η.vMap (Γ.iso.vertexEquiv ⟨v, hv⟩).1 = v := by
      intro v hv
      have := hιv (ι.vertexEquiv.symm ⟨v, hv⟩)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    have hVeq : V(η.imageGraph) = V(K) := congrArg _ hK
    have hEeq : E(η.imageGraph) = E(K) := congrArg _ hK
    have hmem : ∀ v ∈ H₁.V, η.vMap v ∈ V(K) := fun v hv =>
      hVeq.subset (η.bijOn_v.mapsTo hv)
    have hsv' : ∀ v (hv : v ∈ H₁.V) (hk : η.vMap v ∈ V(K)),
        (Γ.iso.vertexEquiv ⟨η.vMap v, hk⟩).1 = v := by
      intro v hv hk
      exact η.bijOn_v.injOn (Γ.iso.vertexEquiv ⟨η.vMap v, hk⟩).2 hv (hsv _ hk)
    refine ⟨Γ, hH₁D, ?_, ?_, ?_, ?_⟩
    · refine subset_antisymm ?_ ?_
      · rintro x ⟨hxU, hxb⟩
        have hxV := hH₁bd ⟨hxU, hxb⟩
        have hxX := (hXH x hxV).mp hxb
        exact ⟨_, hxX, hgH x hxV hxX⟩
      · rintro _ ⟨a, ha, rfl⟩
        have haV : a ∈ V(η.imageGraph) := hVeq.superset (hXK ha)
        obtain ⟨v, hv, rfl⟩ := η.bijOn_v.surjOn haV
        rw [hgH v hv ha]
        exact ⟨H₁.V_subset_U hv, (hXH v hv).mpr ha⟩
    · intro v hvX
      have h := hsv v.1 v.2
      have hx : (Γ.iso.vertexEquiv v).1 ∈ H₁.V := (Γ.iso.vertexEquiv v).2
      have h' := hgH _ hx (by rw [h]; exact hvX)
      rw [h] at h'
      exact h'.symm
    · intro v hv
      ext x
      simp only [graphDrawingVertexSet, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨hk, rfl⟩
        exact hsv' v hv hk
      · rintro rfl
        exact ⟨hmem x hv, hsv' x hv _⟩
    · intro e he
      have hk : η.eMap e ∈ E(K) := hEeq.subset (η.bijOn_e.mapsTo he)
      rw [graphDrawingEdgeSet_eq Γ hk]
      have h1 := hιe (ι.edgeEquiv.symm ⟨η.eMap e, hk⟩)
      rw [Equiv.apply_symm_apply] at h1
      exact η.bijOn_e.injOn (ι.edgeEquiv.symm ⟨η.eMap e, hk⟩).2 he h1.symm
  · -- Otherwise we draw `K` from scratch and move the drawing of `η(H₁)` onto `H₁` by (6.4).
    have hc' := hc.resolve_left hK
    obtain ⟨Y, hYU, hYbd, hYg⟩ := exists_disc_drawing hV hE hc' hD hXK hX hg
      (by rw [← hbdD]; exact hgD)
    rw [← hbdD] at hYbd
    exact extend_piece_drawing η hD hbdD hH₁D hH₁bd hXK hgD hXH hgH hrigid Y hYU hYbd hYg

end GraphMinor.GM14

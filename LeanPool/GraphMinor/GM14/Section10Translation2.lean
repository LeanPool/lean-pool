/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.GM14.PieceDrawing

public import LeanPool.GraphMinor.GM14.Section10Translation1
public import LeanPool.GraphMinor.GM14.Section7
public import LeanPool.GraphMinor.GM14.SegregationDrawing
import LeanPool.GraphMinor.GM11.Section810

/-!
# Graph Minors XIV – Section 10 Translation (Part 2: Extending the Drawing from a 3-Segregation)

This file proves the 3-segregation extension step of Section 10 of Graph Minors XIV (pages 49–50):
if `G` is a 4-connected graph, `H` is a rigid 2-cell drawing in a connected closed
non-spherical surface `S` with respectful tangle `T` of order `θ`, and `G` admits a `T`-local
3-segregation `S_seg` with an `H`-compatible arrangement `(α_disc, α_pt)` in `S`, then `G` has a
drawing `Γ_G : GraphDrawing G S` in `S` extending `H` (`H.IsSubdrawing Γ_G.drawing`).
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
open GraphMinor.GM11 GraphMinor.GM14.Whitney

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]

/-! ## 1. Finite Graphs on at Most 3 Vertices Have a Boundary Drawing and Piece Drawing -/

omit [T2Space S] in
/-- In a cyclic permutation `Ω` of at most 3 elements, for any two distinct `u, w ∈ Ω.bar`,
one of the two intervals `Ω.interval u w` or `Ω.interval w u` is empty. -/
theorem interval_eq_empty_or_swap_of_ncard_le_three (Ω : CyclicPerm α)
    (hcard : Ω.bar.ncard ≤ 3) {u w : α} (hu : u ∈ Ω.bar) (hw : w ∈ Ω.bar) (huw : u ≠ w) :
    Ω.interval u w = ∅ ∨ Ω.interval w u = ∅ := by
  by_contra! h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  have hxy : x ≠ y := fun h => Set.disjoint_left.mp (Ω.disjoint_interval_swap u w) hx (h ▸ hy)
  have hxu : x ≠ u := fun h => Ω.not_mem_interval_left u w (h ▸ hx)
  have hxw : x ≠ w := fun h => Ω.not_mem_interval_right u w (h ▸ hx)
  have hyu : y ≠ u := fun h => Ω.not_mem_interval_right w u (h ▸ hy)
  have hyw : y ≠ w := fun h => Ω.not_mem_interval_left w u (h ▸ hy)
  have hsub : ({x, y, u, w} : Set α) ⊆ Ω.bar := by
    rintro z (rfl | rfl | rfl | rfl)
    · exact Ω.interval_subset_bar u w hx
    · exact Ω.interval_subset_bar w u hy
    · exact hu
    · exact hw
  have hc4 : ({x, y, u, w} : Set α).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair huw]
    · simp [hyu, hyw]
    · simp [hxy, hxu, hxw]
  have hle := Set.ncard_le_ncard hsub Ω.finite_bar
  omega

omit [T2Space S] in
/-- Every finite graph `K` with a vertex and `V(K).ncard ≤ 3` has a rural drawing with all its
vertices on the boundary. -/
theorem exists_boundaryRural_of_ncard_le_three {K : Graph α β}
    (hV : V(K).Finite) (hE : E(K).Finite) (hc : V(K).ncard ≤ 3) (hne : V(K).Nonempty) :
    ∃ L, BoundaryRural K L := by
  let K₀ : Graph α β := K.restrict ∅
  have hVK₀ : V(K₀) = V(K) := vertexSet_restrict K ∅
  have hEK₀ : E(K₀) = ∅ := by simp [K₀, edgeSet_restrict]
  have hc₀ : {C : Graph α β | IsGraphCircuit K₀ C}.ncard ≤ 1 := by
    have hemp : {C : Graph α β | IsGraphCircuit K₀ C} = ∅ := by
      refine eq_empty_of_forall_notMem fun C hC => ?_
      obtain ⟨hCK₀, u, W, _, hpos, _, _⟩ := hC
      cases W with
      | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hpos
      | cons hl _ =>
        have he : _ ∈ E(K₀) := hCK₀.edgeSet_mono hl.edge_mem
        rw [hEK₀] at he
        exact he
    rw [hemp, Set.ncard_empty]
    omega
  obtain ⟨L, hL₀⟩ := exists_boundaryRural (hVK₀ ▸ hV) (hEK₀ ▸ finite_empty) hc₀ (hVK₀ ▸ hne)
  suffices hstep : ∀ (n : ℕ) (F : Set β), F ⊆ E(K) → F.ncard = n →
      BoundaryRural (K.restrict F) L by
    have hK_eq : K.restrict E(K) = K :=
      le_antisymm restrict_le ⟨by simp, fun {_ _ _} hl => ⟨hl.edge_mem, hl⟩⟩
    exact ⟨L, hK_eq ▸ hstep E(K).ncard E(K) Subset.rfl rfl⟩
  intro n
  induction n with
  | zero =>
    intro F hF hn
    have hF_fin : F.Finite := hE.subset hF
    have hF_empty : F = ∅ := (Set.ncard_eq_zero hF_fin).mp hn
    subst hF_empty
    exact hL₀
  | succ n ih =>
    intro F hF hn
    have hF_fin : F.Finite := hE.subset hF
    obtain ⟨e, heF⟩ := (Set.ncard_pos hF_fin).mp (by omega)
    let F' : Set β := F \ {e}
    have hF'_sub : F' ⊆ E(K) := sdiff_subset.trans hF
    have hF'_card : F'.ncard = n := by
      change (F \ {e}).ncard = n
      rw [Set.ncard_sdiff_singleton_of_mem heF, hn]
      omega
    have ih' := ih F' hF'_sub hF'_card
    let K' : Graph α β := K.restrict F'
    let K₁ : Graph α β := K.restrict F
    have hle : K' ≤ K₁ := ⟨by simp [K', K₁], fun {_ _ _} hl => ⟨sdiff_subset hl.1, hl.2⟩⟩
    have hV_eq : V(K₁) = V(K') := by simp [K', K₁, vertexSet_restrict]
    have hE_eq : E(K₁) = insert e E(K') := by
      ext f
      simp only [K', K₁, F', edgeSet_restrict, mem_inter_iff, mem_insert_iff, mem_sdiff,
        mem_singleton_iff]
      by_cases hfe : f = e
      · subst hfe
        exact ⟨fun _ => Or.inl rfl, fun _ => ⟨hF heF, heF⟩⟩
      · tauto
    have he_not : e ∉ E(K') := by simp [K', F', edgeSet_restrict]
    have hV₁_fin : V(K₁).Finite := by simpa [K₁, vertexSet_restrict] using hV
    have hE₁_fin : E(K₁).Finite := hE.subset (by simp [K₁, edgeSet_restrict])
    obtain ⟨u, w, hlK⟩ := K.exists_isLink_of_mem_edgeSet (hF heF)
    have hl₁ : K₁.IsLink e u w := ⟨heF, hlK⟩
    by_cases huw : u = w
    · subst huw
      exact ih'.add_loop hV₁_fin hE₁_fin hle hV_eq hE_eq he_not hl₁
    · obtain ⟨hLV, hnd, hne', _⟩ := id ih'
      have hbar_eq : (CyclicPerm.ofNodupList L hnd hne').bar = V(K) := by
        change {x | x ∈ L} = V(K)
        rw [hLV]
        exact vertexSet_restrict K F'
      have hu_bar : u ∈ (CyclicPerm.ofNodupList L hnd hne').bar := hbar_eq.symm ▸ hlK.left_mem
      have hw_bar : w ∈ (CyclicPerm.ofNodupList L hnd hne').bar := hbar_eq.symm ▸ hlK.right_mem
      rcases interval_eq_empty_or_swap_of_ncard_le_three
          (CyclicPerm.ofNodupList L hnd hne') (hbar_eq.symm ▸ hc) hu_bar hw_bar huw with hgap | hgap
      · exact ih'.add_edge hV₁_fin hE₁_fin hle hV_eq hE_eq he_not hl₁ huw (fun _ _ => hgap)
      · exact ih'.add_edge hV₁_fin hE₁_fin hle hV_eq hE_eq he_not hl₁.symm (Ne.symm huw) (fun _ _
          => hgap)

omit [T2Space S] in
/-- Every finite graph `K` with `V(K).ncard ≤ 3` can be drawn in the plane inside a closed disc `Δ`
with all its vertices on `subBd Δ`. -/
theorem exists_boundary_drawing_of_ncard_le_three {K : Graph α β}
    (hV : V(K).Finite) (hE : E(K).Finite) (hc : V(K).ncard ≤ 3) :
    ∃ (Γ : GraphDrawing K EuclideanPlane) (Δ : Set EuclideanPlane), IsClosedDisc Δ ∧
      Γ.drawing.U ⊆ Δ ∧ Γ.drawing.V ⊆ subBd Δ := by
  by_cases hne : V(K).Nonempty
  · obtain ⟨L, hL, hnd, hne', N, rfl, hΩ, -, Γ, Δ, Δ₀, hΔ, -, hU, hbd, -⟩ :=
      exists_boundaryRural_of_ncard_le_three hV hE hc hne
    refine ⟨Γ, Δ, hΔ, fun x hx => (hU hx).1, ?_⟩
    intro x hx
    let v := Γ.iso.vertexEquiv.symm ⟨x, hx⟩
    have hv : v.1 ∈ N.Ω.bar := by
      rw [hΩ]
      change v.1 ∈ {x | x ∈ L}
      rw [hL]
      exact v.2
    have hsub := (hbd v.1 v.2).mpr hv
    apply hsub
    refine ⟨v.2, ?_⟩
    simp [v]
  · have hVe : V(K) = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hEe : E(K) = ∅ := by
      refine eq_empty_of_forall_notMem fun f hf => ?_
      obtain ⟨x, y, hxy⟩ := K.exists_isLink_of_mem_edgeSet hf
      exact hne ⟨x, hxy.left_mem⟩
    obtain ⟨Γ, hU, _⟩ := GraphDrawing.of_edgeless (S := EuclideanPlane) hV hEe
      (ν := fun _ => 0) (by rw [hVe]; exact injOn_empty _)
    refine ⟨Γ, ClosedUnitDisc, ⟨Homeomorph.refl ClosedUnitDisc⟩, ?_, ?_⟩
    · rw [hU, hVe]
      simp
    · have : Γ.drawing.V ⊆ Γ.drawing.U := Γ.drawing.V_subset_U
      rw [hU, hVe, image_empty] at this
      exact this.trans (empty_subset _)

/-- A finite graph `K` with `V(K).ncard ≤ 3` can be drawn in a closed disc `D`, with a subset
`X ⊆ V(K)` of at most three vertices at given points of `discBd D` and nothing else on `discBd D`.
-/
theorem exists_disc_drawing_of_ncard_le_three {K : Graph α β}
    (hV : V(K).Finite) (hE : E(K).Finite) (hc : V(K).ncard ≤ 3)
    {D : Set S} (hD : IsClosedDisc D) {X : Set α}
    (hXK : X ⊆ V(K)) (hX : X.ncard ≤ 3) {g : α → S} (hg : InjOn g X)
    (hgD : MapsTo g X (discBd D)) :
    ∃ Γ : GraphDrawing K S, Γ.drawing.U ⊆ D ∧ Γ.drawing.U ∩ discBd D = g '' X ∧
      ∀ v : V(K), v.1 ∈ X → (Γ.iso.vertexEquiv v).1 = g v.1 := by
  classical
  obtain ⟨Y, Δ, hΔ, hYU, hYV⟩ := exists_boundary_drawing_of_ncard_le_three hV hE hc
  exact place_boundary_drawing hV Y hΔ hYU hYV hD hXK hX hg hgD

/-- Suppose `H₁` is drawn in the closed disc `D`, is a subgraph `η(H₁)` of `K`, is rigid in `D`,
and `V(K).ncard ≤ 3`. Then `K` has a drawing in `D` extending `H₁`, with the vertices of `X` at
given points of `subBd D` and nothing else on `subBd D`. -/
theorem exists_piece_drawing_of_ncard_le_three {H₁ : Drawing S} {K : Graph α β}
    (η : SpanEmbedding H₁ K) (hV : V(K).Finite) (hE : E(K).Finite) (hc : V(K).ncard ≤ 3)
    {D : Set S} (hD : IsClosedDisc D) (hbdD : subBd D = discBd D)
    (hH₁D : H₁.U ⊆ D) (hH₁bd : H₁.U ∩ subBd D ⊆ H₁.V)
    {X : Set α} (hXK : X ⊆ V(K)) (hX : X.ncard ≤ 3) {g : α → S} (hg : InjOn g X)
    (hgD : MapsTo g X (subBd D)) (hXH : ∀ v ∈ H₁.V, v ∈ subBd D ↔ η.vMap v ∈ X)
    (hgH : ∀ v ∈ H₁.V, η.vMap v ∈ X → g (η.vMap v) = v)
    (hrigid : ∀ F : Set S, F ⊆ D → IsOArc F → F ∩ H₁.U ⊆ H₁.V →
      (F ∩ H₁.V).ncard ≤ 2 → ∃ Δ' : Set S, Δ' ⊆ D ∧ IsDial H₁ F Δ') :
    ∃ Γ : GraphDrawing K S, Γ.drawing.U ⊆ D ∧ Γ.drawing.U ∩ subBd D = g '' X ∧
      (∀ v : V(K), v.1 ∈ X → (Γ.iso.vertexEquiv v).1 = g v.1) ∧
      (∀ v ∈ H₁.V, graphDrawingVertexSet Γ (η.vMap v) = {v}) ∧
      ∀ e ∈ H₁.E, graphDrawingEdgeSet Γ (η.eMap e) = e := by
  obtain ⟨Y, hYU, hYbd, hYg⟩ := exists_disc_drawing_of_ncard_le_three hV hE hc hD hXK hX hg
    (by rw [← hbdD]; exact hgD)
  rw [← hbdD] at hYbd
  exact extend_piece_drawing η hD hbdD hH₁D hH₁bd hXK hgD hXH hgH hrigid Y hYU hYbd hYg

/-- If `H` is rigid on a connected closed non-spherical surface `S` and `d ⊆ S` is a closed disc
with `subBd d ∩ H.U ⊆ H.V`, then `H.interSet d` is rigid inside `d`. -/
theorem isRigidIn_interSet_of_isRigid [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) {H : Drawing S} (hrig : IsRigid H)
    {d : Set S} (hd : IsClosedDisc d) (hbd : subBd d ∩ H.U ⊆ H.V) :
    ∀ F : Set S, F ⊆ d → IsOArc F → F ∩ (H.interSet d).U ⊆ (H.interSet d).V →
      (F ∩ (H.interSet d).V).ncard ≤ 2 → ∃ Δ' : Set S, Δ' ⊆ d ∧ IsDial (H.interSet d) F Δ' := by
  have hcl : IsClosed d := hd.isClosed
  obtain ⟨hV, hU⟩ := interSet_V_and_U hcl hbd
  intro F hFd hF hFn hFc
  have hFV : F ∩ (H.interSet d).V = F ∩ H.V := by
    rw [hV]
    ext x
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hFd h.1⟩⟩
  have hFn' : F ∩ H.U ⊆ H.V := by
    rintro x ⟨hx, hxU⟩
    have : x ∈ F ∩ (H.interSet d).U := ⟨hx, hU.superset ⟨hxU, hFd hx⟩⟩
    have := hFn this
    rw [hV] at this
    exact this.1
  obtain ⟨Δ, hΔd, hΔb, hor⟩ := hrig F hF hFn' (hFV ▸ hFc)
  have hbdΔ : discBd Δ = F := (IsClosedDisc.subBd_eq_discBd hS hΔd).symm.trans hΔb
  obtain ⟨D', ⟨hD'd, hD'disc, hbD', -⟩, -⟩ := disc_oArc d F hd hFd hF
  have hD'_eq : D' = Δ :=
    eq_of_discBd_eq (IsClosedSurface.isSurface hS) hns hD'disc hΔd (hbD'.trans hbdΔ.symm)
  have hsub : Δ ⊆ d := hD'_eq ▸ hD'd
  refine ⟨Δ, hsub, hΔd, hΔb, ?_⟩
  rcases hor with h | ⟨u, v, huv, hcap, hp⟩
  · left
    rw [hU]
    exact fun x hx => h ⟨hx.1, hx.2.1⟩
  · right
    refine ⟨u, v, huv, hFV.trans hcap, ?_⟩
    have heq : (H.interSet d).interSet Δ = H.interSet Δ := by
      have hE₁ : ((H.interSet d).interSet Δ).E = (H.interSet Δ).E := by
        rw [Whitney.interSet_E, Whitney.interSet_E, Whitney.interSet_E]
        ext e
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hsub⟩, h.2⟩⟩
      refine Drawing.ext_of_V_E ?_ hE₁
      ext x
      rw [GM11.mem_interSet_V_iff hΔd.isClosed, GM11.mem_interSet_V_iff hΔd.isClosed, hV]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hsub h.2⟩, h.2⟩⟩
    rwa [heq]

/-! ## 3. Extending the Drawing across a `T`-Local 3-Segregation -/

/-- **Lemma 3 (`exists_extending_drawing_of_threeSegregation`):** Under the hypotheses of (1.1),
if `G` is a 4-connected graph, `H` is rigid with a respectful tangle `T` of order `θ`, and
`S_seg` is a `T`-local 3-segregation of `G` with an `H`-compatible arrangement `(α_disc, α_pt)` in
`S`, then `G` has a drawing `Γ_G : GraphDrawing G S` in `S` such that `H.IsSubdrawing Γ_G.drawing`.
-/
theorem exists_extending_drawing_of_threeSegregation [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    (hG_4conn : 5 ≤ V(G).ncard ∧
      ∀ A B : Graph α β, IsGraphSeparation G A B → (V(A) ∩ V(B)).ncard < 4 →
        V(A) = V(G) ∨ V(B) = V(G))
    (hrig : IsRigid H) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T)
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hseg : IsThreeSegregation G S_seg)
    (hloc : IsTangleLocal G H η T S_seg)
    (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hcompat : IsCompatibleWith G H η S_seg α_disc α_pt) :
    ∃ Γ_G : GraphDrawing G S, H.IsSubdrawing Γ_G.drawing := by
  obtain ⟨hs, h3⟩ := id hseg
  have hmember : ∀ S₀ ∈ S_seg,
      ∃ Γ : GraphDrawing S₀.G S, Γ.drawing.U ⊆ α_disc S₀ ∧
        Γ.drawing.U ∩ subBd (α_disc S₀) = α_pt '' S₀.Ω.bar ∧
        (∀ v : V(S₀.G), v.1 ∈ S₀.Ω.bar → (Γ.iso.vertexEquiv v).1 = α_pt v.1) ∧
        (∀ v ∈ H.V, v ∈ α_disc S₀ → graphDrawingVertexSet Γ (η.vMap v) = {v}) ∧
        ∀ e ∈ H.E, e ⊆ α_disc S₀ → graphDrawingEdgeSet Γ (η.eMap e) = e := by
    intro S₀ hS₀
    have hle₀ : S₀.G ≤ G := hs.le S₀ hS₀
    obtain ⟨B, hsepB, hV_inter, _, _⟩ := exists_separation_of_segregation hs hS₀
    have hcard_lt : (V(S₀.G) ∩ V(B)).ncard < 4 := by
      rw [hV_inter]
      exact Nat.lt_succ_of_le (h3 S₀ hS₀)
    have hVB_eq : V(B) = V(G) := by
      rcases hG_4conn.2 S₀.G B hsepB hcard_lt with hVS₀ | hVB
      · exfalso
        obtain ⟨A_H, B_H, _, hAV, _, _, _, _, hmemT⟩ :=
          exists_tangle_separation_of_threeSegregation hseg hloc hS₀
        have hAV_eq : A_H.vertexSet = H.V := by
          rw [hAV]
          ext v
          simp only [mem_ofPred_eq, and_iff_left_iff_imp]
          intro hv
          rw [hVS₀]
          exact η.imageGraph_le.vertexSet_mono (η.bijOn_v.mapsTo hv)
        exact hT.2.1.axiom3 hmemT hAV_eq
      · exact hVB
    have hVS₀_eq : V(S₀.G) = S₀.Ω.bar := by
      rw [← hV_inter, hVB_eq, eq_comm, inter_eq_left]
      exact hle₀.vertexSet_mono
    have hVS₀_card : V(S₀.G).ncard ≤ 3 := hVS₀_eq ▸ h3 S₀ hS₀
    obtain ⟨hd, hbarpt⟩ := harr.isClosedDisc S₀ hS₀
    have hbdd : subBd (α_disc S₀) = discBd (α_disc S₀) := IsClosedDisc.subBd_eq_discBd hS hd
    obtain ⟨η₁, _, hv, he, hbd, hIV, hU, hn, hXH⟩ :=
      exists_compatible_pieceEmbedding hS₀ hle₀ hd.isClosed hcompat
    have hrig₁ := isRigidIn_interSet_of_isRigid hS hns hrig hd hbd
    obtain ⟨Γ, h₁, h₂, h₃', h₄, h₅⟩ := exists_piece_drawing_of_ncard_le_three η₁
      S₀.finite_V S₀.finite_E hVS₀_card hd hbdd hU hn
      S₀.bar_subset (h3 S₀ hS₀)
      (harr.injOn_pts.mono fun x hx => mem_iUnion₂.mpr ⟨S₀, hS₀, hx⟩) hbarpt hXH
      (fun v hv' h => by
        rw [hIV] at hv'
        rw [hv] at h ⊢
        exact hcompat.pt_eq v hv'.1 (mem_iUnion₂.mpr ⟨S₀, hS₀, h⟩))
      hrig₁
    refine ⟨Γ, h₁, h₂, h₃', fun v hv' hvd => ?_, fun e he' hed => ?_⟩
    · have := h₄ v (by rw [hIV]; exact ⟨hv', hvd⟩)
      rwa [hv] at this
    · have := h₅ e (by rw [Whitney.interSet_E]; exact ⟨he', hed⟩)
      rwa [he] at this
  choose Γs h₁ h₂ h₃ h₄ h₅ using hmember
  obtain ⟨Γ, ν, _, hv, _, hηv, hηe, _⟩ :=
    exists_drawing_of_compatible_members hs harr hcompat Γs h₁ h₂ h₃ h₄ h₅
  refine ⟨Γ, ⟨?_, ?_⟩⟩
  · intro v hv'
    have hvG : η.vMap v ∈ V(G) := η.imageGraph_le.vertexSet_mono (η.bijOn_v.mapsTo hv')
    have heq := (hv ⟨η.vMap v, hvG⟩).trans (hηv v hv')
    exact heq ▸ (Γ.iso.vertexEquiv ⟨η.vMap v, hvG⟩).2
  · intro e he'
    have heG : η.eMap e ∈ E(G) := η.imageGraph_le.edgeSet_mono (η.bijOn_e.mapsTo he')
    have heq := (graphDrawingEdgeSet_eq Γ heG).symm.trans (hηe e he')
    exact heq ▸ (Γ.iso.edgeEquiv ⟨η.eMap e, heG⟩).2

end GraphMinor.GM14

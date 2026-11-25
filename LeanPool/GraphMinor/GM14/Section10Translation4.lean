/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section10Translation1
public import LeanPool.GraphMinor.GM14.Section10Translation2
public import LeanPool.GraphMinor.GM14.Section10Translation3
public import LeanPool.GraphMinor.GM14.Adapted
import LeanPool.GraphMinor.GM14.DiscTangleSep
import LeanPool.GraphMinor.GM14.RigidGood
import LeanPool.GraphMinor.GM14.Section7a
import LeanPool.GraphMinor.GM11.Theorem64
import LeanPool.GraphMinor.Surface.Epstein

/-!
# Graph Minors XIV – Section 10 Translation (Part 4: Eye Obstruction and Main Translation)

This file completes the translation between the hypotheses and conclusions of Graph Minors XIV,
(1.1) (pages 24–25) and (4.1) (pages 30–31):
- `isSubdivisionOfSimpleThreeConnected_clearedSubdrawing_of_drawingEye`: for a 39-zone `Λ₀` around
  `z` such that `H' = H ∩ (Σ - Λ₀)` is rigid and `Λ₀` is an eye of `H'` in `G` with respect to the
  cleared tangle `T'` of order `51`, the graph of `H'` is a subdivision of a simple 3-connected
  graph (`(1.1)(iii)(i)`).
- `four_le_subBd_diff_zone_encard`: for any closed disc `Δ ⊆ Σ` containing `{a, b, c, d}`,
  `4 ≤ ((bd(Δ) \ Λ₀) ∩ U(H)).encard` (`(1.1)(iii)(iii)`).
- `eye_obstruction_of_drawingEye`: combines `(1.1)(iii)(i)–(iv)` when a 39-zone `Λ` is an eye of
  `H ∩ (Σ - Λ)` in `G` with respect to the cleared tangle `T'`.
- `theorem11TranslationStatement_proved`: proves `Theorem11TranslationStatement`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14.Whitney

universe u v w

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Basic Facts on `clearedSubdrawing` -/

omit [T2Space S] in
theorem clearedSubdrawing_E [T1Space S] (H : Drawing S) (Λ : Set S) :
    (clearedSubdrawing H Λ).E = {e | e ∈ H.E ∧ e ⊆ univ \ Λ} := by
  change (H.span _ _).E = _
  rw [H.span_E]
  ext e
  simp only [mem_inter_iff, mem_ofPred_eq]
  tauto

theorem clearedSubdrawing_V {H : Drawing S} {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ) :
    (clearedSubdrawing H Λ).V = H.V \ Λ := by
  apply subset_antisymm
  · intro x hx
    have hxH : x ∈ H.V := (clearedSubdrawing_isSubdrawing H Λ).1 hx
    have hxU : x ∈ (clearedSubdrawing H Λ).U := (clearedSubdrawing H Λ).V_subset_U hx
    rw [clearedSubdrawing_U hZone] at hxU
    exact ⟨hxH, hxU.2⟩
  · rintro x ⟨hxV, hxΛ⟩
    exact Or.inl ⟨⟨hxV, mem_univ _, hxΛ⟩, hxV⟩

omit [T2Space S] in
theorem clearedSubdrawing_no_loop [T1Space S] {H : Drawing S} {Λ : Set S}
    (hnl : ∀ e v, ¬ H.toGraph.IsLink e v v) :
    ∀ e v, ¬ (clearedSubdrawing H Λ).toGraph.IsLink e v v := by
  intro e v hl
  have hs := clearedSubdrawing_isSubdrawing H Λ
  refine hnl e v ⟨hs.2 hl.1, hs.1 hl.2.1, hs.1 hl.2.2.1, ?_⟩
  rw [← hs.closure_inter_V hl.1]
  exact hl.2.2.2

/-! ## 2. Tangle Dials and Threads on a Non-Spherical Surface -/

theorem rad_normal_arc {J Γ' : Drawing S} (r : Rad J Γ') (hS : IsClosedSurface S)
    {A : Set (Set S)} (hA : A ⊆ J.E) {F : Set S}
    (hFN : F ⊆ (boundaryDrawing Γ' (tiles Γ' A)).U) :
    F ∩ J.U ⊆ J.V ∧ F ∩ J.V ⊆ Whitney.bdry J.toGraph A := by
  have hNs : (boundaryDrawing Γ' (tiles Γ' A)).IsSubdrawing Γ' := Drawing.span_isSubdrawing Γ' _ _
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have : x ∈ J.U ∩ Γ'.U := ⟨hx.2, hNs.U_subset (hFN hx.1)⟩
    rwa [r.cap] at this
  · have hxN : x ∈ (boundaryDrawing Γ' (tiles Γ' A)).V := by
      rcases hFN hx.1 with h₁ | h₁
      · exact h₁
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp h₁
        exact Or.inr (mem_iUnion₂.mpr ⟨e, he, hxe, r.vsub hx.2⟩)
    exact r.mem_bdry hS hx.2 hxN hA

theorem holder_inner_edges_self {J : Drawing S} {F D : Set S} {x y : S}
    (h : Holder J univ F D x y) (hS : IsClosedSurface S)
    {v : S} (hv : v ∈ (J.interSet D).V) (hx : v ≠ x) (hy : v ≠ y) :
    ∀ g ∈ J.E, J.toGraph.Inc g v → g ∈ (J.interSet D).E := by
  have hi := h.inner hS hv hx hy
  intro g hg hinc
  have hc := mem_closure_of_inc hinc
  obtain ⟨q, hqi, hqg⟩ := mem_closure_iff.mp hc _ isOpen_interior hi
  exact mem_interSet_E.mpr ⟨hg, h.meets hS hg ⟨q, hqg, interior_subset hqi⟩⟩

/-- Each edge of a set `A ⊆ J.E` with `|bdry(A)| ≤ 2` and `(drawingEdgeSepA J A, drawingEdgeSepB J
A) ∈ T'`
lies in a dial bounded by a circuit of `N(tiles Γ' A)` that holds a path of `J`. -/
theorem exists_dial_of_edge_tangle [ConnectedSpace S] {J Γ' : Drawing S} {θ : ℕ}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins' : Drawing S → Set S}
    (r : Rad J Γ') (hrig : IsRigid J) (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    (hd' : IsDerivedSlope (PaintingOrDrawing.drawing J) Γ' θ T' ins')
    (hT_eq : T' = inducedPretangle (PaintingOrDrawing.drawing J) Γ' θ ins')
    {A : Set (Set S)} (hA : A ⊆ J.E) (hb : (Whitney.bdry J.toGraph A).ncard ≤ 2)
    (hmem : (drawingEdgeSepA J A, drawingEdgeSepB J A) ∈ T')
    {e : Set S} (he : e ∈ A) :
    ∃ F D x y, IsOArc F ∧ F ⊆ (boundaryDrawing Γ' (tiles Γ' A)).U ∧
      IsClosedDisc D ∧ discBd D = F ∧ e ⊆ D ∧ x ≠ y ∧ F ∩ J.V = {x, y} ∧
      (J.interSet D).IsPathBetween x y ∧ F ∩ J.U ⊆ J.V ∧
      F ∩ J.V ⊆ Whitney.bdry J.toGraph A := by
  have hmem_ind : (drawingEdgeSepA J A, drawingEdgeSepB J A) ∈
      inducedPretangle (PaintingOrDrawing.drawing J) Γ' θ ins' := hT_eq ▸ hmem
  have hreg_eq : PaintingOrDrawing.regionsIncludingEdge Γ' (drawingEdgeSepA J A) = tiles Γ' A := by
    ext s
    simp only [PaintingOrDrawing.regionsIncludingEdge, tiles, drawingEdgeSepA,
      inter_eq_self_of_subset_left hA]
  have hsmall : IsSmall Γ' ins' (2 * θ) J.V θ (tiles Γ' A) := by
    have hs := hmem_ind.2.2
    rwa [hreg_eq] at hs
  obtain ⟨s, hs, hes⟩ := r.exists_tile (hA he)
  have hsZ : s ∈ tiles Γ' A := ⟨hs, e, he, hes⟩
  obtain ⟨C₁, hC₁, hC₁N, hlen, hs_ins⟩ := hsmall.2 s hsZ
  have hNs : (boundaryDrawing Γ' (tiles Γ' A)).IsSubdrawing Γ' := Drawing.span_isSubdrawing Γ' _ _
  have hC₁Γ' : C₁.IsSubdrawing Γ' := hC₁N.trans hNs
  obtain ⟨hdisc, hbd_sub, -⟩ := hd' C₁ hC₁ hC₁Γ' hlen
  set F := C₁.U
  set D := ins' C₁
  have hF : IsOArc F := IsCircuit.isOArc_U hC₁
  have hFN : F ⊆ (boundaryDrawing Γ' (tiles Γ' A)).U := hC₁N.U_subset
  obtain ⟨h₁, h₂⟩ := rad_normal_arc r hS hA hFN
  have hbfin : (Whitney.bdry J.toGraph A).Finite :=
    J.finite_V.subset (fun _ ⟨⟨_, _, hi⟩, _⟩ => hi.vertex_mem)
  have hFV_le : (F ∩ J.V).ncard ≤ 2 := (ncard_le_ncard h₂ hbfin).trans hb
  obtain ⟨D', hdisc', hbd', hcases⟩ := hrig F hF h₁ hFV_le
  have hbd : discBd D = F := (IsClosedDisc.subBd_eq_discBd hS hdisc).symm.trans hbd_sub
  have hbd_D' : discBd D' = F := (IsClosedDisc.subBd_eq_discBd hS hdisc').symm.trans hbd'
  have hDD' : D = D' :=
    eq_of_discBd_eq (IsClosedSurface.isSurface hS) hns hdisc hdisc' (hbd.trans hbd_D'.symm)
  subst hDD'
  have heD : e ⊆ D := hes.trans hs_ins
  obtain ⟨p, hp⟩ := (hA he).1
  have hpD : p ∈ D := heD hp
  have heF : Disjoint e F := disjoint_left.mpr fun x hx hxF =>
    Whitney.edge_notMem_V (hA he) hx (h₁ ⟨hxF, J.closure_subset_U (hA he) (subset_closure hx)⟩)
  rcases hcases with h₃ | ⟨x, y, hxy, hc, hpath⟩
  · exact absurd (h₃ ⟨hpD, J.closure_subset_U (hA he) (subset_closure hp)⟩)
      (disjoint_left.mp heF hp)
  · exact ⟨F, D, x, y, hF, hFN, hdisc, hbd, heD, hxy, hc, hpath, h₁, h₂⟩

/-- Two paths of dials with an edge in only one of them and whose union is null-homotopic cannot
both exist. -/
theorem no_two_paths_tangle [ConnectedSpace S] {J Γ' : Drawing S} {θ : ℕ}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins' : Drawing S → Set S}
    (r : Rad J Γ') (hrig : IsRigid J) (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    (h2cell : (PaintingOrDrawing.drawing J).IsTwoCell)
    (hT : IsPretangle (PaintingOrDrawing.drawing J).toHypergraph θ T')
    (hresp : (PaintingOrDrawing.drawing J).IsRespectful θ T')
    (hd' : IsDerivedSlope (PaintingOrDrawing.drawing J) Γ' θ T' ins')
    (hT_eq : T' = inducedPretangle (PaintingOrDrawing.drawing J) Γ' θ ins')
    (hθ : 3 ≤ θ)
    {F D F' D' : Set S} {x y : S}
    (h₁ : Holder J univ F D x y) (h₂ : Holder J univ F' D' x y)
    {e e' : Set S} (he : e ∈ (J.interSet D).E) (he' : e' ∈ (J.interSet D').E)
    (hne : e' ∉ (J.interSet D).E)
    (hdisj_K : Disjoint (J.interSet D').E (J.interSet D).E →
      (J.interSet D).V ∩ (J.interSet D').V = {x, y} →
      IsNullHomotopicOArc (J.sup (J.interSet D) (J.interSet D')).U) : False := by
  classical
  set P := J.interSet D
  set P' := J.interSet D'
  have hPs : P.IsSubdrawing J := Drawing.span_isSubdrawing J _ _
  have hPs' : P'.IsSubdrawing J := Drawing.span_isSubdrawing J _ _
  have hxy := h₁.ne
  obtain ⟨hV, hE, hK⟩ := h₁.paths_form_circuit hS h₂ he' hne
  let K := J.sup P P'
  have hKU : K.U = P.U ∪ P'.U := sup_U hPs hPs'
  have hKE : K.E = P.E ∪ P'.E := Drawing.sup_E hPs hPs'
  have hKs : K.IsSubdrawing J := Drawing.sup_isSubdrawing _ _ _
  have hKarc : IsOArc K.U := IsCircuit.isOArc_U hK
  have hKnull : IsNullHomotopicOArc K.U := hdisj_K hE.symm hV
  obtain ⟨E₀, -, hE₀, hbE⟩ := epstein_first (IsClosedSurface.isSurface hS) hKarc (subset_univ _)
    (disjoint_left.mpr fun x _ hbd => hbd (hS.2.2 x)) hKnull
  have hfrE : frontier E₀ = K.U := (IsClosedDisc.frontier_eq_discBd hS hE₀).trans hbE
  have hKE₀ : K.U ⊆ E₀ := hbE ▸ Surface.discBd_subset E₀
  let A' : Set (Set S) := {g | g ∈ J.E ∧ g ⊆ E₀}
  have hKA' : K.E ⊆ A' := fun g hg =>
    ⟨hKs.2 hg, (K.closure_subset_U hg).trans hKE₀ |>.trans' subset_closure⟩
  have hinA : ∀ {g q}, g ∈ J.E → q ∈ g → q ∈ interior E₀ → g ∈ A' := by
    intro g q hg hq hqi
    by_cases hgK : g ∈ K.E
    · exact hKA' hgK
    · refine ⟨hg, ?_⟩
      have hdisj : Disjoint g K.U := edge_disjoint_U hKs hg hgK
      rcases subset_or_disjoint_of_frontier hE₀.isClosed hg.2.2.1.isConnected.isPreconnected
        (by rwa [hfrE]) with h₃ | h₃
      · exact h₃
      · exact absurd (interior_subset hqi) (disjoint_left.mp h₃ hq)
  have hBoundaryEdges : ∀ {v g}, v ∈ J.V → v ∈ K.U → v ≠ x → v ≠ y →
      g ∈ J.E → J.toGraph.Inc g v → g ∈ K.E := by
    intro v g' hvJ hvK hvx hvy hg'J hg'i
    rw [hKU] at hvK
    rcases hvK with hv | hv
    · have hvP : v ∈ P.V := by
        rw [(h₁.VU hS).1]
        rw [(h₁.VU hS).2] at hv
        exact ⟨hvJ, hv.2⟩
      exact hKE ▸ Or.inl (holder_inner_edges_self h₁ hS hvP hvx hvy g' hg'J hg'i)
    · have hvP : v ∈ P'.V := by
        rw [(h₂.VU hS).1]
        rw [(h₂.VU hS).2] at hv
        exact ⟨hvJ, hv.2⟩
      exact hKE ▸ Or.inr (holder_inner_edges_self h₂ hS hvP hvx hvy g' hg'J hg'i)
  obtain ⟨hbdry, htile⟩ := enclosed_edges_boundary_and_tiles (A' := A') r hE₀.isClosed hfrE hKs
    (fun _ h => h.2) hKA' hinA hBoundaryEdges
  have hbc : (Whitney.bdry J.toGraph A').ncard ≤ 2 :=
    (ncard_le_ncard hbdry (toFinite _)).trans (ncard_pair hxy).le
  have hA'J : A' ⊆ J.E := fun _ hg => hg.1
  have heA' : e ∈ A' := hKA' (hKE ▸ Or.inl he)
  -- Show `(drawingEdgeSepA J A', drawingEdgeSepB J A') ∈ T'` via (6.4).
  have hsepA' : (PaintingOrDrawing.drawing J).toHypergraph.IsSeparation
      (drawingEdgeSepA J A') (drawingEdgeSepB J A') :=
    isSeparation_drawingEdgeSep J A'
  have hordA' : separationOrder (drawingEdgeSepA J A') (drawingEdgeSepB J A') < θ := by
    change (drawingEdgeSepA J A' ∩ drawingEdgeSepB J A').vertexSet.ncard < θ
    rw [inter_vertexSet_drawingEdgeSep]
    omega
  have hundA' : PaintingOrDrawing.underlying (drawingEdgeSepA J A') ⊆ E₀ := by
    rintro z (⟨g, hgA', hinc⟩ | ⟨g, hgA', hzg⟩)
    · exact closure_minimal hgA'.2 hE₀.isClosed (mem_closure_of_inc hinc)
    · exact hgA'.1.2 hzg
  have hmemA' : (drawingEdgeSepA J A', drawingEdgeSepB J A') ∈ T' := by
    have h64 := (GM11.theorem_6_4_proof hS hns h2cell hT hresp).1
      (drawingEdgeSepA J A') (drawingEdgeSepB J A') hsepA' hordA'
    exact h64.1.mpr fun F₀ hF₀A' hF₀ =>
      isNullHomotopicOArcIn_of_subset_disc hF₀ (subset_univ _) hE₀ (hF₀A'.trans hundA')
  obtain ⟨F₁, D₁, x₁, y₁, hF₁, hF₁N, hD₁, hbD₁, heD₁, hxy₁, hcap₁, hpath₁, hn₁, -⟩ :=
    exists_dial_of_edge_tangle r hrig hS hns hd' hT_eq hA'J hbc hmemA' heA'
  have hF₁int := radial_boundary_disjoint_interior hS hF₁N htile
  have hfrD₁ : frontier D₁ = F₁ := (IsClosedDisc.frontier_eq_discBd hS hD₁).trans hbD₁
  have hInt : E₀ \ frontier E₀ ⊆ interior E₀ := fun z hz => by
    by_contra hn
    exact hz.2 ⟨subset_closure hz.1, hn⟩
  obtain ⟨p, hp⟩ := (hPs.2 he).1
  have hpF₁ : p ∉ F₁ := fun h' => by
    have hh : p ∈ J.U := J.closure_subset_U (hPs.2 he) (subset_closure hp)
    exact Whitney.edge_notMem_V (hPs.2 he) hp (hn₁ ⟨h', hh⟩)
  have hpi : p ∈ interior D₁ := by
    by_contra hn
    exact hpF₁ (hfrD₁ ▸ ⟨subset_closure (heD₁ hp), hn⟩)
  have hpE₀ : p ∈ E₀ := hKE₀ (hKU ▸ Or.inl (P.closure_subset_U he (subset_closure hp)))
  have hsubInt : E₀ \ frontier E₀ ⊆ D₁ := by
    rcases subset_or_disjoint_of_frontier hD₁.isClosed
      (IsClosedDisc.isPreconnected_diff_frontier hS hE₀)
      (by
        rw [hfrD₁]
        exact disjoint_left.mpr fun z hz hzF => disjoint_left.mp hF₁int hzF (hInt hz)) with h₃ | h₃
    · exact h₃
    · exfalso
      obtain ⟨q, hqi, hqm⟩ := mem_closure_iff.mp
        (IsClosedDisc.subset_closure_diff_frontier hS hE₀ hpE₀) _ isOpen_interior hpi
      exact disjoint_left.mp h₃ hqm (interior_subset hqi)
  have hE₀D₁ : E₀ ⊆ D₁ := (IsClosedDisc.subset_closure_diff_frontier hS hE₀).trans
    (closure_minimal hsubInt hD₁.isClosed)
  have hh₁ : Holder J univ F₁ D₁ x₁ y₁ := ⟨hD₁, subset_univ _, hbD₁, hxy₁, hcap₁, hpath₁, hn₁⟩
  have hline₁ := isLine_of_isPathBetween hpath₁ hxy₁
  refine not_oArc_subset_line hKarc hline₁ fun z hz => ?_
  rw [(hh₁.VU hS).2]
  exact ⟨hKs.U_subset hz, hE₀D₁ (hKE₀ hz)⟩

/-- A nonempty edge set `A ⊆ J.E` with `|bdry(A)| ≤ 2` and `(drawingEdgeSepA J A, drawingEdgeSepB J
A) ∈ T'`
is the edge set of a path of `J`. -/
theorem exists_thread_tangle [ConnectedSpace S] {J Γ' : Drawing S} {θ : ℕ}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins' : Drawing S → Set S}
    (r : Rad J Γ') (hrig : IsRigid J) (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    (h2cell : (PaintingOrDrawing.drawing J).IsTwoCell)
    (hT : IsPretangle (PaintingOrDrawing.drawing J).toHypergraph θ T')
    (hresp : (PaintingOrDrawing.drawing J).IsRespectful θ T')
    (hd' : IsDerivedSlope (PaintingOrDrawing.drawing J) Γ' θ T' ins')
    (hT_eq : T' = inducedPretangle (PaintingOrDrawing.drawing J) Γ' θ ins')
    (hθ : 3 ≤ θ)
    {A : Set (Set S)} (hA : A ⊆ J.E) (hb : (Whitney.bdry J.toGraph A).ncard ≤ 2)
    (hmem : (drawingEdgeSepA J A, drawingEdgeSepB J A) ∈ T') (hne : A.Nonempty) :
    ∃ (x y : S) (P : Drawing S), x ≠ y ∧ Whitney.bdry J.toGraph A = {x, y} ∧
      P.IsSubdrawing J ∧ P.IsPathBetween x y ∧ P.E = A ∧
      (∀ v ∈ P.V, v ≠ x → v ≠ y → ∀ g ∈ J.E, J.toGraph.Inc g v → g ∈ P.E) := by
  classical
  obtain ⟨e₀, he₀⟩ := hne
  have hbfin : (Whitney.bdry J.toGraph A).Finite :=
    J.finite_V.subset (fun _ ⟨⟨_, _, hi⟩, _⟩ => hi.vertex_mem)
  have key : ∀ e ∈ A, ∃ F D x y, Holder J univ F D x y ∧ e ∈ (J.interSet D).E ∧
      Whitney.bdry J.toGraph A = {x, y} ∧ (J.interSet D).E ⊆ A := by
    intro e he
    obtain ⟨F, D, x, y, hF, -, hD, hbd, heD, hxy, hcap, hpath, hn, hsub⟩ :=
      exists_dial_of_edge_tangle r hrig hS hns hd' hT_eq hA hb hmem he
    have hh : Holder J univ F D x y := ⟨hD, subset_univ _, hbd, hxy, hcap, hpath, hn⟩
    have heP : e ∈ (J.interSet D).E := mem_interSet_E.mpr ⟨hA he, heD⟩
    have hbd_eq : Whitney.bdry J.toGraph A = {x, y} := by
      have h₁ : ({x, y} : Set S) ⊆ Whitney.bdry J.toGraph A := hcap ▸ hsub
      exact (eq_of_subset_of_ncard_le h₁ (by rw [ncard_pair hxy]; exact hb) hbfin).symm
    refine ⟨F, D, x, y, hh, heP, hbd_eq, ?_⟩
    obtain ⟨W, hs, hV, hE⟩ := hpath
    intro g hg
    have hPs : (J.interSet D).IsSubdrawing J := Drawing.span_isSubdrawing J _ _
    have hg' : g ∈ W.edges := by rw [hE] at hg; exact hg
    have he' : e ∈ W.edges := by rw [hE] at heP; exact heP
    refine walk_same_side hPs.1 hPs.2 W hs (fun v _ h₃ h₄ hvb => ?_) e he' g hg' he
    rw [hbd_eq] at hvb
    rcases hvb with h₅ | h₅
    · exact h₃ h₅
    · exact h₄ h₅
  obtain ⟨F, D, x, y, h₁, he₀P, hbd, hPE_sub⟩ := key e₀ he₀
  have hsepA : (PaintingOrDrawing.drawing J).toHypergraph.IsSeparation
      (drawingEdgeSepA J A) (drawingEdgeSepB J A) :=
    isSeparation_drawingEdgeSep J A
  have hordA : separationOrder (drawingEdgeSepA J A) (drawingEdgeSepB J A) < θ := by
    change (drawingEdgeSepA J A ∩ drawingEdgeSepB J A).vertexSet.ncard < θ
    rw [inter_vertexSet_drawingEdgeSep]
    omega
  have hnull_of_A : ∀ {P₁ P₂ : Drawing S}, P₁.IsSubdrawing J → P₂.IsSubdrawing J →
      P₁.IsPathBetween x y → P₂.IsPathBetween x y →
      P₁.V ∩ P₂.V = {x, y} → Disjoint P₁.E P₂.E →
      P₁.E ⊆ A → P₂.E ⊆ A →
      IsNullHomotopicOArc (J.sup P₁ P₂).U := by
    intro P₁ P₂ hPs₁ hPs₂ hp₁ hp₂ hV₁₂ hE₁₂ hsub₁ hsub₂
    let K := J.sup P₁ P₂
    have hK : K.IsCircuit := Drawing.isCircuit_sup hp₁ hp₂ hPs₁ hPs₂ h₁.ne hV₁₂ hE₁₂
    have hKE : K.E = P₁.E ∪ P₂.E := Drawing.sup_E hPs₁ hPs₂
    have hKA : K.E ⊆ A := hKE ▸ union_subset hsub₁ hsub₂
    have hKs : K.IsSubdrawing J := ⟨by
      rw [Drawing.sup_V hPs₁ hPs₂]
      exact union_subset hPs₁.1 hPs₂.1, hKA.trans hA⟩
    have hund : K.U ⊆ PaintingOrDrawing.underlying (drawingEdgeSepA J A) := by
      intro z hz
      rw [Drawing.U_eq] at hz
      rcases hz with hz | hz
      · obtain ⟨e₁, he₁K, hinc₁⟩ : ∃ e₁ ∈ K.E, J.toGraph.Inc e₁ z := by
          obtain ⟨u, W, -, hpos, hCV, hCE⟩ := hK
          have hzW : z ∈ W.support := by rw [hCV] at hz; exact hz
          obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hzW
          set Rot := W₂.append W₁
          have hlen : 0 < Rot.length := by
            rw [GraphWalk.length_append]
            rw [GraphWalk.length_append] at hpos
            omega
          cases hR : Rot with
          | nil => simp [hR, GraphWalk.length] at hlen
          | @cons _ w₁ _ e₁ hl₁ rest =>
            have he₁R : e₁ ∈ Rot.edges := by simp [hR]
            have he₁W : e₁ ∈ (W₁.append W₂).edges := by
              rw [GraphWalk.edges_append, List.mem_append] at he₁R ⊢
              exact he₁R.symm
            have he₁C : e₁ ∈ K.E := by rw [hCE]; exact he₁W
            have hinc : J.toGraph.Inc e₁ z :=
              ⟨w₁, hKs.2 hl₁.1, hKs.1 hl₁.2.1, hKs.1 hl₁.2.2.1, by
                rw [← hKs.closure_inter_V hl₁.1]; exact hl₁.2.2.2⟩
            exact ⟨e₁, he₁C, hinc⟩
        exact Or.inl ⟨e₁, hKA he₁K, hinc₁⟩
      · obtain ⟨g, hgK, hzg⟩ := mem_iUnion₂.mp hz
        by_cases hzV : z ∈ J.V
        · exact Or.inl ⟨g, hKA hgK, inc_of_mem_closure (hKs.2 hgK) hzg hzV⟩
        · have hzg' : z ∈ g := by
            rw [← J.closure_diff_V (hKs.2 hgK)]
            exact ⟨hzg, hzV⟩
          exact Or.inr ⟨g, ⟨hKA hgK, hKs.2 hgK⟩, hzg'⟩
    have h64 := (GM11.theorem_6_4_proof hS hns h2cell hT hresp).1
      (drawingEdgeSepA J A) (drawingEdgeSepB J A) hsepA hordA
    exact h64.1.mp hmem K.U hund (IsCircuit.isOArc_U hK)
  refine ⟨x, y, J.interSet D, h₁.ne, hbd, Drawing.span_isSubdrawing J _ _, h₁.path,
    subset_antisymm hPE_sub ?_, fun v hv h₃ h₄ => holder_inner_edges_self h₁ hS hv h₃ h₄⟩
  intro e he
  by_contra hn
  obtain ⟨F', D', x', y', h₂, heP, hbd', hPE'_sub⟩ := key e he
  have hset : ({x, y} : Set S) = {x', y'} := hbd.symm.trans hbd'
  have hx' : x ∈ ({x', y'} : Set S) := hset ▸ Or.inl rfl
  rcases hx' with rfl | hx'
  · have hy' : y' = y := by
      have : y' ∈ ({x, y} : Set S) := hset ▸ Or.inr rfl
      rcases this with h₃ | h₃
      · exact absurd h₃.symm h₂.ne
      · exact h₃
    subst hy'
    exact no_two_paths_tangle r hrig hS hns h2cell hT hresp hd' hT_eq hθ h₁ h₂ he₀P heP hn
      (fun hdisj hV => hnull_of_A (Drawing.span_isSubdrawing J _ _)
        (Drawing.span_isSubdrawing J _ _)
        h₁.path h₂.path hV hdisj.symm hPE_sub hPE'_sub)
  · obtain rfl : x = y' := hx'
    have hy' : x' = y := by
      have : x' ∈ ({x, y} : Set S) := hset ▸ Or.inl rfl
      rcases this with h₃ | h₃
      · exact absurd h₃ h₂.ne
      · exact h₃
    subst hy'
    have h₂' : Holder J univ F' D' x x' := ⟨h₂.disc, h₂.sub, h₂.bd, h₁.ne, by
      rw [pair_comm]; exact h₂.cap, isPathBetween_symm h₂.path, h₂.norm⟩
    exact no_two_paths_tangle r hrig hS hns h2cell hT hresp hd' hT_eq hθ h₁ h₂' he₀P heP hn
      (fun hdisj hV => hnull_of_A (Drawing.span_isSubdrawing J _ _)
        (Drawing.span_isSubdrawing J _ _)
        h₁.path h₂'.path hV hdisj.symm hPE_sub hPE'_sub)

/-- If `(drawingEdgeSepA J E(G₂), drawingEdgeSepB J E(G₂)) ∈ T'` for a separation `(G₁, G₂)` of
`J.toGraph` of order `≤ 2`, then `Thin J.toGraph G₂ G₁`. -/
theorem thin_of_edge_tangle [ConnectedSpace S] {J Γ' : Drawing S} {θ : ℕ}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins' : Drawing S → Set S}
    (r : Rad J Γ') (hrig : IsRigid J) (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    (h2cell : (PaintingOrDrawing.drawing J).IsTwoCell)
    (hT : IsPretangle (PaintingOrDrawing.drawing J).toHypergraph θ T')
    (hresp : (PaintingOrDrawing.drawing J).IsRespectful θ T')
    (hd' : IsDerivedSlope (PaintingOrDrawing.drawing J) Γ' θ T' ins')
    (hT_eq : T' = inducedPretangle (PaintingOrDrawing.drawing J) Γ' θ ins')
    (hθ : 3 ≤ θ)
    {G₁ G₂ : Graph S (Set S)} (hs : IsGraphSeparation J.toGraph G₁ G₂)
    (hord : (V(G₁) ∩ V(G₂)).ncard ≤ 2)
    (hmem : (drawingEdgeSepA J E(G₂), drawingEdgeSepB J E(G₂)) ∈ T') :
    Thin J.toGraph G₂ G₁ := by
  obtain ⟨hl₁, hl₂, hV, hE, hdis⟩ := id hs
  set X := V(G₁) ∩ V(G₂) with hX
  have hXfin : X.Finite := J.finite_V.subset fun z hz => hl₁.vertexSet_mono hz.1
  have hside : ∀ {v g}, v ∈ V(G₂) → v ∉ X → g ∈ J.E → J.toGraph.Inc g v → g ∈ E(G₂) := by
    intro v g h₁ h₂ hg hi
    have : g ∈ E(G₁) ∪ E(G₂) := hE ▸ hg
    rcases this with h₃ | h₃
    · exact absurd ⟨mem_V_of_closure hl₁ h₃ (mem_closure_of_inc hi) hi.vertex_mem, h₁⟩ h₂
    · exact h₃
  have hbX : Whitney.bdry J.toGraph E(G₂) ⊆ X := by
    rintro v ⟨⟨g, hg, hi⟩, ⟨g', ⟨hg', hgA⟩, hi'⟩⟩
    by_contra hn
    have hv₂ : v ∈ V(G₂) := mem_V_of_closure hl₂ hg (mem_closure_of_inc hi) hi.vertex_mem
    exact hgA (hside hv₂ hn hg' hi')
  have hbc : (Whitney.bdry J.toGraph E(G₂)).ncard ≤ 2 := (ncard_le_ncard hbX hXfin).trans hord
  have hedge : ∀ {v}, v ∈ J.V → ∃ g ∈ J.E, J.toGraph.Inc g v := by
    intro v hv
    obtain ⟨g, hg, hc⟩ := exists_edge_of_regionFacts hS r.facts hv
    exact ⟨g, hg, inc_of_mem_closure hg hc hv⟩
  by_cases hA : E(G₂) = ∅
  · refine Or.inl ⟨fun v hv => ?_, hA⟩
    by_contra hn
    have hnX : v ∉ X := fun h₃ => hn h₃.1
    obtain ⟨g, hg, hi⟩ := hedge (hl₂.vertexSet_mono hv)
    have hg₂ := hside hv hnX hg hi
    rw [hA] at hg₂
    exact hg₂
  · obtain ⟨x, y, P, hxy, hbd, hPs, hpath, hPE, hin⟩ :=
      exists_thread_tangle r hrig hS hns h2cell hT hresp hd' hT_eq hθ
        hl₂.edgeSet_mono hbc hmem (nonempty_iff_ne_empty.mpr hA)
    have hxX : x ∈ X := hbX (hbd ▸ Or.inl rfl)
    have hyX : y ∈ X := hbX (hbd ▸ Or.inr rfl)
    have hXeq : X = {x, y} := by
      have hsub : ({x, y} : Set S) ⊆ X := by
        rintro z (rfl | rfl)
        · exact hxX
        · exact hyX
      exact (eq_of_subset_of_ncard_le hsub (by rw [ncard_pair hxy]; exact hord) hXfin).symm
    have hE₂ : E(G₂) = P.E := hPE.symm
    have hxP : x ∈ P.V := by
      obtain ⟨W₀, -, hV₀, -⟩ := id hpath
      rw [hV₀]
      exact start_mem_support W₀
    have hyP : y ∈ P.V := by
      obtain ⟨W₀, -, hV₀, -⟩ := id hpath
      rw [hV₀]
      exact end_mem_support W₀
    have hX₂ : (V(G₂) ∩ V(G₁)).ncard = 2 := by
      rw [Set.inter_comm, ← hX, hXeq, ncard_pair hxy]
    have hPinV : ∀ {v}, v ∈ P.V → v ≠ x → v ≠ y → v ∈ V(G₂) \ V(G₁) := by
      intro v hv h₁ h₂
      have hedgeP : ∃ g ∈ P.E, P.toGraph.Inc g v := by
        obtain ⟨W₀, hs₀, hV₀, hE₀⟩ := id hpath
        have hvs : v ∈ W₀.support := by rw [hV₀] at hv; exact hv
        obtain ⟨e, he, -, -, -, hie, -⟩ := exists_two_edges_at_inner W₀ hs₀ hvs h₁ h₂
        exact ⟨e, by rw [hE₀]; exact he, hie⟩
      obtain ⟨g, hg, hi⟩ := hedgeP
      have hv₂ : v ∈ V(G₂) := mem_V_of_closure hl₂ (hE₂ ▸ hg) (mem_closure_of_inc hi) (hPs.1 hv)
      refine ⟨hv₂, fun hv₁ => ?_⟩
      have : v ∈ X := ⟨hv₁, hv₂⟩
      rw [hXeq] at this
      rcases this with h₃ | h₃
      · exact h₁ h₃
      · exact h₂ h₃
    have hV₂P : ∀ {v}, v ∈ V(G₂) \ V(G₁) → v ∈ P.V ∧ v ≠ x ∧ v ≠ y := by
      rintro v ⟨hv, hn⟩
      have hnX : v ∉ X := fun h₃ => hn h₃.1
      have hvx : v ≠ x := fun h₃ => hnX (h₃ ▸ hxX)
      have hvy : v ≠ y := fun h₃ => hnX (h₃ ▸ hyX)
      obtain ⟨g, hg, hi⟩ := hedge (hl₂.vertexSet_mono hv)
      have hg₂ := hside hv hnX hg hi
      have hgP : g ∈ P.E := hE₂ ▸ hg₂
      exact ⟨mem_V_of_inc_sub hPs hgP hi, hvx, hvy⟩
    refine Or.inr ⟨hX₂, fun v hv => ?_, ?_⟩
    · obtain ⟨hvP, h₁, h₂⟩ := hV₂P hv
      have hall := hin v hvP h₁ h₂
      have hset : {g | J.toGraph.Inc g v} = {g | P.toGraph.Inc g v} := by
        ext g
        constructor
        · intro hi
          have hgP := hall g hi.edge_mem hi
          exact inc_of_mem_closure hgP (mem_closure_of_inc hi) hvP
        · intro hi
          exact inc_of_mem_closure (hPs.2 hi.edge_mem) (mem_closure_of_inc hi) (hPs.1 hvP)
      change {g | J.toGraph.Inc g v}.ncard = 2
      rw [hset]
      exact path_two hpath hvP h₁ h₂
    · rw [hE₂]
      have hsub : P.V \ {x, y} ⊆ V(G₂) \ V(G₁) := fun v hv =>
        hPinV hv.1 (fun h₃ => hv.2 (Or.inl h₃)) (fun h₃ => hv.2 (Or.inr h₃))
      have hfinV : (V(G₂) \ V(G₁)).Finite :=
        J.finite_V.subset fun z hz => hl₂.vertexSet_mono hz.1
      exact (path_count hpath hxy hxP hyP).trans (by
        have := ncard_le_ncard hsub hfinV
        omega)

/-! ## 3. Degree and Boundary Lower Bounds for `H' = H ∩ (Σ - Λ₀)` -/

omit [T2Space S] in
/-- Every vertex of a circuit `C` in a loop-free drawing `J` is incident with two distinct edges
of `C`. -/
theorem two_edges_of_mem_circuit {J C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing J)
    (hnl : ∀ e v, ¬ J.toGraph.IsLink e v v) {v : S} (hv : v ∈ C.V) :
    ∃ e₁ ∈ C.E, ∃ e₂ ∈ C.E, e₁ ≠ e₂ ∧ J.toGraph.Inc e₁ v ∧ J.toGraph.Inc e₂ v := by
  obtain ⟨u, W, ⟨_, hed⟩, hpos, hCV, hCE⟩ := hC
  have hvW : v ∈ W.support := by rw [hCV] at hv; exact hv
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hvW
  set Rot := W₂.append W₁ with hRot
  have hedRot : Rot.edges.Nodup := by
    rw [hRot, GraphWalk.edges_append]
    rw [GraphWalk.edges_append] at hed
    exact (List.perm_append_comm.nodup_iff).mp hed
  have hmemE : ∀ e, e ∈ Rot.edges → e ∈ C.E := by
    intro e he
    rw [hCE]
    change e ∈ (W₁.append W₂).edges
    rw [hRot, GraphWalk.edges_append, List.mem_append] at he
    rw [GraphWalk.edges_append, List.mem_append]
    exact he.symm
  have hlen : 0 < Rot.length := by
    rw [hRot, GraphWalk.length_append]
    rw [GraphWalk.length_append] at hpos
    omega
  cases hR : Rot with
  | nil => simp [hR, GraphWalk.length] at hlen
  | @cons _ w₁ _ e₁ hl₁ rest =>
    have he₁C : e₁ ∈ C.E := hmemE e₁ (by simp [hR])
    have hinc₁ : J.toGraph.Inc e₁ v :=
      ⟨w₁, hCs.2 hl₁.1, hCs.1 hl₁.2.1, hCs.1 hl₁.2.2.1, by
        rw [← hCs.closure_inter_V hl₁.1]; exact hl₁.2.2.2⟩
    have hnd_cons : e₁ ∉ rest.edges ∧ rest.edges.Nodup := by
      have hed' : (e₁ :: rest.edges).Nodup := by simpa [hR, GraphWalk.edges] using hedRot
      exact List.nodup_cons.mp hed'
    cases hrest_nil : rest with
    | nil =>
      exact absurd ⟨hCs.2 hl₁.1, hCs.1 hl₁.2.1, hCs.1 hl₁.2.2.1, by
        rw [← hCs.closure_inter_V hl₁.1]; exact hl₁.2.2.2⟩ (hnl e₁ v)
    | @cons _ w₀ _ e₀ hl₀ rest₀ =>
      have hlen_rev : 0 < rest.reverse.length := by
        rw [GraphWalk.length_reverse, hrest_nil]
        simp [GraphWalk.length]
      cases hrest : rest.reverse with
      | nil => simp [hrest, GraphWalk.length] at hlen_rev
      | @cons _ w₂ _ e₂ hl₂ rest₂ =>
        have he₂_rev : e₂ ∈ rest.reverse.edges := by simp [hrest]
        have he₂_rest : e₂ ∈ rest.edges := by
          rwa [GraphWalk.edges_reverse, List.mem_reverse] at he₂_rev
        have he₂C : e₂ ∈ C.E := hmemE e₂ (by simp [hR, he₂_rest])
        have hinc₂ : J.toGraph.Inc e₂ v :=
          ⟨w₂, hCs.2 hl₂.1, hCs.1 hl₂.2.1, hCs.1 hl₂.2.2.1, by
            rw [← hCs.closure_inter_V hl₂.1]; exact hl₂.2.2.2⟩
        have hne : e₁ ≠ e₂ := fun h => hnd_cons.1 (h ▸ he₂_rest)
        exact ⟨e₁, he₁C, e₂, he₂C, hne, hinc₁, hinc₂⟩

omit [T2Space S] in
/-- Every vertex in `bdry J.toGraph C.E` for a circuit `C` of a loop-free drawing `J` has degree
at least `3` in `J.toGraph`. -/
theorem mem_deg_ne_two_of_mem_bdry_circuit {J C : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing J) (hnl : ∀ e v, ¬ J.toGraph.IsLink e v v) :
    Whitney.bdry J.toGraph C.E ⊆ {v | v ∈ V(J.toGraph) ∧ Whitney.deg J.toGraph v ≠ 2} := by
  rintro v ⟨⟨e₀, he₀C, hinc₀⟩, ⟨e₃, ⟨he₃J, he₃nC⟩, hinc₃⟩⟩
  have hvC : v ∈ C.V := mem_V_of_inc_sub hCs he₀C hinc₀
  obtain ⟨e₁, he₁C, e₂, he₂C, hne₁₂, hinc₁, hinc₂⟩ := two_edges_of_mem_circuit hC hCs hnl hvC
  refine ⟨hinc₀.vertex_mem, ?_⟩
  have hsub : ({e₁, e₂, e₃} : Set (Set S)) ⊆ {g | J.toGraph.Inc g v} := by
    rintro g (rfl | rfl | rfl)
    · exact hinc₁
    · exact hinc₂
    · exact hinc₃
  have hfin : {g | J.toGraph.Inc g v}.Finite :=
    J.finite_edges.subset fun g hg => hg.edge_mem
  have hne₁₃ : e₁ ≠ e₃ := fun h => he₃nC (h ▸ he₁C)
  have hne₂₃ : e₂ ≠ e₃ := fun h => he₃nC (h ▸ he₂C)
  have hcard3 : ({e₁, e₂, e₃} : Set (Set S)).ncard = 3 := by
    rw [ncard_insert_of_notMem (by simp [hne₁₂, hne₁₃]), ncard_pair hne₂₃]
  have hle := ncard_le_ncard hsub hfin
  rw [hcard3] at hle
  change {g | J.toGraph.Inc g v}.ncard ≠ 2
  omega

/-- Part 6(i) of the Section 10 translation: if a 39-zone `Λ₀` around `z` is an eye of
`H' = clearedSubdrawing H Λ₀` with respect to the cleared tangle `T'` of order `51` and `H'` is
rigid, then `H'.toGraph` is a subdivision of a simple 3-connected graph. -/
theorem isSubdivisionOfSimpleThreeConnected_clearedSubdrawing_of_drawingEye
    {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hnot_sphere : ¬ IsSphere S)
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    (hH_subdiv : IsSubdivisionOfSimpleThreeConnected η.imageGraph)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Λ₀ : Set S}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d' : Set S → Set S → ℕ}
    {η_cl : SpanEmbedding (clearedSubdrawing H Λ₀) G}
    (hZone : IsLambdaZoneAround H d 39 z Λ₀)
    (hrig : IsRigid (clearedSubdrawing H Λ₀))
    (hCleared : IsClearedTangle H T d 209 39 Λ₀ T' d')
    (heye : IsDrawingEye G (clearedSubdrawing H Λ₀) η_cl (209 - 158) T' Λ₀) :
    IsSubdivisionOfSimpleThreeConnected (clearedSubdrawing H Λ₀).toGraph := by
  have : ConnectedSpace S := hConn
  set H' := clearedSubdrawing H Λ₀
  obtain ⟨G₀, Q, hsd⟩ := exists_subData (isSubdivision_toGraph_of_spanEmbedding η hH_subdiv)
  have hnl : ∀ e v, ¬ H'.toGraph.IsLink e v v :=
    clearedSubdrawing_no_loop (fun e u hl => Whitney.no_loop hsd hl)
  obtain ⟨hΛ₀R, C, a, b, c, d_v, P₁, P₂, hC, hCs, hCU, ha, hb, hc, hd_v, hnodup, -, hfree, -⟩ :=
    heye
  have hMetric' : HasTangleMetric H' 51 T' d' := hCleared.hasMetric
  rcases hMetric' with ⟨hResp', K', ins', hK', hd', hd'_eq⟩
  have hMetric' : HasTangleMetric H' 51 T' d' := ⟨hResp', K', ins', hK', hd', hd'_eq⟩
  have h2cell' : (PaintingOrDrawing.drawing H').IsTwoCell := hResp'.1
  have hT' : GM10.IsTangle H'.toHypergraph 51 T' := hResp'.2.1
  have hresp' : (PaintingOrDrawing.drawing H').IsRespectful 51 T' := hResp'.2.2
  obtain ⟨e₀, he₀C⟩ := IsCircuit.E_nonempty hC
  have hE' : H'.E.Nonempty := ⟨e₀, hCs.2 he₀C⟩
  have hrad_facts : RegionFacts (PaintingOrDrawing.drawing H') K' :=
    GM11.regionFacts_of_radial ⟨hK'.1, hK'.2.1⟩ hS hK'.2.2 hE'
  have r : Rad H' K' := ⟨hK'.2.1.1, hK'.2.1.2.1, hrad_facts⟩
  have hT_eq : T' = inducedPretangle (PaintingOrDrawing.drawing H') K' 51 ins' :=
    (GM11.theorem_6_3_proof S hS hConn (PaintingOrDrawing.drawing H') K' 51 T' ins'
      h2cell' hE' hT'.isPretangle hresp' hK' hd').2
  -- Show `4 ≤ {v | v ∈ V(H'.toGraph) ∧ deg H'.toGraph v ≠ 2}.ncard`.
  have hfour : 4 ≤ {v | v ∈ V(H'.toGraph) ∧ Whitney.deg H'.toGraph v ≠ 2}.ncard := by
    have hbd_sub := mem_deg_ne_two_of_mem_bdry_circuit hC hCs hnl
    have hfin_deg : {v | v ∈ V(H'.toGraph) ∧ Whitney.deg H'.toGraph v ≠ 2}.Finite :=
      H'.finite_V.subset fun _ h => h.1
    suffices hbd4 : 4 ≤ (Whitney.bdry H'.toGraph C.E).ncard from
      hbd4.trans (ncard_le_ncard hbd_sub hfin_deg)
    by_contra hlt4
    have hlt4' : (Whitney.bdry H'.toGraph C.E).ncard < 4 := Nat.lt_of_not_le hlt4
    let A₁ := drawingEdgeSepA H' C.E
    let A₂ := drawingEdgeSepB H' C.E
    have hsep12 : H'.toHypergraph.IsSeparation A₁ A₂ := isSeparation_drawingEdgeSep H' C.E
    have hord12 : separationOrder A₁ A₂ < 4 := by
      change (A₁ ∩ A₂).vertexSet.ncard < 4
      rwa [inter_vertexSet_drawingEdgeSep]
    have hCV_sub : C.V ⊆ A₁.vertexSet := by
      intro v hv
      obtain ⟨e₁, he₁C, -, -, -, hinc₁, -⟩ := two_edges_of_mem_circuit hC hCs hnl hv
      exact ⟨e₁, he₁C, hinc₁⟩
    have habcd_sub : ({a, b, c, d_v} : Set S) ⊆ A₁.vertexSet := by
      rintro v (rfl | rfl | rfl | rfl)
      · exact hCV_sub ha
      · exact hCV_sub hb
      · exact hCV_sub hc
      · exact hCV_sub hd_v
    have habcd_card : ({a, b, c, d_v} : Set S).ncard = 4 := by
      classical
      have h1 : ({a, b, c, d_v} : Set S) = ↑([a, b, c, d_v].toFinset) := by
        ext x; simp
      rw [h1, ncard_coe_finset, List.toFinset_card_of_nodup hnodup]
      rfl
    have hnot_A₁ : (A₁, A₂) ∉ T' := by
      intro hmem
      have hle := hfree.2.2 hmem habcd_sub
      omega
    have hA₂A₁ : (A₂, A₁) ∈ T' :=
      (hT'.axiom1 hsep12 (by omega)).resolve_left hnot_A₁
    have hA₁_ne : A₁.edgeSet ≠ {Λ₀} := by
      intro heq
      have he₀A₁ : e₀ ∈ A₁.edgeSet := ⟨he₀C, hCs.2 he₀C⟩
      rw [heq, mem_singleton_iff] at he₀A₁
      subst he₀A₁
      obtain ⟨p, hp⟩ := (hCs.2 he₀C).1
      exact region_subset hΛ₀R hp (H'.closure_subset_U (hCs.2 he₀C) (subset_closure hp))
    obtain ⟨e, heA₁, hdist_ge⟩ :=
      theorem_7_3_proof H' 51 T' d' A₂ A₁ Λ₀ hS hConn hE' hMetric' (Or.inr hΛ₀R) hA₂A₁ hA₁_ne
    have hord21 : separationOrder A₂ A₁ < 4 := by
      rwa [separationOrder_comm]
    have heC : e ∈ C.E := heA₁.1
    have heH' : e ∈ H'.E := heA₁.2
    have heH : e ∈ H.E := (clearedSubdrawing_isSubdrawing H Λ₀).2 heH'
    have he_cl : e ⊆ closure Λ₀ := by
      have heCU : e ⊆ C.U := (C.closure_subset_U heC).trans' subset_closure
      rw [hCU, subBd_eq_frontier] at heCU
      exact heCU.trans frontier_subset_closure
    have hle_zone : d z e ≤ 39 := hZone.dist_le e (Or.inl (Or.inr heH)) he_cl
    have hle_clear : d' Λ₀ e ≤ d z e :=
      (hCleared.dist_bounds z hZone.z_mem e (Or.inl (Or.inr heH))
        Λ₀ (Or.inr hΛ₀R) e (Or.inl (Or.inr heH')) hZone.z_subset subset_rfl).2
    omega
  -- Show `Good H'.toGraph`.
  have hgood : Whitney.Good H'.toGraph := by
    refine ⟨H'.finite_V, H'.finite_edges, hnl, hfour, ?_⟩
    intro G₁ G₂ hs hord
    obtain ⟨hl₁, hl₂, hV, hE, hdis⟩ := id hs
    have hb₁ : Whitney.bdry H'.toGraph E(G₁) ⊆ V(G₁) ∩ V(G₂) := by
      rintro v ⟨⟨g, hg, hi⟩, ⟨g', ⟨hg', hgA⟩, hi'⟩⟩
      have hv₁ : v ∈ V(G₁) := mem_V_of_closure hl₁ hg (mem_closure_of_inc hi) hi.vertex_mem
      have hg'₂ : g' ∈ E(G₂) := by
        have : g' ∈ E(G₁) ∪ E(G₂) := hE ▸ hg'
        exact this.resolve_left hgA
      have hv₂ : v ∈ V(G₂) := mem_V_of_closure hl₂ hg'₂ (mem_closure_of_inc hi') hi'.vertex_mem
      exact ⟨hv₁, hv₂⟩
    have hfinX : (V(G₁) ∩ V(G₂)).Finite :=
      H'.finite_V.subset fun z hz => hl₁.vertexSet_mono hz.1
    have hord₁ : separationOrder (drawingEdgeSepA H' E(G₁)) (drawingEdgeSepB H' E(G₁)) < 51 := by
      change (drawingEdgeSepA H' E(G₁) ∩ drawingEdgeSepB H' E(G₁)).vertexSet.ncard < 51
      rw [inter_vertexSet_drawingEdgeSep]
      have := (ncard_le_ncard hb₁ hfinX).trans hord
      omega
    rcases hT'.axiom1 (isSeparation_drawingEdgeSep H' E(G₁)) hord₁ with hmem₁ | hmem₂
    · left
      have hs_symm : IsGraphSeparation H'.toGraph G₂ G₁ :=
        ⟨hl₂, hl₁, Set.union_comm _ _ ▸ hV, Set.union_comm _ _ ▸ hE, hdis.symm⟩
      exact thin_of_edge_tangle r hrig hS hnot_sphere h2cell' hT'.isPretangle hresp' hd' hT_eq
        (by decide) hs_symm (by rwa [Set.inter_comm]) hmem₁
    · right
      have hE_diff₁ : H'.E \ E(G₁) = E(G₂) := by
        ext g
        constructor
        · rintro ⟨hg, hg₁⟩
          have : g ∈ E(G₁) ∪ E(G₂) := hE ▸ hg
          exact this.resolve_left hg₁
        · intro hg₂
          exact ⟨hl₂.edgeSet_mono hg₂, disjoint_right.mp hdis hg₂⟩
      have hE_diff₂ : H'.E \ E(G₂) = E(G₁) := by
        ext g
        constructor
        · rintro ⟨hg, hg₂⟩
          have : g ∈ E(G₁) ∪ E(G₂) := hE ▸ hg
          exact this.resolve_right hg₂
        · intro hg₁
          exact ⟨hl₁.edgeSet_mono hg₁, disjoint_left.mp hdis hg₁⟩
      have hverts_union :
          Whitney.verts H'.toGraph E(G₁) ∪ Whitney.verts H'.toGraph E(G₂) = H'.V := by
        refine subset_antisymm (union_subset
          (fun _ ⟨_, _, _, hl⟩ => hl.left_mem) (fun _ ⟨_, _, _, hl⟩ => hl.left_mem)) ?_
        intro v hv
        obtain ⟨g, hg, hc⟩ := exists_edge_of_regionFacts hS r.facts hv
        have hinc : H'.toGraph.Inc g v := inc_of_mem_closure hg hc hv
        have : g ∈ E(G₁) ∪ E(G₂) := hE ▸ hg
        rcases this with hg₁ | hg₂
        · exact Or.inl ⟨g, hg₁, hinc⟩
        · exact Or.inr ⟨g, hg₂, hinc⟩
      have hB₁_eq : drawingEdgeSepB H' E(G₁) = drawingEdgeSepA H' E(G₂) := by
        refine Hypergraph.ext ?_ ?_ ?_
        · change (H'.V \ Whitney.verts H'.toGraph E(G₁)) ∪ Whitney.verts H'.toGraph (H'.E \ E(G₁)) =
            Whitney.verts H'.toGraph E(G₂)
          rw [hE_diff₁]
          refine union_eq_self_of_subset_left fun v ⟨hv, hnv₁⟩ => ?_
          rw [← hverts_union] at hv
          exact hv.resolve_left hnv₁
        · change H'.E \ E(G₁) = E(G₂) ∩ H'.E
          rw [hE_diff₁]
          exact (inter_eq_self_of_subset_left hl₂.edgeSet_mono).symm
        · funext g v
          apply propext
          change H'.toHypergraph.Inc g v ∧ g ∉ E(G₁) ↔ H'.toHypergraph.Inc g v ∧ g ∈ E(G₂)
          exact ⟨fun ⟨hi, hn⟩ => ⟨hi, hE_diff₁ ▸ ⟨hi.1, hn⟩⟩,
            fun ⟨hi, hg₂⟩ => ⟨hi, disjoint_right.mp hdis hg₂⟩⟩
      have hA₁_eq : drawingEdgeSepA H' E(G₁) = drawingEdgeSepB H' E(G₂) := by
        refine Hypergraph.ext ?_ ?_ ?_
        · change Whitney.verts H'.toGraph E(G₁) =
            (H'.V \ Whitney.verts H'.toGraph E(G₂)) ∪ Whitney.verts H'.toGraph (H'.E \ E(G₂))
          rw [hE_diff₂]
          symm
          refine union_eq_self_of_subset_left fun v ⟨hv, hnv₂⟩ => ?_
          rw [← hverts_union] at hv
          exact hv.resolve_right hnv₂
        · change E(G₁) ∩ H'.E = H'.E \ E(G₂)
          rw [hE_diff₂]
          exact inter_eq_self_of_subset_left hl₁.edgeSet_mono
        · funext g v
          apply propext
          change H'.toHypergraph.Inc g v ∧ g ∈ E(G₁) ↔ H'.toHypergraph.Inc g v ∧ g ∉ E(G₂)
          exact ⟨fun ⟨hi, hg₁⟩ => ⟨hi, disjoint_left.mp hdis hg₁⟩,
            fun ⟨hi, hn⟩ => ⟨hi, hE_diff₂ ▸ ⟨hi.1, hn⟩⟩⟩
      rw [hB₁_eq, hA₁_eq] at hmem₂
      exact thin_of_edge_tangle r hrig hS hnot_sphere h2cell' hT'.isPretangle hresp' hd' hT_eq
        (by decide) hs hord hmem₂
  exact Whitney.good_sub hgood

/-! ## 4. Disc Boundary Intersection and Eye Obstruction -/

/-- Part 6(iii) of the Section 10 translation: if `Λ₀` is a 39-zone around `z` with cleared tangle
`T'` of order `51` and `{a, b, c, d_v}` is a 4-element free set with respect to `T'`, then for any
closed disc `Δ ⊆ Σ` containing `{a, b, c, d_v}`, `4 ≤ ((subBd Δ \ Λ₀) ∩ H.U).encard`. -/
theorem four_le_subBd_diff_zone_encard
    (hS : IsClosedSurface S) (hnot_sphere : ¬ IsSphere S)
    {H : Drawing S}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Λ₀ : Set S}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d' : Set S → Set S → ℕ}
    (hZone : IsLambdaZoneAround H d 39 z Λ₀)
    (hCleared : IsClearedTangle H T d 209 39 Λ₀ T' d')
    (hE' : (clearedSubdrawing H Λ₀).E.Nonempty)
    {a b c d_v : S}
    (hnodup : [a, b, c, d_v].Nodup)
    (hfree : IsFreeSet (clearedSubdrawing H Λ₀).toHypergraph T' (209 - 158) {a, b, c, d_v})
    (Δ : Set S) (hΔ : IsClosedDisc Δ)
    (habcd : ({a, b, c, d_v} : Set S) ⊆ Δ) :
    4 ≤ ((subBd Δ \ Λ₀) ∩ H.U).encard := by
  set H' := clearedSubdrawing H Λ₀
  have hU' : H'.U = H.U \ Λ₀ := clearedSubdrawing_U hZone
  have hcap_eq : (subBd Δ \ Λ₀) ∩ H.U = subBd Δ ∩ H'.U := by
    rw [hU']
    ext x
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  rw [hcap_eq]
  by_contra hlt4
  have hfin : (subBd Δ ∩ H'.U).Finite := by
    by_contra hinf
    rw [encard_eq_top_iff.mpr hinf] at hlt4
    exact hlt4 le_top
  have hncard_lt : ¬ 4 ≤ (subBd Δ ∩ H'.U).ncard := by
    intro h4
    apply hlt4
    rw [← hfin.cast_ncard_eq]
    exact_mod_cast h4
  have hncard_le : (subBd Δ ∩ H'.U).ncard ≤ 3 := by omega
  have hResp' : IsRespectfulDrawingTangle H' 51 T' := hCleared.hasMetric.1
  have : ConnectedSpace S := hResp'.1.1
  obtain ⟨A, B, hAB, hAV, hord_le, -⟩ :=
    disc_sep_mem_tangle hS hnot_sphere (by decide) hE' hResp' hΔ hfin hncard_le
  have habcd_A : ({a, b, c, d_v} : Set S) ⊆ A.vertexSet := by
    rw [hAV]
    exact subset_inter hfree.1 habcd
  have habcd_card : ({a, b, c, d_v} : Set S).ncard = 4 := by
    classical
    have h1 : ({a, b, c, d_v} : Set S) = ↑([a, b, c, d_v].toFinset) := by
      ext x; simp
    rw [h1, ncard_coe_finset, List.toFinset_card_of_nodup hnodup]
    rfl
  have hfree_le : ({a, b, c, d_v} : Set S).ncard ≤ separationOrder A B :=
    hfree.2.2 hAB habcd_A
  omega

/-- Part 6 of the Section 10 translation: if a 39-zone `Λ` is an eye of `H ∩ (Σ - Λ)` in `G` with
respect to the cleared tangle `T'` of order `51` and `H ∩ (Σ - Λ)` is rigid, then the eye
obstruction `(1.1)(iii)` holds. -/
theorem eye_obstruction_of_drawingEye
    {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hnot_sphere : ¬ IsSphere S)
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (hH_subdiv : IsSubdivisionOfSimpleThreeConnected η.imageGraph)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (hMetric : HasTangleMetric H 209 T d)
    (Λ : Set S)
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ)
    (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G)
    (hzone : IsLambdaZone H d 39 Λ)
    (hrig : IsRigid (clearedSubdrawing H Λ))
    (hCleared : IsClearedTangle H T d 209 39 Λ T' d')
    (hv_cl : ∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η.vMap v)
    (heye : IsDrawingEye G (clearedSubdrawing H Λ) η_cl (209 - 158) T' Λ) :
    ∃ (C : Drawing S) (Λ₀ : Set S) (x : S) (a b c d_v : S) (P₁ P₂ : Graph α β),
      C.IsCircuit ∧ C.IsSubdrawing H ∧ IsOpenDisc Λ₀ ∧ subBd Λ₀ = C.U ∧ x ∈ Λ₀ ∧
      a ∈ C.V ∧ b ∈ C.V ∧ c ∈ C.V ∧ d_v ∈ C.V ∧
      OccurInCircuitOrder C a b c d_v ∧
      IsSubdivisionOfSimpleThreeConnected (clearedSubdrawing H Λ₀).toGraph ∧
      (∀ y ∈ Λ₀, ∃ φ : C(Circle, S),
        (range φ ∩ H.U).encard ≤ 39 ∧ x ∈ curveIns φ ∧ y ∈ curveIns φ) ∧
      (∀ Δ : Set S, IsClosedDisc Δ → ({a, b, c, d_v} : Set S) ⊆ Δ →
        4 ≤ ((subBd Δ \ Λ₀) ∩ H.U).encard) ∧
      Disjoint V(P₁) V(P₂) ∧
      IsGraphPathWithEnds G P₁ (η.vMap a) (η.vMap c) ∧
      IsGraphPathWithEnds G P₂ (η.vMap b) (η.vMap d_v) := by
  have : ConnectedSpace S := hConn
  obtain ⟨z, _, hZone⟩ := hzone
  have hsub3 : IsSubdivisionOfSimpleThreeConnected (clearedSubdrawing H Λ).toGraph :=
    isSubdivisionOfSimpleThreeConnected_clearedSubdrawing_of_drawingEye
      hS hConn hnot_sphere hH_subdiv hZone hrig hCleared heye
  obtain ⟨hΛR, C, a, b, c, d_v, P₁, P₂, hC, hCs, hCU, ha, hb, hc, hd_v, hnodup, hord, hfree,
    hdisj, hP₁, hP₂⟩ := heye
  obtain ⟨e₀, he₀C⟩ := IsCircuit.E_nonempty hC
  have hE' : (clearedSubdrawing H Λ).E.Nonempty := ⟨e₀, hCs.2 he₀C⟩
  have hCH : C.IsSubdrawing H := hCs.trans (clearedSubdrawing_isSubdrawing H Λ)
  obtain ⟨x, hxΛ, hcurve⟩ :=
    exists_curve_le_of_mem_lambdaZone hS (by decide) hMetric hZone hC hCH hCU
  refine ⟨C, Λ, x, a, b, c, d_v, P₁, P₂, hC, hCH, hZone.isOpenDisc, hCU.symm, hxΛ,
    ha, hb, hc, hd_v, hord, hsub3, hcurve, ?_, hdisj, ?_, ?_⟩
  · exact four_le_subBd_diff_zone_encard hS hnot_sphere hZone hCleared hE' hnodup hfree
  · rw [← hv_cl a (hCs.1 ha), ← hv_cl c (hCs.1 hc)]
    exact hP₁.2.1
  · rw [← hv_cl b (hCs.1 hb), ← hv_cl d_v (hCs.1 hd_v)]
    exact hP₂.2.1

/-- Complete proof of `Theorem11TranslationStatement` combining Parts 1–4
(`isRigid_and_isTwoCell_of_subdivision_and_representative`), Part 5
(`not_exists_curve_of_dist_ge_twelve`), Part 6 (`eye_obstruction_of_drawingEye`), and Part 7
(`exists_extending_drawing_of_threeSegregation`). -/
theorem theorem11TranslationStatement_proved : Theorem11TranslationStatement.{u, v, w} := by
  intro S _ _ α β hS hConn hnot_sphere G H η hV_fin hE_fin hG_4conn hH_subdiv hrep
  have : ConnectedSpace S := hConn
  obtain ⟨T, d, h2cell, hrigid, hT, hmetric⟩ :=
    isRigid_and_isTwoCell_of_subdivision_and_representative hS hnot_sphere η hH_subdiv hrep
  refine ⟨T, d, h2cell, hrigid, hT, hmetric, ?_, ?_, ?_⟩
  · intro P u v hu hv hP hgt
    obtain ⟨G₀, Q, hsd⟩ := exists_subData (isSubdivision_toGraph_of_spanEmbedding η hH_subdiv)
    obtain ⟨e₀, he₀, -⟩ := SubDataSepGeneral.exists_inc_of_mem_V hsd hu
    have hE : H.E.Nonempty := ⟨e₀, he₀⟩
    exact ⟨P, u, v, hu, hv, hP,
      not_exists_curve_of_dist_ge_twelve hS hnot_sphere (by decide) hE hmetric hu hv hgt⟩
  · intro Λ T' d' η_cl hzone hrig_cl hCleared hv_cl heye
    exact eye_obstruction_of_drawingEye hS hConn hnot_sphere G H η hH_subdiv T d hmetric
      Λ T' d' η_cl hzone hrig_cl hCleared hv_cl heye
  · rintro ⟨S_seg, α_disc, α_pt, hSeg3, hLocal, hArr, hCompat⟩
    exact exists_extending_drawing_of_threeSegregation hS hnot_sphere
      hG_4conn hrigid hT hSeg3 hLocal hArr hCompat

end GraphMinor.GM14

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Theorem63
public import LeanPool.GraphMinor.GM11.Theorem75

/-!
# Graph Minors XI, (6.4): the first part

This file proves claims (1) and (3) of the proof of (6.4), and the existence of the derived slope.

Claim (1) says that if `(A, B) ∈ T` then `U(A)` includes no non-null-homotopic `O`-arc. The paper
goes through (3.1)
and (7.3). We use (7.5) instead. The union of the circuits of (6.3) lies in a closed disc `Δ`, by
(7.5), and so
each `ins(Cᵢ)` lies in `Δ`, since `Σ` is not a sphere.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S]

section Null

variable [ConnectedSpace S]

/-- If each circuit of `N` is null-homotopic, then `U(N)` lies in a closed disc, by (7.5). -/
theorem exists_disc_of_circuits (hS : IsClosedSurface S) (N : Drawing S)
    (hnull : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing N → IsNullHomotopicOArc C.U) :
    ∃ Δ, IsClosedDisc Δ ∧ N.U ⊆ Δ := by
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hc := N.isClosed_U
  have hn : IsNice N.U := ⟨N, isGammaNice_of_frontier (Drawing.IsSubdrawing.refl N) subset_rfl
    (hc.frontier_eq.subset.trans sdiff_subset)⟩
  have hu : N.U ≠ univ := by
    obtain ⟨x⟩ : Nonempty S := inferInstance
    obtain ⟨y, -, hy⟩ := exists_notMem_U (Γ := N) hS isOpen_univ ⟨x, mem_univ x⟩
    exact fun h => hy (h ▸ mem_univ y)
  obtain ⟨Δ, hΔ, -, hsub⟩ := theorem_7_5_proof hS hc hn hu finite_empty (disjoint_empty _)
    (fun F hF hO => by
    obtain ⟨C, hC, hCs, rfl⟩ := exists_circuit_of_oArc hO hF
    rw [sdiff_empty]
    exact hnull C hC hCs)
  exact ⟨Δ, hΔ, hsub⟩

/-- A closed disc of `Σ` whose boundary lies in a closed disc `Δ` lies in `Δ`, if `Σ` is not a
sphere. -/
theorem disc_subset_of_bd (hS : IsClosedSurface S) (hns : ¬ IsSphere S) {D Δ : Set S}
  (hD : IsClosedDisc D)
    (hΔ : IsClosedDisc Δ) (hsub : discBd D ⊆ Δ) : D ⊆ Δ := by
  obtain ⟨E, ⟨hEΔ, hE, hb, -⟩, -⟩ := disc_oArc Δ (discBd D) hΔ hsub (IsClosedDisc.isOArc_discBd hD)
  rw [eq_of_discBd_eq (IsClosedSurface.isSurface hS) hns hD hE hb.symm]
  exact hEΔ

omit [ConnectedSpace S] in
/-- An `O`-arc in the union of a finite set and the edges of a family inside a closed disc lies in
the disc. -/
theorem oArc_subset_of_edges [T2Space S] {F Δ V₀ : Set S} {E₀ : Set (Set S)} (hF : IsOArc F)
    (hΔ : IsClosed Δ) (hV : V₀.Finite) (hE : ∀ e ∈ E₀, e ⊆ Δ) (hsub : F ⊆ V₀ ∪ ⋃₀ E₀) : F ⊆ Δ := by
  have hin : F \ V₀ ⊆ Δ := by
    rintro x ⟨hx, hxV⟩
    obtain ⟨e, he, hxe⟩ := (hsub hx).resolve_left hxV
    exact hE e he hxe
  obtain ⟨x, hx, hxV⟩ := (infinite_of_isOArc hF).exists_notMem_finite hV
  intro y hy
  by_contra hyn
  have hcov : F ⊆ Δ ∪ (V₀ \ Δ) := fun z hz => by
    by_cases hzΔ : z ∈ Δ
    · exact Or.inl hzΔ
    · have hzV : z ∈ V₀ := by
        by_contra h
        exact hzΔ (hin ⟨hz, h⟩)
      exact Or.inr ⟨hzV, hzΔ⟩
  obtain ⟨z, -, hz₁, -, hz₂⟩ := isPreconnected_closed_iff.mp hF.isPreconnected _ _ hΔ
    (hV.subset sdiff_subset).isClosed hcov ⟨x, hx, hin ⟨hx, hxV⟩⟩ ⟨y, hy,
      (hcov hy).resolve_left hyn⟩
  exact hz₂ hz₁

end Null

variable {Γ : PaintingOrDrawing S} {Γ' : Drawing S} {θ : ℕ}
  {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}

omit [TopologicalSpace S] in
/-- The first vertex of a closed walk of positive length comes again later. -/
theorem mem_tail_of_closed {α β : Type*} {G : Graph α β} {u : α} (W : GraphWalk G u u)
  (hpos : 0 < W.length) {x : α}
    (hx : x ∈ W.support) : x ∈ W.support.tail := by
  rw [W.support_eq_cons, List.mem_cons] at hx
  rcases hx with rfl | hx
  · cases W with
    | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hpos
    | cons hl r => exact r.end_mem_support
  · exact hx

/-- In a circuit of a bipartite drawing, at most half of the length lies on one side. -/
theorem two_mul_ncard_le_length {G : Drawing S} (X : Set S) (hb : ∀ e x y, G.toGraph.IsLink e x y →
  (x ∈ X ↔ y ∉ X))
    {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing G) : 2 * (X ∩ C.V).ncard ≤ C.length
      := by
  classical
  obtain ⟨u, W, ⟨hnd, hed⟩, hpos, hCV, hCE⟩ := hC
  have hlen : C.length = W.length := by
    rw [Drawing.length, hCE]
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by
      ext x
      simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
    rfl
  have hb' : ∀ e x y, C.toGraph.IsLink e x y → (x ∈ Xᶜ ↔ y ∉ Xᶜ) := by
    intro e x y hl
    have h := hb e x y ⟨hCs.2 hl.1, hCs.1 hl.2.1, hCs.1 hl.2.2.1, by
      rw [← hCs.closure_inter_V hl.1]
      exact hl.2.2.2⟩
    simp only [mem_compl_iff, not_not]
    tauto
  have hc := two_mul_count_le Xᶜ hb' W
  have htail : W.support.tail.length = W.length := by
    rw [List.length_tail, length_support]
    rfl
  have hsum : W.support.tail.countP (· ∈ X) + W.support.tail.countP (· ∈ Xᶜ) = W.length := by
    rw [← htail, List.length_eq_countP_add_countP (fun x => decide (x ∈ X))]
    congr 1
  have hmem : ∀ x ∈ W.support, x ∈ W.support.tail := fun _ hx => mem_tail_of_closed W hpos hx
  have hcard : (X ∩ C.V).ncard ≤ W.support.tail.countP (· ∈ X) := by
    have hsub : X ∩ C.V ⊆ ((W.support.tail.filter (· ∈ X)).toFinset : Set S) := by
      rintro x ⟨hxX, hxV⟩
      rw [hCV] at hxV
      simpa using ⟨hmem x hxV, hxX⟩
    have := ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [ncard_coe_finset, List.toFinset_card_of_nodup (hnd.filter _)] at this
    rwa [List.countP_eq_length_filter]
  omega

variable [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- The derived slope exists: for each short circuit `C` of `Γ'`, the set `U(C)` is a normal `O`-arc
with fewer than `θ`
vertices of `Γ`, so that a respectful set `T` gives a closed disc. -/
theorem exists_derivedSlope_of_preRadial [T2Space S] (hresp : Γ.IsRespectful θ T)
    (hrad : Γ.IsPreRadialDrawing Γ') :
    ∃ ins, IsDerivedSlope Γ Γ' θ T ins := by
  classical
  have hb := bipartite_of_preRadial hrad
  have hex : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing Γ' → C.length < 2 * θ →
      ∃ Δ, IsClosedDisc Δ ∧ subBd Δ = C.U ∧ (Γ.inter Δ, Γ.interOutside Δ) ∈ T := by
    intro C hC hCs hl
    have hUs : C.U ⊆ Γ'.U := hCs.U_subset
    have hsub : C.U ∩ Γ.V ⊆ Γ.V ∩ C.V := by
      rintro x ⟨hxC, hxV⟩
      refine ⟨hxV, ?_⟩
      by_contra hn
      obtain ⟨e, he, hxe⟩ := C.exists_edge_of_mem hxC hn
      exact ((hCs.2 he).2.1 hxe).2 (hrad.2.1 hxV)
    have hcard : (C.U ∩ Γ.V).ncard < θ := by
      have h₁ := two_mul_ncard_le_length Γ.V hb hC hCs
      have h₂ := ncard_le_ncard hsub (C.finite_V.subset inter_subset_right)
      omega
    refine hresp.2 C.U (IsCircuit.isOArc_U hC) ?_ hcard
    rintro x ⟨hxC, hxU⟩
    rw [← hrad.1]
    exact ⟨hxU, hUs hxC⟩
  refine ⟨fun C => if h : C.IsCircuit ∧ C.IsSubdrawing Γ' ∧ C.length < 2 * θ then
    (hex C h.1 h.2.1 h.2.2).choose else ∅, fun C hC hCs hl => ?_⟩
  have h : C.IsCircuit ∧ C.IsSubdrawing Γ' ∧ C.length < 2 * θ := ⟨hC, hCs, hl⟩
  simp only [h, and_self, dite_true]
  exact (hex C hC hCs hl).choose_spec

omit [ConnectedSpace S] in
/-- A respectful tangle on a closed surface gives a derived slope in any pre-radial drawing. -/
theorem exists_derivedSlope [T2Space S] (_hS : IsClosedSurface S) (hresp : Γ.IsRespectful θ T)
    (hrad : Γ.IsPreRadialDrawing Γ') :
    ∃ ins, IsDerivedSlope Γ Γ' θ T ins :=
  exists_derivedSlope_of_preRadial hresp hrad

omit [ConnectedSpace S] in
/-- A short circuit of `Γ'` bounds a disc in a slope, so it is null-homotopic. -/
theorem null_of_disc [T2Space S] {D Δ : Set S} (hD : IsOArc D) (d : IsClosedDisc Δ) (b : subBd Δ
  = D) :
    IsNullHomotopicOArc D := by
  refine isNullHomotopicOArcIn_of_subset_disc hD (subset_univ _) d ?_
  rw [← b, subBd_eq_frontier]
  exact (IsClosedDisc.isCompact d).isClosed.frontier_subset

omit [ConnectedSpace S] in
/-- A short circuit of `Γ'` is null-homotopic. -/
theorem null_of_short [T2Space S] {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S} (hd : IsDerivedSlope Γ Γ' θ T ins) {D : Drawing S} (hD : D.IsCircuit)
    (hDs : D.IsSubdrawing Γ') (hl : D.length < 2 * θ) : IsNullHomotopicOArc D.U := by
  obtain ⟨d, b, -⟩ := hd D hD hDs hl
  exact null_of_disc (IsCircuit.isOArc_U hD) d b

omit [ConnectedSpace S] in
/-- A circuit of `Γ'` with few vertices in `Γ` is short, and so it is null-homotopic. -/
theorem null_of_few [T2Space S] {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S
  (Set S))} {ins : Drawing S → Set S}
    (hw : IsWeighting Γ' (2 * θ) Γ.V θ) (hd : IsDerivedSlope Γ Γ' θ T ins) {D : Drawing S}
      (hD : D.IsCircuit)
    (hDs : D.IsSubdrawing Γ') (hfew : (Γ.V ∩ D.V).ncard < θ) : IsNullHomotopicOArc D.U := by
  have hl : D.length < 2 * θ := by
    by_contra hl
    exact absurd (hw.le_ncard D hD hDs (not_lt.mp hl)) (not_le.mpr hfew)
  exact null_of_short hd hD hDs hl

omit [ConnectedSpace S] in
/-- If circuits of `Γ'` with vertices in `V(A ∩ B)` have discs that include the edges of `A`, then
every `O`-arc in
`U(A)` is null-homotopic. This is the core of claim (1) of (6.4) (page 90). -/
theorem no_oArc_of_circuits [ConnectedSpace S] (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
  (hθ : 1 ≤ θ)
    (hrad : Γ.IsRadialDrawing Γ') (hd : IsDerivedSlope Γ Γ' θ T ins) {A B : Hypergraph S (Set S)}
    (hord : separationOrder A B < θ) {k : ℕ} {C : Fin k → Drawing S}
    (hC : ∀ i : Fin k, (C i).IsCircuit ∧ (C i).IsSubdrawing Γ' ∧ (C i).length < 2 * θ ∧
      (C i).V ∩ Γ.V ⊆ (A ∩ B).vertexSet) (hcov : ∀ e ∈ A.edgeSet, ∃ i : Fin k, e ⊆ ins (C i))
    {F : Set S} (hF : IsOArc F) (hFA : F ⊆ PaintingOrDrawing.underlying A) : IsNullHomotopicOArc F
      := by
  have : T2Space S := hS.2.1
  have hw : IsWeighting Γ' (2 * θ) Γ.V θ := isWeighting_radial hθ hrad.2.1.2.1
    (bipartite_of_preRadial hrad.2.1)
  let N : Drawing S := Γ'.span (⋃ i, (C i).V) (⋃ i, (C i).E)
  have hNs : N.IsSubdrawing Γ' := Drawing.span_isSubdrawing Γ' _ _
  have hCN : ∀ i, (C i).IsSubdrawing N := fun i => by
    refine ⟨fun x hx => Or.inl ⟨mem_iUnion.mpr ⟨i, hx⟩, (hC i).2.1.1 hx⟩, fun e he => ?_⟩
    change e ∈ (Γ'.span _ _).E
    rw [Γ'.span_E]
    exact ⟨mem_iUnion.mpr ⟨i, he⟩, (hC i).2.1.2 he⟩
  have hNV : N.V ∩ Γ.V ⊆ (A ∩ B).vertexSet := by
    rintro x ⟨hx | hx, hxV⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
      exact (hC i).2.2.2 ⟨hi, hxV⟩
    · obtain ⟨e, ⟨he, -⟩, hxe⟩ := mem_iUnion₂.mp hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp he
      have hxi : x ∈ closure e ∩ (C i).V := by
        rw [(hC i).2.1.closure_inter_V hi]
        exact hxe
      exact (hC i).2.2.2 ⟨hxi.2, hxV⟩
  obtain ⟨Δ, hΔ, hNΔ⟩ := exists_disc_of_circuits hS N fun D hD hDs =>
    null_of_few hw hd hD (hDs.trans hNs) ((ncard_le_ncard (fun x (hx : x ∈ Γ.V ∩ D.V) =>
      hNV ⟨hDs.1 hx.2, hx.1⟩) (A ∩ B).vertexSet_finite).trans_lt hord)
  have hsub : ∀ i, ins (C i) ⊆ Δ := fun i => by
    obtain ⟨d, b, -⟩ := hd (C i) (hC i).1 (hC i).2.1 (hC i).2.2.1
    refine disc_subset_of_bd hS hns d hΔ ?_
    rw [← IsClosedDisc.frontier_eq_discBd hS d, ← subBd_eq_frontier, b]
    exact (hCN i).U_subset.trans hNΔ
  have hFΔ : F ⊆ Δ := oArc_subset_of_edges hF (IsClosedDisc.isCompact hΔ).isClosed
    A.vertexSet_finite
    (fun e he => by
      obtain ⟨i, hi⟩ := hcov e he
      exact hi.trans (hsub i)) hFA
  exact isNullHomotopicOArcIn_of_subset_disc hF (subset_univ _) hΔ hFΔ

/-- **Claim (1) of (6.4)** (page 90). -/
theorem no_oArc_of_mem (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    (hE : Γ.E.Nonempty) (hT2 : Γ.IsTwoCell) (hT : IsPretangle Γ.toHypergraph θ T)
      (hresp : Γ.IsRespectful θ T)
    (hrad : Γ.IsRadialDrawing Γ') (hd : IsDerivedSlope Γ Γ' θ T ins) {A B : Hypergraph S (Set S)}
    (hsep : Γ.toHypergraph.IsSeparation A B) (hord : separationOrder A B < θ) (hmem : (A, B) ∈ T)
    {F : Set S} (hF : IsOArc F) (hFA : F ⊆ PaintingOrDrawing.underlying A) : IsNullHomotopicOArc F
      := by
  have : T2Space S := hS.2.1
  obtain ⟨k, C, hC, hcov⟩ := ((theorem_6_3_proof S hS inferInstance Γ Γ' θ T ins hT2 hE hT hresp
    hrad hd).1 A B hsep hord).mp hmem
  exact no_oArc_of_circuits hS hns hT.one_le hrad hd hord hC hcov hF hFA

end GraphMinor.GM11

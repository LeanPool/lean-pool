/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM12.Section4WalkMetric
import LeanPool.GraphMinor.GM11.Section64
import LeanPool.GraphMinor.GM11.Section7b
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM12.Section4MetricExistence

/-!
# Graph Minors XII, (7.9): uniqueness and restriction of subdrawing tangles

This file formalizes **(7.9)** of Graph Minors XII (page 270) using the proved `(2.1)`
via `(7.7)`, `(1.1)` (`GM11.theorem_6_3_of_regionFacts`), and `(1.2)`
(`exists_atom_dist_eq_theta`).
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Function Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Truncation and subgraph-induction of respectful tangles -/

omit [T2Space S] in
/-- If `H` is a 2-cell drawing and `T` is a respectful tangle of order `θ` in `H`, then for any
`1 ≤ θ' ≤ θ`, the truncation `GM10.truncation T θ'` is a respectful tangle of order `θ'` in `H`. -/
theorem IsRespectfulDrawingTangle.truncation {H : Drawing S} {θ θ' : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h : IsRespectfulDrawingTangle H θ T) (hpos : 1 ≤ θ') (hle : θ' ≤ θ) :
    IsRespectfulDrawingTangle H θ' (GM10.truncation T θ') := by
  rcases h with ⟨h2cell, hT, hConn, hResp⟩
  refine ⟨h2cell, hT.truncation hpos hle, hConn, fun F hF hNorm hcard => ?_⟩
  obtain ⟨Δ, hΔ, hbd, hmem⟩ := hResp F hF hNorm (lt_of_lt_of_le hcard hle)
  refine ⟨Δ, hΔ, hbd, hmem, ?_⟩
  have hsub : (((PaintingOrDrawing.drawing H).inter Δ) ∩
      ((PaintingOrDrawing.drawing H).interOutside Δ)).vertexSet ⊆ F ∩ H.V := by
    rintro x ⟨⟨hxV, hxΔ⟩, ⟨_, hxOut⟩⟩
    refine ⟨?_, hxV⟩
    rw [← hbd, GM11.subBd_eq_frontier, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
    exact ⟨subset_closure hxΔ, hxOut⟩
  exact lt_of_le_of_lt (ncard_le_ncard hsub (H.finite_V.subset inter_subset_right)) hcard

private theorem metric_walk_of_lt {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (ins : Drawing S → Set S) {θ : ℕ} {x y : Set S} (hne : x ≠ y)
    (hlt : tangleMetric H K ins θ x y < θ) :
    ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
      W.length < 2 * θ ∧ W.length = 2 * tangleMetric H K ins θ x y ∧
      x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W := by
  classical
  unfold tangleMetric at hlt ⊢
  simp only [hne, ↓reduceIte] at hlt ⊢
  split_ifs at hlt ⊢ with hex
  · have hnonempty : {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
        IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
        W.length < 2 * θ ∧ W.length = 2 * k ∧
        x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W}.Nonempty := by
      obtain ⟨u, W, x', y', hx, hy, hlen, hxW, hyW⟩ := hex
      refine ⟨W.support.tail.countP (· ∈ H.V), u, W, x', y', hx, hy, hlen, ?_, hxW, hyW⟩
      exact closed_walk_length_eq_two_mul hK.2.1 W
    exact Nat.sInf_mem hnonempty
  · exact (Nat.lt_irrefl _ hlt).elim

/-- Changing the order from `θ` to `θ' ≤ θ` truncates the radial metric at `θ'`. -/
theorem tangleMetric_truncation {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (ins : Drawing S → Set S) {θ θ' : ℕ} (hle : θ' ≤ θ) (x y : Set S) :
    tangleMetric H K ins θ' x y = min (tangleMetric H K ins θ x y) θ' := by
  classical
  by_cases heq : x = y
  · subst y
    simp only [tangleMetric, ↓reduceIte, Nat.zero_min]
  have hsmall := tangleMetric_le_order hK ins θ' x y
  apply le_antisymm
  · apply le_min _ hsmall
    by_cases hlt : tangleMetric H K ins θ x y < θ'
    · obtain ⟨u, W, x', y', hx, hy, _, hlen, hxW, hyW⟩ :=
        metric_walk_of_lt hK ins heq (hlt.trans_le hle)
      exact tangleMetric_le_of_walk hx hy W (by omega) hlen hxW hyW
    · exact hsmall.trans (Nat.le_of_not_gt hlt)
  · by_cases hlt : tangleMetric H K ins θ' x y < θ'
    · obtain ⟨u, W, x', y', hx, hy, hshort, hlen, hxW, hyW⟩ :=
        metric_walk_of_lt hK ins heq hlt
      have hw : W.length < 2 * θ := lt_of_lt_of_le hshort (Nat.mul_le_mul_left 2 hle)
      exact (min_le_left _ _).trans (tangleMetric_le_of_walk hx hy W hw hlen hxW hyW)
    · exact (min_le_right _ _).trans (Nat.le_of_not_gt hlt)

/-- Truncation of a respectful drawing tangle cuts off its metric at the new order. -/
theorem HasTangleMetric.truncation {H : Drawing S} {θ θ' : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (h : HasTangleMetric H θ T d)
    (hpos : 1 ≤ θ') (hle : θ' ≤ θ) :
    HasTangleMetric H θ' (GM10.truncation T θ') (fun a b => min (d a b) θ') := by
  classical
  obtain ⟨hresp, K, ins, hK, hins, hd⟩ := h
  refine ⟨IsRespectfulDrawingTangle.truncation hresp hpos hle, K, ins, hK, ?_, ?_⟩
  · intro C hC hCK hlen
    obtain ⟨hD, hbd, hmem⟩ := hins C hC hCK (lt_of_lt_of_le hlen (Nat.mul_le_mul_left 2 hle))
    refine ⟨hD, hbd, hmem, ?_⟩
    have hsub : (((PaintingOrDrawing.drawing H).inter (ins C)) ∩
        ((PaintingOrDrawing.drawing H).interOutside (ins C))).vertexSet ⊆ C.V ∩ H.V := by
      rintro x ⟨⟨hxH, hxD⟩, ⟨_, hxout⟩⟩
      have hxC : x ∈ C.U := hbd ▸ (show x ∈ subBd (ins C) from ⟨subset_closure hxD, hxout⟩)
      rw [C.U_eq] at hxC
      rcases hxC with hxCV | hxE
      · exact ⟨hxCV, hxH⟩
      · obtain ⟨e, heC, hxe⟩ := mem_iUnion₂.mp hxE
        have hxK := hK.2.1.2.1 hxH
        have hxCV : x ∈ closure e ∩ C.V := by
          rw [hCK.closure_inter_V heC]
          exact ⟨hxe, hxK⟩
        exact ⟨hxCV.2, hxH⟩
    have hc := (circuit_length_eq_two_mul_ncard hK.2.1 hC hCK).1
    have hcount := ncard_le_ncard hsub (C.finite_V.subset inter_subset_left)
    change (((PaintingOrDrawing.drawing H).inter (ins C)) ∩
        ((PaintingOrDrawing.drawing H).interOutside (ins C))).vertexSet.ncard < θ'
    omega
  · intro a ha b hb
    change min (d a b) θ' = _
    rw [hd a ha b hb, tangleMetric_truncation hK ins hle]

omit [T2Space S] in
private theorem drawing_inter_le (H' : Drawing S) {D : Set S} (hD : IsClosed D) :
    (PaintingOrDrawing.drawing H').inter D ≤ H'.toHypergraph := by
  refine ⟨inter_subset_left, fun _ h => h.1, fun e he => ?_⟩
  ext v
  change (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ↔
    (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ∧ e ⊆ D ∧ v ∈ D
  exact ⟨fun h => ⟨h, he.2, hD.closure_subset_iff.mpr he.2 h.2.2⟩, fun h => h.1⟩

/-- If `H₀` is a subdrawing of `H'` and `T₀` is a respectful tangle of order `θ'` in `H₀`, then
`inducedBySubgraph H'.toHypergraph H₀.toHypergraph θ' T₀` is respectful in `H'`. -/
theorem isRespectful_inducedBySubgraph {H₀ H' : Drawing S} {θ' : ℕ}
    {T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hSub : H₀.IsSubdrawing H')
    (hResp₀ : (PaintingOrDrawing.drawing H₀).IsRespectful θ' T₀) :
    (PaintingOrDrawing.drawing H').IsRespectful θ'
      (inducedBySubgraph H'.toHypergraph H₀.toHypergraph θ' T₀) := by
  refine ⟨hResp₀.1, fun F hF hNorm' hcard' => ?_⟩
  have hNorm₀ : (PaintingOrDrawing.drawing H₀).IsNormal F :=
    isNormal_of_isSubdrawing hSub hNorm'
  have hcard₀ : (F ∩ H₀.V).ncard < θ' :=
    lt_of_le_of_lt
      (ncard_le_ncard (inter_subset_inter_right F hSub.1) (H'.finite_V.subset inter_subset_right))
      hcard'
  obtain ⟨Δ, hΔ, hbd, hmem₀⟩ := hResp₀.2 F hF hNorm₀ hcard₀
  refine ⟨Δ, hΔ, hbd, ?_, ?_, ?_⟩
  · have hAl : (PaintingOrDrawing.drawing H').inter Δ ≤ H'.toHypergraph :=
      drawing_inter_le H' hΔ.isClosed
    have hBl : (PaintingOrDrawing.drawing H').interOutside Δ ≤ H'.toHypergraph :=
      drawing_inter_le H' isClosed_closure
    refine (isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩
    · ext x
      change (x ∈ H'.V ∩ Δ ∨ x ∈ H'.V ∩ closure (univ \ Δ)) ↔ x ∈ H'.V
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        by_cases hxΔ : x ∈ Δ
        · exact Or.inl ⟨hx, hxΔ⟩
        · exact Or.inr ⟨hx, subset_closure ⟨mem_univ x, hxΔ⟩⟩
    · ext e
      change (e ∈ {e ∈ H'.E | e ⊆ Δ} ∨ e ∈ {e ∈ H'.E | e ⊆ closure (univ \ Δ)}) ↔ e ∈ H'.E
      constructor
      · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
      · intro he
        obtain ⟨x, hxe⟩ := he.1
        have he_pre : IsPreconnected e :=
          (GM11.PaintingOrDrawing.edge_props (Γ := PaintingOrDrawing.drawing H') he).1
        have hdisF : Disjoint e (frontier Δ) := by
          rw [GM11.subBd_eq_frontier' Δ, hbd]
          exact disjoint_left.mpr fun y hye hyF =>
            (he.2.1 hye).2 (hNorm' ⟨hyF, (he.2.1 hye).1⟩)
        by_cases hxΔ : x ∈ Δ
        · exact Or.inl ⟨he, subset_of_disjoint_frontier
            he_pre hΔ.isClosed hdisF hxe hxΔ⟩
        · have hdisF' : Disjoint e (frontier (closure (univ \ Δ))) := by
            refine Disjoint.mono_right ?_ hdisF
            intro y hy
            have hy1 : y ∈ frontier (univ \ Δ) := frontier_closure_subset hy
            rwa [← compl_eq_univ_sdiff, frontier_compl] at hy1
          exact Or.inr ⟨he, subset_of_disjoint_frontier
            he_pre isClosed_closure hdisF' hxe (subset_closure ⟨mem_univ x, hxΔ⟩)⟩
    · ext e
      change (e ∈ {e ∈ H'.E | e ⊆ Δ} ∧ e ∈ {e ∈ H'.E | e ⊆ closure (univ \ Δ)}) ↔
        e ∈ (∅ : Set (Set S))
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨he, heΔ⟩, ⟨_, heOut⟩⟩
      obtain ⟨x, hxe⟩ := he.1
      have hxF : x ∈ F := by
        rw [← hbd, GM11.subBd_eq_frontier, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
        exact ⟨subset_closure (heΔ hxe), heOut hxe⟩
      exact (he.2.1 hxe).2 (hNorm' ⟨hxF, (he.2.1 hxe).1⟩)
  · have hsub : (((PaintingOrDrawing.drawing H').inter Δ) ∩
        ((PaintingOrDrawing.drawing H').interOutside Δ)).vertexSet ⊆ F ∩ H'.V := by
      rintro x ⟨⟨hxV, hxΔ⟩, ⟨_, hxOut⟩⟩
      refine ⟨?_, hxV⟩
      rw [← hbd, GM11.subBd_eq_frontier, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
      exact ⟨subset_closure hxΔ, hxOut⟩
    exact lt_of_le_of_lt (ncard_le_ncard hsub (H'.finite_V.subset inter_subset_right)) hcard'
  · rwa [drawing_inter_inter_subdrawing hSub Δ, drawing_interOutside_inter_subdrawing hSub Δ]

/-- Every circuit `C` of a pre-radial drawing `K` of `H` has `C.U` an `O`-arc,
`C.length = 2 * (C.U ∩ H.V).ncard`, and `2 ≤ C.length`. -/
theorem circuit_props_of_preRadial {H K C : Drawing S}
    (hP : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing K) :
    IsOArc C.U ∧ C.length = 2 * (C.U ∩ H.V).ncard ∧ 2 ≤ C.length := by
  have hoarc : IsOArc C.U := IsCircuit.isOArc_U hC
  obtain ⟨hlen, hne⟩ := circuit_length_eq_two_mul_ncard hP hC hCs
  have hUV : C.U ∩ H.V = C.V ∩ H.V := by
    refine Subset.antisymm ?_ (inter_subset_inter_left H.V C.V_subset_U)
    rintro x ⟨hxCU, hxHV⟩
    exact ⟨(isSubdrawing_U_inter_V hCs).subset ⟨hxCU, hP.2.1 hxHV⟩, hxHV⟩
  rw [hUV]
  obtain ⟨x, hxCV, hxHV⟩ := hne
  have h1 : 1 ≤ (C.V ∩ H.V).ncard :=
    (ncard_pos (C.finite_V.subset inter_subset_left)).mpr ⟨x, hxCV, hxHV⟩
  exact ⟨hoarc, hlen, by omega⟩

/-- Every respectful tangle `T` of order `θ` in a 2-cell drawing `H` has a derived slope `ins` in
any radial drawing `K` of `H`. -/
theorem exists_derivedSlope_of_respectful {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hResp : IsRespectfulDrawingTangle H θ T)
    (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) :
    ∃ ins : Drawing S → Set S, IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins :=
  GM11.exists_derivedSlope_of_preRadial hResp.2.2 hrad

/-- Every respectful tangle `T` of order `θ` in a 2-cell drawing `H` in a closed surface `S` has a
tangle metric `d` (`HasTangleMetric H θ T d`). -/
theorem exists_hasTangleMetric (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hResp : IsRespectfulDrawingTangle H θ T) :
    ∃ d : Set S → Set S → ℕ, HasTangleMetric H θ T d :=
  exists_metric_of_respectful_drawing_tangle hS hResp

/-! ## 2. Helper lemmas for (7.9) -/

/-- For any 2-cell drawing `H` in a closed surface `S` with a respectful tangle `T` of order `θ ≥ 2`
with metric `d`, and any atom `z ∈ H.A`, there exists an atom `b ∈ H.A` with `d z b = θ`
(Graph Minors XII, (1.2), page 242). -/
theorem exists_atom_dist_eq_theta (hS : IsClosedSurface S) [ConnectedSpace S]
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hMetric : HasTangleMetric H θ T d) (hθ : 2 ≤ θ)
    {z : Set S} (hz : z ∈ H.A) :
    ∃ b ∈ H.A, d z b = θ := by
  have hE : H.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hMetric.1.2.1 hθ
  obtain ⟨e, he, hDist⟩ := exists_edge_for_metric_eq_order hS inferInstance hMetric hE hz
  by_cases hze : z = e
  · have hEnds : (closure e ∩ H.V).Nonempty := by
      rcases H.edge_cond e he with ⟨u, v, _, hcl, _⟩ | ⟨u, hcl, _⟩
      · exact ⟨u, by rw [hcl]; simp⟩
      · exact ⟨u, by rw [hcl]; simp⟩
    obtain ⟨u, hu⟩ := hEnds
    have huA : ({u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u, hu.2, rfl⟩)
    have hne : z ≠ {u} := fun h =>
      (he.2.1 ((hze.symm.trans h).symm ▸ mem_singleton u)).2 hu.2
    exact ⟨{u}, huA, hDist _ huA hne (Or.inr hze)⟩
  · have heA : e ∈ H.A := Or.inl (Or.inr he)
    exact ⟨e, heA, hDist _ heA hze (Or.inl rfl)⟩

/-- By `(2.1)`, if `F` is a `Γ'`-normal `O`-arc with `(F ∩ Γ'.V).ncard < θ'` and `Δ` is its inside
disc with respect to `(T', d')`, then any two atoms `a', b' ∈ Γ'.A` meeting `Δ` have
`d' a' b' ≤ (F ∩ Γ'.V).ncard`. -/
theorem dist_le_of_oarc_disc
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ' : Drawing S} {θ' : ℕ}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d' : Set S → Set S → ℕ}
    (hd' : HasTangleMetric Γ' θ' T' d')
    {F Δ : Set S} (hF : IsOArc F)
    (hF_norm : (PaintingOrDrawing.drawing Γ').IsNormal F)
    (hcard : (F ∩ Γ'.V).ncard < θ')
    (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hmem : ((PaintingOrDrawing.drawing Γ').inter Δ,
      (PaintingOrDrawing.drawing Γ').interOutside Δ) ∈ T')
    {a' b' : Set S} (ha' : a' ∈ Γ'.A) (hb' : b' ∈ Γ'.A)
    (ha'Δ : (a' ∩ Δ).Nonempty) (hb'Δ : (b' ∩ Δ).Nonempty) :
    d' a' b' ≤ (F ∩ Γ'.V).ncard := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_cases hab' : a' = b'
  · subst hab'
    rw [metric_self hd' ha']
    exact Nat.zero_le _
  obtain ⟨hResp', K', ins', hrad', hslope', hd'_eq⟩ := id hd'
  obtain ⟨e⟩ := id hF
  let φ : C(Circle, S) := ⟨fun z => (e z).1, continuous_subtype_val.comp e.continuous⟩
  have hφ_inj : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hran : range φ = F := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (e z).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp [φ]⟩
  have hhit_eq : φ '' {z : Circle | φ z ∈ Γ'.U} = F ∩ Γ'.U := by
    ext x
    simp only [mem_image, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(e z).2, hz⟩
    · rintro ⟨hxF, hxU⟩
      exact ⟨e.symm ⟨x, hxF⟩, by simpa [φ] using hxU, by simp [φ]⟩
  have hFU_eq : F ∩ Γ'.U = F ∩ Γ'.V := by
    refine Subset.antisymm (fun x hx => ⟨hx.1, hF_norm hx⟩)
      (inter_subset_inter_right F Γ'.V_subset_U)
  have hhit_fin : {z : Circle | φ z ∈ Γ'.U}.Finite := by
    refine Finite.of_finite_image ?_ hφ_inj.injOn
    rw [hhit_eq, hFU_eq]
    exact Γ'.finite_V.subset inter_subset_right
  have hnormφ : IsNormalCurve Γ' φ := ⟨hhit_fin, by rwa [hran]⟩
  have hclen : curveLength Γ' φ = (F ∩ Γ'.V).ncard := by
    unfold curveLength
    rw [← ncard_image_of_injective _ hφ_inj, hhit_eq, hFU_eq]
  have hclen_lt : curveLength Γ' φ < θ' := hclen.symm ▸ hcard
  have h21_app := theorem_2_1_statement S hS Γ' K' θ' T' ins' hrad' hResp'.2.1.one_le hResp'.2.1
    hResp'.2.2
    hslope' φ hnormφ hclen_lt
  obtain ⟨⟨v, W', htr'⟩, h21_prop⟩ := h21_app
  obtain ⟨hW'_lt, h21_disc⟩ := h21_prop v W' htr'
  have hW'_len : W'.length = 2 * curveLength Γ' φ := by
    rcases htr'.2 with ⟨h0, hW0, -⟩ | ⟨-, hW2, -⟩
    · rw [h0, hW0]
    · exact hW2
  have ha'W : (a' ∩ insWalk ins' K' W').Nonempty :=
    h21_disc a' ha' F Δ hF (by rw [hran]) hΔ hbd hmem ha'Δ
  have hb'W : (b' ∩ insWalk ins' K' W').Nonempty :=
    h21_disc b' hb' F Δ hF (by rw [hran]) hΔ hbd hmem hb'Δ
  obtain ⟨a'_K, ha'_K, -⟩ := existsUnique_correspondingAtom' hrad' ha'
  obtain ⟨b'_K, hb'_K, -⟩ := existsUnique_correspondingAtom' hrad' hb'
  have ha'_sub : a'_K ⊆ insWalk ins' K' W' :=
    (corresponding_atom_subset_iff hS hrad' hslope' ha'_K W' hW'_lt).mpr ha'W
  have hb'_sub : b'_K ⊆ insWalk ins' K' W' :=
    (corresponding_atom_subset_iff hS hrad' hslope' hb'_K W' hW'_lt).mpr hb'W
  rw [hd'_eq a' ha' b' hb', ← hclen]
  exact tangleMetric_le_of_walk ha'_K hb'_K W' hW'_lt hW'_len ha'_sub hb'_sub

/-- If `H₁` is a 2-cell drawing in a closed surface `S` with `H₁.E = ∅`, then `H₁.V.ncard ≤ 1`. -/
theorem ncard_V_le_one_of_E_empty [ConnectedSpace S]
    (hS : IsClosedSurface S) {H₁ : Drawing S} (h2cell : (PaintingOrDrawing.drawing H₁).IsTwoCell)
    (hE : H₁.E = ∅) : H₁.V.ncard ≤ 1 := by
  classical
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_contra hgt
  have h1lt : 1 < H₁.V.ncard := Nat.lt_of_not_le hgt
  obtain ⟨x, z, hx, hz, hxz⟩ := (Set.one_lt_ncard_iff H₁.finite_V).mp h1lt
  let Bad : Set S := H₁.V \ {x}
  have hBad : IsClosed Bad := (H₁.finite_V.subset sdiff_subset).isClosed
  have hxBad : x ∉ Bad := fun h => h.2 rfl
  obtain ⟨D, D', hD, hD', hxD', hD'D, hDO, hbdD⟩ :=
    exists_closedDisc_nbhd hS hBad.isOpen_compl hxBad
  have hU_eq : H₁.U = H₁.V := by rw [H₁.U_eq, hE]; simp
  have hbdU : Disjoint (discBd D) H₁.U := by
    refine disjoint_left.mpr fun y hy hyU => ?_
    have hyD : y ∈ D := GM11.discBd_subset D hy
    have hyx : y ≠ x := fun h => (hbdD ▸ hy).2 (h ▸ hxD')
    exact hDO hyD ⟨hU_eq ▸ hyU, hyx⟩
  have hF := hD.isOArc_discBd
  have hbdne : (discBd D).Nonempty := by obtain ⟨φ⟩ := hF; exact ⟨_, (φ 1).2⟩
  have hbdconn : IsPreconnected (discBd D) := by
    obtain ⟨φ⟩ := hF
    have : discBd D = range fun w => (φ w).1 := by
      ext y
      exact ⟨fun hy => ⟨φ.symm ⟨y, hy⟩, by simp⟩, by rintro ⟨w, rfl⟩; exact (φ w).2⟩
    rw [this]
    exact isPreconnected_range (by fun_prop)
  obtain ⟨y, hy⟩ := hbdne
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem (disjoint_left.mp hbdU hy)
  have hsub : discBd D ⊆ r := subset_region hr hbdconn hbdU hy hyr
  obtain ⟨Δ, hΔr, hΔ, hb⟩ := GM11.exists_disc_in_openDisc (h2cell.2 r hr) hF hsub
  have hxΔ : x ∉ Δ := fun h => region_subset hr (hΔr h) (H₁.V_subset_U hx)
  have hcov := GM11.cover_of_discBd_eq hS hD hΔ hb.symm fun h => hxΔ (h ▸ hD'D hxD')
  have hzU : z ∈ H₁.U := H₁.V_subset_U hz
  rcases (hcov ▸ mem_univ z : z ∈ D ∪ Δ) with h | h
  · exact hDO h ⟨hz, hxz.symm⟩
  · exact region_subset hr (hΔr h) hzU

/-! ## 3. Proof of (7.9) -/

/-- Second claim of **(7.9)**: uniqueness of the respectful tangle `T'` of order `θ - k` in `Γ'`
whose metric `d'` satisfies `d'(a', b') ≥ d(a, b) - k`. -/
theorem theorem_7_9_unique
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ Γ' : Drawing S} {θ k : ℕ}
    {T T' T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' d'' : Set S → Set S → ℕ}
    (hd : HasTangleMetric Γ θ T d)
    (hSub : Γ'.IsSubdrawing Γ)
    (hk : k < θ)
    (hd' : HasTangleMetric Γ' (θ - k) T' d')
    (hge' : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
      a ⊆ a' → b ⊆ b' → d a b - k ≤ d' a' b')
    (hd'' : HasTangleMetric Γ' (θ - k) T'' d'')
    (hge'' : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
      a ⊆ a' → b ⊆ b' → d a b - k ≤ d'' a' b') :
    T'' = T' := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hResp', K', ins', hK', hins', _⟩ := id hd'
  obtain ⟨ins'', hins''⟩ := exists_derivedSlope_of_respectful hd''.1 hK'.2.1
  have hCircEq : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing K' →
      C.length < 2 * (θ - k) → ins' C = ins'' C := by
    intro C hC hCs hlen
    obtain ⟨hoarc, hlen_eq, h2le⟩ := circuit_props_of_preRadial hK'.2.1 hC hCs
    have hcard_lt : (C.U ∩ Γ'.V).ncard < θ - k := by omega
    have hθ2 : 2 ≤ θ := by omega
    have hnorm' : (PaintingOrDrawing.drawing Γ').IsNormal C.U := by
      rintro x ⟨hxC, hxH⟩
      have : x ∈ (PaintingOrDrawing.drawing Γ').U ∩ K'.U := ⟨hxH, hCs.U_subset hxC⟩
      rwa [hK'.2.1.1] at this
    obtain ⟨v, W_C, _, _, hCV, _⟩ := id hC
    have hvU : v ∈ C.U := C.V_subset_U (hCV ▸ W_C.start_mem_support)
    obtain ⟨a, ha, hva⟩ := GM11.exists_atom Γ v
    obtain ⟨b, hb, hd_ab⟩ := exists_atom_dist_eq_theta hS hd hθ2 ha
    obtain ⟨σ, hσb⟩ := atom_nonempty' hb
    obtain ⟨a', ha', haa'⟩ := exists_atom_superset_of_isSubdrawing hSub ha
    obtain ⟨b', hb', hbb'⟩ := exists_atom_superset_of_isSubdrawing hSub hb
    have hd'_ge : θ - k ≤ d' a' b' := by
      have := hge' a ha b hb a' ha' b' hb' haa' hbb'
      omega
    have hd''_ge : θ - k ≤ d'' a' b' := by
      have := hge'' a ha b hb a' ha' b' hb' haa' hbb'
      omega
    obtain ⟨hD₁, hbd₁, hmem₁⟩ := hins' C hC hCs hlen
    obtain ⟨hD₂, hbd₂, hmem₂⟩ := hins'' C hC hCs hlen
    have hv_D₁ : v ∈ ins' C := by
      have : v ∈ subBd (ins' C) := hbd₁ ▸ hvU
      exact hD₁.isClosed.closure_eq ▸ this.1
    have hv_D₂ : v ∈ ins'' C := by
      have : v ∈ subBd (ins'' C) := hbd₂ ▸ hvU
      exact hD₂.isClosed.closure_eq ▸ this.1
    have ha'_D₁ : (a' ∩ ins' C).Nonempty := ⟨v, haa' hva, hv_D₁⟩
    have ha'_D₂ : (a' ∩ ins'' C).Nonempty := ⟨v, haa' hva, hv_D₂⟩
    have hσ_not_D₁ : σ ∉ ins' C := fun hσ₁ => by
      have hb'_D₁ : (b' ∩ ins' C).Nonempty := ⟨σ, hbb' hσb, hσ₁⟩
      have hle := dist_le_of_oarc_disc hS hd' hoarc hnorm' hcard_lt hD₁ hbd₁ hmem₁
        ha' hb' ha'_D₁ hb'_D₁
      omega
    have hσ_not_D₂ : σ ∉ ins'' C := fun hσ₂ => by
      have hb'_D₂ : (b' ∩ ins'' C).Nonempty := ⟨σ, hbb' hσb, hσ₂⟩
      have hle := dist_le_of_oarc_disc hS hd'' hoarc hnorm' hcard_lt hD₂ hbd₂ hmem₂
        ha' hb' ha'_D₂ hb'_D₂
      omega
    by_contra hne
    have hdb : discBd (ins' C) = discBd (ins'' C) := by
      rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hD₁,
        ← GM11.IsClosedDisc.frontier_eq_discBd hS hD₂,
        GM11.subBd_eq_frontier', GM11.subBd_eq_frontier', hbd₁, hbd₂]
    have hcov := GM11.cover_of_discBd_eq hS hD₁ hD₂ hdb hne
    rcases (hcov ▸ mem_univ σ : σ ∈ ins' C ∪ ins'' C) with h | h
    · exact hσ_not_D₁ h
    · exact hσ_not_D₂ h
  have hT' : IsTangle Γ'.toHypergraph (θ - k) T' := hResp'.2.1
  have hT'' : IsTangle Γ'.toHypergraph (θ - k) T'' := hd''.1.2.1
  have hPre' : IsPretangle (PaintingOrDrawing.drawing Γ').toHypergraph (θ - k) T' :=
    ⟨hT'.one_le, hT'.isSeparation, hT'.order_lt, hT'.axiom1, hT'.axiom2⟩
  have hPre'' : IsPretangle (PaintingOrDrawing.drawing Γ').toHypergraph (θ - k) T'' :=
    ⟨hT''.one_le, hT''.isSeparation, hT''.order_lt, hT''.axiom1, hT''.axiom2⟩
  have hsub_tangle : ∀ {U₁ U₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
      {ins₁ ins₂ : Drawing S → Set S},
      IsTangle Γ'.toHypergraph (θ - k) U₁ →
      IsTangle Γ'.toHypergraph (θ - k) U₂ →
      IsPretangle (PaintingOrDrawing.drawing Γ').toHypergraph (θ - k) U₁ →
      IsPretangle (PaintingOrDrawing.drawing Γ').toHypergraph (θ - k) U₂ →
      IsDerivedSlope (PaintingOrDrawing.drawing Γ') K' (θ - k) U₁ ins₁ →
      IsDerivedSlope (PaintingOrDrawing.drawing Γ') K' (θ - k) U₂ ins₂ →
      (∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing K' →
        C.length < 2 * (θ - k) → ins₁ C = ins₂ C) →
      U₁ ⊆ U₂ := by
    intro U₁ U₂ ins₁ ins₂ hU₁ hU₂ hPU₁ hPU₂ hins₁ hins₂ hCEq
    by_cases hE : Γ'.E.Nonempty
    · have hf : GM11.RegionFacts (PaintingOrDrawing.drawing Γ') K' :=
        GM11.regionFacts_of_radial ⟨hK'.1, hK'.2.1⟩ hS hK'.2.2 hE
      have h63_1 := (GM11.theorem_6_3_of_regionFacts hS hPU₁ hK'.2.1 hins₁ hf).1
      have h63_2 := (GM11.theorem_6_3_of_regionFacts hS hPU₂ hK'.2.1 hins₂ hf).1
      rintro ⟨A, B⟩ hAB
      have hsep := hU₁.isSeparation hAB
      have hord := hU₁.order_lt hAB
      obtain ⟨m, C, hC, hin⟩ := (h63_1 A B hsep hord).mp hAB
      refine (h63_2 A B hsep hord).mpr ⟨m, C, hC, fun e he => ?_⟩
      obtain ⟨i, hi⟩ := hin e he
      obtain ⟨hc, hs, hl, _⟩ := hC i
      rw [hCEq (C i) hc hs hl] at hi
      exact ⟨i, hi⟩
    · have hE_empty : Γ'.E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
      have hV_le : Γ'.V.ncard ≤ 1 := ncard_V_le_one_of_E_empty hS hK'.1 hE_empty
      have hord_le : θ - k ≤ 1 := hU₁.order_le_ncard_vertexSet.trans hV_le
      rintro ⟨A, B⟩ hAB
      have hsep := hU₁.isSeparation hAB
      have hVA_empty : A.vertexSet = ∅ := by
        by_contra hne
        obtain ⟨x, hxA⟩ := Set.nonempty_iff_ne_empty.mpr hne
        have hxV : x ∈ Γ'.V := hsep.left_le.vertexSet_subset hxA
        have hV_eq : Γ'.V = {x} := by
          apply Set.Subset.antisymm _ (Set.singleton_subset_iff.mpr hxV)
          intro y hy
          by_contra hyx
          have hxy_ne : x ≠ y := fun h => hyx (h.symm ▸ Set.mem_singleton x)
          have h2 : ({x, y} : Set S).ncard = 2 := Set.ncard_pair hxy_ne
          have hsub : ({x, y} : Set S) ⊆ Γ'.V := by
            rintro w (rfl | rfl)
            · exact hxV
            · exact hy
          have := Set.ncard_le_ncard hsub Γ'.finite_V
          omega
        have hVA : A.vertexSet = Γ'.V :=
          Set.Subset.antisymm hsep.left_le.vertexSet_subset (hV_eq ▸ Set.singleton_subset_iff.mpr
            hxA)
        exact hU₁.axiom3 hAB hVA
      have hVB_eq : B.vertexSet = Γ'.V := by
        have := hsep.vertexSet_union
        rwa [hVA_empty, Set.empty_union] at this
      have hord₂ : separationOrder A B < θ - k := hU₁.order_lt hAB
      exact (hU₂.axiom1 hsep hord₂).resolve_right fun hBA => hU₂.axiom3 hBA hVB_eq
  exact Subset.antisymm
    (hsub_tangle hT'' hT' hPre'' hPre' hins'' hins' fun C hC hCs hlen =>
      (hCircEq C hC hCs hlen).symm)
    (hsub_tangle hT' hT'' hPre' hPre'' hins' hins'' hCircEq)

/-- **(7.9)** of Graph Minors XII (page 270):
"Let $k \ge 0$ be an integer. Let $\mathscr{T}$ be a respectful tangle of order $\theta > k$
in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$; let its metric be $d$. Let
$\Gamma'$ be a 2-cell subdrawing of $\Gamma$, and let $\mathscr{T}'$ be a respectful tangle
of order $\theta - k$ in $\Gamma'$, with metric $d'$, such that $d'(a', b') \ge d(a, b) - k$
for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$ and $b
\subseteq b'$. Then $(A \cap \Gamma', B \cap \Gamma') \in \mathscr{T}'$ for all $(A, B) \in
\mathscr{T}$ of order $< \theta - k$. Moreover, if $\mathscr{T}''$ is another respectful
tangle of order $\theta - k$ in $\Gamma'$, with metric $d''$, and again $d''(a', b') \ge
d(a, b) - k$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$
and $b \subseteq b'$, then $\mathscr{T}'' = \mathscr{T}'$." -/
theorem theorem_7_9_proof
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ Γ' : Drawing S} {θ k : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ}
    (hd : HasTangleMetric Γ θ T d)
    (hSub : Γ'.IsSubdrawing Γ)
    (h2cell' : (PaintingOrDrawing.drawing Γ').IsTwoCell)
    (hk : k < θ)
    (hd' : HasTangleMetric Γ' (θ - k) T' d')
    (hge' : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
      a ⊆ a' → b ⊆ b' → d a b - k ≤ d' a' b') :
    (∀ A B : Hypergraph S (Set S),
      (A, B) ∈ T → separationOrder A B < θ - k →
        (A ∩ Γ'.toHypergraph, B ∩ Γ'.toHypergraph) ∈ T') ∧
    (∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d'' : Set S → Set S → ℕ),
      HasTangleMetric Γ' (θ - k) T'' d'' →
      (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d a b - k ≤ d'' a' b') →
      T'' = T') := by
  refine ⟨?_, fun T'' d'' hd'' hge'' =>
    theorem_7_9_unique hS hd hSub hk hd' hge' hd'' hge''⟩
  let T₁ := inducedBySubgraph Γ.toHypergraph Γ'.toHypergraph (θ - k) T'
  let T₂ := GM10.truncation T (θ - k)
  have hSubHyp : Γ'.toHypergraph ≤ Γ.toHypergraph := toHypergraph_le_of_isSubdrawing hSub
  have hT₁ : IsTangle Γ.toHypergraph (θ - k) T₁ :=
    inducedBySubgraph_isTangle hSubHyp hd'.1.2.1
  have hResp₁ : (PaintingOrDrawing.drawing Γ).IsRespectful (θ - k) T₁ :=
    isRespectful_inducedBySubgraph hSub hd'.1.2.2
  have hRDT₁ : IsRespectfulDrawingTangle Γ (θ - k) T₁ :=
    ⟨hd.1.1, hT₁, hResp₁⟩
  obtain ⟨d₁, hd₁⟩ := exists_hasTangleMetric hS hRDT₁
  have h77_ii := (theorem_7_7_proof hS hd₁ hSub h2cell' le_rfl hd').2 rfl rfl
  have hge₁ : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ.A, ∀ b' ∈ Γ.A,
      a ⊆ a' → b ⊆ b' → d a b - k ≤ d₁ a' b' := by
    intro a ha b hb a' ha' b' hb' haa' hbb'
    obtain ⟨x, hxa⟩ := atom_nonempty' ha
    obtain ⟨y, hyb⟩ := atom_nonempty' hb
    have ha_eq : a' = a := atom_eq_of_inter_nonempty ha' ha ⟨x, haa' hxa, hxa⟩
    have hb_eq : b' = b := atom_eq_of_inter_nonempty hb' hb ⟨y, hbb' hyb, hyb⟩
    rw [ha_eq, hb_eq]
    obtain ⟨a₁, ha₁, haa₁⟩ := exists_atom_superset_of_isSubdrawing hSub ha
    obtain ⟨b₁, hb₁, hbb₁⟩ := exists_atom_superset_of_isSubdrawing hSub hb
    exact (hge' a ha b hb a₁ ha₁ b₁ hb₁ haa₁ hbb₁).trans
      (h77_ii a ha b hb a₁ ha₁ b₁ hb₁ haa₁ hbb₁)
  have hd₂ : HasTangleMetric Γ (θ - k) T₂ (fun a b => min (d a b) (θ - k)) :=
    HasTangleMetric.truncation hd (by omega) (Nat.sub_le θ k)
  have hge₂ : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ.A, ∀ b' ∈ Γ.A,
      a ⊆ a' → b ⊆ b' → d a b - k ≤ min (d a' b') (θ - k) := by
    intro a ha b hb a' ha' b' hb' haa' hbb'
    obtain ⟨x, hxa⟩ := atom_nonempty' ha
    obtain ⟨y, hyb⟩ := atom_nonempty' hb
    have ha_eq : a' = a := atom_eq_of_inter_nonempty ha' ha ⟨x, haa' hxa, hxa⟩
    have hb_eq : b' = b := atom_eq_of_inter_nonempty hb' hb ⟨y, hbb' hyb, hyb⟩
    rw [ha_eq, hb_eq]
    obtain ⟨_, K, ins, hK, _, hd_eq⟩ := id hd
    have hle_θ : d a b ≤ θ := by
      rw [hd_eq a ha b hb]
      exact tangleMetric_le_order hK ins θ a b
    exact le_min (Nat.sub_le _ _) (by omega)
  have hT₁_eq_T₂ : T₂ = T₁ :=
    theorem_7_9_unique hS hd (Drawing.IsSubdrawing.refl Γ) hk hd₁ hge₁ hd₂ hge₂
  intro A B hAB hord
  have hmem₂ : (A, B) ∈ T₂ := ⟨hAB, hord⟩
  rw [hT₁_eq_T₂] at hmem₂
  exact hmem₂.2.2

end GraphMinor.GM12

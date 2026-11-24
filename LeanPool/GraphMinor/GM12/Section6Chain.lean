/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section6Walk
public import LeanPool.GraphMinor.GM12.Section78
public import LeanPool.GraphMinor.GM12.Section4WalkMetric
public import LeanPool.GraphMinor.GM11.Section92
public import LeanPool.GraphMinor.GM11.Theorem61
public import LeanPool.GraphMinor.GM12.Section5Side

/-!
# Graph Minors XII, Section 6: claim (2) of (6.1)

`claim_two` is claim (2) of the paper: a restraint `Y` holding all of `F ∩ V(Γ)` has `l(Y) ≥ 2θ`.

`two_points` says that a closed walk through two points whose levels differ by `n` has length at
least
`2n`, when each edge changes the level by at most one. It is used for the closed walk `W*` in (6.1).
-/


public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem frontier_sub_U (hS : IsClosedSurface S) {K : Drawing S} {Y : Set S}
    (hc : IsClosed Y) (hn : IsGammaNice K Y) : frontier Y ⊆ K.U := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  intro x hx
  by_contra hU
  obtain ⟨s, hs, hxs⟩ := exists_region_of_notMem hU
  have hsY := nice_region hn hs ⟨x, hxs, hc.frontier_subset hx⟩
  exact hx.2 (mem_interior.mpr ⟨s, hsY, region_isOpen hs, hxs⟩)

open Classical in
omit [TopologicalSpace S] [T2Space S] in
theorem ncard_list_inter (l : List S) (A : Set S) :
    ({x | x ∈ l} ∩ A).ncard ≤ l.countP (· ∈ A) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    by_cases hy : y ∈ A
    · have hsub : {x | x ∈ y :: l} ∩ A ⊆ insert y ({x | x ∈ l} ∩ A) := by
        rintro x ⟨hx, hxA⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact .inl rfl
        · exact .inr ⟨hx, hxA⟩
      have h1 := ncard_le_ncard hsub (((List.finite_toSet l).inter_of_left A).insert y)
      have h2 := ncard_insert_le y ({x | x ∈ l} ∩ A)
      rw [List.countP_cons_of_pos (by simpa using hy)]
      omega
    · have hsub : {x | x ∈ y :: l} ∩ A ⊆ {x | x ∈ l} ∩ A := by
        rintro x ⟨hx, hxA⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (hy hxA).elim
        · exact ⟨hx, hxA⟩
      have h1 := ncard_le_ncard hsub ((List.finite_toSet l).inter_of_left A)
      rw [List.countP_cons_of_neg (by simpa using hy)]
      omega

omit [T2Space S] in
/-- A closed walk of `K` of length `< 4k` meets `V(Γ)` in fewer than `2k` points. -/
theorem order_lt {Γ K : Drawing S} (hpr : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {u :
  S}
    (W : GraphWalk K.toGraph u u) {k : ℕ} (_hk : 2 ≤ k) (hl : W.length < 4 * k) :
    ({x | x ∈ W.support} ∩ Γ.V).ncard < 2 * k := by
  classical
  have h2 := closed_walk_length_eq_two_mul hpr W
  cases W with
  | nil hv =>
    have hsub : {x | x ∈ (GraphWalk.nil hv : GraphWalk K.toGraph u u).support} ∩ Γ.V ⊆ {u} := by
      rintro x ⟨hx, -⟩
      simpa [GraphWalk.support] using hx
    have := ncard_le_ncard hsub (finite_singleton u)
    rw [ncard_singleton] at this
    omega
  | @cons _ y _ e hlk r =>
    have hsub : {x | x ∈ (GraphWalk.cons hlk r).support} ∩ Γ.V ⊆ {x | x ∈ r.support} ∩ Γ.V := by
      rintro x ⟨hx, hxV⟩
      refine ⟨?_, hxV⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact r.end_mem_support
      · exact hx
    have h1 := ncard_le_ncard hsub ((List.finite_toSet _).inter_of_left _)
    have h3 := ncard_list_inter r.support Γ.V
    have h4 : (GraphWalk.cons hlk r).support.tail = r.support := rfl
    rw [h4] at h2
    have h5 : r.support.countP (· ∈ Γ.V) * 2 < 4 * k := by
      convert (show _ < 4 * k from hl) using 1
      rw [h2]
      ring_nf
    omega

omit [T2Space S] in
/-- Walks and a level function that changes by at most one on each step. -/
theorem level_bound {K : Drawing S} {lev : S → ℕ} {x y : S} (w : GraphWalk K.toGraph x y)
    (hstep : ∀ e ∈ w.edges, ∀ p q, closure e ∩ K.V = {p, q} → lev p ≤ lev q + 1 ∧ lev q
      ≤ lev p + 1) :
    lev y ≤ lev x + w.length ∧ lev x ≤ lev y + w.length := by
  induction w with
  | nil _ => simp [GraphWalk.length, GraphWalk.edges]
  | @cons a b c e hl r ih =>
    have h1 := hstep e List.mem_cons_self a b hl.2.2.2
    have h2 := ih fun f hf => hstep f (List.mem_cons_of_mem _ hf)
    have h3 : (GraphWalk.cons hl r).length = r.length + 1 := by
      simp [GraphWalk.length, GraphWalk.edges]
    omega

omit [T2Space S] in
/-- A closed walk through two points of levels differing by `n` has length at least `2n`. -/
theorem two_points {K : Drawing S} {lev : S → ℕ} {u p q : S} (W : GraphWalk K.toGraph u u)
    (hstep : ∀ e ∈ W.edges, ∀ x y, closure e ∩ K.V = {x, y} → lev x ≤ lev y + 1 ∧ lev y ≤ lev x + 1)
    (hp : p ∈ W.support) (hq : q ∈ W.support) {n : ℕ} (hn : lev q = lev p + n) :
    2 * n ≤ W.length := by
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hp
  have hmem : q ∈ (W₂.append W₁).support := by
    rcases (GraphWalk.mem_support_append _ _).mp hq with h | h
    · exact (GraphWalk.mem_support_append _ _).mpr (.inr h)
    · exact (GraphWalk.mem_support_append _ _).mpr (.inl h)
  have hstep' : ∀ e ∈ (W₂.append W₁).edges, ∀ x y, closure e ∩ K.V = {x, y} →
      lev x ≤ lev y + 1 ∧ lev y ≤ lev x + 1 := fun e he => hstep e (by
    rw [GraphWalk.edges_append, List.mem_append] at he ⊢
    exact he.symm)
  have hlen : (W₂.append W₁).length = (W₁.append W₂).length := by
    rw [GraphWalk.length_append, GraphWalk.length_append, add_comm]
  rw [← hlen]
  obtain ⟨R₁, R₂, hR⟩ := (W₂.append W₁).exists_append_of_mem hmem
  rw [hR] at hstep' ⊢
  rw [GraphWalk.edges_append] at hstep'
  have h1 := level_bound R₁ fun e he => hstep' e (List.mem_append_left _ he)
  have h2 := level_bound R₂ fun e he => hstep' e (List.mem_append_right _ he)
  rw [GraphWalk.length_append]
  omega

variable [ConnectedSpace S] {Γ K : Drawing S}
  {F Δ : Set S} {k : ℕ} {a b : Fin k → S} {P : Fin k → Drawing S} (h : Setup61 Γ F Δ k a b P)

include h in
omit [ConnectedSpace S] in
/-- `F ∩ V(Γ₁)` has `2k` points. -/
theorem size_free : (F ∩ (Γ.interSet (closure (univ \ Δ))).V).ncard = 2 * k := by
  have hFc : F ⊆ closure (univ \ Δ) := fun x hx => by
    have : x ∈ frontier Δ := by
      rw [← subBd_eq_frontier, h.bd]
      exact hx
    rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff] at this
    exact this.2
  have hset : F ∩ (Γ.interSet (closure (univ \ Δ))).V = range (Sum.elim a b) := by
    rw [Set.Sum.elim_range, h.verts]
    ext x
    constructor
    · rintro ⟨hx, hxV⟩
      exact ⟨hx, interSet_isSub.1 hxV⟩
    · rintro ⟨hx, hxV⟩
      exact ⟨hx, mem_interSet_V hxV (hFc hx)⟩
  have hinj : Function.Injective (Sum.elim a b) := by
    rintro (i | i) (j | j) he
    · exact congrArg _ (a_inj h he)
    · exact (a_ne_b h _ _ he).elim
    · exact (a_ne_b h _ _ he.symm).elim
    · exact congrArg _ (b_inj h he)
  rw [hset, ← image_univ, ncard_image_of_injective _ hinj, ncard_univ]
  simp
  omega

omit [ConnectedSpace S] in
/-- A separation of `𝒯` with `F ∩ V(Γ)` on its first side has order at least `2k`. This is the use
of
freeness in the paper. -/
theorem free_contra {θ₁ : ℕ} {T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hfree : IsFreeSet (Γ.interSet (closure (univ \ Δ))).toHypergraph T₁ θ₁
      (F ∩ (Γ.interSet (closure (univ \ Δ))).V))
    (hsize : (F ∩ (Γ.interSet (closure (univ \ Δ))).V).ncard = 2 * k) {D : Set S}
    (hD : ((PaintingOrDrawing.drawing Γ).inter D, (PaintingOrDrawing.drawing Γ).interOutside D) ∈
      inducedBySubgraph Γ.toHypergraph (Γ.interSet (closure (univ \ Δ))).toHypergraph θ₁ T₁)
    (hsub : F ∩ Γ.V ⊆ D) (hord : (frontier D ∩ Γ.V).ncard < 2 * k) : False := by
  have hmem := hD.2.2
  have hle := hfree.2.2 hmem (fun x hx => by
    have hxV : x ∈ Γ.V := interSet_isSub.1 hx.2
    exact ⟨⟨hxV, hsub ⟨hx.1, hxV⟩⟩, hx.2⟩)
  have hsubset : (((PaintingOrDrawing.drawing Γ).inter D ∩
      (Γ.interSet (closure (univ \ Δ))).toHypergraph) ∩
      ((PaintingOrDrawing.drawing Γ).interOutside D ∩
      (Γ.interSet (closure (univ \ Δ))).toHypergraph)).vertexSet ⊆ frontier D ∩ Γ.V :=
    fun x hx => inter_outside_subset (Γ := PaintingOrDrawing.drawing Γ) ⟨hx.1.1, hx.2.1⟩
  have hle2 := ncard_le_ncard hsubset (Γ.finite_V.subset inter_subset_right)
  unfold separationOrder at hle
  have hle3 : (F ∩ (Γ.interSet (closure (univ \ Δ))).V).ncard ≤ (frontier D ∩ Γ.V).ncard :=
    hle.trans hle2
  omega

/-- **Claim (2) of the paper.** A restraint `Y` holding `F ∩ V(Γ)` has length at least `4k`. As in
the
paper, the separation of `Y` is in the tangle by (1.1), and it has small order, against the freeness
of
`F ∩ V(Γ₁)`. -/
theorem claim_two (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) {θ₁ : ℕ}
    {T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hk : 2 ≤ k) (hθ : 2 * k < θ₁)
    (hT : IsRespectfulDrawingTangle Γ θ₁
      (inducedBySubgraph Γ.toHypergraph (Γ.interSet (closure (univ \ Δ))).toHypergraph θ₁ T₁))
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ₁
      (inducedBySubgraph Γ.toHypergraph (Γ.interSet (closure (univ \ Δ))).toHypergraph θ₁ T₁) ins)
    (hs : IsSlope K (2 * θ₁) ins)
    (hfree : IsFreeSet (Γ.interSet (closure (univ \ Δ))).toHypergraph T₁ θ₁
      (F ∩ (Γ.interSet (closure (univ \ Δ))).V))
    (hsize : (F ∩ (Γ.interSet (closure (univ \ Δ))).V).ncard = 2 * k) {Y : Set S}
    (hY : IsRestraint K ins (2 * θ₁) Y) (hsub : F ∩ Γ.V ⊆ Y)
    (hl : perimeterWalkLength K Y < 4 * k) : False := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hrad : PreRad (.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  obtain ⟨u, W', -, hlen, -, -, hwd⟩ := hY.exists_walk hS
  have hYc := hY.isClosed
  have hfrU := frontier_sub_U hS hYc hY.isGammaNice
  have hn : frontier Y ∩ Γ.U ⊆ Γ.V := fun x hx => by
    have : x ∈ Γ.U ∩ K.U := ⟨hx.2, hfrU hx.1⟩
    rw [show Γ.U ∩ K.U = Γ.V from hrad.2.1] at this
    exact this
  have hsep := isSeparation_inter (Γ := PaintingOrDrawing.drawing Γ) hYc hn
  have hfrs : frontier Y ∩ Γ.V ⊆ {x | x ∈ W'.support} ∩ Γ.V := fun x hx => by
    refine ⟨?_, hx.2⟩
    have : x ∈ (K.interSet (frontier Y)).V := mem_interSet_V (radial_V hrad hx.2) hx.1
    rw [← hwd, walkDrawing_V] at this
    exact this
  have hord : (frontier Y ∩ Γ.V).ncard < 2 * k :=
    (ncard_le_ncard hfrs ((List.finite_toSet _).inter_of_left _)).trans_lt
      (order_lt hrad.2 W' hk (hlen ▸ hl))
  have hAB : ((PaintingOrDrawing.drawing Γ).inter Y ∩ (PaintingOrDrawing.drawing Γ).interOutside
    Y).vertexSet
      ⊆ frontier Y ∩ Γ.V := fun x hx => inter_outside_subset (Γ := PaintingOrDrawing.drawing Γ) hx
  have ho : separationOrder ((PaintingOrDrawing.drawing Γ).inter Y)
      ((PaintingOrDrawing.drawing Γ).interOutside Y) < θ₁ := by
    have := ncard_le_ncard hAB (Γ.finite_V.subset inter_subset_right)
    unfold separationOrder
    omega
  refine free_contra hfree hsize ((theorem_1_1_proof hS hT hE hK hd hsep ho).mpr ?_) hsub hord
  rintro e ⟨heE, heY⟩
  have heΓ : e ∈ Γ.E := heE
  obtain ⟨y, hy⟩ := heΓ.1
  have hdis := edge_disjoint hrad heΓ
  obtain ⟨s, hs', hes⟩ := edge_region hS hrad heΓ
  have hyY : y ∈ insOf ins (K.interSet (frontier Y)) := by
    rw [insOf_frontier hS hs hY]
    exact heY hy
  rcases hyY with hyU | hyU
  · exact (Set.disjoint_left.mp hdis hy (interSet_isSub.U_subset hyU)).elim
  obtain ⟨C, ⟨hC, hCs⟩, hyC⟩ := mem_iUnion₂.mp hyU
  have hCK := hCs.trans interSet_isSub
  have hCl : C.length < 2 * θ₁ := hY.isConfined hS C hC hCs
  obtain ⟨-, -, hnice⟩ := ins_slope_facts hS hs hC hCK hCl
  refine ⟨C, hC, hCK, hCl, fun x hx => ?_, (hes.trans (nice_region hnice hs' ⟨y, hes hy, hyC⟩))⟩
  have hxF : x ∈ frontier Y := ((mem_interSet_V_iff isClosed_frontier).mp (hCs.1 hx.1)).2
  have hxY := hYc.frontier_subset hxF
  have hxC : x ∈ closure (univ \ Y) := by
    rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff] at hxF
    exact hxF.2
  exact ⟨⟨hx.2, hxY⟩, hx.2, hxC⟩

end GraphMinor.GM12

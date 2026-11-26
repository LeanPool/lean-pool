/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM11.Theorem63

/-!
# Graph Minors XII, Section 1: atoms and closed walks

This file proves (1.1) from Graph Minors XI, (6.3), choosing one circuit for each edge
of the small side. It also proves that the tangle metric vanishes on the diagonal, and
"the easy observation" of Graph Minors XII, Section 1, page 242, which is (3.1) of
Graph Minors XIV: for a closed walk `W` of a radial drawing `K` of length `< 2θ` and an atom `c` of
`Γ`, the corresponding atom of `K` lies in `ins(W)` exactly when `c` meets `ins(W)`
(`corresponding_atom_subset_iff`).

An edge of `Γ` misses `U(K)`, so its region of `K` lies inside or outside each `ins(C)`. A region
`c`
of `Γ` meets `U(L)`, for a subdrawing `L` of `K`, only if `L` has the vertex of `K` in `c`.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S] {Γ K : Drawing S}

/-- Graph Minors XII, (1.1), page 242. A small side belongs to the tangle exactly when each
of its edges lies inside a radial circuit whose original vertices lie in the separator.
This is the drawing case of Graph Minors XI, (6.3). The finite family required there is obtained
by choosing one circuit for each edge of the small side. -/
theorem theorem_1_1_proof (hS : IsClosedSurface S) [ConnectedSpace S]
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S} (hT : IsRespectfulDrawingTangle Γ θ T)
    (hE : Γ.E.Nonempty) (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    {A B : Hypergraph S (Set S)} (hAB : Γ.toHypergraph.IsSeparation A B)
    (ho : separationOrder A B < θ) :
    (A, B) ∈ T ↔ ∀ e ∈ A.edgeSet, ∃ C : Drawing S,
      C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ ∧
        C.V ∩ Γ.V ⊆ (A ∩ B).vertexSet ∧ e ⊆ ins C := by
  classical
  have hp : IsPretangle Γ.toHypergraph θ T :=
    ⟨hT.2.1.one_le, hT.2.1.isSeparation, hT.2.1.order_lt,
      hT.2.1.axiom1, hT.2.1.axiom2⟩
  have h := (GM11.theorem_6_3_proof S hS inferInstance (.drawing Γ) K θ T ins
    hT.1 hE hp hT.2.2 hK hd).1 A B hAB ho
  constructor
  · intro hm e he
    obtain ⟨k, C, hC, hc⟩ := h.mp hm
    obtain ⟨i, hi⟩ := hc e he
    exact ⟨C i, (hC i).1, (hC i).2.1, (hC i).2.2.1, (hC i).2.2.2, hi⟩
  · intro hc
    let : Fintype A.edgeSet := A.edgeSet_finite.fintype
    let q := Fintype.equivFin A.edgeSet
    have hex : ∀ e : A.edgeSet, ∃ C : Drawing S,
        C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ ∧
          C.V ∩ Γ.V ⊆ (A ∩ B).vertexSet ∧ e.val ⊆ ins C :=
      fun e => hc e.val e.property
    choose C hC using hex
    apply h.mpr
    refine ⟨Fintype.card A.edgeSet, fun i => C (q.symm i), ?_, ?_⟩
    · intro i
      exact ⟨(hC _).1, (hC _).2.1, (hC _).2.2.1, (hC _).2.2.2.1⟩
    · intro e he
      refine ⟨q ⟨e, he⟩, ?_⟩
      simpa only [Equiv.symm_apply_apply] using (hC ⟨e, he⟩).2.2.2.2

/-- The metric of a respectful tangle vanishes on each atom paired with itself. -/
theorem metric_self {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hd : HasTangleMetric Γ θ T d)
    {a : Set S} (ha : a ∈ Γ.A) : d a a = 0 := by
  obtain ⟨_, K, ins, _, _, h⟩ := hd
  rw [h a ha a ha]
  simp only [tangleMetric, ↓reduceIte]

omit [T1Space S] in
/-- If a subdrawing `L` of `K` has a point in a region `c` of `Γ`, it has the vertex of `K` in `c`:
an edge of `K` in `c` has an end off `V(Γ)`, and that end lies in `c`. -/
theorem vertex_of_mem_region [LocallyConnectedSpace S]
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {c : Set S} (hc : c ∈ Γ.R)
    {L : Drawing S} (hL : L.IsSubdrawing K) {x w : S} (hxL : x ∈ L.U) (hxc : x ∈ c) (hw : w ∈ c)
    (hwK : w ∈ K.V) : w ∈ L.V := by
  obtain ⟨hUU, hVV, huniq, -, hbip, -⟩ := hK
  have hUU' : Γ.U ∩ K.U = Γ.V := hUU
  have hVV' : Γ.V ⊆ K.V := hVV
  have huniq' : ∀ r ∈ Γ.R, ∃! w, w ∈ r ∧ w ∈ K.V := huniq
  have heq : ∀ y ∈ c, y ∈ K.V → y = w := fun y hy hyK =>
    (huniq' c hc).unique ⟨hy, hyK⟩ ⟨hw, hwK⟩
  by_cases hxV : x ∈ L.V
  · rw [← heq x hxc (hL.1 hxV)]
    exact hxV
  obtain ⟨e, he, hxe⟩ := L.exists_edge_of_mem hxL hxV
  have heK := hL.2 he
  obtain ⟨v, hv, w', hw', hcap⟩ := hbip e heK
  have hedis : Disjoint e Γ.U := disjoint_left.mpr fun y hy hyU => by
    have hyK : y ∈ K.U := (heK.2.1 hy).1
    have : y ∈ Γ.U ∩ K.U := ⟨hyU, hyK⟩
    rw [hUU'] at this
    exact (heK.2.1 hy).2 (hVV' this)
  have hsub : e ⊆ c := subset_region hc
    (show IsPathConnected e from heK.2.2.1).isConnected.isPreconnected hedis hxe hxc
  have hw'mem : w' ∈ closure e ∩ K.V := by rw [hcap]; simp
  have hw'U : w' ∉ Γ.U := fun h => by
    have : w' ∈ Γ.U ∩ K.U := ⟨h, K.V_subset_U hw'mem.2⟩
    rw [hUU'] at this
    exact hw'.2 this
  have hw'c : w' ∈ c := by
    rcases closure_region_subset hc (closure_mono hsub hw'mem.1) with h | h
    · exact h
    · exact absurd h hw'U
  rw [← heq w' hw'c hw'mem.2]
  exact ((hL.closure_inter_V he).symm ▸ hw'mem : w' ∈ closure e ∩ L.V).2

omit [T1Space S] in
/-- A preconnected set that meets a closed set `D` and misses its frontier lies in `D`. -/
theorem subset_of_disjoint_frontier {A D : Set S} (hA : IsPreconnected A) (hD : IsClosed D)
    (hdis : Disjoint A (frontier D)) {x : S} (hx : x ∈ A) (hxD : x ∈ D) : A ⊆ D := by
  have hcov : A ⊆ interior D ∪ Dᶜ := by
    intro y hy
    by_cases hyD : y ∈ D
    · refine Or.inl ?_
      by_contra h
      exact disjoint_left.mp hdis hy ⟨subset_closure hyD, h⟩
    · exact Or.inr hyD
  have hxi : x ∈ interior D := (hcov hx).resolve_right (fun h => h hxD)
  intro y hy
  by_contra hyD
  obtain ⟨z, -, hz₁, hz₂⟩ := hA _ _ isOpen_interior hD.isOpen_compl hcov ⟨x, hx, hxi⟩ ⟨y, hy, hyD⟩
  exact hz₂ (interior_subset hz₁)

/-- The observation of Graph Minors XII, Section 1, page 242, which is Graph Minors XIV, (3.1): "for
a closed walk $W$ in $K$ of length $<2\theta$, and for $c \in A(\Gamma)$, $a(c)
\subseteq ins(W)$ if and only if $c \cap ins(W) \ne \emptyset$." -/
theorem corresponding_atom_subset_iff (hS : IsClosedSurface S)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins) {c c' : Set S}
    (hc : IsCorrespondingAtom Γ K c c') {u : S} (W : GraphWalk K.toGraph u u)
    (hl : W.length < 2 * θ) :
    c' ⊆ insWalk ins K W ↔ (c ∩ insWalk ins K W).Nonempty := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have : T2Space S := hS.2.1
  have hP := hK.2.1
  have hLs : (walkDrawing K W).IsSubdrawing K := walkDrawing_isSubdrawing K W
  -- A circuit of `K | W` has a disc as its inside.
  have hdisc : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing (walkDrawing K W) →
      IsClosed (ins C) ∧ frontier (ins C) = C.U ∧ C.U ⊆ ins C := by
    intro C hC hCs
    have hlen : C.length < 2 * θ := by
      refine lt_of_le_of_lt ?_ hl
      have hsub : C.E ⊆ {e | e ∈ W.edges} := by
        have := hCs.2
        rwa [walkDrawing_E] at this
      calc C.E.ncard ≤ ({e | e ∈ W.edges} : Set (Set S)).ncard :=
            Set.ncard_le_ncard hsub (List.finite_toSet _)
        _ ≤ W.edges.length := by
            rw [show ({e | e ∈ W.edges} : Set (Set S)) = ↑W.edges.toFinset by ext; simp,
              Set.ncard_coe_finset]
            exact List.toFinset_card_le _
        _ = W.length := rfl
    obtain ⟨h₁, h₂, -⟩ := hd C hC (hCs.trans hLs) hlen
    have hcl : IsClosed (ins C) := h₁.isClosed
    have hfr : frontier (ins C) = C.U := by rw [subBd_eq_frontier', h₂]
    exact ⟨hcl, hfr, hfr ▸ hcl.frontier_subset⟩
  constructor
  · intro h
    obtain ⟨-, -, hcase⟩ := hc
    rcases hcase with ⟨v, -, rfl, rfl⟩ | ⟨he, hr, hsub⟩ | ⟨hr, v, hv, rfl⟩
    · exact ⟨v, rfl, h rfl⟩
    · obtain ⟨x, hx⟩ := he.1
      exact ⟨x, hx, h (hsub hx)⟩
    · exact ⟨v, hv.2, h rfl⟩
  · rintro ⟨x, hxc, hxW⟩
    obtain ⟨-, -, hcase⟩ := hc
    rcases hcase with ⟨v, -, rfl, rfl⟩ | ⟨he, hr, hsub⟩ | ⟨hr, w, hw, rfl⟩
    · exact singleton_subset_iff.mpr (by rwa [mem_singleton_iff.mp hxc] at hxW)
    · -- An edge of `Γ` misses `U(K)`.
      have hUU : Γ.U ∩ K.U = Γ.V := hP.1
      have hxK : x ∉ K.U := fun h => by
        have hxU : x ∈ Γ.U := (he.2.1 hxc).1
        have : x ∈ Γ.U ∩ K.U := ⟨hxU, h⟩
        rw [hUU] at this
        exact (he.2.1 hxc).2 this
      have hdisr : Disjoint c' K.U := disjoint_left.mpr fun y hy hyU => region_subset hr hy hyU
      rcases hxW with hx | hx
      · exact absurd (hLs.U_subset hx) hxK
      · obtain ⟨C, ⟨hC, hCs⟩, hxC⟩ := mem_iUnion₂.mp hx
        obtain ⟨hcl, hfr, -⟩ := hdisc C hC hCs
        have hd' : Disjoint c' (frontier (ins C)) := by
          rw [hfr]
          exact hdisr.mono_right (hCs.trans hLs).U_subset
        have hin := subset_of_disjoint_frontier (region_isPreconnected hr) hcl hd' (hsub hxc) hxC
        exact fun y hy => Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hin hy⟩)
    · refine singleton_subset_iff.mpr ?_
      rcases hxW with hx | hx
      · exact Or.inl ((walkDrawing K W).V_subset_U
          (vertex_of_mem_region hP hr hLs hx hxc hw.2 hw.1))
      · obtain ⟨C, ⟨hC, hCs⟩, hxC⟩ := mem_iUnion₂.mp hx
        obtain ⟨hcl, hfr, hUin⟩ := hdisc C hC hCs
        refine Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, ?_⟩)
        by_cases hwC : w ∈ C.V
        · exact hUin (C.V_subset_U hwC)
        · refine subset_of_disjoint_frontier (region_isPreconnected hr) hcl ?_ hxc hxC hw.2
          rw [hfr]
          refine disjoint_left.mpr fun y hy hyC => hwC ?_
          exact vertex_of_mem_region hP hr (hCs.trans hLs) hyC hy hw.2 hw.1

end GraphMinor.GM12

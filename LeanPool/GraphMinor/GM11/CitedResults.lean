/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section91
public import LeanPool.GraphMinor.GM11.Section92
public import LeanPool.GraphMinor.GM14.Section7a
public import LeanPool.GraphMinor.GM19.Cited
public import LeanPool.GraphMinor.GM12.Cited
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# The results of Graph Minors XI that other papers cite

The statements of (8.5), (8.10), (8.12), (9.1) and (9.2) as they are cited in Graph Minors XIV, XV
and
XIX. Most of this file only passes from a `T1Space` to the `T2Space` of a surface.

The new part is `tangleMetric_vertex_edge_le`: a vertex at an edge has distance at most `2` from the
edge. A tangle puts the edge on the small side of the separation that cuts it off, so a circuit of
the
radial drawing through at most two vertices of the drawing surrounds the edge, by (7.2) of Graph
Minors
XIV. Such a circuit has length at most `4`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface GraphMinor.GM14 GraphMinor.GM10

universe u

section Distance

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- `|W| ≤ 2c + 1`, with `c` the number of vertices of `H` on the walk `W` of a radial drawing after
its first vertex, and with `2c` if the first vertex of `W` is not in `H`. -/
private theorem length_le_count {H D : Drawing S} (hrad : (PaintingOrDrawing.drawing
  H).IsPreRadialDrawing D)
    [DecidablePred (· ∈ H.V)] {u v : S} (W : GraphWalk D.toGraph u v) :
    W.length ≤ 2 * (W.support.tail.filter (· ∈ H.V)).length + if u ∈ H.V then 1 else 0 := by
  have hb := bipartite_of_preRadial hrad
  induction W with
  | nil _ => simp
  | @cons x y z e hl r ih =>
    have hx : x ∈ H.V ↔ y ∉ H.V := hb _ _ _ hl
    have hlen : (GraphWalk.cons hl r).length = r.length + 1 := rfl
    have hsup : (GraphWalk.cons hl r).support.tail = r.support := rfl
    rw [hlen, hsup, r.support_eq_cons, List.filter_cons]
    by_cases hy : y ∈ H.V
    · have hx' : x ∉ H.V := fun h => hx.mp h hy
      simp only [hy, hx', ite_true, ite_false, decide_true, List.length_cons] at ih ⊢
      omega
    · have hx' : x ∈ H.V := hx.mpr hy
      simp only [hy, hx', ite_true, ite_false, decide_false, Bool.false_eq_true] at ih ⊢
      omega

variable [ConnectedSpace S]

/-- A vertex at an edge has distance at most `2` from the edge. This is a statement about the metric
of a respectful tangle and is one of the metric facts used in Graph Minors XV.
For `θ ≤ 2` it holds by
`d ≤ θ`. Otherwise the edge `e` with its ends is the small side of a separation of order at most
`2`,
and (7.2) of Graph Minors XIV gives a circuit `D` of the radial drawing around `e`, with at most two
vertices in `H`. So `|D| ≤ 4`. -/
theorem tangleMetric_vertex_edge_le (hS : IsClosedSurface S) {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hResp : IsRespectfulDrawingTangle H θ T) (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins) {v : S} {e : Set S} (he : e ∈ H.E)
    (hv : v ∈ H.V) (hve : v ∈ closure e) : tangleMetric H K ins θ {v} e ≤ 2 := by
  classical
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hP := hK.2.1
  by_cases hθ : θ ≤ 2
  · exact (tangleMetric_le_order hP _ _).trans hθ
  push Not at hθ
  have hT := hResp.2.1
  have heG : e ∈ H.toHypergraph.edgeSet := he
  have hsep := isSeparation_edgeHypergraph_deleteEdges heG
  obtain ⟨a, b, hl⟩ := (H.toGraph.edge_mem_iff_exists_isLink e).mp he
  have hends : H.toHypergraph.ends e ⊆ {a, b} := fun w hw => by
    rw [← hl.2.2.2]
    exact ⟨hw.2.2, hw.2.1⟩
  have hefin : (H.toHypergraph.ends e).Finite := (toFinite ({a, b} : Set S)).subset hends
  have h2 : (H.toHypergraph.ends e).ncard ≤ 2 :=
    (ncard_le_ncard hends (toFinite _)).trans ((ncard_insert_le a {b}).trans (by simp))
  have hord : Hypergraph.separationOrder (edgeHypergraph H.toHypergraph e)
      (H.toHypergraph.deleteEdges {e}) < θ := by
    rw [separationOrder_edgeHypergraph_deleteEdges]
    change (H.toHypergraph.ends e).ncard < θ
    omega
  have hAB : (edgeHypergraph H.toHypergraph e, H.toHypergraph.deleteEdges {e}) ∈ T :=
    (hT.axiom1 hsep hord).resolve_right fun h => hT.axiom3 h rfl
  obtain ⟨D, hD, hDs, hDl, hDV, heD⟩ := GM14.theorem_7_2_proof hS ‹_› ⟨e, he⟩ hResp hK hd hAB rfl
  have hT' : IsPretangle (PaintingOrDrawing.drawing H).toHypergraph θ T := hT.isPretangle
  have hs := isSlope_of_derived hS hT' hP.1 hd
  obtain ⟨-, -, hnice⟩ := ins_slope_facts hS hs hD hDs hDl
  have hcl : IsClosed (ins D) := (hs.isClosedDisc D hD hDs hDl).isCompact.isClosed
  obtain ⟨u, W₀, hW₀, -, hV, hE⟩ := id hD
  obtain ⟨W, hsu, hed⟩ := hDs.exists_walk_up W₀
  have hcount := length_le_count hP W
  have hnd : W.support.tail.Nodup := by
    rw [hsu]
    exact hW₀.1
  have hF : (W.support.tail.filter (· ∈ H.V)).length ≤ 2 := by
    have hnd' := hnd.filter (· ∈ H.V)
    rw [← List.toFinset_card_of_nodup hnd', ← ncard_coe_finset]
    refine (ncard_le_ncard (fun x hx => ?_) hefin).trans h2
    have hx' : x ∈ W.support.tail ∧ x ∈ H.V := by simpa using hx
    have hxs : x ∈ W.support := List.mem_of_mem_tail hx'.1
    have hxD : x ∈ D.V := by
      rw [hV, ← hsu]
      exact hxs
    have := hDV ⟨hxD, hx'.2⟩
    exact this.1
  obtain ⟨n, hn⟩ := even_length_of_closed hP W
  have hn2 : n ≤ 2 := by
    split_ifs at hcount <;> omega
  have hsub : D.IsSubdrawing (walkDrawing K W) := by
    refine ⟨fun x hx => ?_, fun f hf => ?_⟩
    · rw [walkDrawing_V, hsu]
      rw [hV] at hx
      exact hx
    · rw [walkDrawing_E, hed]
      rw [hE] at hf
      exact hf
  have hins : ins D ⊆ insWalk ins K W := fun x hx =>
    Or.inr (mem_iUnion₂.mpr ⟨D, ⟨hD, hsub⟩, hx⟩)
  obtain ⟨y, hy⟩ := he.1
  have hdisj : Disjoint e K.U := disjoint_left.mpr fun z hz hzK => by
    have hzV : z ∈ H.V := by
      have h₁ : H.U ∩ K.U = H.V := hP.1
      rw [← h₁]
      exact ⟨(he.2.1 hz).1, hzK⟩
    exact (he.2.1 hz).2 hzV
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem (disjoint_left.mp hdisj hy)
  have her : e ⊆ r := subset_region hr he.2.2.1.isConnected.isPreconnected hdisj hy hyr
  have hrD : r ⊆ ins D := nice_atom hnice (Or.inr hr) ⟨y, hyr, heD hy⟩
  have hwit : MetricWitness H K ins θ {v} e n := by
    refine ⟨u, W, {v}, r, ?_, ?_, by omega, by omega, ?_, hrD.trans hins⟩
    · exact ⟨Or.inl (Or.inl ⟨v, hv, rfl⟩), Or.inl (Or.inl ⟨v, hP.2.1 hv, rfl⟩), Or.inl ⟨v, hv,
        rfl, rfl⟩⟩
    · exact ⟨Or.inl (Or.inr he), Or.inr hr, Or.inr (Or.inl ⟨he, hr, her⟩)⟩
    · rw [singleton_subset_iff]
      exact hins (closure_minimal heD hcl hve)
  exact (tangleMetric_le hwit).trans hn2

omit [ConnectedSpace S] in
/-- The metric is symmetric. -/
theorem tangleMetric_comm (H K : Drawing S) (ins : Drawing S → Set S) (θ : ℕ) (x y : Set S) :
    tangleMetric H K ins θ x y = tangleMetric H K ins θ y x := by
  classical
  have h₁ : ∀ x y : Set S, (∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
      W.length < 2 * θ ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W) →
      ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K y x' ∧ IsCorrespondingAtom H K x y' ∧
      W.length < 2 * θ ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W :=
    fun x y ⟨u, W, x', y', a, b, c, d, e⟩ => ⟨u, W, y', x', b, a, c, e, d⟩
  have h₂ : ∀ x y : Set S, {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
      W.length < 2 * θ ∧ W.length = 2 * k ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W} =
      {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K y x' ∧ IsCorrespondingAtom H K x y' ∧
      W.length < 2 * θ ∧ W.length = 2 * k ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W} := by
    intro x y
    ext k
    exact ⟨fun ⟨u, W, x', y', a, b, c, d, e, f⟩ => ⟨u, W, y', x', b, a, c, d, f, e⟩,
      fun ⟨u, W, x', y', a, b, c, d, e, f⟩ => ⟨u, W, y', x', b, a, c, d, f, e⟩⟩
  by_cases hxy : x = y
  · rw [hxy]
  have hyx : ¬ y = x := fun h => hxy h.symm
  unfold tangleMetric
  simp only [hxy, hyx, ite_false]
  have h₃ := propext (Iff.intro (h₁ x y) (h₁ y x))
  simp only [h₃, h₂ x y]

end Distance

section Statements



/-- (8.5) in the form that Graph Minors XII, XIV and XIX cite. -/
theorem gm19_theorem_8_5 : GM19.GM11Theorem85Statement.{u} := by
  intro S _ _ hS hc Γ k ins hs u W hW
  have : T2Space S := hS.2.1
  exact theorem_8_5_proof hS hs W hW

/-- (7.2) in the form that Graph Minors XII cites. -/
theorem gm12_theorem_7_2 : GM12.GM11Theorem72Statement.{u} := by
  intro S _ _ hS hc Z F hF hFZ hn
  exact theorem_7_2_proof hS hF hFZ hn

/-- (8.5) in the form that Graph Minors XII cites. -/
theorem gm12_theorem_8_5 : GM12.GM11Theorem85Statement.{u} := by
  intro S _ _ hS hc Γ k ins hs u W hW
  have : T2Space S := hS.2.1
  exact theorem_8_5_proof hS hs W hW

/-- (8.13) in the form that Graph Minors XII cites. -/
theorem gm12_theorem_8_13 : GM12.GM11Theorem813Statement.{u} := by
  intro S _ _ hS hc Γ k ins hs a b X _ hX ha hb hmax
  exact theorem_8_13_proof hS hs hX ha hb hmax

/-- (8.10) in the form that Graph Minors XIV and XV cite. -/
theorem gm14_theorem_8_10 : GM14.GM11Theorem810Statement.{u} := by
  intro S _ _ hS hc Γ K ins hs c k _ hne
  have : T2Space S := hS.2.1
  exact theorem_8_10_proof hS hs hne

/-- (8.12) in the form that Graph Minors XIV and XV cite. -/
theorem gm14_theorem_8_12 : GM14.GM11Theorem812Statement.{u} := by
  intro S _ _ hS hc Γ K ins hs c
  have : T2Space S := hS.2.1
  exact theorem_8_12_proof hS hs c

/-- (9.2) in the form that Graph Minors XIX cites. -/
theorem gm19_theorem_9_2 : GM19.GM11Theorem92Statement.{u} := by
  intro S _ _ hS hc Γ K ins hs a b Y ha hb hY haY hbY
  have : T2Space S := hS.2.1
  exact theorem_9_2_proof hS hs ha hb hY haY hbY

/-- Metric facts for a respectful tangle used in Graph Minors XV and XIX, including the triangle
inequality from Graph Minors XI, (9.1). -/
theorem gm15_theorem_9_1 : GM15.GM11Theorem91Statement.{u} := by
  intro S _ _ H θ T d hS hc hM
  obtain ⟨hResp, K, ins, hK, hd, hdeq⟩ := hM
  have hP := hK.2.1
  have hT' : IsPretangle (PaintingOrDrawing.drawing H).toHypergraph θ T := hResp.2.1.isPretangle
  have hs := isSlope_of_derived hS hT' hP.1 hd
  have hatom : ∀ a ∈ H.A, IsGammaNice H a := fun a ha => ⟨{a}, by simpa using ha, by simp⟩
  have hvA : ∀ {v}, v ∈ H.V → ({v} : Set S) ∈ H.A := fun {v} hv => Or.inl (Or.inl ⟨v, hv, rfl⟩)
  refine ⟨fun σ => ?_, fun a ha => ?_, fun a ha b hb => ?_, fun a ha b hb => ?_,
    fun a ha b hb c hc' => ?_, fun hE v hv r hr hvr => ?_, fun v hv e he hve => ?_⟩
  · obtain ⟨a, ha, hσ⟩ := exists_atom H σ
    refine ⟨a, ⟨ha, hσ⟩, fun b hb => Subset.antisymm ?_ ?_⟩
    · exact nice_atom (hatom a ha) hb.1 ⟨σ, hb.2, hσ⟩
    · exact nice_atom (hatom b hb.1) ha ⟨σ, hσ, hb.2⟩
  · rw [hdeq a ha a ha]
    simp [tangleMetric]
  · rw [hdeq a ha b hb]
    exact tangleMetric_le_order hP a b
  · rw [hdeq a ha b hb, hdeq b hb a ha]
    exact tangleMetric_comm H K ins θ a b
  · rw [hdeq a ha c hc', hdeq a ha b hb, hdeq b hb c hc']
    exact tangleMetric_triangle hS hP hs a b c
  · rw [hdeq _ (hvA hv) r (Or.inr hr)]
    exact tangleMetric_le_one hS hK hE hv hr hvr
  · rw [hdeq _ (hvA hv) e (Or.inl (Or.inr he))]
    exact tangleMetric_vertex_edge_le hS hResp hK hd he hv hve

end Statements

end GraphMinor.GM11

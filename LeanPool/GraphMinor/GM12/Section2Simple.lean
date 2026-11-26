/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2Case1
public import LeanPool.GraphMinor.GM12.Section2Case2Induction
import LeanPool.GraphMinor.GM12.Section2NonemptyEdges
import LeanPool.GraphMinor.GM11.Theorem66

/-!
# Graph Minors XII (2.1) for simple closed curves

Induct on the length of the embedded normal curve. The zero-length
case stays in one region. At positive length the tangle has order at
least two and hence the drawing has an edge. If every region intersection
is connected, apply Case 1. Otherwise the theta-disc construction of
Case 2 gives a smaller positive-length curve and a trace subdrawing.
Apply the induction and inside monotonicity exactly as on page 244.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem simple_trace_inside_aux
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {c : Set S} (hc : c ∈ Γ.A) (n : ℕ)
    {φ : C(Circle, S)} (hφ : IsEmbedding φ) {u : S} (W : GraphWalk K.toGraph u u)
    (hW : IsTrace Γ K φ W) (hn : curveLength Γ φ = n) (hlen : curveLength Γ φ < θ)
    {D : Set S} (hD : IsClosedDisc D) (hbdD : subBd D = range φ)
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hcD : (c ∩ D).Nonempty) : (c ∩ insWalk ins K W).Nonempty := by
  induction n using Nat.strong_induction_on generalizing φ u D with
  | ind n ih =>
    have hF : IsOArc (range φ) := ⟨hφ.toHomeomorph⟩
    by_cases hzero : curveLength Γ φ = 0
    · exact theorem_2_1_zero hS hT hK.1 hW hzero hF subset_rfl hD hbdD hmD hc hcD
    · have hpos : 0 < curveLength Γ φ := Nat.pos_of_ne_zero hzero
      have hθ : 2 ≤ θ := by omega
      have hE : Γ.E.Nonempty := edges_nonempty_of_tangle_order_two hT hθ
      have hpT := GM11.IsTangle.isPretangle hT
      by_cases hconn : ∀ r ∈ Γ.R, IsPreconnected (range φ ∩ r)
      · exact theorem_2_1_case1 hS hpT hK hE hd hφ W hW hpos hlen hconn hD hbdD hmD hc hcD
      · push Not at hconn
        obtain ⟨r, hr, hdisconn⟩ := hconn
        apply theorem_2_1_case2 hS hK hE hpT hrespect hφ.injective hF W hW hlen
          hr hdisconn hD hbdD hmD hcD
        intro ψ hψ _ hsmall v P hP E hE' hbdE hmE hcE
        have hsmalln : curveLength Γ ψ < n := hn ▸ hsmall
        exact ih (curveLength Γ ψ) hsmalln hψ P hP rfl (hsmall.trans hlen) hE' hbdE hmE hcE

/-- Graph Minors XII, (2.1), pages 243--244, for an embedded normal
closed curve. The selected disc is its inside and every atom meeting
it meets the inside of any trace of that curve. -/
theorem theorem_2_1_simple
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {φ : C(Circle, S)} (hφ : IsEmbedding φ) {u : S} (W : GraphWalk K.toGraph u u)
    (hW : IsTrace Γ K φ W) (hlen : curveLength Γ φ < θ)
    {D c : Set S} (hD : IsClosedDisc D) (hbdD : subBd D = range φ)
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hc : c ∈ Γ.A) (hcD : (c ∩ D).Nonempty) :
    (c ∩ insWalk ins K W).Nonempty :=
  simple_trace_inside_aux hS hT hrespect hK hd hc (curveLength Γ φ) hφ W hW rfl hlen hD hbdD hmD hcD

end GraphMinor.GM12

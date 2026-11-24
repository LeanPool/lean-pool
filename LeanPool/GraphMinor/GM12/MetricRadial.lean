/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM12.Section4WalkMetric
import LeanPool.GraphMinor.GM11.Separate

/-!
# The metric of a tangle does not depend on the radial drawing

Graph Minors XII, Section 1 (page 242), defines the metric $d$ of a respectful tangle from a radial
drawing $K$ of $\Gamma$, and the proof of (6.1) (page 258) chooses a special $K$. The paper does not
say
that $d$ is the same for every $K$. Graph Minors XI, Section 3 (page 75), says that a radial drawing
is
unique up to homeomorphisms of $\Sigma$ that fix $U(\Gamma)$, and omits the proof. We prove the fact
about $d$ that is needed, by (7.7)(ii) of XII applied with $\Gamma' = \Gamma$
(`tangleMetric_eq_of_radial`).
The proof of (7.7) uses only (1.2) and (2.1), and so it does not depend on (6.1).

* `exists_derivedSlope`: every radial drawing has a slope derived from the tangle, as on page 87 of
  XI.
* `inducedBySubgraph_self`: the tangle that a tangle induces in its own graph is itself.
* `HasTangleMetric.eq`: two metrics of one tangle agree on the atoms.
* `HasTangleMetric.of_radial`: so the metric may be computed in any radial drawing.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- **A derived slope in any radial drawing.** For a respectful tangle `T` of order `θ`, each
circuit
`C` of a radial drawing with length `< 2θ` gives a `Γ`-normal `O`-arc `U(C)` with fewer than `θ`
vertices of `Γ`, so it bounds the closed disc of respectfulness (Graph Minors XI, Section 6,
page 87). -/
theorem exists_derivedSlope {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) :
    ∃ ins : Drawing S → Set S, IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins := by
  classical
  have hdisc : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing K → C.length < 2 * θ →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = C.U ∧
        ((PaintingOrDrawing.drawing H).inter Δ,
          (PaintingOrDrawing.drawing H).interOutside Δ) ∈ T := by
    intro C hC hCK hlen
    have hnormal : (PaintingOrDrawing.drawing H).IsNormal C.U := by
      intro x hx
      exact hK.2.1.1 ▸ ⟨hx.2, hCK.U_subset hx.1⟩
    have hinter : C.U ∩ H.V = C.V ∩ H.V := by
      ext x
      constructor
      · rintro ⟨hx, hxH⟩
        rw [C.U_eq] at hx
        rcases hx with hx | hx
        · exact ⟨hx, hxH⟩
        · obtain ⟨e, heC, hxe⟩ := mem_iUnion₂.mp hx
          have hxK := hK.2.1.2.1 hxH
          have hxC : x ∈ closure e ∩ C.V := by
            rw [hCK.closure_inter_V heC]
            exact ⟨hxe, hxK⟩
          exact ⟨hxC.2, hxH⟩
      · exact fun hx => ⟨C.V_subset_U hx.1, hx.2⟩
    have hcount := (GM12.circuit_length_eq_two_mul_ncard hK.2.1 hC hCK).1
    have hsmall : (C.U ∩ H.V).ncard < θ := by
      rw [hinter]
      omega
    exact hT.2.2.2 C.U (IsCircuit.isOArc_U hC) hnormal hsmall
  refine ⟨fun C => if hc : C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ then
    (hdisc C hc.1 hc.2.1 hc.2.2).choose else ∅, ?_⟩
  intro C hC hCK hlen
  have hc : C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ := ⟨hC, hCK, hlen⟩
  simp only [dite_eq_left hc]
  exact (hdisc C hC hCK hlen).choose_spec

omit [TopologicalSpace S] [T2Space S] in
/-- The intersection of a subhypergraph with the hypergraph is the subhypergraph. -/
theorem inter_eq_left_of_le {α β : Type*} {A G : Hypergraph α β} (h : A ≤ G) : A ∩ G = A := by
  refine Hypergraph.ext (Set.inter_eq_left.mpr h.vertexSet_subset)
    (Set.inter_eq_left.mpr h.edgeSet_subset) ?_
  funext e v
  apply propext
  refine ⟨fun hv => hv.1, fun hv => ⟨hv, ?_⟩⟩
  have he : e ∈ A.edgeSet := A.edge_mem_of_inc hv
  have : v ∈ G.ends e := by
    rw [h.ends_eq e he]
    exact hv
  exact this

omit [TopologicalSpace S] [T2Space S] in
/-- **The tangle that a tangle induces in its own graph is itself.** -/
theorem inducedBySubgraph_self {α β : Type*} {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ T) :
    inducedBySubgraph G G θ T = T := by
  ext ⟨A, B⟩
  constructor
  · rintro ⟨hs, -, hm⟩
    rwa [inter_eq_left_of_le hs.left_le, inter_eq_left_of_le hs.right_le] at hm
  · intro hm
    have hs := hT.isSeparation hm
    refine ⟨hs, hT.order_lt hm, ?_⟩
    rwa [inter_eq_left_of_le hs.left_le, inter_eq_left_of_le hs.right_le]

/-- **Two metrics of one tangle agree.** If `d` and `d'` are both metrics of the respectful tangle
`T`
in `H`, computed from two radial drawings, then they agree on the atoms of `H`. This is (7.7)(ii) of
Graph Minors XII with `Γ' = Γ`, applied both ways. -/
theorem HasTangleMetric.eq (hS : IsClosedSurface S) [ConnectedSpace S] {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d d' : Set S → Set S → ℕ}
    (hd : HasTangleMetric H θ T d) (hd' : HasTangleMetric H θ T d') :
    ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = d' x y := by
  have hind : T = inducedBySubgraph H.toHypergraph H.toHypergraph θ T :=
    (inducedBySubgraph_self hd.1.2.1).symm
  have hsub : H.IsSubdrawing H := ⟨subset_rfl, subset_rfl⟩
  intro x hx y hy
  have h1 := (theorem_7_7_proof hS hd hsub hd.1.1 le_rfl hd').2 rfl hind x hx y hy x hx y hy
    subset_rfl subset_rfl
  have h2 := (theorem_7_7_proof hS hd' hsub hd.1.1 le_rfl hd).2 rfl hind x hx y hy x hx y hy
    subset_rfl subset_rfl
  omega

/-- **The metric may be computed in any radial drawing.** For the metric `d` of a respectful tangle
and any radial drawing `K`, there is a slope `ins` in `K` derived from the tangle, and `d` is the
distance computed from `K` and `ins`. -/
theorem HasTangleMetric.of_radial (hS : IsClosedSurface S) [ConnectedSpace S] {H K : Drawing S}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hd : HasTangleMetric H θ T d) (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) :
    ∃ ins : Drawing S → Set S, IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins ∧
      ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y := by
  obtain ⟨ins, hins⟩ := exists_derivedSlope hd.1 hK
  have hd' : HasTangleMetric H θ T (tangleMetric H K ins θ) :=
    ⟨hd.1, K, ins, hK, hins, fun _ _ _ _ => rfl⟩
  exact ⟨ins, hins, HasTangleMetric.eq hS hd hd'⟩

end GraphMinor.GM12

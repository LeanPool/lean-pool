/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RadialAtoms
import LeanPool.GraphMinor.GM12.Section1b
import LeanPool.GraphMinor.GM12.Section4WalkMetric

public import LeanPool.GraphMinor.GM14.Section3
public import LeanPool.GraphMinor.GM14.DiscSlope
public import LeanPool.GraphMinor.GM15.Cited
public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM19.Cited
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM11.PaintingFacts
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.Theorem63
import LeanPool.GraphMinor.Surface.Circle

/-!
# Graph Minors XIV, Section 7 (Part 1): (7.1)–(7.6)

This file formalizes the first six results of Section 7 (*Distance and Freedom*, pages 35–37) of
N. Robertson and P. D. Seymour, *Graph Minors. XIV. Extending an embedding*,
J. Combin. Theory Ser. B **65** (1995) 23–50:

- `theorem_7_1`: Graph Minors XIV, (7.1) (page 35), showing that for a 2-cell drawing `H` with
  `|E(H)| ≥ 2` and a respectful tangle `T` of order `θ ≥ 1` with metric `d`, for every `z ∈ A(H)`
  there exists `e ∈ E(H)` with `d(z, e) = θ`. Deduced from Graph Minors XI, (8.12) and (8.5).
- `theorem_7_2`: Graph Minors XIV, (7.2) (page 36), showing that for `(A, B) ∈ T` and `e ∈ E(A)`,
  there is a circuit `D` of a radial drawing `K` of `H` with `V(D) ∩ V(H) ⊆ V(A ∩ B)` and
  `e ⊆ ins(D)`. Deduced from Graph Minors XI, (6.3) (`GM11.theorem_6_3_proof`).
- `theorem_7_3`: Graph Minors XIV, (7.3) (page 36), proving `GM15.GM14Theorem73Statement`.
- `theorem_7_4`: Graph Minors XIV, (7.4) (page 36), showing that a circuit `C` of `A` with
  `|V(B ∩ C)| ≤ 1` has `U(C) ⊆ ins(D)` for some circuit `D` of `K` with `V(D) ∩ V(H) ⊆ V(A ∩ B)`.
- `theorem_7_5`: Graph Minors XIV, (7.5) (page 36), proving `GM16.GM14Theorem75Statement`.
- `theorem_7_6`: Graph Minors XIV, (7.6) (page 37), showing that if `D` is a circuit of `K` with
  `|E(D)| < 2(θ - λ)` and `bd(Λ) ⊆ ins(D)` for a `λ`-zone `Λ`, then `closure Λ ⊆ ins(D)`.
-/

public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 Hypergraph

universe u w

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-! ## Helper lemmas on corresponding atoms and radial walks -/

/-- Every tangle is a pretangle. -/
theorem _root_.GraphMinor.GM10.IsTangle.isPretangle {α β : Type*} {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ T) :
    IsPretangle G θ T :=
  ⟨hT.one_le, hT.isSeparation, hT.order_lt, hT.axiom1, hT.axiom2⟩

omit [T1Space S] in
/-- An `O`-arc is nonempty. -/
theorem IsOArc.nonempty {F : Set S} (hF : IsOArc F) : F.Nonempty := by
  obtain ⟨φ⟩ := hF
  exact ⟨(φ 1).1, (φ 1).2⟩

omit [T1Space S] in
/-- An open disc is nonempty. -/
theorem IsOpenDisc.nonempty {D : Set S} (hD : IsOpenDisc D) : D.Nonempty := by
  obtain ⟨φ⟩ := hD.2
  have h0 : (0 : EuclideanPlane) ∈ OpenUnitDisc := by simp [OpenUnitDisc]
  exact ⟨(φ ⟨0, h0⟩).1, (φ ⟨0, h0⟩).2⟩

omit [T1Space S] in
/-- An `O`-arc is preconnected. -/
theorem IsOArc.isPreconnected {F : Set S} (hF : IsOArc F) : IsPreconnected F := by
  obtain ⟨φ⟩ := hF
  have h : F = range (fun z : Circle => (φ z).1) := by
    ext x
    exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩, fun ⟨z, hz⟩ => hz ▸ (φ z).2⟩
  rw [h]
  exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)

omit [T1Space S] in
/-- An `O`-arc minus one of its points is path-connected. -/
theorem isPathConnected_oArc_diff {F : Set S} (hF : IsOArc F) {u : S} (hu : u ∈ F) :
    IsPathConnected (F \ {u}) :=
  hF.isPathConnected_sdiff_singleton hu

omit [T1Space S] in
/-- An atom of a drawing is nonempty. -/
theorem atom_nonempty {Γ : Drawing S} {x : Set S} (hx : x ∈ Γ.A) : x.Nonempty := by
  rcases hx with (⟨v, -, rfl⟩ | hx) | hx
  · exact singleton_nonempty v
  · exact hx.1
  · exact region_nonempty hx

omit [T1Space S] in
/-- Any two distinct atoms of a drawing are disjoint. -/
theorem disjoint_of_mem_A_ne {Γ : Drawing S} {x y : Set S}
    (hx : x ∈ Γ.A) (hy : y ∈ Γ.A) (hne : x ≠ y) : Disjoint x y := by
  rcases hx with (⟨u, hu, rfl⟩ | hxE) | hxR <;> rcases hy with (⟨v, hv, rfl⟩ | hyE) | hyR
  · exact disjoint_singleton.mpr fun h => hne (h ▸ rfl)
  · exact disjoint_singleton_left.mpr fun h => (hyE.2.1 h).2 hu
  · exact disjoint_singleton_left.mpr fun h => region_subset hyR h (Γ.V_subset_U hu)
  · exact disjoint_singleton_right.mpr fun h => (hxE.2.1 h).2 hv
  · refine disjoint_left.mpr fun p hpx hpy => hne (Γ.edge_eq_of_mem hxE hyE hpx hpy)
  · exact disjoint_left.mpr fun p hpx hpy => region_subset hyR hpy (hxE.2.1 hpx).1
  · exact disjoint_singleton_right.mpr fun h => region_subset hxR h (Γ.V_subset_U hv)
  · exact disjoint_left.mpr fun p hpx hpy => region_subset hxR hpx (hyE.2.1 hpy).1
  · exact disjoint_left.mpr fun p hpx hpy => hne (region_eq_of_mem hxR hyR hpx hpy)

omit [T1Space S] in
/-- When `E(H) ≠ ∅`, distinct atoms of `H` have distinct corresponding atoms in `K`. -/
theorem correspondingAtom_inj [ConnectedSpace S] (hS : IsClosedSurface S) {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) (hE : H.E.Nonempty)
    {x y x' : Set S} (hx : IsCorrespondingAtom H K x x') (hy : IsCorrespondingAtom H K y x') :
    x = y := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  obtain ⟨hxA, hx'A, hxc⟩ := hx
  obtain ⟨hyA, -, hyc⟩ := hy
  rcases hxc with ⟨u, hu, rfl, rfl⟩ | ⟨hxE, hxr, hxsub⟩ | ⟨hxR, u, ⟨huK, hux⟩, rfl⟩ <;>
    rcases hyc with ⟨v, hv, rfl, hveq⟩ | ⟨hyE, hyr, hysub⟩ | ⟨hyR, v, ⟨hvK, hvy⟩, hveq⟩
  · exact hveq
  · exact absurd (K.V_subset_U (hK.2.1.2.1 hu)) (region_subset hyr (mem_singleton u))
  · have huv : v = u := singleton_eq_singleton_iff.mp hveq.symm
    subst huv
    exact absurd (H.V_subset_U hu) (region_subset hyR hvy)
  · exact absurd (K.V_subset_U (hK.2.1.2.1 hv)) (region_subset hxr (hveq ▸ mem_singleton v))
  · exact hrf.2.1 x' hxr x hxE y hyE hxsub hysub
  · exact absurd (K.V_subset_U hvK) (region_subset hxr (hveq ▸ mem_singleton v))
  · have huv : v = u := singleton_eq_singleton_iff.mp hveq.symm
    subst huv
    exact absurd (H.V_subset_U hv) (region_subset hxR hux)
  · exact absurd (K.V_subset_U huK) (region_subset hyr (mem_singleton u))
  · have huv : v = u := singleton_eq_singleton_iff.mp hveq.symm
    subst huv
    exact region_eq_of_mem hxR hyR hux hvy

omit [T1Space S] in
/-- Every closed walk of a pre-radial drawing `K` of `H` has even length, equal to twice the number
of visits to `V(H)`. -/
theorem closed_walk_length_eq_two_mul {H K : Drawing S}
    (hP : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) {u : S}
    (W : GraphWalk K.toGraph u u) :
    by classical exact W.length = 2 * (W.support.tail.countP (· ∈ H.V)) := by
  exact GM12.closed_walk_length_eq_two_mul hP W

omit [T1Space S] in
/-- Every circuit `D` of a pre-radial drawing `K` of `H` has length `2 * |V(D) ∩ V(H)|` and
contains a vertex of `H`. -/
theorem circuit_length_eq_two_mul_ncard {H K D : Drawing S}
    (hP : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    (hD : D.IsCircuit) (hDs : D.IsSubdrawing K) :
    D.length = 2 * (D.V ∩ H.V).ncard ∧ (D.V ∩ H.V).Nonempty := by
  exact GM12.circuit_length_eq_two_mul_ncard hP hD hDs

/-- For a closed walk `W` of length `0` in `K`, `insWalk ins K W = {u}`. -/
theorem insWalk_of_length_zero (ins : Drawing S → Set S) (K : Drawing S) {u : S}
    (W : GraphWalk K.toGraph u u) (h0 : W.length = 0) :
    insWalk ins K W = {u} := by
  cases W with
  | nil h =>
    have hE : (walkDrawing K (GraphWalk.nil h)).E = ∅ := by
      rw [walkDrawing_E]
      ext e
      simp
    have hV : (walkDrawing K (GraphWalk.nil h)).V = {u} := by
      rw [walkDrawing_V]
      ext x
      simp
    have hU : (walkDrawing K (GraphWalk.nil h)).U = {u} := by
      rw [Drawing.U_eq, hV, hE]
      simp
    have hnoC : {C : Drawing S | C.IsCircuit ∧
        C.IsSubdrawing (walkDrawing K (GraphWalk.nil h))} = ∅ := by
      ext C
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hC hCs
      obtain ⟨_, W_C, _, hpos, _, hCE⟩ := hC
      cases W_C with
      | nil _ => exact Nat.lt_irrefl 0 hpos
      | @cons _ _ _ e _ _ =>
        have heC : e ∈ C.E := by rw [hCE]; exact List.mem_cons_self
        have heW := hCs.2 heC
        rw [hE] at heW
        exact heW
    change (walkDrawing K (GraphWalk.nil h)).U ∪
      ⋃ C ∈ {C : Drawing S | C.IsCircuit ∧
        C.IsSubdrawing (walkDrawing K (GraphWalk.nil h))}, ins C = {u}
    rw [hU, hnoC]
    simp
  | cons _ _ =>
    change (_ + 1 = 0) at h0
    omega

/-- `insWalk ins K W` is closed when `W.length < 2 * θ` and `ins` is a derived slope. -/
theorem isClosed_insWalk (hS : IsClosedSurface S) {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins) {u : S}
    (W : GraphWalk K.toGraph u u) (hW : W.length < 2 * θ) :
    IsClosed (insWalk ins K W) := by
  have : T2Space S := hS.2.1
  set D := walkDrawing K W
  have hDs : D.IsSubdrawing K := walkDrawing_isSubdrawing K W
  have hfinC : {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing D}.Finite := by
    refine Set.Finite.of_finite_image (f := fun C : Drawing S => (C.V, C.E)) ?_ ?_
    · refine (D.finite_V.finite_subsets.prod D.finite_edges.finite_subsets).subset ?_
      rintro _ ⟨C, ⟨-, hs'⟩, rfl⟩
      exact ⟨hs'.1, hs'.2⟩
    · intro C _ C' _ h
      exact Drawing.ext_of_V_E (congrArg Prod.fst h) (congrArg Prod.snd h)
  refine D.isClosed_U.union (hfinC.isClosed_biUnion fun C hC => ?_)
  have hlen : C.length < 2 * θ := by
    refine lt_of_le_of_lt ?_ hW
    refine (ncard_le_ncard ?_ (W.edges.finite_toSet)).trans (GM11.ncard_mem_list_le W.edges)
    intro e he
    have h := hC.2.2 he
    rwa [walkDrawing_E] at h
  exact (hd C hC.1 (hC.2.trans hDs) hlen).1.isClosed

/-- If `x, y ∈ A(H)` and there is a closed walk `W` of `K` of length `< 2θ` with `x', y' ⊆ ins(W)`,
then `2 * d(x, y) ≤ W.length`. -/
theorem two_mul_tangleMetric_le_walk_length {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) {ins : Drawing S → Set S} {θ : ℕ}
    {x y x' y' : Set S} (hx : IsCorrespondingAtom H K x x') (hy : IsCorrespondingAtom H K y y')
    {u : S} (W : GraphWalk K.toGraph u u) (hW : W.length < 2 * θ)
    (hxW : x' ⊆ insWalk ins K W) (hyW : y' ⊆ insWalk ins K W) :
    2 * tangleMetric H K ins θ x y ≤ W.length := by
  obtain ⟨k, hk⟩ := GM11.even_length_of_closed hK.2.1 W
  have heven : W.length = 2 * k := by omega
  have hle := GM11.tangleMetric_le_of_walk W hx hy hW heven hxW hyW
  omega

/-- When `E(H) ≠ ∅`, `1 ≤ θ`, and `x, y ∈ A(H)` with `x ≠ y`, we have `1 ≤ d(x, y)`. -/
theorem one_le_tangleMetric_of_ne [ConnectedSpace S] (hS : IsClosedSurface S) {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) (hE : H.E.Nonempty)
    {ins : Drawing S → Set S} {θ : ℕ} (hθ : 1 ≤ θ) {x y : Set S}
    (_hx : x ∈ H.A) (_hy : y ∈ H.A) (hne : x ≠ y) :
    1 ≤ tangleMetric H K ins θ x y := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rcases GM11.tangleMetric_cases (ins := ins) (θ := θ) hK.2.1 hne with h | ⟨_, hw⟩
  · rw [h]
    exact hθ
  obtain ⟨u, W, x', y', hx', hy', _, hlen, hxW, hyW⟩ := hw
  by_contra hlt
  have hW0 : W.length = 0 := by omega
  rw [insWalk_of_length_zero ins K W hW0] at hxW hyW
  obtain ⟨p, hp⟩ := atom_nonempty hx'.2.1
  obtain ⟨q, hq⟩ := atom_nonempty hy'.2.1
  have hpu : p = u := mem_singleton_iff.mp (hxW hp)
  have hqu : q = u := mem_singleton_iff.mp (hyW hq)
  have hxy' : x' = y' := by
    by_contra hne'
    exact disjoint_left.mp (disjoint_of_mem_A_ne hx'.2.1 hy'.2.1 hne') hp
      (hpu.trans hqu.symm ▸ hq)
  exact hne (correspondingAtom_inj hS hK hE hx' (hxy' ▸ hy'))

private theorem singleton_subset_insWalk_of_edge_atom (hS : IsClosedSurface S)
    {H K : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    {f f' : Set S} {v u : S} (hf : f ∈ H.E) (hvf : v ∈ closure f)
    (hf' : IsCorrespondingAtom H K f f') (W : GraphWalk K.toGraph u u)
    (hW : W.length < 2 * θ) (hfW : f' ⊆ insWalk ins K W) :
    ({v} : Set S) ⊆ insWalk ins K W := by
  have hf_sub : f ⊆ f' := by
    rcases hf'.2.2 with ⟨w, hw, hfw, -⟩ | ⟨-, -, hsub⟩ | ⟨hr, -⟩
    · exact absurd hw (hf.2.1 (hfw ▸ mem_singleton w)).2
    · exact hsub
    · obtain ⟨p, hp⟩ := hf.1
      exact absurd (hf.2.1 hp).1 (region_subset hr hp)
  rw [singleton_subset_iff]
  exact (isClosed_insWalk hS hd W hW).closure_subset_iff.mpr (hf_sub.trans hfW) hvf

/-- If `f ∈ E(H)`, `v ∈ V(H)`, `v ∈ closure f`, and `z ∈ A(H)` with `z ≠ f`, then
`d(z, {v}) ≤ d(z, f)`. -/
theorem tangleMetric_le_of_vertex_mem_closure_edge (hS : IsClosedSurface S)
    {H K : Drawing S} (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    {z f : Set S} {v : S} (hz : z ∈ H.A) (hf : f ∈ H.E) (hv : v ∈ H.V) (hvf : v ∈ closure f)
    (hzf : z ≠ f) :
    tangleMetric H K ins θ z {v} ≤ tangleMetric H K ins θ z f := by
  have : T2Space S := hS.2.1
  have hv_corr : IsCorrespondingAtom H K {v} {v} :=
    ⟨Or.inl (Or.inl ⟨v, hv, rfl⟩), Or.inl (Or.inl ⟨v, hK.2.1.2.1 hv, rfl⟩),
      Or.inl ⟨v, hv, rfl, rfl⟩⟩
  rcases GM11.tangleMetric_cases (ins := ins) (θ := θ) hK.2.1 hzf with h | ⟨_, hw⟩
  · rw [h]
    exact GM11.tangleMetric_le_order hK.2.1 z {v}
  obtain ⟨u, W, z', f', hz', hf', hW, hlen, hzW, hfW⟩ := hw
  exact GM11.tangleMetric_le
    ⟨u, W, z', {v}, ⟨hz, hz'.2⟩, hv_corr, hW, hlen, hzW,
      singleton_subset_insWalk_of_edge_atom hS hd hf hvf hf' W hW hfW⟩

/-- If `v` is an end of the edge `f` and `y ≠ f`, then `d(f, v) ≤ d(f, y)`. The inside of a closed
walk
is closed, so a walk whose inside holds the atom of `f` also holds `v`. This replaces the step
"`1 ≥ d(z, v)`" in the proof of (7.3) (page 36), which fails on a grid, where `d(z, v) = 2`. -/
theorem tangleMetric_edge_vertex_le (hS : IsClosedSurface S)
    {H K : Drawing S} (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    {f y : Set S} {v : S} (hf : f ∈ H.E) (hv : v ∈ H.V) (hvf : v ∈ closure f) (hfy : f ≠ y) :
    tangleMetric H K ins θ f {v} ≤ tangleMetric H K ins θ f y := by
  have : T2Space S := hS.2.1
  have hv_corr : IsCorrespondingAtom H K {v} {v} :=
    ⟨Or.inl (Or.inl ⟨v, hv, rfl⟩), Or.inl (Or.inl ⟨v, hK.2.1.2.1 hv, rfl⟩),
      Or.inl ⟨v, hv, rfl, rfl⟩⟩
  rcases GM11.tangleMetric_cases (ins := ins) (θ := θ) hK.2.1 hfy with h | ⟨_, hw⟩
  · rw [h]
    exact GM11.tangleMetric_le_order hK.2.1 f {v}
  obtain ⟨u, W, f', _, hf', _, hW, hlen, hfW, _⟩ := hw
  exact GM11.tangleMetric_le
    ⟨u, W, f', {v}, hf', hv_corr, hW, hlen, hfW,
      singleton_subset_insWalk_of_edge_atom hS hd hf hvf hf' W hW hfW⟩

/-- If `D` is a circuit of `K` with `D.length < 2 * θ`, `v ∈ V(D) ∩ V(H)`, and `x ∈ A(H)` meets
`ins(D)`, then `2 * d({v}, x) ≤ D.length` and `d({v}, x) ≤ |V(D) ∩ V(H)|`. -/
theorem tangleMetric_vertex_le_of_circuit (hS : IsClosedSurface S) {H K D : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hD : D.IsCircuit) (hDs : D.IsSubdrawing K) (hlen : D.length < 2 * θ)
    {v : S} (hv : v ∈ D.V ∩ H.V) {x : Set S} (hx : x ∈ H.A) (hxD : (x ∩ ins D).Nonempty) :
    2 * tangleMetric H K ins θ {v} x ≤ D.length ∧
      tangleMetric H K ins θ {v} x ≤ (D.V ∩ H.V).ncard := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hD' := hD
  obtain ⟨u, W_D, ⟨hnd, hed⟩, hpos, hDV, hDE⟩ := hD
  obtain ⟨W, hs, he⟩ := hDs.exists_walk_up W_D
  have hWD_eq : walkDrawing K W = D := by
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hs, hDV]
    · rw [walkDrawing_E, he, hDE]
  have hWlen : W.length = D.length := by
    rw [Drawing.length, hDE, ← he]
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext; simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup (he ▸ hed)]
    rfl
  have hWlt : W.length < 2 * θ := hWlen ▸ hlen
  have hinsD_sub : ins D ⊆ insWalk ins K W := by
    intro p hp
    refine Or.inr (mem_iUnion₂.mpr ⟨D, ⟨hD', ?_⟩, hp⟩)
    rw [hWD_eq]
    exact ⟨subset_rfl, subset_rfl⟩
  have hvW : ({v} : Set S) ⊆ insWalk ins K W := by
    rw [singleton_subset_iff]
    refine Or.inl ?_
    rw [hWD_eq]
    exact D.V_subset_U hv.1
  have hv_corr : IsCorrespondingAtom H K {v} {v} :=
    ⟨Or.inl (Or.inl ⟨v, hv.2, rfl⟩), Or.inl (Or.inl ⟨v, hK.2.1.2.1 hv.2, rfl⟩),
      Or.inl ⟨v, hv.2, rfl, rfl⟩⟩
  obtain ⟨x', hx', -⟩ := existsUnique_correspondingAtom hK hx
  have hx'W : x' ⊆ insWalk ins K W :=
    (theorem_3_1_proof hS hK hd hx' W hWlt).mpr (hxD.mono (inter_subset_inter_right x hinsD_sub))
  have h2le : 2 * tangleMetric H K ins θ {v} x ≤ D.length := by
    rw [← hWlen]
    exact two_mul_tangleMetric_le_walk_length hK hv_corr hx' W hWlt hvW hx'W
  have hDeq := (circuit_length_eq_two_mul_ncard hK.2.1 hD' hDs).1
  refine ⟨h2le, ?_⟩
  omega

/-! ## Proof of (7.1) -/

/-- General form of (7.1): if `E(H) ≠ ∅`, `z ∈ A(H)`, and either `|E(H)| ≥ 2` or `z ∉ E(H)`,
then there exists `e ∈ E(H)` with `d(z, e) = θ`. -/
theorem exists_edge_dist_eq_theta
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty)
    {z : Set S} (hz : z ∈ H.A) (hzE : 2 ≤ H.E.ncard ∨ z ∉ H.E) :
    ∃ e ∈ H.E, d z e = θ := by
  exact GM12.exists_edge_dist_eq_theta_of_metric hS hConn hMetric hE hz hzE

/-- Graph Minors XIV, (7.1) (page 35):
"Let $H$ be a 2-cell drawing with $|E(H)| \ge 2$ in a surface $\Sigma$, and let $\mathscr{T}$
be a respectful tangle in $H$ of order $\theta \ge 1$, with metric $d$. Then for every $z
\in A(H)$ there exists $e \in E(H)$ with $d(z, e) = \theta$." -/
theorem theorem_7_1_proof
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE2 : 2 ≤ H.E.ncard)
    {z : Set S} (hz : z ∈ H.A) :
    ∃ e ∈ H.E, d z e = θ := by
  have hpos : 0 < H.E.ncard := by omega
  have hE : H.E.Nonempty := (ncard_pos H.finite_edges).mp hpos
  exact exists_edge_dist_eq_theta hS hConn hMetric hE hz (Or.inl hE2)

/-! ## Proof of (7.2) -/

/-- Graph Minors XIV, (7.2) (page 36):
"Let $H$ be a 2-cell drawing in $\Sigma$ with $E(H) \ne \emptyset$, and let $\mathscr{T}$ be
a respectful tangle in $H$. Let $K$ be a radial drawing of $H$, and let $(A, B) \in
\mathscr{T}$. Then for every edge $e$ of $A$ there is a circuit $D$ of $K$ with $V(D) \cap
V(H) \subseteq V(A \cap B)$ and with $e \subseteq ins(D)$." -/
theorem theorem_7_2_proof (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S} {A B : Hypergraph S (Set S)} {e : Set S}
    (hE : H.E.Nonempty)
    (hResp : IsRespectfulDrawingTangle H θ T)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hAB : (A, B) ∈ T) (he : e ∈ A.edgeSet) :
    ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing K ∧ D.length < 2 * θ ∧
      D.V ∩ H.V ⊆ (A ∩ B).vertexSet ∧ e ⊆ ins D := by
  have : T2Space S := hS.2.1
  have h63 := (GM11.theorem_6_3_proof S hS hConn (PaintingOrDrawing.drawing H) K θ T ins
    hResp.1 hE hResp.2.1.isPretangle hResp.2.2 hK hd).1
  have hsep := hResp.2.1.isSeparation hAB
  have hord := hResp.2.1.order_lt hAB
  obtain ⟨k, C, hC, hin⟩ := (h63 A B hsep hord).mp hAB
  obtain ⟨i, hi⟩ := hin e he
  exact ⟨C i, (hC i).1, (hC i).2.1, (hC i).2.2.1, (hC i).2.2.2, hi⟩

/-! ## Proof of (7.3) -/

/-- Graph Minors XIV, (7.3) (page 36), proving `GM15.GM14Theorem73Statement`:
"Let $H$ be a 2-cell drawing in $\Sigma$ with $E(H) \ne \emptyset$, and let $\mathscr{T}$ be
a respectful tangle in $H$ of order $\theta$, with metric $d$. Let $z \in A(H)$, and let
$(A, B) \in \mathscr{T}$ with $E(B) \ne \{z\}$. Then there exists $e \in E(B)$ with $d(z, e)
\ge \theta - |V(A \cap B)|$." -/
theorem theorem_7_3_proof :
    GM15.GM14Theorem73Statement.{u} := by
  intro S _ _ H θ T d A₀ B₀ z hS hConn hE hMetric hz hAB₀ hBz₀
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rcases hMetric with ⟨hResp, K, ins, hK, hd, hd_eq⟩
  have hMetric' : HasTangleMetric H θ T d := ⟨hResp, K, ins, hK, hd, hd_eq⟩
  have hT := hResp.2.1
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hT.isPretangle hK.2.1.1 hd
  have htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c := fun a ha b hb c hc => by
    rw [hd_eq a ha c hc, hd_eq a ha b hb, hd_eq b hb c hc]
    exact GM11.tangleMetric_triangle hS hK.2.1 hsl a b c
  have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  -- Induction on `|V(B)|`.
  suffices hind : ∀ n : ℕ, ∀ B : Hypergraph S (Set S), B.vertexSet.ncard = n →
      (A₀, B) ∈ T → B.edgeSet ≠ {z} →
      ∃ e ∈ B.edgeSet, θ - separationOrder A₀ B ≤ d z e by
    exact hind B₀.vertexSet.ncard B₀ rfl hAB₀ hBz₀
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro B hBn hAB hBz
    have hsep : H.toHypergraph.IsSeparation A₀ B := hT.isSeparation hAB
    have hord : separationOrder A₀ B < θ := hT.order_lt hAB
    -- Step 1: check if some `v ∈ V(A₀ ∩ B)` has no incident edge in `B`.
    by_cases hex_iso : ∃ v ∈ (A₀ ∩ B).vertexSet, ∀ f ∈ B.edgeSet, ¬ B.Inc f v
    · obtain ⟨v, hvAB, hiso⟩ := hex_iso
      set B' := B.deleteVertices {v}
      have hB'le : B' ≤ H.toHypergraph := (deleteVertices_le B {v}).trans hsep.right_le
      have hB'E : B'.edgeSet = B.edgeSet := by
        ext f
        simp only [B', deleteVertices, mem_ofPred_eq, and_iff_left_iff_imp]
        intro hf w hw
        rw [mem_singleton_iff.mp hw]
        exact hiso f hf
      have hsep' : H.toHypergraph.IsSeparation A₀ B' := by
        rw [isSeparation_iff_of_le hsep.left_le hB'le]
        refine ⟨?_, by rw [hB'E, hsep.edgeSet_union], by rw [hB'E]; exact hsep.edgeSet_inter_eq⟩
        ext w
        simp only [B', deleteVertices, mem_union, mem_sdiff, mem_singleton_iff]
        constructor
        · rintro (hwA | ⟨hwB, -⟩)
          · exact hsep.left_le.vertexSet_subset hwA
          · exact hsep.right_le.vertexSet_subset hwB
        · intro hwH
          have hwU : w ∈ A₀.vertexSet ∪ B.vertexSet := hsep.vertexSet_union ▸ hwH
          by_cases hwv : w = v
          · subst hwv
            exact Or.inl hvAB.1
          · rcases hwU with hwA | hwB
            · exact Or.inl hwA
            · exact Or.inr ⟨hwB, hwv⟩
      have hord_le : separationOrder A₀ B' ≤ separationOrder A₀ B := by
        refine ncard_le_ncard ?_ (A₀ ∩ B).vertexSet_finite
        intro w hw
        exact ⟨hw.1, hw.2.1⟩
      have hord' : separationOrder A₀ B' < θ := lt_of_le_of_lt hord_le hord
      have hAB' : (A₀, B') ∈ T :=
        GM10.theorem_2_9_proof hT hAB hsep' hord' (Or.inr (Or.inl subset_rfl))
      have hB'lt : B'.vertexSet.ncard < n := by
        rw [← hBn]
        refine ncard_lt_ncard ?_ B.vertexSet_finite
        refine ⟨sdiff_subset, fun hsub => ?_⟩
        exact (hsub hvAB.2).2 (mem_singleton v)
      obtain ⟨e, heB', hde⟩ := ih B'.vertexSet.ncard hB'lt B' rfl hAB' (hB'E ▸ hBz)
      refine ⟨e, hB'E ▸ heB', ?_⟩
      omega
    · push Not at hex_iso
      have hBE_ne : B.edgeSet.Nonempty := by
        by_contra hBE_empty
        rw [not_nonempty_iff_eq_empty] at hBE_empty
        have hAE : A₀.edgeSet = H.E := by
          have hU := hsep.edgeSet_union
          rw [hBE_empty, union_empty] at hU
          exact hU
        have hAV : A₀.vertexSet = H.V := by
          apply subset_antisymm hsep.left_le.vertexSet_subset
          intro v hv
          obtain ⟨e, he, hve⟩ := GM11.exists_edge_of_regionFacts hS hrf hv
          have heA : e ∈ A₀.edgeSet := hAE.symm ▸ he
          have hincH : H.toHypergraph.Inc e v :=
            (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing H)).mpr ⟨he, hv,
              hve⟩
          have hincA : A₀.Inc e v := (inc_iff_of_le hsep.left_le heA).mpr hincH
          exact A₀.vertex_mem_of_inc hincA
        exact hT.axiom3 hAB hAV
      by_cases hE2 : 2 ≤ H.E.ncard
      · obtain ⟨e, heH, hze⟩ := theorem_7_1_proof hS hConn hMetric' hE2 hz
        have heU : e ∈ A₀.edgeSet ∪ B.edgeSet := hsep.edgeSet_union.symm ▸ heH
        rcases heU with heA | heB
        · obtain ⟨D, hD, hDs, hDlen, hDV, heD⟩ :=
            theorem_7_2_proof hS hConn hE hResp hK hd hAB heA
          obtain ⟨v, hv⟩ := (circuit_length_eq_two_mul_ncard hK.2.1 hD hDs).2
          have hvAB : v ∈ (A₀ ∩ B).vertexSet := hDV hv
          obtain ⟨p, hp⟩ := heH.1
          have hve_le : d {v} e ≤ (A₀ ∩ B).vertexSet.ncard := by
            rw [hd_eq {v} (Or.inl (Or.inl ⟨v, hv.2, rfl⟩)) e (Or.inl (Or.inr heH))]
            refine (tangleMetric_vertex_le_of_circuit hS hK hd hD hDs hDlen hv
              (Or.inl (Or.inr heH)) ⟨p, hp, heD hp⟩).2.trans ?_
            exact ncard_le_ncard hDV (A₀ ∩ B).vertexSet_finite
          have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hv.2, rfl⟩)
          have he_mem_A : e ∈ H.A := Or.inl (Or.inr heH)
          have hzv_tri : d z e ≤ d z {v} + d {v} e := htri z hz {v} hvA e he_mem_A
          have hzv_ge : θ - separationOrder A₀ B ≤ d z {v} := by
            change θ - (A₀ ∩ B).vertexSet.ncard ≤ d z {v}
            omega
          obtain ⟨f, hfB, hfv⟩ := hex_iso v hvAB
          have hfH : f ∈ H.E := hsep.right_le.edgeSet_subset hfB
          have hf_inc : H.toHypergraph.Inc f v := inc_of_le hsep.right_le hfv
          have hvf : v ∈ closure f :=
            ((PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing H)).mp hf_inc).2.2
          by_cases hzf : z = f
          · subst hzf
            have hex_g : ∃ g ∈ B.edgeSet, g ≠ z := by
              by_contra hno_g
              push Not at hno_g
              apply hBz
              exact subset_antisymm hno_g (singleton_subset_iff.mpr hfB)
            obtain ⟨g, hgB, hgz⟩ := hex_g
            have hgH : g ∈ H.E := hsep.right_le.edgeSet_subset hgB
            -- The paper writes `d(z, g) ≥ 1 ≥ d(z, v)` here, but `d(z, v)` can be 2. The bound
            -- `d(z, v) ≤ d(z, g)` is what is needed, and it holds for the reason of the next case.
            have hle_zg : d z {v} ≤ d z g := by
              rw [hd_eq z hz {v} hvA, hd_eq z hz g (Or.inl (Or.inr hgH))]
              exact tangleMetric_edge_vertex_le hS hK hd hfH hv.2 hvf hgz.symm
            refine ⟨g, hgB, ?_⟩
            omega
          · refine ⟨f, hfB, ?_⟩
            have hle_zf : d z {v} ≤ d z f := by
              rw [hd_eq z hz {v} hvA, hd_eq z hz f (Or.inl (Or.inr hfH))]
              exact tangleMetric_le_of_vertex_mem_closure_edge hS hK hd hz hfH hv.2 hvf hzf
            omega
        · refine ⟨e, heB, ?_⟩
          omega
      · obtain ⟨e, heB⟩ := hBE_ne
        have heH : e ∈ H.E := hsep.right_le.edgeSet_subset heB
        have hHE_eq : H.E = {e} := by
          have h1 : H.E.ncard ≤ 1 := by omega
          exact (eq_of_subset_of_ncard_le (singleton_subset_iff.mpr heH)
            (by rw [ncard_singleton]; exact h1) H.finite_edges).symm
        have hBE_eq : B.edgeSet = {e} :=
          subset_antisymm (hsep.right_le.edgeSet_subset.trans (hHE_eq ▸ subset_rfl))
            (singleton_subset_iff.mpr heB)
        have hze : z ≠ e := fun h => hBz (h ▸ hBE_eq)
        have hz_not_E : z ∉ H.E := by
          rw [hHE_eq, mem_singleton_iff]
          exact hze
        obtain ⟨e', he'H, hze'⟩ := exists_edge_dist_eq_theta hS hConn hMetric' hE hz
          (Or.inr hz_not_E)
        have he'e : e = e' := (mem_singleton_iff.mp (hHE_eq ▸ he'H)).symm
        subst he'e
        refine ⟨e, heB, ?_⟩
        omega

/-! ## Proof of (7.4) -/

/-- Graph Minors XIV, (7.4) (page 36):
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in
$H$. Let $K$ be a radial drawing of $H$, let $(A, B) \in \mathscr{T}$, and let $C$ be a
circuit of $A$ with $|V(B \cap C)| \le 1$. Then there is a circuit $D$ of $K$ with $V(D)
\cap V(H) \subseteq V(A \cap B)$ and $U(C) \subseteq ins(D)$." -/
theorem theorem_7_4_proof (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H K C : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S} {A B : Hypergraph S (Set S)}
    (hResp : IsRespectfulDrawingTangle H θ T)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hAB : (A, B) ∈ T)
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing H)
    (hCA : C.V ⊆ A.vertexSet ∧ C.E ⊆ A.edgeSet)
    (hBC : (B.vertexSet ∩ C.V).ncard ≤ 1) :
    ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing K ∧ D.length < 2 * θ ∧
      D.V ∩ H.V ⊆ (A ∩ B).vertexSet ∧ C.U ⊆ ins D := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hsep := hResp.2.1.isSeparation hAB
  have hC' := hC
  obtain ⟨_, W_C, _, hpos, _, hCE⟩ := hC
  have hCE_ne : C.E.Nonempty := by
    cases W_C with
    | nil _ => exact absurd hpos (Nat.lt_irrefl 0)
    | @cons _ _ _ e _ _ => exact ⟨e, by rw [hCE]; exact List.mem_cons_self⟩
  obtain ⟨e, heC⟩ := hCE_ne
  have heA : e ∈ A.edgeSet := hCA.2 heC
  have heH : e ∈ H.E := hsep.left_le.edgeSet_subset heA
  obtain ⟨D, hD, hDs, hDlen, hDV, heD⟩ :=
    theorem_7_2_proof hS hConn ⟨e, heH⟩ hResp hK hd hAB heA
  refine ⟨D, hD, hDs, hDlen, hDV, ?_⟩
  obtain ⟨hDdisc, hDbd, -⟩ := hd D hD hDs hDlen
  have hDcl : IsClosed (ins D) := hDdisc.isClosed
  have hDfr : frontier (ins D) = D.U := by rw [subBd_eq_frontier', hDbd]
  have hDU_sub : D.U ⊆ ins D := hDfr ▸ hDcl.frontier_subset
  have hCU_oArc : IsOArc C.U := isOArc_of_isCircuit hC'
  have hUU : H.U ∩ K.U = H.V := hK.2.1.1
  have hcap_sub : C.U ∩ D.U ⊆ B.vertexSet ∩ C.V := by
    rintro x ⟨hxC, hxD⟩
    have hxHV : x ∈ H.V := by
      have : x ∈ H.U ∩ K.U := ⟨hCs.U_subset hxC, hDs.U_subset hxD⟩
      rwa [hUU] at this
    have hxCV : x ∈ C.V := by
      by_contra hxCV
      obtain ⟨f, hfC, hxf⟩ := C.exists_edge_of_mem hxC hxCV
      exact ((hCs.2 hfC).2.1 hxf).2 hxHV
    have hxDV : x ∈ D.V := by
      by_contra hxDV
      obtain ⟨g, hgD, hxg⟩ := D.exists_edge_of_mem hxD hxDV
      exact ((hDs.2 hgD).2.1 hxg).2 (hK.2.1.2.1 hxHV)
    exact ⟨(hDV ⟨hxDV, hxHV⟩).2, hxCV⟩
  have hcap_le1 : (C.U ∩ D.U).ncard ≤ 1 :=
    (ncard_le_ncard hcap_sub ((B.vertexSet_finite).subset inter_subset_left)).trans hBC
  have hcap_fin : (C.U ∩ D.U).Finite :=
    (B.vertexSet_finite.subset inter_subset_left).subset hcap_sub
  have hconn_diff : IsPreconnected (C.U \ D.U) := by
    have heq : C.U \ D.U = C.U \ (C.U ∩ D.U) := by ext; simp
    rw [heq]
    by_cases hne : (C.U ∩ D.U).Nonempty
    · obtain ⟨u, hu⟩ := hne
      have hsing : C.U ∩ D.U = {u} :=
        (eq_of_subset_of_ncard_le (singleton_subset_iff.mpr hu)
          (by rw [ncard_singleton]; exact hcap_le1) hcap_fin).symm
      rw [hsing]
      exact (isPathConnected_oArc_diff hCU_oArc hu.1).isConnected.isPreconnected
    · rw [not_nonempty_iff_eq_empty.mp hne, sdiff_empty]
      exact IsOArc.isPreconnected hCU_oArc
  have he_sub_diff : e ⊆ C.U \ D.U := by
    intro p hp
    refine ⟨(heC.2.1 hp).1, fun hpD => ?_⟩
    exact (heC.2.1 hp).2 (hcap_sub ⟨(heC.2.1 hp).1, hpD⟩).2
  obtain ⟨p₀, hp₀⟩ := heC.1
  have hdis_fr : Disjoint (C.U \ D.U) (frontier (ins D)) := by
    rw [hDfr]
    exact disjoint_sdiff_left
  have hdiff_sub : C.U \ D.U ⊆ ins D :=
    subset_of_disjoint_frontier hconn_diff hDcl hdis_fr (he_sub_diff hp₀) (heD hp₀)
  intro x hxC
  by_cases hxD : x ∈ D.U
  · exact hDU_sub hxD
  · exact hdiff_sub ⟨hxC, hxD⟩

/-! ## Proof of (7.5) -/

/-- Graph Minors XIV, (7.5) (pages 36–37), proving `GM16.GM14Theorem75Statement`:
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$ of
order $\theta$. Let $\lambda \ge 0$ be an integer, and let $\Lambda \subseteq \Sigma$ be an
$\lambda$-zone. Let $K$ be ... a radial drawing of $H$, and let $D$ be a circuit of $K$ with $U(D)
\subseteq \bar{\Lambda}$ and $|E(D)| < 2(\theta - \lambda)$. Then $ins(D) \subseteq
\bar{\Lambda}$." -/
theorem theorem_7_5_proof :
    GM16.GM14Theorem75Statement.{w} := by
  intro S _ _ H K D θ lam T d ins z Λ hS hConn hMetric hK hd hZone hD hDs hDU_sub hDlen
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rcases hMetric with ⟨hResp, K₀, ins₀, hK₀, hd₀, hd_eq⟩
  have hMetric' : HasTangleMetric H θ T d := ⟨hResp, K₀, ins₀, hK₀, hd₀, hd_eq⟩
  have hsl₀ : IsSlope K₀ (2 * θ) ins₀ :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hResp.2.1.isPretangle hK₀.2.1.1
      hd₀
  have htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c := fun a ha b hb c hc => by
    rw [hd_eq a ha c hc, hd_eq a ha b hb, hd_eq b hb c hc]
    exact GM11.tangleMetric_triangle hS hK₀.2.1 hsl₀ a b c
  have hDlt : D.length < 2 * θ := by omega
  obtain ⟨hDdisc, hDbd, hDsep⟩ := hd D hD hDs hDlt
  have hDU_oArc : IsOArc D.U := isOArc_of_isCircuit hD
  obtain ⟨Δ, ⟨hΔsub, hΔdisc, hΔbd, -⟩, -⟩ :=
    disc_oArc (closure Λ) D.U hZone.isClosedDisc_closure hDU_sub hDU_oArc
  have hΔbd_sub : subBd Δ = D.U := by
    rw [IsClosedDisc.subBd_eq_discBd hS hΔdisc, hΔbd]
  by_cases h_eq : ins D = Δ
  · exact h_eq ▸ hΔsub
  · exfalso
    have hbd_eq : discBd (ins D) = discBd Δ := by
      rw [← IsClosedDisc.subBd_eq_discBd hS hDdisc, hDbd, hΔbd]
    have hcov : ins D ∪ Δ = univ := cover_of_discBd_eq hS hDdisc hΔdisc hbd_eq h_eq
    have hOD₁ : IsOpenDisc (ins D \ D.U) :=
      hDbd ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS hDdisc).1
    have hOD₂ : IsOpenDisc (Δ \ D.U) :=
      hΔbd_sub ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS hΔdisc).1
    have hO₁ : IsOpen (ins D \ D.U) := hOD₁.1
    have hne₁ : (ins D \ D.U).Nonempty := IsOpenDisc.nonempty hOD₁
    have hO₂ : IsOpen (Δ \ D.U) := hOD₂.1
    have hne₂ : (Δ \ D.U).Nonempty := IsOpenDisc.nonempty hOD₂
    have hdis_int : Disjoint (ins D \ D.U) (Δ \ D.U) := by
      have hcl_sub : Δ \ D.U ⊆ univ \ ins D := by
        intro x ⟨hxΔ, hxU⟩
        refine ⟨mem_univ x, fun hxin => ?_⟩
        have hfrΔ : frontier Δ = D.U := by rw [subBd_eq_frontier', hΔbd_sub]
        have hfrD : frontier (ins D) = D.U := by rw [subBd_eq_frontier', hDbd]
        have hsub₁ : ins D \ D.U ⊆ Δ :=
          subset_of_disjoint_frontier
            (hfrD ▸ IsClosedDisc.isPreconnected_diff_frontier hS hDdisc)
            hΔdisc.isClosed (hfrΔ ▸ disjoint_sdiff_left) ⟨hxin, hxU⟩ hxΔ
        have hsub₁' : ins D ⊆ Δ := by
          intro y hy
          exact hΔdisc.isClosed.closure_subset_iff.mpr hsub₁
            (hfrD ▸ IsClosedDisc.subset_closure_diff_frontier hS hDdisc hy)
        have hsub₂ : Δ \ D.U ⊆ ins D :=
          subset_of_disjoint_frontier
            (hfrΔ ▸ IsClosedDisc.isPreconnected_diff_frontier hS hΔdisc)
            hDdisc.isClosed (hfrD ▸ disjoint_sdiff_left) ⟨hxΔ, hxU⟩ hxin
        have hsub₂' : Δ ⊆ ins D := by
          intro y hy
          exact hDdisc.isClosed.closure_subset_iff.mpr hsub₂
            (hfrΔ ▸ IsClosedDisc.subset_closure_diff_frontier hS hΔdisc hy)
        exact h_eq (subset_antisymm hsub₁' hsub₂')
      exact disjoint_left.mpr fun x hx₁ hx₂ => (hcl_sub hx₂).2 hx₁.1
    obtain ⟨y₁, hy₁, hy₁K⟩ := exists_notMem_U (Γ := K) hS hO₁ hne₁
    obtain ⟨r₁, hr₁, hy₁r₁⟩ := exists_region_of_notMem hy₁K
    obtain ⟨y₂, hy₂, hy₂K⟩ := exists_notMem_U (Γ := K) hS hO₂ hne₂
    obtain ⟨r₂, hr₂, hy₂r₂⟩ := exists_region_of_notMem hy₂K
    have hbd_inf : (subBd Λ).Infinite := GM11.infinite_of_isOArc hZone.isOArc_bd
    obtain ⟨x₀, hx₀bd, hx₀V⟩ := hbd_inf.exists_notMem_finite H.finite_V
    obtain ⟨e₀, he₀, -⟩ := H.exists_edge_of_mem (hZone.bd_subset_U hx₀bd) hx₀V
    have hE_ne : H.E.Nonempty := ⟨e₀, he₀⟩
    have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE_ne
    obtain ⟨e₁, he₁, he₁r₁⟩ := hrf.1 r₁ hr₁
    obtain ⟨e₂, he₂, he₂r₂⟩ := hrf.1 r₂ hr₂
    have hr₁_sub : r₁ ⊆ ins D \ D.U := by
      have hdis : Disjoint r₁ (frontier (ins D)) := by
        rw [subBd_eq_frontier', hDbd]
        exact disjoint_left.mpr fun x hxr hxD => region_subset hr₁ hxr (hDs.U_subset hxD)
      have hsub := subset_of_disjoint_frontier (region_isPreconnected hr₁) hDdisc.isClosed hdis
        hy₁r₁ hy₁.1
      exact fun x hx => ⟨hsub hx, fun hxD => region_subset hr₁ hx (hDs.U_subset hxD)⟩
    have hr₂_sub : r₂ ⊆ Δ \ D.U := by
      have hdis : Disjoint r₂ (frontier Δ) := by
        rw [subBd_eq_frontier', hΔbd_sub]
        exact disjoint_left.mpr fun x hxr hxD => region_subset hr₂ hxr (hDs.U_subset hxD)
      have hsub := subset_of_disjoint_frontier (region_isPreconnected hr₂) hΔdisc.isClosed hdis
        hy₂r₂ hy₂.1
      exact fun x hx => ⟨hsub hx, fun hxD => region_subset hr₂ hx (hDs.U_subset hxD)⟩
    have he₁_ne_e₂ : e₁ ≠ e₂ := by
      intro heq
      subst heq
      obtain ⟨p, hp⟩ := he₁.1
      exact disjoint_left.mp hdis_int (hr₁_sub (he₁r₁ hp)) (hr₂_sub (he₂r₂ hp))
    have hE2 : 2 ≤ H.E.ncard :=
      (one_lt_ncard H.finite_edges).mpr ⟨e₁, he₁, e₂, he₂, he₁_ne_e₂⟩
    obtain ⟨e, heH, hze⟩ := theorem_7_1_proof hS hConn hMetric' hE2 hZone.z_mem
    have he_not_cl : ¬ e ⊆ closure Λ := by
      intro hsub
      have hle := hZone.dist_le e (Or.inl (Or.inr heH)) hsub
      have hpos : 0 < D.length := by
        obtain ⟨v, hv⟩ := (circuit_length_eq_two_mul_ncard hK.2.1 hD hDs).2
        have := (circuit_length_eq_two_mul_ncard hK.2.1 hD hDs).1
        have : 0 < (D.V ∩ H.V).ncard :=
          (ncard_pos (D.finite_V.subset inter_subset_left)).mpr ⟨v, hv⟩
        omega
      omega
    have hUU : H.U ∩ K.U = H.V := hK.2.1.1
    have he_dis_DU : Disjoint e D.U := by
      refine disjoint_left.mpr fun x hxe hxD => ?_
      have : x ∈ H.U ∩ K.U := ⟨(heH.2.1 hxe).1, hDs.U_subset hxD⟩
      rw [hUU] at this
      exact (heH.2.1 hxe).2 this
    have he_sub_insD : e ⊆ ins D := by
      have he_not_Δ : ¬ (e ∩ Δ).Nonempty := by
        rintro ⟨x, hxe, hxΔ⟩
        have hfrΔ : frontier Δ = D.U := by rw [subBd_eq_frontier', hΔbd_sub]
        have hsub : e ⊆ Δ :=
          subset_of_disjoint_frontier heH.2.2.1.isConnected.isPreconnected hΔdisc.isClosed
            (hfrΔ ▸ he_dis_DU) hxe hxΔ
        exact he_not_cl (hsub.trans hΔsub)
      intro x hxe
      have hx_univ : x ∈ ins D ∪ Δ := hcov.symm ▸ mem_univ x
      exact hx_univ.resolve_right fun hxΔ => he_not_Δ ⟨x, hxe, hxΔ⟩
    set A := (PaintingOrDrawing.drawing H).inter (ins D)
    set B := (PaintingOrDrawing.drawing H).interOutside (ins D)
    have heA : e ∈ A.edgeSet := ⟨heH, he_sub_insD⟩
    have hAB_V : (A ∩ B).vertexSet ⊆ D.V ∩ H.V := by
      intro x hx
      have hfrD : frontier (ins D) = D.U := by rw [subBd_eq_frontier', hDbd]
      exact inter_outside_vertex hK.2.1.2.1 hDs hfrD hx
    obtain ⟨D₀, hD₀, hD₀s, hD₀len, hD₀V, heD₀⟩ :=
      theorem_7_2_proof hS hConn hE_ne hResp hK₀ hd₀ hDsep heA
    obtain ⟨v, hv₀⟩ := (circuit_length_eq_two_mul_ncard hK₀.2.1 hD₀ hD₀s).2
    have hvD : v ∈ D.V ∩ H.V := hAB_V (hD₀V hv₀)
    have hv_cl : ({v} : Set S) ⊆ closure Λ :=
      singleton_subset_iff.mpr (hDU_sub (D.V_subset_U hvD.1))
    have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hvD.2, rfl⟩)
    have hzv_le : d z {v} ≤ lam := hZone.dist_le {v} hvA hv_cl
    obtain ⟨p, hp⟩ := heH.1
    have hve_le : d {v} e ≤ (D.V ∩ H.V).ncard := by
      rw [hd_eq {v} hvA e (Or.inl (Or.inr heH))]
      refine (tangleMetric_vertex_le_of_circuit hS hK₀ hd₀ hD₀ hD₀s hD₀len hv₀
        (Or.inl (Or.inr heH)) ⟨p, hp, heD₀ hp⟩).2.trans ?_
      exact ncard_le_ncard (hD₀V.trans hAB_V) (D.finite_V.subset inter_subset_left)
    have hDeq := (circuit_length_eq_two_mul_ncard hK.2.1 hD hDs).1
    have htri' := htri z hZone.z_mem {v} hvA e (Or.inl (Or.inr heH))
    omega

/-! ## Proof of (7.6) -/

/-- For an open disc `Λ` whose boundary `subBd Λ` is an `O`-arc and whose closure `closure Λ` is a
closed disc, `discBd (closure Λ) = subBd Λ`. -/
theorem discBd_closure_eq_subBd {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Λ : Set S} (hΛ : IsOpenDisc Λ) (hO : IsOArc (subBd Λ))
    (hcl : IsClosedDisc (closure Λ)) :
    discBd (closure Λ) = subBd Λ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨Δ₀, ⟨hΔ₀sub, hΔ₀disc, hΔ₀bd, -⟩, -⟩ :=
    disc_oArc (closure Λ) (subBd Λ) hcl (fun x hx => hx.1) hO
  have hΔ₀bd_sub : subBd Δ₀ = subBd Λ := by
    rw [IsClosedDisc.subBd_eq_discBd hS hΔ₀disc, hΔ₀bd]
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ.1
  have hOD₀ : IsOpenDisc (Δ₀ \ subBd Λ) :=
    hΔ₀bd_sub ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₀disc).1
  obtain ⟨p, hp⟩ := IsOpenDisc.nonempty hOD₀
  have hpΛ : p ∈ Λ := by
    have hp_cl : p ∈ closure Λ := hΔ₀sub hp.1
    rw [hclL] at hp_cl
    exact hp_cl.resolve_right hp.2
  have hfr₀ : frontier Δ₀ = subBd Λ := by rw [subBd_eq_frontier', hΔ₀bd_sub]
  have hΛ_sub : Λ ⊆ Δ₀ :=
    subset_of_disjoint_frontier hΛ.isPathConnected.isConnected.isPreconnected hΔ₀disc.isClosed
      (hfr₀ ▸ hdisL) hpΛ hp.1
  have h_eq : closure Λ = Δ₀ :=
    subset_antisymm (hΔ₀disc.isClosed.closure_subset_iff.mpr hΛ_sub) hΔ₀sub
  rw [h_eq, hΔ₀bd]

/-- Graph Minors XIV, (7.6) (page 37):
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$
of order $\theta$. Let $\lambda \ge 0$ be an integer, and let $\Lambda \subseteq \Sigma$ be
a $\lambda$-zone. Let $K$ be a radial drawing of $H$, and let $D$ be a circuit of $K$ with
$|E(D)| < 2(\theta - \lambda)$ and $bd(\Lambda) \subseteq ins(D)$. Then $\bar{\Lambda}
\subseteq ins(D)$." -/
theorem theorem_7_6_proof
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H K D : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {ins : Drawing S → Set S} {z Λ : Set S}
    (hMetric : HasTangleMetric H θ T d)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hZone : IsLambdaZoneAround H d lam z Λ)
    (hD : D.IsCircuit) (hDs : D.IsSubdrawing K)
    (hDlen : D.length < 2 * (θ - lam))
    (hbd_sub : subBd Λ ⊆ ins D) :
    closure Λ ⊆ ins D := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hDlt : D.length < 2 * θ := by omega
  obtain ⟨hDdisc, hDbd, -⟩ := hd D hD hDs hDlt
  obtain ⟨Δ', ⟨hΔ'sub, hΔ'disc, hΔ'bd, -⟩, -⟩ :=
    disc_oArc (ins D) (subBd Λ) hDdisc hbd_sub hZone.isOArc_bd
  by_cases h_eq : closure Λ = Δ'
  · exact h_eq ▸ hΔ'sub
  · exfalso
    have hcl_bd : discBd (closure Λ) = subBd Λ :=
      discBd_closure_eq_subBd hS hZone.isOpenDisc hZone.isOArc_bd hZone.isClosedDisc_closure
    have hcov : closure Λ ∪ Δ' = univ :=
      cover_of_discBd_eq hS hZone.isClosedDisc_closure hΔ'disc (hcl_bd.trans hΔ'bd.symm) h_eq
    have hΔ'bd_sub : subBd Δ' = subBd Λ := by
      rw [IsClosedDisc.subBd_eq_discBd hS hΔ'disc, hΔ'bd]
    have hOD' : IsOpenDisc (Δ' \ subBd Λ) :=
      hΔ'bd_sub ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS hΔ'disc).1
    have hO' : IsOpen (Δ' \ subBd Λ) := hOD'.1
    have hfrD : frontier (ins D) = D.U := by rw [subBd_eq_frontier', hDbd]
    have hDU_dis : Disjoint D.U (Δ' \ subBd Λ) := by
      refine disjoint_left.mpr fun x hxD hxΔ' => ?_
      have hx_int : x ∈ interior (ins D) :=
        interior_maximal (sdiff_subset.trans hΔ'sub) hO' hxΔ'
      have hx_fr : x ∈ frontier (ins D) := hfrD ▸ hxD
      exact hx_fr.2 hx_int
    have hDU_sub : D.U ⊆ closure Λ := by
      intro x hxD
      have hx_univ : x ∈ closure Λ ∪ Δ' := hcov.symm ▸ mem_univ x
      rcases hx_univ with hxcl | hxΔ'
      · exact hxcl
      · by_cases hxbd : x ∈ subBd Λ
        · exact hxbd.1
        · exact absurd ⟨hxΔ', hxbd⟩ (disjoint_left.mp hDU_dis hxD)
    have hins_sub : ins D ⊆ closure Λ :=
      theorem_7_5_proof H K D θ lam T d ins z Λ hS hConn hMetric hK hd hZone hD hDs
        hDU_sub hDlen
    have hΔ'_sub_cl : Δ' ⊆ closure Λ := hΔ'sub.trans hins_sub
    have hcl_univ : closure Λ = univ := by
      rw [← hcov, union_eq_left.mpr hΔ'_sub_cl]
    have hbd_empty : subBd (closure Λ) = ∅ := by
      rw [← subBd_eq_frontier', hcl_univ, frontier_univ]
    have hbd_eq' : subBd (closure Λ) = subBd Λ := by
      rw [IsClosedDisc.subBd_eq_discBd hS hZone.isClosedDisc_closure, hcl_bd]
    obtain ⟨q, hq⟩ := IsOArc.nonempty hZone.isOArc_bd
    rw [← hbd_eq', hbd_empty] at hq
    exact hq

end GraphMinor.GM14

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section76
public import LeanPool.GraphMinor.GM12.Section79
public import LeanPool.GraphMinor.GM12.Section711a
public import LeanPool.GraphMinor.GM12.Section4CircuitMeet
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Graph Minors XII, (7.8): respectful tangle in a 2-cell subdrawing deleting a ball of edges

This file proves the walk and metric lemmas for **(7.8)** of Graph Minors XII (page 268).
The main proof is in `Section7Proved.lean`.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Function Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Helper lemmas on walks in a radial drawing -/

omit [T2Space S] in
/-- Every walk `W` between `a` and `b` contains a simple walk `W'` between `a` and `b` of length at
most `W.length` whose vertices are a subset of `W.support`. -/
theorem exists_simple_subwalk {Γ : Drawing S} {a b : S} (W : GraphWalk Γ.toGraph a b) :
    ∃ W' : GraphWalk Γ.toGraph a b, W'.IsSimple ∧ W'.length ≤ W.length ∧
      ∀ x ∈ W'.support, x ∈ W.support := by
  induction W with
  | nil h => exact ⟨.nil h, by simp [GraphWalk.IsSimple], le_rfl, fun _ hx => hx⟩
  | @cons u v w e h r ih =>
    obtain ⟨r', hr', hlen, hsub⟩ := ih
    by_cases hu : u ∈ r'.support
    · obtain ⟨R₁, R₂, rfl⟩ := r'.exists_append_of_mem hu
      refine ⟨R₂, (isSimple_of_append hr').2, ?_, fun x hx => List.mem_cons_of_mem u (hsub x ?_)⟩
      · rw [GraphWalk.length_append] at hlen
        simp only [GraphWalk.length_cons]
        omega
      · exact (GraphWalk.mem_support_append _ _).mpr (Or.inr hx)
    · refine ⟨.cons h r', List.nodup_cons.mpr ⟨hu, hr'⟩, ?_, ?_⟩
      · simp only [GraphWalk.length_cons]
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem u (hsub x hx)

omit [T2Space S] in
/-- In a pre-radial drawing `K` of `Γ`, the parity of a walk's length determines whether its
endpoints lie on the same side of the bipartition `(Γ.V, K.V \ Γ.V)`, and the number of visits to
`Γ.V` along `W.support` is bounded by `W.length / 2 + 1` (if `a ∈ Γ.V`) or `(W.length + 1) / 2`
(if `a ∉ Γ.V`). -/
theorem walk_bipartite_parity_and_count {Γ K : Drawing S}
    (hP : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {a b : S} (W : GraphWalk K.toGraph a b) :
    (Even W.length ↔ (a ∈ Γ.V ↔ b ∈ Γ.V)) ∧
    by classical exact W.support.countP (· ∈ Γ.V) ≤
      if a ∈ Γ.V then W.length / 2 + 1 else (W.length + 1) / 2 := by
  classical
  have hbip := bipartite_of_preRadial hP
  induction W with
  | nil h =>
    refine ⟨by simp, ?_⟩
    split_ifs with ha <;> simp [ha]
  | @cons u v w e hl r ih =>
    have huv : u ∈ Γ.V ↔ v ∉ Γ.V := hbip e u v hl
    obtain ⟨ih_even, ih_count⟩ := ih
    constructor
    · rw [GraphWalk.length_cons, Nat.even_add_one, ih_even]
      tauto
    · rw [GraphWalk.support_cons, List.countP_cons, GraphWalk.length_cons]
      by_cases hu : u ∈ Γ.V
      · have hv : v ∉ Γ.V := huv.mp hu
        simp only [hu, hv, decide_true, ↓reduceIte] at ih_count ⊢
        omega
      · have hv : v ∈ Γ.V := not_not.mp (huv.not.mp hu)
        simp only [hu, hv, decide_false, Bool.false_eq_true, ↓reduceIte] at ih_count ⊢
        omega

/-- If there is a walk in a radial drawing `K` of `Γ` from `v₀ ∈ r` (`r ∈ Γ.R`, `v₀ ∈ K.V \ Γ.V`)
to `v ∈ Γ.V` of length at most `2 * k`, then `v ∈ regionLineVertices Γ r k`. -/
theorem mem_regionLineVertices_of_radial_walk {Γ K : Drawing S}
    (hP : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {r : Set S} {v₀ v : S} {k : ℕ}
    (hv₀_r : v₀ ∈ r) (hv₀_not : v₀ ∉ Γ.V) (hv : v ∈ Γ.V)
    (W : GraphWalk K.toGraph v₀ v) (hWlen : W.length ≤ 2 * k) :
    v ∈ regionLineVertices Γ r k := by
  classical
  obtain ⟨W', hW'_sim, hW'_len, _⟩ := exists_simple_subwalk W
  have hv₀_ne_v : v₀ ≠ v := fun h => hv₀_not (h ▸ hv)
  have hP_path : (walkDrawing K W').IsPathBetween v₀ v := walkDrawing_isPathBetween K hW'_sim
  have hline_ends : IsLineWithEnds (walkDrawing K W').U v₀ v :=
    GM11.isLine_of_isPathBetween hP_path hv₀_ne_v
  obtain ⟨f_line, -⟩ := hline_ends
  have hline : IsLine (walkDrawing K W').U := ⟨f_line⟩
  have hSubK : (walkDrawing K W').IsSubdrawing K := walkDrawing_isSubdrawing K W'
  have hnorm : (PaintingOrDrawing.drawing Γ).IsNormal (walkDrawing K W').U := by
    intro x ⟨hxP, hxΓ⟩
    have hx : x ∈ Γ.U ∩ K.U := ⟨hxΓ, hSubK.U_subset hxP⟩
    have hUU : Γ.U ∩ K.U = Γ.V := hP.1
    rwa [hUU] at hx
  have hv₀_U : v₀ ∈ (walkDrawing K W').U :=
    (walkDrawing K W').V_subset_U (by rw [walkDrawing_V]; exact W'.start_mem_support)
  have hv_U : v ∈ (walkDrawing K W').U :=
    (walkDrawing K W').V_subset_U (by rw [walkDrawing_V]; exact W'.end_mem_support)
  have hU_inter_V : (walkDrawing K W').U ∩ Γ.V ⊆
      ((W'.support.filter (· ∈ Γ.V)).toFinset : Set S) := by
    intro x ⟨hxU, hxV⟩
    have hxPV : x ∈ (walkDrawing K W').V :=
      subdrawing_vertex_of_mem_U hSubK hxU (hP.2.1 hxV)
    rw [walkDrawing_V] at hxPV
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨hxPV, hxV⟩
  have hcard_le : ((walkDrawing K W').U ∩ Γ.V).ncard ≤ W'.support.countP (· ∈ Γ.V) := by
    calc ((walkDrawing K W').U ∩ Γ.V).ncard
      _ ≤ ((W'.support.filter (· ∈ Γ.V)).toFinset : Set S).ncard :=
          ncard_le_ncard hU_inter_V (Finset.finite_toSet _)
      _ = (W'.support.filter (· ∈ Γ.V)).length := by
          rw [ncard_coe_finset, List.toFinset_card_of_nodup (hW'_sim.filter _)]
      _ = W'.support.countP (· ∈ Γ.V) := List.countP_eq_length_filter.symm
  obtain ⟨hpar, hcnt⟩ := walk_bipartite_parity_and_count hP W'
  simp only [hv₀_not, ↓reduceIte] at hcnt
  have hnot_even : ¬ Even W'.length := by
    rw [hpar]
    intro hiff
    exact hv₀_not (hiff.mpr hv)
  rw [Nat.not_even_iff_odd] at hnot_even
  obtain ⟨m, hm⟩ := hnot_even
  have hlen_le : W'.length ≤ 2 * k := hW'_len.trans hWlen
  have hdiv_le : (W'.length + 1) / 2 ≤ k := by omega
  refine ⟨hv, (walkDrawing K W').U, hline, hnorm, hv_U, ⟨v₀, hv₀_U, hv₀_r⟩,
    hcard_le.trans (hcnt.trans hdiv_le)⟩

/-- If `W` is a closed walk of `K` of length at most `4 * k` containing `v₀ ∈ r` (`v₀ ∉ Γ.V`) and
`v ∈ Γ.V`, then `v ∈ regionLineVertices Γ r k`. -/
theorem mem_regionLineVertices_of_closed_walk {Γ K : Drawing S}
    (hP : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {r : Set S} {u v₀ v : S} {k : ℕ}
    (hv₀_r : v₀ ∈ r) (hv₀_not : v₀ ∉ Γ.V)
    (W : GraphWalk K.toGraph u u) (hWlen : W.length ≤ 4 * k)
    (hv₀_W : v₀ ∈ (walkDrawing K W).V)
    (hv_W : v ∈ (walkDrawing K W).V) (hv_Γ : v ∈ Γ.V) :
    v ∈ regionLineVertices Γ r k := by
  rw [walkDrawing_V, mem_ofPred_eq] at hv₀_W hv_W
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hv₀_W
  set Rot := W₂.append W₁
  have hRot_len : Rot.length ≤ 4 * k := by
    rw [GraphWalk.length_append] at hWlen ⊢
    omega
  have hv_Rot : v ∈ Rot.support := by
    rw [GraphWalk.mem_support_append] at hv_W ⊢
    exact hv_W.symm
  obtain ⟨P₁, P₂, hRot_eq⟩ := Rot.exists_append_of_mem hv_Rot
  have hsum : P₁.length + P₂.reverse.length ≤ 4 * k := by
    rw [GraphWalk.length_reverse, ← GraphWalk.length_append, ← hRot_eq]
    exact hRot_len
  rcases le_or_gt P₁.length (2 * k) with hle₁ | hgt₁
  · exact mem_regionLineVertices_of_radial_walk hP hv₀_r hv₀_not hv_Γ P₁ hle₁
  · have hle₂ : P₂.reverse.length ≤ 2 * k := by omega
    exact mem_regionLineVertices_of_radial_walk hP hv₀_r hv₀_not hv_Γ P₂.reverse hle₂

omit [T2Space S] in
/-- Rotating a closed walk `W` at a vertex `v ∈ W.support` produces a closed walk at `v` with the
same length and the same walk drawing. -/
theorem rotate_closed_walk [T1Space S] {K : Drawing S} {u v : S}
    (W : GraphWalk K.toGraph u u) (hv : v ∈ W.support) :
    ∃ V : GraphWalk K.toGraph v v,
      V.length = W.length ∧ walkDrawing K V = walkDrawing K W := by
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hv
  refine ⟨W₂.append W₁, ?_, Drawing.ext_of_V_E ?_ ?_⟩
  · simp only [GraphWalk.length_append]
    omega
  · rw [walkDrawing_V, walkDrawing_V]
    ext x
    simp only [mem_ofPred_eq, GraphWalk.mem_support_append, or_comm]
  · rw [walkDrawing_E, walkDrawing_E]
    ext e
    simp only [mem_ofPred_eq, GraphWalk.edges_append, List.mem_append, or_comm]

/-- For a restraint `X`, its boundary `subBd X` is preconnected. -/
theorem isPreconnected_subBd_of_isRestraint (hS : IsClosedSurface S) [ConnectedSpace S]
    {K : Drawing S} {ins : Drawing S → Set S} {two_theta : ℕ} {X : Set S}
    (hr : IsRestraint K ins two_theta X) : IsPreconnected (subBd X) := by
  obtain ⟨_, _, ⟨h, -, -, hrng, -, -⟩, -⟩ :=
    exists_perimeterWalk hS hr.isClosed hr.isGammaNice hr.isSimplyConnected hr.nonempty hr.ne_univ
  rw [← hrng]
  exact isPreconnected_range (h.continuous.comp (continuous_id.prodMk continuous_const))

/-- The underlying point set `D.U` of a 2-cell drawing `D` in a connected closed surface is
preconnected. -/
theorem isPreconnected_U_of_isTwoCell (hS : IsClosedSurface S) [ConnectedSpace S]
    {D : Drawing S} (h2cell : (PaintingOrDrawing.drawing D).IsTwoCell) :
    IsPreconnected D.U := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed D.isClosed_U]
  intro U V hU hV hUV hdisj
  let U' := D.U ∩ U
  let V' := D.U ∩ V
  have hU' : IsClosed U' := D.isClosed_U.inter hU
  have hV' : IsClosed V' := D.isClosed_U.inter hV
  have hdisj' : Disjoint U' V' := hdisj.mono inter_subset_right inter_subset_right
  have hUV' : U' ∪ V' = D.U := by
    rw [← inter_union_distrib_left]
    exact inter_eq_left.mpr hUV
  by_cases hU'ne : U'.Nonempty
  · have hV'0 : V' = ∅ := eq_empty_of_split hS h2cell.2 hU' hV' hdisj' hUV' hU'ne
    refine Or.inl fun x hx => ?_
    have hx' : x ∈ U' ∪ V' := hUV'.symm ▸ hx
    rw [hV'0, union_empty] at hx'
    exact hx'.2
  · rw [not_nonempty_iff_eq_empty] at hU'ne
    refine Or.inr fun x hx => ?_
    have hx' : x ∈ U' ∪ V' := hUV'.symm ▸ hx
    rw [hU'ne, empty_union] at hx'
    exact hx'.2

/-- In the setting of (7.8), for any edge `e ∈ Γ.E` with `d c e ≤ k < θ` and `(c = e → 2 ≤ k)`,
there is a closed walk `W` of `K` of length at most `2 * k` such that `h ⊆ insWalk ins K W` and
`e ⊆ insWalk ins K W`. -/
theorem exists_walk_of_edge_dist_le (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ K : Drawing S} {θ k : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {ins : Drawing S → Set S}
    (hResp : IsRespectfulDrawingTangle Γ θ T) (hE : Γ.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hd_eq : ∀ x ∈ Γ.A, ∀ y ∈ Γ.A, d x y = tangleMetric Γ K ins θ x y)
    {c h e : Set S} (hc : c ∈ Γ.A) (hh : IsCorrespondingAtom Γ K c h)
    (he : e ∈ Γ.E) (hkθ : k < θ) (hd_ce : d c e ≤ k) (hce_k : c = e → 2 ≤ k) :
    ∃ (u : S) (W : GraphWalk K.toGraph u u),
      W.length ≤ 2 * k ∧ h ⊆ insWalk ins K W ∧ e ⊆ insWalk ins K W := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have heA : e ∈ Γ.A := Or.inl (Or.inr he)
  obtain ⟨r_e, hr_e, -⟩ := existsUnique_correspondingAtom hK heA
  have her_e : e ⊆ r_e := by
    rcases hr_e.2.2 with ⟨v, hv, rfl, -⟩ | ⟨_, _, hsub⟩ | ⟨hr, -⟩
    · exact absurd hv (he.2.1 (mem_singleton v)).2
    · exact hsub
    · obtain ⟨p₀, hp₀⟩ := he.1
      exact absurd (he.2.1 hp₀).1 (region_subset hr hp₀)
  by_cases hce : c = e
  · subst hce
    have hk2 : 2 ≤ k := hce_k rfl
    have hT := hResp.2.1
    have hcH : c ∈ Γ.toHypergraph.edgeSet := he
    have hsep := isSeparation_edgeHypergraph_deleteEdges hcH
    have hsize : edgeSize Γ.toHypergraph c ≤ 2 := edgeSize_drawing_le_two he
    have hord : separationOrder (edgeHypergraph Γ.toHypergraph c)
        (Γ.toHypergraph.deleteEdges {c}) < θ := by
      rw [separationOrder_edgeHypergraph_deleteEdges]
      omega
    have hmemT : (edgeHypergraph Γ.toHypergraph c, Γ.toHypergraph.deleteEdges {c}) ∈ T :=
      (GM10.theorem_2_7_proof hT.one_le hT.isSeparation hT.order_lt hT.axiom1 hT.axiom2).mp
        hT c hcH (by omega)
    obtain ⟨C, hC, hCs, hClen, hCV, hcC⟩ :=
      (theorem_1_1_proof hS hResp hE hK hd hsep hord).mp hmemT c (by simp [edgeHypergraph])
    have hCeven := (circuit_length_eq_two_mul_ncard hK.2.1 hC hCs).1
    have hCV_le : (C.V ∩ Γ.V).ncard ≤ 2 := by
      have hsubV : C.V ∩ Γ.V ⊆ Γ.toHypergraph.ends c :=
        hCV.trans fun x hx => hx.1
      have hends_fin : (Γ.toHypergraph.ends c).Finite :=
        Γ.toHypergraph.vertexSet_finite.subset fun x hx => Γ.toHypergraph.vertex_mem_of_inc hx
      exact (ncard_le_ncard hsubV hends_fin).trans hsize
    have hC' : C.IsCircuit := hC
    obtain ⟨u₀, W₀, -, -, hV₀, -⟩ := hC'
    have hu₀ : u₀ ∈ C.V := hV₀ ▸ W₀.start_mem_support
    obtain ⟨W, hWC, hWlen⟩ := circuit_walk_at hC hCs hu₀
    have hWlt : W.length < 2 * θ := hWlen.trans_lt hClen
    have hcW : (c ∩ insWalk ins K W).Nonempty := by
      obtain ⟨p₀, hp₀⟩ := he.1
      refine ⟨p₀, hp₀, Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, ?_⟩, hcC hp₀⟩)⟩
      rw [hWC]
      exact Drawing.IsSubdrawing.refl C
    have hhW : h ⊆ insWalk ins K W :=
      (corresponding_atom_subset_iff hS hK hd hh W hWlt).mpr hcW
    have hhr_e : h = r_e := (existsUnique_correspondingAtom hK hc).unique hh hr_e
    refine ⟨u₀, W, ?_, hhW, her_e.trans (hhr_e ▸ hhW)⟩
    omega
  · classical
    rw [hd_eq c hc e heA] at hd_ce
    by_cases hex : ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
        IsCorrespondingAtom Γ K c x' ∧ IsCorrespondingAtom Γ K e y' ∧
        W.length < 2 * θ ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W
    · simp only [tangleMetric, hce, hex, ↓reduceIte] at hd_ce
      set S_k := {m : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
        IsCorrespondingAtom Γ K c x' ∧ IsCorrespondingAtom Γ K e y' ∧
        W.length < 2 * θ ∧ W.length = 2 * m ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W}
      have hle' : sInf S_k ≤ k := hd_ce
      obtain ⟨u, W, x', y', hx', hy', hWlt, hx'W, hy'W⟩ := hex
      obtain ⟨m₀, hm₀⟩ : ∃ m₀, W.length = 2 * m₀ := ⟨_, closed_walk_length_eq_two_mul hK.2.1 W⟩
      have hSk_ne : S_k.Nonempty := ⟨m₀, u, W, x', y', hx', hy', hWlt, hm₀, hx'W, hy'W⟩
      obtain ⟨u₁, W₁, x₁', y₁', hx₁', hy₁', _, hW₁len, hx₁'W, hy₁'W⟩ := Nat.sInf_mem hSk_ne
      have hx₁_eq : x₁' = h := (existsUnique_correspondingAtom hK hc).unique hx₁' hh
      have hy₁_eq : y₁' = r_e := (existsUnique_correspondingAtom hK heA).unique hy₁' hr_e
      refine ⟨u₁, W₁, by omega, hx₁_eq ▸ hx₁'W, her_e.trans (hy₁_eq ▸ hy₁'W)⟩
    · simp only [tangleMetric, hce, hex, ↓reduceIte] at hd_ce
      omega


end GraphMinor.GM12

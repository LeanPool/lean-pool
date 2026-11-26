/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Nice73

/-!
# Graph Minors XI, (8.5)

`theorem_8_5` says that `ins(W)` is a restraint with `l(ins(W)) ≤ l(W)`, for a closed walk `W` of
length
`< 2θ`. `isSimplyConnected_insOf` gives simple connectivity by way of (7.3) and (3.1), which are
`nice_73` and `nice_31`.

The proof in the paper says that any `O`-arc in `U(W)` bounds a disc in `ins(W)`. This needs that an
`O`-arc
in a drawing is a circuit, which is `exists_circuit_of_oArc`. The count of edges in `l(ins(W)) ≤
l(W)` is
`perimeterCount_le`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A walk with one use of `e` splits at that use. -/
theorem exists_split_at_edge [DecidableEq (Set S)] {Γ : Drawing S} {e : Set S} {a b : S}
    (W : GraphWalk Γ.toGraph a b) (he : W.edges.count e = 1) :
    ∃ (p q : S) (P : GraphWalk Γ.toGraph a p) (Q : GraphWalk Γ.toGraph q b),
      Γ.toGraph.IsLink e p q ∧ e ∉ P.edges ∧ e ∉ Q.edges := by
  induction W with
  | nil h => simp [GraphWalk.edges] at he
  | @cons a c b f hl rest ih =>
    by_cases hfe : f = e
    · subst hfe
      refine ⟨a, c, .nil hl.2.1, rest, hl, by simp [GraphWalk.edges], ?_⟩
      have : (f :: rest.edges).count f = 1 := he
      rw [List.count_cons_self] at this
      exact List.count_eq_zero.mp (by omega)
    · have h' : rest.edges.count e = 1 := by
        have : (f :: rest.edges).count e = 1 := he
        rwa [List.count_cons_of_ne hfe] at this
      obtain ⟨p, q, P, Q, hlk, hP, hQ⟩ := ih h'
      refine ⟨p, q, .cons hl P, Q, hlk, ?_, hQ⟩
      simp only [GraphWalk.edges, List.mem_cons, not_or]
      exact ⟨fun h => hfe h.symm, hP⟩

variable [T2Space S]

/-- An edge used once by a closed walk lies on a circuit of the walk, since the rest of the walk
joins its
ends. -/
theorem exists_circuit_of_count_one {Γ : Drawing S} (hγ' : ∃ γ, EdgePar Γ γ) [DecidableEq (Set S)]
    {u : S} (W : GraphWalk Γ.toGraph u u) {e : Set S} (he : W.edges.count e = 1) :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing (walkDrawing Γ W) ∧ e ∈ C.E := by
  obtain ⟨γ, hγ⟩ := hγ'
  let G := walkDrawing Γ W
  have hG : G.IsSubdrawing Γ := walkDrawing_isSubdrawing Γ W
  have heW : e ∈ W.edges := List.count_pos_iff.mp (by omega)
  have heG : e ∈ G.E := by
    change e ∈ (walkDrawing Γ W).E
    rw [walkDrawing_E]
    exact heW
  obtain ⟨W', -, hW'⟩ := hG.exists_walk_down W
    (fun x hx => by
      change x ∈ (walkDrawing Γ W).V
      rw [walkDrawing_V]
      exact hx)
    (fun f hf => by
      change f ∈ (walkDrawing Γ W).E
      rw [walkDrawing_E]
      exact hf)
  obtain ⟨p, q, P, Q, hlk, hP, hQ⟩ := exists_split_at_edge W' (by rw [hW']; exact he)
  let R := Q.append P
  have hRe : e ∉ R.edges := by
    simp only [R, GraphWalk.edges_append, List.mem_append, not_or]
    exact ⟨hQ, hP⟩
  have hDG : (G.deleteEdge e).IsSubdrawing G := deleteEdge_isSubdrawing G e
  obtain ⟨R', -, hR'⟩ := hDG.exists_walk_down R
    (fun x hx => by
      rw [deleteEdge_V]
      exact mem_V_of_mem_support R hx)
    (fun f hf => by
      rw [deleteEdge_E]
      exact ⟨mem_E_of_mem_edges R hf, fun h => hRe (mem_singleton_iff.mp h ▸ hf)⟩)
  have hlink := isLink_ends hγ hG heG false
  have hpair : ({p, q} : Set S) = {γ e (endOf false), γ e (endOf true)} := by
    rw [← hlk.2.2.2]
    exact hlink.2.2.2
  have hreach : Nonempty (GraphWalk (G.deleteEdge e).toGraph (γ e (endOf false)) (γ e
    (endOf true))) := by
    rcases Set.pair_eq_pair_iff.mp hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [← h₁, ← h₂]
      exact ⟨R'.reverse⟩
    · rw [← h₁, ← h₂]
      exact ⟨R'⟩
  exact exists_circuit_of_reach hγ hG heG hreach

variable {Γ : Drawing S} {k : ℕ} {ins : Drawing S → Set S}

omit [T2Space S] in
theorem insOf_mono {D₁ D₂ : Drawing S} (h : D₁.IsSubdrawing D₂) : insOf ins D₁ ⊆ insOf ins D₂ := by
  rintro x (hx | hx)
  · exact Or.inl (h.U_subset hx)
  · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC.1, hC.2.trans h⟩, hxC⟩)

omit [T2Space S] in
/-- A drawing has finitely many circuits. -/
theorem finite_circuits (D : Drawing S) : {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing D}.Finite
  := by
  refine Set.Finite.of_finite_image (f := fun C : Drawing S => (C.V, C.E)) ?_ ?_
  · refine (D.finite_V.finite_subsets.prod D.finite_edges.finite_subsets).subset ?_
    rintro _ ⟨C, ⟨-, hs'⟩, rfl⟩
    exact ⟨hs'.1, hs'.2⟩
  · intro C _ C' _ h
    exact Drawing.ext_of_V_E (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- `Γ | W` is confined, for a closed walk of length `< 2θ`. -/
theorem isConfined_walk {u v : S} (W : GraphWalk Γ.toGraph u v) (hW : W.length < k) :
    IsConfined k (walkDrawing Γ W) := by
  intro C _ hCs
  have hle : C.length ≤ W.edges.length := by
    refine (ncard_le_ncard ?_ (W.edges.finite_toSet)).trans (ncard_mem_list_le W.edges)
    intro e he
    have h := hCs.2 he
    rwa [walkDrawing_E] at h
  exact lt_of_le_of_lt hle hW

theorem interSet_U_subset {T : Set S} (hT : IsClosed T) : (Γ.interSet T).U ⊆ T := by
  rw [Drawing.U_eq]
  have hE : ∀ f, f ∈ (Γ.interSet T).E → f ⊆ T := fun f hf => by
    change f ∈ (Γ.span _ _).E at hf
    rw [Γ.span_E] at hf
    exact hf.1.2
  rintro x (hx | hx)
  · rcases hx with ⟨⟨-, hx⟩, -⟩ | hx
    · exact hx
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
      exact closure_minimal hf.1.2 hT hxf.1
  · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
    exact closure_minimal (hE f hf) hT hxf

/-- If `T ⊆ U(D)` then `Γ ∩ T` is a subdrawing of `D`. -/
theorem interSet_isSubdrawing {D : Drawing S} {T : Set S} (hD : D.IsSubdrawing Γ)
    (hTc : IsClosed T) (hT : T ⊆ D.U) : (Γ.interSet T).IsSubdrawing D := by
  have hH : (Γ.interSet T).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · have hxU : x ∈ D.U := hT (interSet_U_subset hTc ((Γ.interSet T).V_subset_U hx))
    have hxV : x ∈ Γ.V := hH.1 hx
    rw [D.U_eq] at hxU
    rcases hxU with h | h
    · exact h
    · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
      exact (hD.closure_inter_V hg ▸ (⟨hxg, hxV⟩ : x ∈ closure g ∩ Γ.V) : x ∈ closure g ∩ D.V).2
  · have hfΓ := hH.2 hf
    have hfT : f ⊆ T := by
      change f ∈ (Γ.span _ _).E at hf
      rw [Γ.span_E] at hf
      exact hf.1.2
    obtain ⟨y, hy⟩ := hfΓ.1
    have hyV : y ∉ D.V := fun h => (hfΓ.2.1 hy).2 (hD.1 h)
    obtain ⟨g, hg, hyg⟩ := D.exists_edge_of_mem (hT (hfT hy)) hyV
    obtain rfl := Γ.edge_eq_of_mem hfΓ (hD.2 hg) hy hyg
    exact hg

/-- `U(D) ⊆ ins(D)` and the frontier of `ins(D)` is in `U(D)`, for confined `D`. -/
theorem frontier_insOf_subset (hs : IsSlope Γ k ins) {D : Drawing S} (hD : D.IsSubdrawing Γ)
    (hconf : IsConfined k D) : IsClosed (insOf ins D) ∧ frontier (insOf ins D) ⊆ D.U := by
  have hcl : IsClosed (insOf ins D) := D.isClosed_U.union ((finite_circuits D).isClosed_biUnion
    fun C hC => (hs.isClosedDisc C hC.1 (hC.2.trans hD) (hconf C hC.1 hC.2)).isClosed)
  refine ⟨hcl, fun x hx => ?_⟩
  by_contra hxU
  have hxZ : x ∈ insOf ins D := hcl.frontier_subset hx
  rcases hxZ with h | h
  · exact hxU h
  obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp h
  have hsm := hconf C hC.1 hC.2
  have hb := hs.subBd_eq C hC.1 (hC.2.trans hD) hsm
  rw [subBd_eq_frontier] at hb
  have hint : x ∈ interior (ins C) := by
    by_contra hni
    exact hxU (hC.2.U_subset (hb ▸ ⟨subset_closure hxC, hni⟩))
  refine hx.2 (interior_mono ?_ hint)
  exact subset_biUnion_of_mem (u := ins) hC |>.trans subset_union_right

variable [ConnectedSpace S] (hS : IsClosedSurface S)
include hS

omit [ConnectedSpace S] in
/-- `ins(D)` is nice, for confined `D`. -/
theorem isGammaNice_insOf (hs : IsSlope Γ k ins) {D : Drawing S} (hD : D.IsSubdrawing Γ)
    (hconf : IsConfined k D) : IsGammaNice Γ (insOf ins D) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  exact isGammaNice_of_frontier hD subset_union_left (frontier_insOf_subset hs hD hconf).2

omit [ConnectedSpace S] in
/-- `ins(C)` is nice and bounded by `U(C)`, for a circuit `C` of length `< 2θ`. -/
theorem ins_slope_facts (hs : IsSlope Γ k ins) {C : Drawing S} (hC : C.IsCircuit)
  (hCs : C.IsSubdrawing Γ)
    (hl : C.length < k) : frontier (ins C) = C.U ∧ C.U ⊆ ins C ∧ IsGammaNice Γ (ins C) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hb := hs.subBd_eq C hC hCs hl
  rw [subBd_eq_frontier] at hb
  have hsub : C.U ⊆ ins C := by
    rw [← hb]
    exact (hs.isClosedDisc C hC hCs hl).isCompact.isClosed.frontier_subset
  exact ⟨hb, hsub, isGammaNice_of_frontier hCs hsub hb.subset⟩

/-- `ins(D)` is simply-connected, for confined `D` with `U(D)` arc-wise connected. The paper shows
this
inside the proof of (8.5), by (7.3) and repeated use of (3.1). -/
theorem isSimplyConnected_insOf
    (hs : IsSlope Γ k ins) {D : Drawing S} (hD : D.IsSubdrawing Γ) (hconf : IsConfined k D)
    (hpc : IsPathConnected D.U) : IsSimplyConnectedSet (insOf ins D) := by
  classical
  obtain ⟨hZc, -⟩ := frontier_insOf_subset hs hD hconf
  have hZn := isGammaNice_insOf hS hs hD hconf
  have hUn : IsGammaNice Γ D.U := by
    have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
    exact isGammaNice_of_frontier hD subset_rfl D.isClosed_U.frontier_subset
  let L : List (Set S) := (finite_circuits D).toFinset.toList.map ins
  have hmem : ∀ Y ∈ L, ∃ C : Drawing S, (C.IsCircuit ∧ C.IsSubdrawing D) ∧ ins C = Y := by
    intro Y hY
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hY
    exact ⟨C, (finite_circuits D).mem_toFinset.mp (Finset.mem_toList.mp hC), rfl⟩
  have hfacts : ∀ Y ∈ L, IsClosedDisc Y ∧ frontier Y ⊆ D.U ∧ IsGammaNice Γ Y := by
    intro Y hY
    obtain ⟨C, ⟨hC, hCs⟩, rfl⟩ := hmem Y hY
    have hl := hconf C hC hCs
    have hf := ins_slope_facts hS hs hC (hCs.trans hD) hl
    exact ⟨hs.isClosedDisc C hC (hCs.trans hD) hl, hf.1.subset.trans hCs.U_subset, hf.2.2⟩
  have heq : insOf ins D = withDiscs D.U L := by
    refine congrArg (D.U ∪ ·) ?_
    ext x
    simp only [mem_iUnion₂, mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨C, hC, hx⟩
      exact ⟨ins C, List.mem_map.mpr ⟨C, Finset.mem_toList.mpr ((finite_circuits
        D).mem_toFinset.mpr hC),
        rfl⟩, hx⟩
    · rintro ⟨Y, hY, hx⟩
      obtain ⟨C, hC, rfl⟩ := hmem Y hY
      exact ⟨C, hC, hx⟩
  have hsub : ∀ L' : List (Set S), (∀ Y ∈ L', Y ∈ L) →
      IsClosed (withDiscs D.U L') ∧ IsGammaNice Γ (withDiscs D.U L') := by
    intro L' hL'
    refine ⟨D.isClosed_U.union (L'.finite_toSet.isClosed_biUnion fun Y hY =>
      (hfacts Y (hL' Y hY)).1.isCompact.isClosed), isGammaNice_of_sat fun a ha hne => ?_⟩
    obtain ⟨x, hxa, hx | hx⟩ := hne
    · exact (nice_atom hUn ha ⟨x, hxa, hx⟩).trans subset_union_left
    · obtain ⟨Y, hY, hxY⟩ := mem_iUnion₂.mp hx
      refine (nice_atom (hfacts Y (hL' Y hY)).2.2 ha ⟨x, hxa, hxY⟩).trans ?_
      exact (subset_biUnion_of_mem (u := id) (s := {Y | Y ∈ L'}) hY).trans subset_union_right
  rw [heq]
  refine theorem_7_11_proof hS D.isClosed_U hpc (fun Y hY => ⟨(hfacts Y hY).1,
    (hfacts Y hY).2.1⟩) ?_ ?_
  · intro Y L' hsuf hcap
    have hsubL : ∀ Z ∈ Y :: L', Z ∈ L := fun Z hZ => hsuf.subset hZ
    have hYL := hsubL Y List.mem_cons_self
    have hL' := hsub L' fun Z hZ => hsubL Z (List.mem_cons_of_mem _ hZ)
    exact nice_31 S hS Γ Y _ (hfacts Y hYL).1.isCompact.isClosed hL'.1 (hfacts Y hYL).2.2 hL'.2
      (IsClosedDisc.isSimplyConnectedSet (hfacts Y hYL).1) hcap
  · intro φ hφ
    by_contra hnot
    have hZ := hsub L fun _ h => h
    obtain ⟨F, hF, hFφ, hFn⟩ := nice_73 S hS Γ _ hZ.1 hZ.2 φ (hφ.trans subset_union_left) hnot
    obtain ⟨C, hC, hCs, rfl⟩ := exists_circuit_of_oArc hF (hFφ.trans hφ)
    have hl := hconf C hC hCs
    have hf := ins_slope_facts hS hs hC (hCs.trans hD) hl
    refine hFn (isNullHomotopicOArcIn_of_subset_disc hF ?_ (hs.isClosedDisc C hC
      (hCs.trans hD) hl) hf.2.1)
    rw [← heq]
    exact subset_biUnion_of_mem (u := ins) (show C ∈ {C | C.IsCircuit
      ∧ C.IsSubdrawing D} from ⟨hC, hCs⟩)
      |>.trans subset_union_right

/-- The count behind `l(ins(W)) ≤ l(W)`, in the proof of (8.5). A perimeter walk of `ins(W)` uses
only
edges of `W`, and if it uses an edge twice then `W` does too. For otherwise the edge is on a circuit
`C` of
`Γ | W`, and `ins(C)` has points on both sides of it, so the complement of `ins(W)` cannot be on
both
sides. -/
theorem perimeterCount_le (hs : IsSlope Γ k ins) {u : S} (W : GraphWalk Γ.toGraph u u)
    (hW : W.length < k) {e : Set S} (he : e ∈ Γ.E) :
    perimeterCount (insWalk ins Γ W) e ≤ edgeCount W.edges e := by
  classical
  let G := walkDrawing Γ W
  have hG : G.IsSubdrawing Γ := walkDrawing_isSubdrawing Γ W
  have hconf : IsConfined k G := isConfined_walk W hW
  obtain ⟨hcl, hfr⟩ := frontier_insOf_subset hs hG hconf
  change frontier (insWalk ins Γ W) ⊆ G.U at hfr
  unfold perimeterCount
  by_cases hne : (e ∩ frontier (insWalk ins Γ W)).Nonempty
  swap
  · simp only [hne, ite_false]
    exact Nat.zero_le _
  obtain ⟨y, hye, hyf⟩ := id hne
  simp only [hne, ite_true]
  have hyV : y ∉ G.V := fun h => (he.2.1 hye).2 (hG.1 h)
  obtain ⟨g, hg, hyg⟩ := G.exists_edge_of_mem (hfr hyf) hyV
  obtain rfl := Γ.edge_eq_of_mem he (hG.2 hg) hye hyg
  have heW : e ∈ W.edges := by
    have h : e ∈ (walkDrawing Γ W).E := hg
    rwa [walkDrawing_E] at h
  have hpos : 1 ≤ edgeCount W.edges e := List.count_pos_iff.mpr heW
  by_cases h2 : IsTwoSided (insWalk ins Γ W)ᶜ e
  swap
  · simpa only [h2, ite_false] using hpos
  simp only [h2, ite_true]
  by_contra hlt
  have hone : edgeCount W.edges e = 1 := by omega
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  obtain ⟨C, hC, hCs, heC⟩ := exists_circuit_of_count_one ⟨γ, hγ⟩ W hone
  have hl := hconf C hC hCs
  have hd := hs.isClosedDisc C hC (hCs.trans hG) hl
  have hf := ins_slope_facts hS hs hC (hCs.trans hG) hl
  have hbd : discBd (ins C) = C.U := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hd, hf.1]
  have heb : e ⊆ discBd (ins C) := by
    rw [hbd]
    exact subset_closure.trans (C.closure_subset_U heC)
  obtain ⟨y', hy'e, hy'⟩ := h2
  obtain ⟨w, hwO, hwi⟩ := mem_closure_iff.mp (discBd_subset_closure hd
    (heb hy'e)) _ isOpen_interior hy'
  rcases interior_subset hwO with h | h
  · refine h (Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hwi.1⟩))
  · exact hwi.2 (heb h)


/-- **(8.5)** of Graph Minors XI (page 97): "Let $W$ be a closed walk in $\Gamma$ of length $<
2\theta$. Then $\mathrm{ins}(W)$ is a
restraint and $l(\mathrm{ins}(W)) \le l(W)$." -/
theorem theorem_8_5_proof (hs : IsSlope Γ k ins) {u : S} (W : GraphWalk Γ.toGraph u u)
  (hW : W.length < k) :
    IsRestraint Γ ins k (insWalk ins Γ W) ∧ perimeterWalkLength Γ (insWalk ins Γ W) ≤ W.length := by
  classical
  let G := walkDrawing Γ W
  have hG : G.IsSubdrawing Γ := walkDrawing_isSubdrawing Γ W
  have hconf : IsConfined k G := isConfined_walk W hW
  obtain ⟨hcl, hfr⟩ := frontier_insOf_subset hs hG hconf
  have hn := isGammaNice_insOf hS hs hG hconf
  have hUeq : G.U = {x | x ∈ W.support ∨ ∃ e ∈ W.edges, x ∈ closure e} := by
    ext x
    exact mem_walkDrawing_U Γ W
  have hsc : IsSimplyConnectedSet (insOf ins G) :=
    isSimplyConnected_insOf hS hs hG hconf (hUeq ▸ isPathConnected_walk_U W)
  have hne : (insOf ins G).Nonempty :=
    ⟨u, Or.inl ((mem_walkDrawing_U Γ W).mpr (Or.inl W.start_mem_support))⟩
  have hu : insOf ins G ≠ univ := by
    intro h
    obtain ⟨r, -, hr, -, -⟩ := theorem_8_2_proof hS hs W W W hW hW hW
    exact hr (subset_of_subset_of_eq (subset_univ r) h.symm)
  have hle : perimeterWalkLength Γ (insOf ins G) ≤ W.length := by
    rw [perimeterWalkLength_eq hS hcl hn hsc hne hu, length_eq_sum W]
    exact Finset.sum_le_sum fun e he => perimeterCount_le hS hs W hW
      (Γ.finite_edges.mem_toFinset.mp he)
  refine ⟨⟨hne, hcl, hsc, hn, hle.trans_lt hW, fun h => hu ?_⟩, hle⟩
  have hsub : (Γ.interSet (subBd (insOf ins G))).IsSubdrawing G := by
    rw [subBd_eq_frontier]
    exact interSet_isSubdrawing hG isClosed_frontier hfr
  refine eq_univ_of_forall fun x => ?_
  by_contra hx
  exact hx (insOf_mono hsub (h ⟨mem_univ x, hx⟩))

/-- **(8.6)** of Graph Minors XI (page 97): "If $X, Y$ are restraints, and $X \cup Y$ is
simply-connected and $l(X \cup Y) < 2\theta$,
then $X \cup Y$ is a restraint." -/
theorem theorem_8_6_proof (hs : IsSlope Γ k ins) {X Y : Set S} (hX : IsRestraint Γ ins k X)
    (hY : IsRestraint Γ ins k Y) (hsc : IsSimplyConnectedSet (X ∪ Y))
    (hl : perimeterWalkLength Γ (X ∪ Y) < k) : IsRestraint Γ ins k (X ∪ Y) := by
  have hc : IsClosed (X ∪ Y) := hX.isClosed.union hY.isClosed
  have hn : IsGammaNice Γ (X ∪ Y) := hX.isGammaNice.union hY.isGammaNice
  have hne : (X ∪ Y).Nonempty := hX.nonempty.mono subset_union_left
  have h₁ : X ∪ Y ∪ X ≠ univ := theorem_8_4_proof hS hs hX hY hX
  have hu : X ∪ Y ≠ univ := fun h => h₁ (by rw [h, univ_union])
  obtain ⟨u', W, hW, hlen, -, hcount⟩ := exists_minimal_perimeterWalk hS hc hn hsc hne hu
  have hd := walkDrawing_eq hS hc hn hW hcount
  have hZ := (theorem_8_5_proof hS hs W (hlen ▸ hl)).1
  have h₂ := theorem_8_4_proof hS hs hX hY hZ
  refine ⟨hne, hc, hsc, hn, hl, fun hsub => h₂ ?_⟩
  refine eq_univ_of_forall fun x => ?_
  by_cases hx : x ∈ X ∪ Y
  · exact Or.inl hx
  · refine Or.inr ?_
    have hmem := hsub ⟨mem_univ x, hx⟩
    rw [subBd_eq_frontier, ← hd] at hmem
    exact hmem

end GraphMinor.GM11

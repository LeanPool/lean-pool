/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Ties

/-!
# Graph Minors XI, (9.2)

`theorem_9_2` is (9.2) of the paper: any two atoms in a restraint `Y` lie together in a tie `X ⊆ Y`
with
`l(X) ≤ l(Y)`. The proof follows the paper. Each atom `a` gets a set `A ⊇ a`, which is a closed disc
`ins(C)` with `C` in `Γ ∩ bd(Y)`, or the closure of an edge used twice by the perimeter walk of `Y`,
or
a vertex of `bd(Y)`. We call the triple a *piece* (`IsPiece`), and `exists_piece` finds it. The
paper's
cases for two pieces `A` and `B` are then, in order: their interiors meet, they share at least two
points, they share one point, or they are disjoint.

Each tie is `ins(W)` for a closed walk `W` no longer than the perimeter walk of `Y`, so it is a
restraint by (8.5) (`tie_of_walk`). The count of the length is a count of how many times each edge
is
used, compared with `perimeterCount`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
  {Γ : Drawing S} {ins : Drawing S → Set S} {k : ℕ} {Y : Set S}

/-- `A` is the set that the proof of (9.2) attaches to an atom in `Y`, and `G` is the part of
`Γ ∩ bd(Y)` around it: the circuit bounding the disc `A`, or an edge with its two ends, or a vertex.
-/
structure IsPiece (Γ : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (Y A : Set S) (G : Drawing S) :
    Prop where
  sub : G.IsSubdrawing (Γ.interSet (frontier Y))
  subY : A ⊆ Y
  absorbing : IsAbsorbing Γ ins k A
  U_sub : G.U ⊆ A
  sub_ins : A ⊆ insOf ins G
  rest : A \ G.U ⊆ interior Y
  Vne : G.V.Nonempty
  walk : ∀ v ∈ G.V, ∃ Z : GraphWalk Γ.toGraph v v, walkDrawing Γ Z = G ∧
    ∀ e ∈ Γ.E, edgeCount Z.edges e ≤ perimeterCount Y e
  block : IsBlock G
  kind : (G.IsCircuit ∧ A = ins G) ∨
    (∃ (e : Set S) (u v : S), u ≠ v ∧ e ∈ Γ.E ∧ closure e ∩ Γ.V = {u, v} ∧ G.V = {u, v} ∧ G.E = {e}
      ∧
      A = closure e ∧ A ⊆ G.U) ∨
    (∃ v, G.V = {v} ∧ G.E = ∅ ∧ A = {v} ∧ G.U = {v})

omit [T2Space S] [ConnectedSpace S] in
theorem one_le_perimeterCount {e : Set S} (he : e ∈ Γ.E) (hf : e ⊆ frontier Y) : 1
  ≤ perimeterCount Y e := by
  classical
  obtain ⟨x, hx⟩ := he.1
  have hn : (e ∩ frontier Y).Nonempty := ⟨x, hx, hf hx⟩
  unfold perimeterCount
  simp only [hn, ite_true]
  split_ifs <;> omega

omit [TopologicalSpace S] [T2Space S] [ConnectedSpace S] in
theorem length_le_of_edgeCount {L L' : List (Set S)} (h : ∀ e, edgeCount L e ≤ edgeCount L' e) :
    L.length ≤ L'.length := by
  classical
  refine (List.subperm_ext_iff.mpr fun x _ => ?_).length_le
  have := h x
  unfold edgeCount at this
  convert this

omit [TopologicalSpace S] [T2Space S] [ConnectedSpace S] in
theorem edges_length {G : Graph S (Set S)} {a b : S} (W : GraphWalk G a b) :
    W.edges.length = W.length := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [ih]

omit [T2Space S] [ConnectedSpace S] in
/-- A point of two subdrawings of `Γ` is a vertex of both, or lies on an edge of both. -/
theorem U_inter_cases {G H : Drawing S} (hG : G.IsSubdrawing Γ) (hH : H.IsSubdrawing Γ) {x : S}
    (hxG : x ∈ G.U) (hxH : x ∈ H.U) : (x ∈ G.V ∧ x ∈ H.V) ∨ ∃ e ∈ G.E, e ∈ H.E ∧ x ∈ e := by
  have hc : ∀ {D : Drawing S}, x ∈ D.U → x ∈ D.V ∨ ∃ e ∈ D.E, x ∈ e := fun {D} hx => by
    by_cases h : x ∈ D.V
    · exact Or.inl h
    · obtain ⟨e, he, hxe⟩ := D.exists_edge_of_mem hx h
      exact Or.inr ⟨e, he, hxe⟩
  rcases hc hxG with h₁ | ⟨e, he, hxe⟩ <;> rcases hc hxH with h₂ | ⟨f, hf, hxf⟩
  · exact Or.inl ⟨h₁, h₂⟩
  · exact (edge_notMem_V (hH.2 hf) hxf (hG.1 h₁)).elim
  · exact (edge_notMem_V (hG.2 he) hxe (hH.1 h₂)).elim
  · obtain rfl : e = f := Γ.edge_eq_of_mem (hG.2 he) (hH.2 hf) hxe hxf
    exact Or.inr ⟨e, he, hf, hxe⟩

variable (hS : IsClosedSurface S)

include hS in
theorem insOf_frontier (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) :
    insOf ins (Γ.interSet (frontier Y)) = Y := by
  have := theorem_8_3_proof hS hs hY
  rwa [subBd_eq_frontier] at this

include hS in
/-- A circuit of `Γ ∩ bd(Y)` gives a piece. -/
theorem piece_of_circuit (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {C : Drawing S}
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing (Γ.interSet (frontier Y))) :
    IsPiece Γ ins k Y (ins C) C := by
  classical
  have hl := hY.isConfined hS C hC hCs
  have hCΓ : C.IsSubdrawing Γ := hCs.trans interSet_isSub
  obtain ⟨hfr, hU, -⟩ := ins_slope_facts hS hs hC hCΓ hl
  have hsubY : ins C ⊆ Y := by
    rw [← insOf_frontier hS hs hY]
    exact fun x hx => Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hx⟩)
  have hcl : IsClosed (ins C) := (hs.isClosedDisc C hC hCΓ hl).isCompact.isClosed
  refine ⟨hCs, hsubY, isAbsorbing_ins hs hC hCΓ hl, hU,
    fun x hx => Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, ⟨Subset.rfl, Subset.rfl⟩⟩, hx⟩), ?_, ?_, ?_,
    isBlock_of_isCircuit hC, Or.inl ⟨hC, rfl⟩⟩
  · rintro x ⟨hx, hxU⟩
    refine interior_mono hsubY ?_
    by_contra hxi
    exact hxU (hfr ▸ (⟨subset_closure hx, hxi⟩ : x ∈ closure (ins C) \ interior (ins C)))
  · obtain ⟨u, W, -, -, hV, -⟩ := hC
    exact ⟨u, by rw [hV]; exact W.start_mem_support⟩
  · intro v hv
    obtain ⟨W, hW, -, hV, hE⟩ := exists_walk_at hC hv
    obtain ⟨Z, hsu, hed⟩ := hCΓ.exists_walk_up W
    refine ⟨Z, Drawing.ext_of_V_E ?_ ?_, fun e he => ?_⟩
    · rw [walkDrawing_V, hV, hsu]
    · rw [walkDrawing_E, hE, hed]
    · by_cases hm : e ∈ Z.edges
      · have heC : e ∈ C.E := by
          rw [hE, ← hed]
          exact hm
        have hnd : Z.edges.Nodup := hed ▸ hW.2
        have h₁ : edgeCount Z.edges e = 1 := by
          unfold edgeCount
          convert List.count_eq_one_of_mem hnd hm
        rw [h₁]
        exact one_le_perimeterCount he (mem_interSet_E_iff.mp (hCs.2 heC)).2
      · rw [edgeCount_eq_zero hm]
        exact Nat.zero_le _

omit [ConnectedSpace S] in
/-- A vertex of `bd(Y)` gives a piece. -/
theorem piece_of_vertex (hY : IsRestraint Γ ins k Y) {v : S} (hv : v ∈ Γ.V) (hf : v ∈ frontier Y) :
    IsPiece Γ ins k Y {v} (walkDrawing Γ (GraphWalk.nil (G := Γ.toGraph) hv)) := by
  set G := walkDrawing Γ (GraphWalk.nil (G := Γ.toGraph) hv) with hG
  have hsu : (GraphWalk.nil (G := Γ.toGraph) hv).support = [v] := rfl
  have hed : (GraphWalk.nil (G := Γ.toGraph) hv).edges = [] := rfl
  have hV : G.V = {v} := by
    rw [hG, walkDrawing_V, hsu]
    ext x
    simp
  have hE : G.E = ∅ := by
    rw [hG, walkDrawing_E, hed]
    ext x
    simp
  have hU : G.U = {v} := by
    rw [Drawing.U_eq, hV, hE]
    simp
  have hvY : v ∈ Y := hY.isClosed.frontier_subset hf
  refine ⟨⟨fun x hx => ?_, fun e he => ?_⟩, singleton_subset_iff.mpr hvY, ?_, hU.subset,
    fun x hx => Or.inl (hU ▸ hx), ?_, ⟨v, by rw [hV]; rfl⟩, ?_, isBlock_of_subsingleton
      (by rw [hE]; simp),
    Or.inr (Or.inr ⟨v, hV, hE, rfl, hU⟩)⟩
  · rw [hV] at hx
    obtain rfl : x = v := hx
    exact mem_interSet_V hv hf
  · rw [hE] at he
    exact he.elim
  · exact IsArm.isAbsorbing (p := v) (Or.inl rfl)
  · rintro x ⟨hx, hxU⟩
    exact (hxU (hU ▸ hx)).elim
  · intro w hw
    rw [hV] at hw
    obtain rfl : w = v := hw
    refine ⟨GraphWalk.nil hv, rfl, fun e _ => ?_⟩
    have : edgeCount (GraphWalk.nil (G := Γ.toGraph) hv).edges e = 0 :=
      edgeCount_eq_zero (by rw [hed]; simp)
    omega

omit [ConnectedSpace S] in
/-- An edge of `bd(Y)` that the perimeter walk of `Y` uses twice, with two ends, gives a piece. -/
theorem piece_of_edge (hY : IsRestraint Γ ins k Y) {e : Set S} (he : e ∈ Γ.E) {u v : S}
  (huv : u ≠ v)
    (hcap : closure e ∩ Γ.V = {u, v}) (hf : e ⊆ frontier Y) (hc : 2 ≤ perimeterCount Y e) :
    ∃ G, IsPiece Γ ins k Y (closure e) G := by
  classical
  have hl : Γ.toGraph.IsLink e u v := by
    have hu : u ∈ closure e ∩ Γ.V := by rw [hcap]; simp
    have hv : v ∈ closure e ∩ Γ.V := by rw [hcap]; simp
    exact ⟨he, hu.2, hv.2, hcap⟩
  have hl' : Γ.toGraph.IsLink e v u := hl.symm
  have hclf : closure e ⊆ frontier Y := closure_minimal hf isClosed_frontier
  let Zu : GraphWalk Γ.toGraph u u := .cons hl (.cons hl' (.nil hl.2.1))
  let Zv : GraphWalk Γ.toGraph v v := .cons hl' (.cons hl (.nil hl.2.2.1))
  have hsu : Zu.support = [u, v, u] := rfl
  have hed : Zu.edges = [e, e] := rfl
  have hsv : Zv.support = [v, u, v] := rfl
  have hedv : Zv.edges = [e, e] := rfl
  set G := walkDrawing Γ Zu with hG
  have hV : G.V = {u, v} := by
    rw [hG, walkDrawing_V, hsu]
    ext x
    change x ∈ [u, v, u] ↔ x ∈ ({u, v} : Set S)
    simp only [List.mem_cons, List.not_mem_nil, or_false, mem_insert_iff, mem_singleton_iff]
    tauto
  have hE : G.E = {e} := by
    rw [hG, walkDrawing_E, hed]
    ext x
    simp
  have hU : G.U = closure e := by
    ext x
    rw [hG, mem_walkDrawing_U]
    constructor
    · rintro (h | ⟨f, hf, hx⟩)
      · have hu : u ∈ closure e ∩ Γ.V := by rw [hcap]; simp
        have hv : v ∈ closure e ∩ Γ.V := by rw [hcap]; simp
        rw [hsu] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact hu.1
        · exact hv.1
        · exact hu.1
      · obtain rfl : f = e := by
          rw [hed] at hf
          simpa using hf
        exact hx
    · exact fun hx => Or.inr ⟨e, by rw [hed]; simp, hx⟩
  have hYc := hY.isClosed
  have hcountZ : ∀ {w : S} (Z : GraphWalk Γ.toGraph w w), Z.edges = [e, e] → ∀ f ∈ Γ.E,
      edgeCount Z.edges f ≤ perimeterCount Y f := by
    intro w Z hZ f _
    rw [hZ]
    by_cases hfe : f = e
    · subst hfe
      have : edgeCount [f, f] f = 2 := by simp [edgeCount]
      omega
    · have : edgeCount [e, e] f = 0 := edgeCount_eq_zero (by simpa using hfe)
      omega
  have hLu : IsLineWithEnds (closure e) u v := isLine_closure he huv hcap
  have hArm : ∀ {w}, w ∈ G.V → IsArm (closure e) w := by
    intro w hw
    rw [hV] at hw
    rcases hw with rfl | hw
    · exact Or.inr ⟨v, hLu⟩
    · obtain rfl : w = v := hw
      exact Or.inr ⟨u, IsLineWithEnds.symm hLu⟩
  refine ⟨G, ⟨fun x hx => ?_, fun f hf => ?_⟩, hclf.trans hYc.frontier_subset, ?_, hU.subset,
    fun x hx => Or.inl (hU ▸ hx), ?_, ⟨u, by rw [hV]; simp⟩, ?_,
    isBlock_of_subsingleton (by rw [hE]; simp), Or.inr (Or.inl ⟨e, u, v, huv, he, hcap, hV, hE,
      rfl, hU.superset⟩)⟩
  · have hm : x ∈ closure e ∩ Γ.V := by
      rw [hcap]
      rwa [hV] at hx
    exact mem_interSet_V hm.2 (hclf hm.1)
  · rw [hE] at hf
    obtain rfl : f = e := hf
    exact mem_interSet_E_iff.mpr ⟨he, hclf.trans' subset_closure⟩
  · exact IsArm.isAbsorbing (hArm (by rw [hV]; simp : u ∈ G.V))
  · rintro x ⟨hx, hxU⟩
    exact (hxU (hU ▸ hx)).elim
  · intro w hw
    rw [hV] at hw
    rcases hw with rfl | hw
    · exact ⟨Zu, rfl, hcountZ Zu rfl⟩
    · obtain rfl : w = v := hw
      refine ⟨Zv, Drawing.ext_of_V_E ?_ ?_, hcountZ Zv rfl⟩
      · rw [walkDrawing_V, hV, hsv]
        ext x
        change x ∈ [w, u, w] ↔ x ∈ ({u, w} : Set S)
        simp only [List.mem_cons, List.not_mem_nil, or_false, mem_insert_iff, mem_singleton_iff]
        tauto
      · rw [walkDrawing_E, hE, hedv]
        ext x
        simp


include hS in
/-- **The set attached to an atom.** The first paragraph of the proof of (9.2). -/
theorem exists_piece (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {a : Set S} (ha : a ∈ Γ.A)
    (haY : a ⊆ Y) : ∃ A G, IsPiece Γ ins k Y A G ∧ a ⊆ A := by
  classical
  have hconf := hY.isConfined hS
  by_cases hcirc : ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing (Γ.interSet (frontier Y)) ∧
      (a ∩ ins C).Nonempty
  · obtain ⟨C, hC, hCs, hne⟩ := hcirc
    have hCΓ : C.IsSubdrawing Γ := hCs.trans interSet_isSub
    obtain ⟨-, -, hnice⟩ := ins_slope_facts hS hs hC hCΓ (hconf C hC hCs)
    exact ⟨ins C, C, piece_of_circuit hS hs hY hC hCs, nice_atom hnice ha hne⟩
  push Not at hcirc
  have hoff : ∀ x ∈ a, x ∈ (Γ.interSet (frontier Y)).U := by
    intro x hx
    have hxY := haY hx
    rw [← insOf_frontier hS hs hY] at hxY
    rcases hxY with h | h
    · exact h
    · obtain ⟨C, ⟨hC, hCs⟩, hxC⟩ := mem_iUnion₂.mp h
      have := hcirc C hC hCs
      exact (this.subset ⟨hx, hxC⟩).elim
  have hUfr : (Γ.interSet (frontier Y)).U ⊆ frontier Y := interSet_U_subset isClosed_frontier
  have hUΓ : (Γ.interSet (frontier Y)).U ⊆ Γ.U := (interSet_isSub (Γ := Γ)).U_subset
  rcases ha with (⟨v, hv, rfl⟩ | he) | hr
  · have hvf := hUfr (hoff v rfl)
    exact ⟨{v}, _, piece_of_vertex hY hv hvf, Subset.rfl⟩
  · obtain ⟨x, hx⟩ := he.1
    have hxf := hUfr (hoff x hx)
    have hef : a ⊆ frontier Y := edge_subset_frontier hS hY.isClosed hY.isGammaNice he hx hxf
    have hclf : closure a ⊆ frontier Y := closure_minimal hef isClosed_frontier
    obtain ⟨u, v, hl⟩ := (Γ.toGraph.edge_mem_iff_exists_isLink a).mp he
    by_cases huv : u = v
    · subst huv
      -- A loop of `bd(Y)` is a circuit, and then the first case applies.
      let W : GraphWalk Γ.toGraph u u := .cons hl (.nil hl.2.1)
      have hWsu : W.support = [u, u] := rfl
      have hWed : W.edges = [a] := rfl
      have hWc : (walkDrawing Γ W).IsCircuit := isCircuit_walkDrawing Γ
        (W := W) ⟨by rw [hWsu]; simp, by rw [hWed]; simp⟩ (by simp [W])
      have hWs : (walkDrawing Γ W).IsSubdrawing (Γ.interSet (frontier Y)) := by
        refine ⟨fun y hy => ?_, fun f hf => ?_⟩
        · rw [walkDrawing_V] at hy
          obtain rfl : y = u := by
            rw [hWsu] at hy
            simpa using hy
          have hu : y ∈ closure a ∩ Γ.V := by rw [hl.2.2.2]; simp
          exact mem_interSet_V hu.2 (hclf hu.1)
        · rw [walkDrawing_E] at hf
          obtain rfl : f = a := by
            rw [hWed] at hf
            simpa using hf
          exact mem_interSet_E_iff.mpr ⟨he, hef⟩
      obtain ⟨-, hUi, -⟩ := ins_slope_facts hS hs hWc (hWs.trans interSet_isSub) (hconf _ hWc hWs)
      have hxU : x ∈ (walkDrawing Γ W).U :=
        (mem_walkDrawing_U Γ W).mpr (Or.inr ⟨a, by rw [hWed]; simp, subset_closure hx⟩)
      exact ((hcirc _ hWc hWs).subset ⟨hx, hUi hxU⟩).elim
    · -- Each side of the edge lies outside `Y`, so the perimeter walk uses it twice.
      obtain ⟨O, A₁, A₂, hO, hxO, hOe, hcov, c₁, c₂, d₁, d₂, h₁, h₂⟩ :=
        exists_edge_sides hS Γ he hx
      have hside : ∀ {B : Set S}, IsPreconnected B → Disjoint B Γ.U → a ∩ O ⊆ closure B → ¬ B ⊆ Y
        := by
        intro B hB hd hcl hsub
        obtain ⟨z, -, hzB⟩ := mem_closure_iff.mp (hcl ⟨hx, hxO⟩) univ isOpen_univ (mem_univ _)
        have hzY := hsub hzB
        rw [← insOf_frontier hS hs hY] at hzY
        rcases hzY with h | h
        · exact disjoint_left.mp hd hzB (hUΓ h)
        · obtain ⟨C, ⟨hC, hCs⟩, hzC⟩ := mem_iUnion₂.mp h
          have hCΓ : C.IsSubdrawing Γ := hCs.trans interSet_isSub
          have hl' := hconf C hC hCs
          obtain ⟨-, -, hnice⟩ := ins_slope_facts hS hs hC hCΓ hl'
          have hBC : B ⊆ ins C := side_subset hnice hB hd ⟨z, hzB, hzC⟩
          have hcl' : IsClosed (ins C) := (hs.isClosedDisc C hC hCΓ hl').isCompact.isClosed
          exact (hcirc C hC hCs).subset ⟨hx, closure_minimal hBC hcl' (hcl ⟨hx, hxO⟩)⟩
      have hcount := perimeterCount_eq hS hY.isClosed hY.isGammaNice he hx hO hxO hOe hcov c₁ c₂ d₁
        d₂ h₁ h₂
      have hn₁ := hside c₁ d₁ h₁
      have hn₂ := hside c₂ d₂ h₂
      have haY' : a ⊆ Y := haY
      simp only [haY', hn₁, hn₂, ite_true, ite_false] at hcount
      obtain ⟨G, hG⟩ := piece_of_edge hY he huv hl.2.2.2 hef (by omega)
      exact ⟨closure a, G, hG, subset_closure⟩
  · obtain ⟨x, hx⟩ := region_nonempty hr
    exact (region_subset hr hx (hUΓ (hoff x hx))).elim

/-- Two parts `G`, `H` of `Γ ∩ bd(Y)` are joined inside the budget of `Y`: there are closed walks
around them, and a walk `Q`
between them, with `|Z₁| + |Z₂| + 2|Q| ≤ l(Y)`. -/
def IsPieceLink (Γ : Drawing S) (Y : Set S) (G H : Drawing S) : Prop :=
  ∃ (a b : S) (Q : GraphWalk Γ.toGraph a b) (Z₁ : GraphWalk Γ.toGraph a a)
    (Z₂ : GraphWalk Γ.toGraph b b), a ∈ G.V ∧ b ∈ H.V ∧
    walkDrawing Γ Z₁ = G ∧ walkDrawing Γ Z₂ = H ∧ Z₁.length + Z₂.length + 2 * Q.length
      ≤ perimeterWalkLength Γ Y

include hS in
/-- A set `X ⊆ Y` of the shape of a tie is a tie, if it is `ins(Z)` for a closed walk `Z` no longer
than the perimeter walk of `Y`. -/
theorem tie_of_walk (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {X : Set S} {u : S}
    (Z : GraphWalk Γ.toGraph u u) (hlen : Z.length ≤ perimeterWalkLength Γ Y)
    (hU : (walkDrawing Γ Z).U ⊆ X) (hab : IsAbsorbing Γ ins k X) (hsup : X ⊆ insWalk ins Γ Z)
    (hsh : IsTieShape X) (hXY : X ⊆ Y) :
    IsTie Γ ins k X ∧ X ⊆ Y ∧ perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y := by
  have hk : Z.length < k := hlen.trans_lt hY.length_lt
  have heq : insWalk ins Γ Z = X := Subset.antisymm (insWalk_subset Z hk hab hU) hsup
  have h := theorem_8_5_proof hS hs Z hk
  rw [heq] at h
  exact ⟨⟨h.1, hsh⟩, hXY, h.2.trans hlen⟩

include hS in
/-- The length of a closed walk that uses each edge at most `perimeterCount Y e` times. -/
theorem length_le_of_count (hY : IsRestraint Γ ins k Y) {L : List (Set S)} (hLE : ∀ e ∈ L, e ∈ Γ.E)
    (hL : ∀ e ∈ Γ.E, edgeCount L e ≤ perimeterCount Y e) : L.length ≤ perimeterWalkLength Γ Y := by
  obtain ⟨u, W, -, hlen, -, hcnt, -⟩ := hY.exists_walk hS
  rw [← hlen]
  have : L.length ≤ W.edges.length := length_le_of_edgeCount fun e => by
    by_cases he : e ∈ Γ.E
    · rw [hcnt e he]
      exact hL e he
    · rw [edgeCount_eq_zero fun h => he (hLE e h)]
      exact Nat.zero_le _
  rwa [edges_length] at this

include hS in
/-- A piece that is not a disc is an arm at each of its vertices. -/
theorem IsPiece.shape (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {A : Set S} {G : Drawing
  S}
    (hP : IsPiece Γ ins k Y A G) : IsClosedDisc A ∨ ∀ v ∈ G.V, IsArm A v := by
  rcases hP.kind with ⟨hC, rfl⟩ | ⟨e, u, v, huv, he, hcap, hV, -, rfl, -⟩ | ⟨v, hV, -, rfl, -⟩
  · have hGs : G.IsSubdrawing Γ := hP.sub.trans interSet_isSub
    exact Or.inl (hs.isClosedDisc G hC hGs (hY.isConfined hS G hC hP.sub))
  · refine Or.inr fun w hw => ?_
    have hL : IsLineWithEnds (closure e) u v := isLine_closure he huv hcap
    rw [hV] at hw
    rcases hw with rfl | hw
    · exact Or.inr ⟨v, hL⟩
    · obtain rfl : w = v := hw
      exact Or.inr ⟨u, IsLineWithEnds.symm hL⟩
  · refine Or.inr fun w hw => ?_
    rw [hV] at hw
    obtain rfl : w = v := hw
    exact Or.inl rfl

include hS in
/-- A piece alone is a tie. -/
theorem tie_of_piece (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {A : Set S} {G : Drawing S}
    (hP : IsPiece Γ ins k Y A G) :
    IsTie Γ ins k A ∧ A ⊆ Y ∧ perimeterWalkLength Γ A ≤ perimeterWalkLength Γ Y := by
  obtain ⟨v, hv⟩ := hP.Vne
  obtain ⟨Z, hZ, hcnt⟩ := hP.walk v hv
  have hlen : Z.length ≤ perimeterWalkLength Γ Y := by
    have := length_le_of_count hS hY (fun e he => mem_E_of_mem_edges Z he) hcnt
    rwa [edges_length] at this
  have hsh : IsTieShape A := by
    rcases hP.shape hS hs hY with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact (h v hv).isTieShape
  refine tie_of_walk hS hs hY Z hlen (hZ ▸ hP.U_sub) hP.absorbing ?_ hsh hP.subY
  rw [insWalk, hZ]
  exact hP.sub_ins

omit [TopologicalSpace S] [T2Space S] [ConnectedSpace S] in
private theorem pair_eq {u v x y : S} (hx : x ∈ ({u, v} : Set S)) (hy : y ∈ ({u, v} : Set S))
    (hxy : x ≠ y) : ({u, v} : Set S) = {x, y} := by
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact (hxy rfl).elim
  · rw [mem_singleton_iff.mp hy]
  · rw [mem_singleton_iff.mp hx, pair_comm]
  · exact (hxy ((mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm)).elim

omit [T2Space S] [ConnectedSpace S] in
/-- A vertex of `Γ` on a subdrawing is a vertex of the subdrawing. -/
theorem mem_V_of_mem_U {G : Drawing S} (hG : G.IsSubdrawing Γ) {x : S} (hx : x ∈ G.U)
  (hV : x ∈ Γ.V) :
    x ∈ G.V := by
  by_contra h
  obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hx h
  exact edge_notMem_V (hG.2 he) hxe hV

omit [T2Space S] [ConnectedSpace S] in
/-- A simple walk that meets `T` only in `c` has no edge whose closure lies in `T`. -/
theorem edge_off {a b c : S} {S' : GraphWalk Γ.toGraph a b} (hS' : S'.IsSimple) {T : Set S}
    (h : ∀ x ∈ S'.support, x ∈ T → x = c) {e : Set S} (he : e ∈ S'.edges)
      (hT : closure e ⊆ T) : False := by
  obtain ⟨x, y, W₁, hl, W₂, hW⟩ := exists_split_edge S' he
  have hx : x ∈ S'.support := by
    rw [hW]
    exact (GraphWalk.mem_support_append _ _).mpr (Or.inl W₁.end_mem_support)
  have hy : y ∈ S'.support := by
    rw [hW]
    exact (GraphWalk.mem_support_append _ _).mpr (Or.inr (by simp [W₂.start_mem_support]))
  have hxe : x ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; simp
  have hye : y ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; simp
  have hxy : x = y := (h x hx (hT hxe.1)).trans (h y hy (hT hye.1)).symm
  have hnd : (W₁.append (.cons hl W₂)).support.Nodup := hW ▸ hS'
  rw [GraphWalk.support_append] at hnd
  exact (List.nodup_append.mp hnd).2.2 x W₁.end_mem_support y W₂.start_mem_support hxy

omit [ConnectedSpace S] in
/-- A vertex of a piece that holds two points lies on an edge of the piece. -/
theorem IsPiece.vertex_on_edge {A : Set S} {G : Drawing S} (hP : IsPiece Γ ins k Y A G) {x y : S}
    (hxy : x ≠ y) (hx : x ∈ G.U) (hy : y ∈ G.U) {v : S} (hv : v ∈ G.V) : ∃ e ∈ G.E, v ∈ closure e
      := by
  rcases hP.kind with ⟨hC, -⟩ | ⟨e, u, w, -, -, hcap, hV, hE, -, -⟩ | ⟨w, -, -, -, hU⟩
  · obtain ⟨W, -, hpos, -, hE⟩ := exists_walk_at hC hv
    cases W with
    | nil _ => simp at hpos
    | @cons _ w _ e hl r =>
      refine ⟨e, by rw [hE]; simp, ?_⟩
      have : v ∈ closure e ∩ G.V := by rw [hl.2.2.2]; simp
      exact this.1
  · refine ⟨e, by rw [hE]; rfl, ?_⟩
    have hvΓ : v ∈ closure e ∩ Γ.V := by
      rw [hcap, ← hV]
      exact hv
    exact hvΓ.1
  · rw [hU] at hx hy
    exact (hxy (hx.trans hy.symm)).elim

include hS in
/-- The interiors of two pieces: if they meet, the first piece lies in the second. -/
private theorem star_subset (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {A B : Set S}
    {G H : Drawing S} (hP : IsPiece Γ ins k Y A G) (hQ : IsPiece Γ ins k Y B H) {x : S}
      (hxA : x ∈ A)
    (hxG : x ∉ G.U) (hxB : x ∈ B) (hxH : x ∉ H.U) : A ⊆ B := by
  have hconf := hY.isConfined hS
  have hdisc : ∀ {A : Set S} {G : Drawing S}, IsPiece Γ ins k Y A G → (∃ x ∈ A, x ∉ G.U) →
      IsClosedDisc A ∧ frontier A = G.U ∧ discBd A = G.U := by
    intro A G hP ⟨x, hxA, hxG⟩
    rcases hP.kind with ⟨hC, rfl⟩ | ⟨-, -, -, -, -, -, -, -, -, hU⟩ | ⟨v, -, -, rfl, hU⟩
    · have hGs : G.IsSubdrawing Γ := hP.sub.trans interSet_isSub
      have hl := hconf G hC hP.sub
      have hD := hs.isClosedDisc G hC hGs hl
      obtain ⟨hfr, -, -⟩ := ins_slope_facts hS hs hC hGs hl
      exact ⟨hD, hfr, by rw [← IsClosedDisc.frontier_eq_discBd hS hD, hfr]⟩
    · exact (hxG (hU hxA)).elim
    · exact (hxG (hU ▸ hxA)).elim
  obtain ⟨hdA, -, hbA⟩ := hdisc hP ⟨x, hxA, hxG⟩
  obtain ⟨hdB, hfB, -⟩ := hdisc hQ ⟨x, hxB, hxH⟩
  have hBc : IsClosed B := hdB.isCompact.isClosed
  have hstar : IsPreconnected (A \ discBd A) :=
    (isPathConnected_disc_sdiff hdA inter_subset_left).isConnected.isPreconnected
  have hsplit : ∀ {y}, y ∉ frontier B → y ∈ interior B ∪ Bᶜ := fun {y} hy => by
    by_cases hyB : y ∈ B
    · refine Or.inl ?_
      by_contra hi
      exact hy ⟨subset_closure hyB, hi⟩
    · exact Or.inr hyB
  have hmem : A \ discBd A ⊆ interior B := by
    refine hstar.subset_left_of_subset_union isOpen_interior hBc.isOpen_compl
      (disjoint_left.mpr fun y h₁ h₂ => h₂ (interior_subset h₁)) (fun y hy => hsplit ?_) ?_
    · intro hy'
      rw [hfB] at hy'
      have h₁ : y ∈ interior Y := hP.rest ⟨hy.1, by rw [← hbA]; exact hy.2⟩
      have h₂ : y ∈ frontier Y := interSet_U_subset isClosed_frontier (hQ.sub.U_subset hy')
      exact h₂.2 h₁
    · refine ⟨x, ⟨hxA, by rw [hbA]; exact hxG⟩, ?_⟩
      by_contra hi
      exact hxH (hfB ▸ (⟨subset_closure hxB, hi⟩ : x ∈ frontier B))
  intro y hy
  by_cases hyb : y ∈ discBd A
  · exact closure_minimal (hmem.trans interior_subset) hBc (discBd_subset_closure hdA hyb)
  · exact interior_subset (hmem ⟨hy, hyb⟩)

include hS in
/-- The case of (9.2) with two pieces that share at least two points. -/
theorem piece_of_two_points (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {A B : Set S}
    {G H : Drawing S} (hP : IsPiece Γ ins k Y A G) (hQ : IsPiece Γ ins k Y B H) {x y : S}
      (hxy : x ≠ y)
    (hxG : x ∈ G.U) (hxH : x ∈ H.U) (hyG : y ∈ G.U) (hyH : y ∈ H.U) :
    ∃ X K, IsPiece Γ ins k Y X K ∧ A ⊆ X ∧ B ⊆ X := by
  classical
  have hGΓ : G.IsSubdrawing Γ := hP.sub.trans interSet_isSub
  have hHΓ : H.IsSubdrawing Γ := hQ.sub.trans interSet_isSub
  obtain ⟨v₀, hv₁, hv₂⟩ : ∃ v, v ∈ G.V ∧ v ∈ H.V := by
    rcases U_inter_cases hGΓ hHΓ hxG hxH with h | ⟨e, he₁, he₂, -⟩
    · exact ⟨x, h⟩
    · obtain ⟨p, q, hl⟩ := (G.toGraph.edge_mem_iff_exists_isLink e).mp he₁
      have hp : p ∈ closure e ∩ G.V := by rw [hl.2.2.2]; simp
      refine ⟨p, hp.2, ?_⟩
      have : p ∈ closure e ∩ H.V := by
        rw [hHΓ.closure_inter_V he₂]
        exact ⟨hp.1, hGΓ.1 hp.2⟩
      exact this.2
  obtain ⟨Z₁, hZ₁, -⟩ := hP.walk v₀ hv₁
  obtain ⟨Z₂, hZ₂, -⟩ := hQ.walk v₀ hv₂
  have hed : ∀ {K : Drawing S} {A' : Set S} (Z : GraphWalk Γ.toGraph v₀ v₀), IsPiece Γ ins k Y A' K
    →
      walkDrawing Γ Z = K → x ∈ K.U → y ∈ K.U → ∀ z ∈ Z.support, ∃ e ∈ Z.edges, z ∈ closure e := by
    intro K A' Z hR hZ hx hy z hz
    have hzV : z ∈ K.V := by
      rw [← hZ, walkDrawing_V]
      exact hz
    obtain ⟨e, he, hze⟩ := hR.vertex_on_edge hxy hx hy hzV
    rw [← hZ, walkDrawing_E] at he
    exact ⟨e, he, hze⟩
  have hns := isNonSeparable_walk Z₁ Z₂ (hZ₁ ▸ hP.block) (hZ₂ ▸ hQ.block) (hed Z₁ hP hZ₁ hxG hyG)
    (hed Z₂ hQ hZ₂ hxH hyH) hxy (hZ₁ ▸ hxG) (hZ₂ ▸ hxH) (hZ₁ ▸ hyG) (hZ₂ ▸ hyH)
  set D := walkDrawing Γ (Z₁.append Z₂) with hD
  have hs₁ : G.IsSubdrawing D := hZ₁ ▸ walkDrawing_mono
    (fun z h => (GraphWalk.mem_support_append _ _).mpr (Or.inl h))
    (fun e h => by rw [GraphWalk.edges_append]; exact List.mem_append.mpr (Or.inl h))
  have hs₂ : H.IsSubdrawing D := hZ₂ ▸ walkDrawing_mono
    (fun z h => (GraphWalk.mem_support_append _ _).mpr (Or.inr h))
    (fun e h => by rw [GraphWalk.edges_append]; exact List.mem_append.mpr (Or.inr h))
  have hDsub : D.IsSubdrawing (Γ.interSet (frontier Y)) := by
    refine ⟨fun z hz => ?_, fun e he => ?_⟩
    · rw [hD, walkDrawing_V] at hz
      rcases (GraphWalk.mem_support_append _ _).mp hz with h | h
      · exact hP.sub.1 (by rw [← hZ₁, walkDrawing_V]; exact h)
      · exact hQ.sub.1 (by rw [← hZ₂, walkDrawing_V]; exact h)
    · rw [hD, walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append] at he
      rcases he with h | h
      · exact hP.sub.2 (by rw [← hZ₁, walkDrawing_E]; exact h)
      · exact hQ.sub.2 (by rw [← hZ₂, walkDrawing_E]; exact h)
  have hDΓ : D.IsSubdrawing Γ := hDsub.trans interSet_isSub
  have hconf := hY.isConfined hS
  have hconfD : IsConfined k D := fun C hC hCs => hconf C hC (hCs.trans hDsub)
  by_cases hc : ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing D
  · obtain ⟨C₁, hC₁, hC₁s⟩ := hc
    obtain ⟨m, hm⟩ := ((finite_circuits D).image ins).exists_maximal ⟨ins C₁, C₁, ⟨hC₁, hC₁s⟩, rfl⟩
    obtain ⟨C, ⟨hC, hCs⟩, rfl⟩ := hm.1
    have heq := theorem_4_3_iii hs hDΓ hconfD hC hCs
      (fun C' h₁ h₂ h₃ => hm.2 ⟨C', ⟨h₁, h₂⟩, rfl⟩ h₃) hns
    exact ⟨ins C, C, piece_of_circuit hS hs hY hC (hCs.trans hDsub),
      heq ▸ hP.sub_ins.trans (insOf_mono hs₁), heq ▸ hQ.sub_ins.trans (insOf_mono hs₂)⟩
  push Not at hc
  have hkind : ∀ {A' : Set S} {K : Drawing S}, IsPiece Γ ins k Y A' K → K.IsSubdrawing D → x ∈ K.U →
      y ∈ K.U → ∃ (e : Set S) (u v : S), e ∈ Γ.E ∧ closure e ∩ Γ.V = {u, v} ∧ K.V = {u, v} ∧
        K.E = {e} ∧ A' = closure e := by
    intro A' K hR hKs hx hy
    rcases hR.kind with ⟨hC, -⟩ | ⟨e, u, v, -, he, hcap, hV, hE, hA', -⟩ | ⟨w, -, -, -, hU⟩
    · exact (hc K hC hKs).elim
    · exact ⟨e, u, v, he, hcap, hV, hE, hA'⟩
    · rw [hU] at hx hy
      exact (hxy (hx.trans hy.symm)).elim
  obtain ⟨e, u₁, v₁, he, hcap₁, hV₁, hE₁, rfl⟩ := hkind hP hs₁ hxG hyG
  obtain ⟨f, u₂, v₂, hf, hcap₂, hV₂, hE₂, rfl⟩ := hkind hQ hs₂ hxH hyH
  by_cases hef : e = f
  · subst hef
    exact ⟨closure e, G, hP, Subset.rfl, Subset.rfl⟩
  have hv : ∀ {z}, z ∈ G.U → z ∈ H.U → z ∈ G.V ∧ z ∈ H.V := fun {z} h₁ h₂ => by
    rcases U_inter_cases hGΓ hHΓ h₁ h₂ with h | ⟨g, hg₁, hg₂, -⟩
    · exact h
    · rw [hE₁] at hg₁
      rw [hE₂] at hg₂
      exact (hef ((mem_singleton_iff.mp hg₁).symm.trans (mem_singleton_iff.mp hg₂))).elim
  have hx' := hv hxG hxH
  have hy' := hv hyG hyH
  have hcap₁' : closure e ∩ Γ.V = {x, y} :=
    hcap₁.trans (pair_eq (hV₁ ▸ hx'.1) (hV₁ ▸ hy'.1) hxy)
  have hcap₂' : closure f ∩ Γ.V = {y, x} :=
    hcap₂.trans (pair_eq (hV₂ ▸ hy'.2) (hV₂ ▸ hx'.2) hxy.symm)
  have hl₁ : Γ.toGraph.IsLink e x y := ⟨he, hGΓ.1 hx'.1, hGΓ.1 hy'.1, hcap₁'⟩
  have hl₂ : Γ.toGraph.IsLink f y x := ⟨hf, hGΓ.1 hy'.1, hGΓ.1 hx'.1, hcap₂'⟩
  let W : GraphWalk Γ.toGraph x x := .cons hl₁ (.cons hl₂ (.nil hl₂.2.2.1))
  have hsu : W.support = [x, y, x] := rfl
  have hed' : W.edges = [e, f] := rfl
  have hWc : (walkDrawing Γ W).IsCircuit := isCircuit_walkDrawing Γ (W := W)
    ⟨by rw [hsu]; simpa using hxy.symm, by rw [hed']; simpa using hef⟩ (by simp [W])
  refine (hc _ hWc ⟨fun z hz => ?_, fun g hg => ?_⟩).elim
  · rw [walkDrawing_V, hsu] at hz
    have hz' : z = x ∨ z = y ∨ z = x := by simpa using hz
    rcases hz' with rfl | rfl | rfl
    · exact hs₁.1 hx'.1
    · exact hs₁.1 hy'.1
    · exact hs₁.1 hx'.1
  · rw [walkDrawing_E, hed'] at hg
    have hg' : g = e ∨ g = f := by simpa using hg
    rcases hg' with rfl | rfl
    · exact hs₁.2 (by rw [hE₁]; rfl)
    · exact hs₂.2 (by rw [hE₂]; rfl)

include hS in
/-- The case of (9.2) with two pieces that share exactly one point. -/
private theorem tie_of_one_point (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {A B : Set S}
    {G H : Drawing S} (hP : IsPiece Γ ins k Y A G) (hQ : IsPiece Γ ins k Y B H) {p : S}
    (hpG : p ∈ G.V) (hpH : p ∈ H.V) (hAB : A ∩ B = {p}) (hdis : ∀ e ∈ G.E, e ∉ H.E) :
    (∃ X, (IsTie Γ ins k X ∧ X ⊆ Y ∧ perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y) ∧ A ⊆ X
      ∧ B ⊆ X) ∧
      IsPieceLink Γ Y G H := by
  classical
  obtain ⟨Z₁, hZ₁, hc₁⟩ := hP.walk p hpG
  obtain ⟨Z₂, hZ₂, hc₂⟩ := hQ.walk p hpH
  have hEZ₁ : ∀ e, e ∈ Z₁.edges ↔ e ∈ G.E := fun e => by rw [← hZ₁, walkDrawing_E]; rfl
  have hEZ₂ : ∀ e, e ∈ Z₂.edges ↔ e ∈ H.E := fun e => by rw [← hZ₂, walkDrawing_E]; rfl
  have hlen : (Z₁.append Z₂).length ≤ perimeterWalkLength Γ Y := by
    rw [← edges_length]
    refine length_le_of_count hS hY (fun e he => mem_E_of_mem_edges _ he) fun e he => ?_
    rw [GraphWalk.edges_append]
    have hadd : edgeCount (Z₁.edges ++ Z₂.edges) e = edgeCount Z₁.edges e + edgeCount Z₂.edges e
      := by
      simp [edgeCount, List.count_append]
    rw [hadd]
    by_cases h : e ∈ Z₂.edges
    · rw [edgeCount_eq_zero fun h' => hdis e ((hEZ₁ e).mp h') ((hEZ₂ e).mp h)]
      simpa using hc₂ e he
    · rw [edgeCount_eq_zero h]
      simpa using hc₁ e he
  have hs₁ : G.IsSubdrawing (walkDrawing Γ (Z₁.append Z₂)) := hZ₁ ▸ walkDrawing_mono
    (fun z h => (GraphWalk.mem_support_append _ _).mpr (Or.inl h))
    (fun e h => by rw [GraphWalk.edges_append]; exact List.mem_append.mpr (Or.inl h))
  have hs₂ : H.IsSubdrawing (walkDrawing Γ (Z₁.append Z₂)) := hZ₂ ▸ walkDrawing_mono
    (fun z h => (GraphWalk.mem_support_append _ _).mpr (Or.inr h))
    (fun e h => by rw [GraphWalk.edges_append]; exact List.mem_append.mpr (Or.inr h))
  have hsh : IsTieShape (A ∪ B) := by
    rcases hP.shape hS hs hY with hd₁ | ha₁ <;> rcases hQ.shape hS hs hY with hd₂ | ha₂
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨A, B, hd₁, hd₂, ?_, ?_, rfl⟩)))
      · rw [hAB]
        simp
      · rw [hAB]
        exact finite_singleton p
    · exact (ha₂ p hpH).isTieShape_disc hd₁ hAB
    · rw [union_comm]
      exact (ha₁ p hpG).isTieShape_disc hd₂ (by rw [inter_comm, hAB])
    · exact (ha₁ p hpG).isTieShape_union (ha₂ p hpH) hAB
  refine ⟨⟨A ∪ B, tie_of_walk hS hs hY (Z₁.append Z₂) hlen ?_
    (hP.absorbing.union hQ.absorbing hAB.subset) ?_ hsh (union_subset hP.subY hQ.subY),
    subset_union_left, subset_union_right⟩, p, p, .nil ((hP.sub.trans interSet_isSub).1 hpG), Z₁,
      Z₂, hpG, hpH, hZ₁, hZ₂, ?_⟩
  · intro z hz
    rcases mem_U_append.mp hz with h | h
    · exact Or.inl (hP.U_sub (hZ₁ ▸ h))
    · exact Or.inr (hQ.U_sub (hZ₂ ▸ h))
  · exact union_subset (hP.sub_ins.trans (insOf_mono hs₁)) (hQ.sub_ins.trans (insOf_mono hs₂))
  · have h₁ : (Z₁.append Z₂).length = Z₁.length + Z₂.length := GraphWalk.length_append _ _
    have h₂ : (GraphWalk.nil ((hP.sub.trans interSet_isSub).1 hpG) : GraphWalk Γ.toGraph p
      p).length = 0 := rfl
    omega

include hS in
/-- The case of (9.2) with two disjoint pieces, joined by a line `F` with ends `a`, `b` along a
simple
walk `Q` of `Γ ∩ bd(Y)`. The list `L` holds the edges of the other segment of the perimeter walk,
which
is no shorter than `Q`. -/
private theorem tie_of_line (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {A B : Set S}
    {G H : Drawing S} (hP : IsPiece Γ ins k Y A G) (hQ : IsPiece Γ ins k Y B H) (hAB : Disjoint A B)
    {a b : S} (ha : a ∈ G.V) (hb : b ∈ H.V) (Q : GraphWalk Γ.toGraph a b) (hQs : Q.IsSimple)
    (hQA : ∀ x ∈ Q.support, x ∈ A → x = a) (hQB : ∀ x ∈ Q.support, x ∈ B → x = b)
    (hQsub : (walkDrawing Γ Q).IsSubdrawing (Γ.interSet (frontier Y))) {L : List (Set S)}
    (hLlen : Q.length ≤ L.length) (hLE : ∀ e ∈ L, e ∈ Γ.E) (hLG : ∀ e ∈ L, e ∉ G.E ∧ e ∉ H.E)
    (hcount : ∀ e ∈ Γ.E, edgeCount Q.edges e + edgeCount L e ≤ perimeterCount Y e) :
    (∃ X, (IsTie Γ ins k X ∧ X ⊆ Y ∧ perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y) ∧ A ⊆ X
      ∧ B ⊆ X) ∧
      IsPieceLink Γ Y G H := by
  classical
  obtain ⟨Z₁, hZ₁, hc₁⟩ := hP.walk a ha
  obtain ⟨Z₂, hZ₂, hc₂⟩ := hQ.walk b hb
  have hEZ₁ : ∀ e, e ∈ Z₁.edges ↔ e ∈ G.E := fun e => by rw [← hZ₁, walkDrawing_E]; rfl
  have hEZ₂ : ∀ e, e ∈ Z₂.edges ↔ e ∈ H.E := fun e => by rw [← hZ₂, walkDrawing_E]; rfl
  have haA : a ∈ A := hP.U_sub (G.V_subset_U ha)
  have hbB : b ∈ B := hQ.U_sub (H.V_subset_U hb)
  have hne : a ≠ b := fun h => disjoint_left.mp hAB haA (h ▸ hbB)
  have hGΓ : G.IsSubdrawing Γ := hP.sub.trans interSet_isSub
  have hHΓ : H.IsSubdrawing Γ := hQ.sub.trans interSet_isSub
  have hGcl : ∀ e ∈ G.E, closure e ⊆ A := fun e he => (G.closure_subset_U he).trans hP.U_sub
  have hHcl : ∀ e ∈ H.E, closure e ⊆ B := fun e he => (H.closure_subset_U he).trans hQ.U_sub
  have hQG : ∀ e ∈ Q.edges, e ∉ G.E := fun e he hG => edge_off hQs hQA he (hGcl e hG)
  have hQH : ∀ e ∈ Q.edges, e ∉ H.E := fun e he hG => edge_off hQs hQB he (hHcl e hG)
  have hGH : ∀ e ∈ G.E, e ∉ H.E := fun e h₁ h₂ => by
    obtain ⟨x, hx⟩ := (hGΓ.2 h₁).1
    exact disjoint_left.mp hAB (hGcl e h₁ (subset_closure hx)) (hHcl e h₂ (subset_closure hx))
  -- The closed walk around `A`, along `Q`, around `B` and back along `Q`.
  set Z := Z₁.append (Q.append (Z₂.append Q.reverse)) with hZ
  have hlen : Z.length ≤ perimeterWalkLength Γ Y := by
    have hM : (Z₁.edges ++ Z₂.edges ++ Q.edges ++ L).length ≤ perimeterWalkLength Γ Y := by
      refine length_le_of_count hS hY ?_ fun e he => ?_
      · intro e he
        simp only [List.mem_append] at he
        rcases he with ((h | h) | h) | h
        · exact mem_E_of_mem_edges _ h
        · exact mem_E_of_mem_edges _ h
        · exact mem_E_of_mem_edges _ h
        · exact hLE e h
      · have hadd : edgeCount (Z₁.edges ++ Z₂.edges ++ Q.edges ++ L) e =
            edgeCount Z₁.edges e + edgeCount Z₂.edges e + edgeCount Q.edges e + edgeCount L e := by
          simp only [edgeCount, List.count_append]
        rw [hadd]
        by_cases h₁ : e ∈ G.E
        · rw [edgeCount_eq_zero (l := Z₂.edges) fun h => hGH e h₁ ((hEZ₂ e).mp h),
            edgeCount_eq_zero (l := Q.edges) fun h => hQG e h h₁,
            edgeCount_eq_zero (l := L) fun h => (hLG e h).1 h₁]
          simpa using hc₁ e he
        · by_cases h₂ : e ∈ H.E
          · rw [edgeCount_eq_zero (l := Z₁.edges) fun h => h₁ ((hEZ₁ e).mp h),
              edgeCount_eq_zero (l := Q.edges) fun h => hQH e h h₂,
              edgeCount_eq_zero (l := L) fun h => (hLG e h).2 h₂]
            simpa using hc₂ e he
          · rw [edgeCount_eq_zero (l := Z₁.edges) fun h => h₁ ((hEZ₁ e).mp h),
              edgeCount_eq_zero (l := Z₂.edges) fun h => h₂ ((hEZ₂ e).mp h)]
            simpa using hcount e he
    simp only [List.length_append, edges_length] at hM
    have hZl : Z.length = Z₁.length + (Q.length + (Z₂.length + Q.length)) := by
      simp [hZ, GraphWalk.length_append, GraphWalk.length_reverse]
    omega
  set F : Set S := (walkDrawing Γ Q).U with hF
  have hFeq : F = {x | x ∈ Q.support} ∪ ⋃ e ∈ {e | e ∈ Q.edges}, closure e := by
    ext x
    rw [hF, mem_walkDrawing_U]
    simp
  have hL : IsLineWithEnds F a b := hFeq ▸ walk_isLine Γ Q hQs hne
  have hFfr : F ⊆ frontier Y := hQsub.U_subset.trans (interSet_U_subset isClosed_frontier)
  have hFΓ := walkDrawing_isSubdrawing Γ Q
  have hmeet : ∀ {T : Set S} {K : Drawing S} {c : S}, IsPiece Γ ins k Y T K →
    (∀ e ∈ Q.edges, e ∉ K.E) →
      (∀ x ∈ Q.support, x ∈ T → x = c) → c ∈ F → c ∈ T → F ∩ T = {c} := by
    intro T K c hR hE hO hcF hcT
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hcF, hcT⟩)
    rintro x ⟨hxF, hxT⟩
    have hxK : x ∈ K.U := by
      by_contra hn
      have h₁ : x ∈ interior Y := hR.rest ⟨hxT, hn⟩
      exact (hFfr hxF).2 h₁
    rcases U_inter_cases hFΓ (hR.sub.trans interSet_isSub) hxF hxK with h | ⟨e, he₁, he₂, -⟩
    · refine hO x ?_ hxT
      rw [walkDrawing_V] at h
      exact h.1
    · rw [walkDrawing_E] at he₁
      exact (hE e he₁ he₂).elim
  have haF : a ∈ F := IsLineWithEnds.left_mem hL
  have hbF : b ∈ F := IsLineWithEnds.right_mem hL
  have hFA : F ∩ A = {a} := hmeet hP hQG hQA haF haA
  have hFB : F ∩ B = {b} := hmeet hQ hQH hQB hbF hbB
  have hsh : IsTieShape (A ∪ (F ∪ B)) := by
    have hAFB : A ∩ (B ∪ F) = {a} := by
      rw [inter_union_distrib_left, disjoint_iff_inter_eq_empty.mp hAB, empty_union, inter_comm,
        hFA]
    have hBFA : B ∩ (A ∪ F) = {b} := by
      rw [inter_union_distrib_left, inter_comm B A, disjoint_iff_inter_eq_empty.mp hAB, empty_union,
        inter_comm, hFB]
    rcases hP.shape hS hs hY with hd₁ | ha₁ <;> rcases hQ.shape hS hs hY with hd₂ | ha₂
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨A, B, F, a, b, hd₁, hd₂, hAB, hL, hFA, hFB,
        ?_⟩))))
      rw [← union_assoc, union_right_comm A F B]
    · have h₁ : IsArm (B ∪ F) a := (ha₂ b hb).extend (IsLineWithEnds.symm hL)
        (by rw [inter_comm, hFB])
      rw [union_comm F B]
      exact h₁.isTieShape_disc hd₁ hAFB
    · have h₁ : IsArm (A ∪ F) b := (ha₁ a ha).extend hL (by rw [inter_comm, hFA])
      have : A ∪ (F ∪ B) = B ∪ (A ∪ F) := by
        rw [← union_assoc, union_comm]
      rw [this]
      exact h₁.isTieShape_disc hd₂ hBFA
    · have h₁ : IsArm (A ∪ F) b := (ha₁ a ha).extend hL (by rw [inter_comm, hFA])
      have : A ∪ (F ∪ B) = (A ∪ F) ∪ B := by
        rw [union_assoc]
      rw [this]
      exact h₁.isTieShape_union (ha₂ b hb) (by rw [inter_comm, hBFA])
  have hab₂ : IsAbsorbing Γ ins k (F ∪ B) :=
    (IsArm.isAbsorbing (p := a) (Or.inr ⟨b, hL⟩)).union hQ.absorbing hFB.subset
  have hab : IsAbsorbing Γ ins k (A ∪ (F ∪ B)) := hP.absorbing.union hab₂ (p := a) (by
    rintro x ⟨hxA, hxF | hxB⟩
    · have : x ∈ F ∩ A := ⟨hxF, hxA⟩
      rwa [hFA] at this
    · exact (disjoint_left.mp hAB hxA hxB).elim)
  have hUZ : ∀ z, z ∈ (walkDrawing Γ Z).U ↔ z ∈ (walkDrawing Γ Z₁).U ∨ z ∈ F ∨
      z ∈ (walkDrawing Γ Z₂).U ∨ z ∈ F := fun z => by
    rw [hZ, mem_U_append, mem_U_append, mem_U_append, mem_U_reverse]
  have hs₁ : G.IsSubdrawing (walkDrawing Γ Z) := hZ₁ ▸ walkDrawing_mono
    (fun z h => (GraphWalk.mem_support_append _ _).mpr (Or.inl h))
    (fun e h => by rw [hZ, GraphWalk.edges_append]; exact List.mem_append.mpr (Or.inl h))
  have hs₂ : H.IsSubdrawing (walkDrawing Γ Z) := hZ₂ ▸ walkDrawing_mono
    (fun z h => (GraphWalk.mem_support_append _ _).mpr (Or.inr
      ((GraphWalk.mem_support_append _ _).mpr (Or.inr ((GraphWalk.mem_support_append _ _).mpr
        (Or.inl h))))))
    (fun e h => by
      rw [hZ, GraphWalk.edges_append, GraphWalk.edges_append, GraphWalk.edges_append]
      simp [h])
  have hFZ : F ⊆ (walkDrawing Γ Z).U := fun z hz => (hUZ z).mpr (Or.inr (Or.inl hz))
  have hlink : IsPieceLink Γ Y G H := ⟨a, b, Q, Z₁, Z₂, ha, hb, hZ₁, hZ₂, by
    have hZl : Z.length = Z₁.length + (Q.length + (Z₂.length + Q.length)) := by
      simp [hZ, GraphWalk.length_append, GraphWalk.length_reverse]
    omega⟩
  refine ⟨⟨A ∪ (F ∪ B), tie_of_walk hS hs hY Z hlen ?_ hab ?_ hsh ?_,
    subset_union_left, subset_union_right.trans subset_union_right⟩, hlink⟩
  · intro z hz
    rcases (hUZ z).mp hz with h | h | h | h
    · exact Or.inl (hP.U_sub (hZ₁ ▸ h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hQ.U_sub (hZ₂ ▸ h)))
    · exact Or.inr (Or.inl h)
  · refine union_subset (hP.sub_ins.trans (insOf_mono hs₁))
      (union_subset (hFZ.trans subset_union_left) (hQ.sub_ins.trans (insOf_mono hs₂)))
  · exact union_subset hP.subY (union_subset (hFfr.trans hY.isClosed.frontier_subset) hQ.subY)

include hS in
/-- The case of (9.2) with two disjoint pieces: the two segments of the perimeter walk from `A` to
`B`, and the shorter of them gives the line. The paper takes the segments minimizing the total
length.
We only need that they do not overlap and that each meets `A ∪ B` at its ends only. -/
private theorem tie_of_disjoint (hs : IsSlope Γ k ins) (hY : IsRestraint Γ ins k Y) {A B : Set S}
    {G H : Drawing S} (hP : IsPiece Γ ins k Y A G) (hQ : IsPiece Γ ins k Y B H)
      (hAB : Disjoint A B) :
    (∃ X, (IsTie Γ ins k X ∧ X ⊆ Y ∧ perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y) ∧ A ⊆ X
      ∧ B ⊆ X) ∧
      IsPieceLink Γ Y G H := by
  classical
  obtain ⟨u, W, -, -, -, hcnt, hdraw⟩ := hY.exists_walk hS
  have hGΓ : G.IsSubdrawing Γ := hP.sub.trans interSet_isSub
  have hHΓ : H.IsSubdrawing Γ := hQ.sub.trans interSet_isSub
  have hVW : ∀ {x}, x ∈ (Γ.interSet (frontier Y)).V → x ∈ W.support := fun {x} hx => by
    rw [← hdraw, walkDrawing_V] at hx
    exact hx
  obtain ⟨a₀, ha₀⟩ := hP.Vne
  obtain ⟨b₀, hb₀⟩ := hQ.Vne
  have ha₀A : a₀ ∈ A := hP.U_sub (G.V_subset_U ha₀)
  have hb₀B : b₀ ∈ B := hQ.U_sub (H.V_subset_U hb₀)
  obtain ⟨P₁, P₂, hW⟩ := W.exists_append_of_mem (hVW (hP.sub.1 ha₀))
  have hb₁ : b₀ ∈ (P₂.append P₁).support := by
    have h := hVW (hQ.sub.1 hb₀)
    rw [hW] at h
    exact (GraphWalk.mem_support_append _ _).mpr ((GraphWalk.mem_support_append _ _).mp h).symm
  obtain ⟨Q₁, Q₂, hR⟩ := (P₂.append P₁).exists_append_of_mem hb₁
  have hsupp : ∀ {x}, x ∈ Q₁.support ∨ x ∈ Q₂.support → x ∈ W.support := fun {x} h => by
    have h₁ : x ∈ (P₂.append P₁).support := by
      rw [hR]
      exact (GraphWalk.mem_support_append _ _).mpr h
    rw [hW]
    exact (GraphWalk.mem_support_append _ _).mpr ((GraphWalk.mem_support_append _ _).mp h₁).symm
  have hcountW : ∀ e, edgeCount Q₁.edges e + edgeCount Q₂.edges e = edgeCount W.edges e := fun e
    => by
    have h₁ : (P₂.append P₁).edges = Q₁.edges ++ Q₂.edges := by rw [hR, GraphWalk.edges_append]
    have h₂ : W.edges = P₁.edges ++ P₂.edges := by rw [hW, GraphWalk.edges_append]
    rw [GraphWalk.edges_append] at h₁
    have h₃ := congrArg (fun l => List.count e l) h₁
    simp only [List.count_append] at h₃
    rw [h₂]
    simp only [edgeCount, List.count_append]
    omega
  obtain ⟨a₁, ha₁, b₁, hb₁', T₁, hT₁, hT₁s, hT₁A, hT₁B⟩ := exists_crossing A B Q₁ ha₀A hb₀B
  obtain ⟨a₂, ha₂, b₂, hb₂', T₂, hT₂, hT₂s, hT₂A, hT₂B⟩ := exists_crossing A B Q₂.reverse ha₀A hb₀B
  obtain ⟨S₁, hS₁, hS₁s, hS₁e⟩ := GraphWalk.exists_isSimple T₁
  obtain ⟨S₂, hS₂, hS₂s, hS₂e⟩ := GraphWalk.exists_isSimple T₂
  have hc₁ : ∀ e, edgeCount S₁.edges e ≤ edgeCount Q₁.edges e := fun e => by
    have h₁ := hT₁.count_le e
    by_cases he : e ∈ S₁.edges
    · have h₂ : edgeCount S₁.edges e = 1 := by
        unfold edgeCount
        convert List.count_eq_one_of_mem hS₁.edges_nodup he
      have h₃ : 0 < T₁.edges.count e := List.count_pos_iff.mpr (hS₁e e he)
      unfold edgeCount at h₂ ⊢
      convert_to _ ≤ Q₁.edges.count e
      omega
    · rw [edgeCount_eq_zero he]
      exact Nat.zero_le _
  have hc₂ : ∀ e, edgeCount S₂.edges e ≤ edgeCount Q₂.edges e := fun e => by
    have h₁ := hT₂.count_le e
    rw [GraphWalk.edges_reverse, List.count_reverse] at h₁
    by_cases he : e ∈ S₂.edges
    · have h₂ : edgeCount S₂.edges e = 1 := by
        unfold edgeCount
        convert List.count_eq_one_of_mem hS₂.edges_nodup he
      have h₃ : 0 < T₂.edges.count e := List.count_pos_iff.mpr (hS₂e e he)
      unfold edgeCount at h₂ ⊢
      convert_to _ ≤ Q₂.edges.count e
      omega
    · rw [edgeCount_eq_zero he]
      exact Nat.zero_le _
  have hs₁W : ∀ {x}, x ∈ S₁.support → x ∈ W.support := fun {x} h => hsupp (Or.inl (hT₁s x
    (hS₁s x h)))
  have hs₂W : ∀ {x}, x ∈ S₂.support → x ∈ W.support := fun {x} h => hsupp (Or.inr (by
    have := hT₂s x (hS₂s x h)
    rw [GraphWalk.support_reverse] at this
    exact List.mem_reverse.mp this))
  have hsubW : ∀ {c d : S} (R : GraphWalk Γ.toGraph c d), (∀ x ∈ R.support, x ∈ W.support) →
      (∀ e ∈ R.edges, e ∈ W.edges) → (walkDrawing Γ R).IsSubdrawing (Γ.interSet (frontier Y)) := by
    intro c d R h₁ h₂
    have := walkDrawing_mono (Z := R) (Z' := W) h₁ h₂
    rwa [hdraw] at this
  have hedW : ∀ e, 0 < edgeCount Q₁.edges e ∨ 0 < edgeCount Q₂.edges e → e ∈ W.edges := fun e h
    => by
    have h₁ := hcountW e
    have h₂ : 0 < edgeCount W.edges e := by omega
    by_contra hn
    rw [edgeCount_eq_zero hn] at h₂
    omega
  have hposn : ∀ {l : List (Set S)} {e}, e ∈ l → 0 < edgeCount l e := fun {l e} h => by
    unfold edgeCount
    exact List.count_pos_iff.mpr h
  have hs₁E : ∀ e ∈ S₁.edges, e ∈ W.edges := fun e he =>
    hedW e (Or.inl ((hposn he).trans_le (hc₁ e)))
  have hs₂E : ∀ e ∈ S₂.edges, e ∈ W.edges := fun e he =>
    hedW e (Or.inr ((hposn he).trans_le (hc₂ e)))
  have hsub₁ := hsubW S₁ (fun x h => hs₁W h) hs₁E
  have hsub₂ := hsubW S₂ (fun x h => hs₂W h) hs₂E
  have hend : ∀ {T : Set S} {K : Drawing S} {x : S}, IsPiece Γ ins k Y T K → x ∈ T → x ∈ W.support
    → x ∈ K.V := by
    intro T K x hR hxT hx
    have hxV : x ∈ (walkDrawing Γ W).V := by
      rw [walkDrawing_V]
      exact hx
    rw [hdraw] at hxV
    have hxf : x ∈ frontier Y :=
      interSet_U_subset isClosed_frontier ((Γ.interSet (frontier Y)).V_subset_U hxV)
    have hxU : x ∈ K.U := by
      by_contra hn
      exact hxf.2 (hR.rest ⟨hxT, hn⟩)
    exact mem_V_of_mem_U (hR.sub.trans interSet_isSub) hxU ((interSet_isSub (Γ := Γ)).1 hxV)
  have hoffA : ∀ {a b : S} {R : GraphWalk Γ.toGraph a b} {T : Set S} {c : S}, IsPiece Γ ins k Y T G
    → R.IsSimple →
      (∀ x ∈ R.support, x ∈ T → x = c) → ∀ e ∈ R.edges, e ∉ G.E := by
    intro a b R T c hR hs' hO e he hG
    exact edge_off hs' hO he ((G.closure_subset_U hG).trans hR.U_sub)
  have hoffB : ∀ {a b : S} {R : GraphWalk Γ.toGraph a b} {T : Set S} {c : S}, IsPiece Γ ins k Y T H
    → R.IsSimple →
      (∀ x ∈ R.support, x ∈ T → x = c) → ∀ e ∈ R.edges, e ∉ H.E := by
    intro a b R T c hR hs' hO e he hG
    exact edge_off hs' hO he ((H.closure_subset_U hG).trans hR.U_sub)
  have hO₁A : ∀ x ∈ S₁.support, x ∈ A → x = a₁ := fun x h => hT₁A x (hS₁s x h)
  have hO₁B : ∀ x ∈ S₁.support, x ∈ B → x = b₁ := fun x h => hT₁B x (hS₁s x h)
  have hO₂A : ∀ x ∈ S₂.support, x ∈ A → x = a₂ := fun x h => hT₂A x (hS₂s x h)
  have hO₂B : ∀ x ∈ S₂.support, x ∈ B → x = b₂ := fun x h => hT₂B x (hS₂s x h)
  rcases le_total S₁.length S₂.length with hle | hle
  · refine tie_of_line hS hs hY hP hQ hAB (hend hP ha₁ (hs₁W S₁.start_mem_support))
      (hend hQ hb₁' (hs₁W S₁.end_mem_support)) S₁ hS₁ hO₁A hO₁B hsub₁ (L := S₂.edges)
      (by rwa [edges_length]) (fun e he => mem_E_of_mem_edges S₂ he)
      (fun e he => ⟨hoffA hP hS₂ hO₂A e he, hoffB hQ hS₂ hO₂B e he⟩) fun e he => ?_
    rw [← hcnt e he, ← hcountW]
    exact Nat.add_le_add (hc₁ e) (hc₂ e)
  · refine tie_of_line hS hs hY hP hQ hAB (hend hP ha₂ (hs₂W S₂.start_mem_support))
      (hend hQ hb₂' (hs₂W S₂.end_mem_support)) S₂ hS₂ hO₂A hO₂B hsub₂ (L := S₁.edges)
      (by rwa [edges_length]) (fun e he => mem_E_of_mem_edges S₁ he)
      (fun e he => ⟨hoffA hP hS₁ hO₁A e he, hoffB hQ hS₁ hO₁B e he⟩) fun e he => ?_
    rw [← hcnt e he, ← hcountW, add_comm]
    exact Nat.add_le_add (hc₁ e) (hc₂ e)

include hS in
/-- The proof of (9.2) of Graph Minors XI: either one piece holds `a` and `b`, or there are two
pieces, joined inside the budget
of `Y`. -/
theorem exists_pieces (hs : IsSlope Γ k ins) {a b : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A)
    (hY : IsRestraint Γ ins k Y) (haY : a ⊆ Y) (hbY : b ⊆ Y) :
    (∃ A G, IsPiece Γ ins k Y A G ∧ a ⊆ A ∧ b ⊆ A) ∨
      ∃ A G B H, IsPiece Γ ins k Y A G ∧ IsPiece Γ ins k Y B H ∧ a ⊆ A ∧ b ⊆ B ∧
        (∃ X, (IsTie Γ ins k X ∧ X ⊆ Y ∧ perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y) ∧ A ⊆ X
          ∧ B ⊆ X) ∧
        IsPieceLink Γ Y G H := by
  obtain ⟨A, G, hP, haA⟩ := exists_piece hS hs hY ha haY
  obtain ⟨B, H, hQ, hbB⟩ := exists_piece hS hs hY hb hbY
  have hfinish : ((∃ X, (IsTie Γ ins k X ∧ X ⊆ Y ∧ perimeterWalkLength Γ X
    ≤ perimeterWalkLength Γ Y) ∧ A ⊆ X ∧ B ⊆ X) ∧
      IsPieceLink Γ Y G H) → ∃ A G B H, IsPiece Γ ins k Y A G ∧ IsPiece Γ ins k Y B H ∧ a ⊆ A
        ∧ b ⊆ B ∧
        (∃ X, (IsTie Γ ins k X ∧ X ⊆ Y ∧ perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y) ∧ A ⊆ X
          ∧ B ⊆ X) ∧
        IsPieceLink Γ Y G H := fun h => ⟨A, G, B, H, hP, hQ, haA, hbB, h.1, h.2⟩
  have hGΓ : G.IsSubdrawing Γ := hP.sub.trans interSet_isSub
  have hHΓ : H.IsSubdrawing Γ := hQ.sub.trans interSet_isSub
  by_cases h₁ : ∃ x, x ∈ A ∧ x ∉ G.U ∧ x ∈ B ∧ x ∉ H.U
  · obtain ⟨x, hxA, hxG, hxB, hxH⟩ := h₁
    have hAB : A = B := Subset.antisymm (star_subset hS hs hY hP hQ hxA hxG hxB hxH)
      (star_subset hS hs hY hQ hP hxB hxH hxA hxG)
    subst hAB
    exact Or.inl ⟨A, G, hP, haA, hbB⟩
  push Not at h₁
  have hin : ∀ {x}, x ∈ A → x ∈ B → x ∈ G.U ∧ x ∈ H.U := fun {x} hxA hxB => by
    have hfr : ∀ {D : Drawing S}, D.IsSubdrawing (Γ.interSet (frontier Y)) → x ∈ D.U
      → x ∈ frontier Y :=
      fun hD hx => interSet_U_subset isClosed_frontier (hD.U_subset hx)
    by_cases hxG : x ∈ G.U
    · refine ⟨hxG, ?_⟩
      by_contra hxH
      exact (hfr hP.sub hxG).2 (hQ.rest ⟨hxB, hxH⟩)
    · by_cases hxH : x ∈ H.U
      · exact ((hfr hQ.sub hxH).2 (hP.rest ⟨hxA, hxG⟩)).elim
      · exact (hxH (h₁ x hxA hxG hxB)).elim
  by_cases h₂ : ∃ x y, x ≠ y ∧ x ∈ A ∧ x ∈ B ∧ y ∈ A ∧ y ∈ B
  · obtain ⟨x, y, hxy, hxA, hxB, hyA, hyB⟩ := h₂
    obtain ⟨X, K, hK, hAX, hBX⟩ := piece_of_two_points hS hs hY hP hQ hxy (hin hxA hxB).1
      (hin hxA hxB).2
      (hin hyA hyB).1 (hin hyA hyB).2
    exact Or.inl ⟨X, K, hK, haA.trans hAX, hbB.trans hBX⟩
  push Not at h₂
  by_cases h₃ : (A ∩ B).Nonempty
  · obtain ⟨p, hpA, hpB⟩ := h₃
    have hdis : ∀ e ∈ G.E, e ∉ H.E := by
      intro e he₁ he₂
      obtain ⟨q, q', hl⟩ := (G.toGraph.edge_mem_iff_exists_isLink e).mp he₁
      have hq : q ∈ closure e ∩ G.V := by rw [hl.2.2.2]; simp
      obtain ⟨z, hz⟩ := (hGΓ.2 he₁).1
      have hzq : z ≠ q := fun h => edge_notMem_V (hGΓ.2 he₁) hz (hGΓ.1 (h ▸ hq.2))
      have hm₁ : ∀ {w}, w ∈ closure e → w ∈ A ∧ w ∈ B := fun hw =>
        ⟨hP.U_sub (G.closure_subset_U he₁ hw), hQ.U_sub (H.closure_subset_U he₂ hw)⟩
      exact h₂ z q hzq (hm₁ (subset_closure hz)).1 (hm₁ (subset_closure hz)).2 (hm₁ hq.1).1
        (hm₁ hq.1).2
    have hAB : A ∩ B = {p} := by
      refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hpA, hpB⟩)
      rintro x ⟨hxA, hxB⟩
      by_contra hxp
      exact h₂ x p hxp hxA hxB hpA hpB
    obtain ⟨hpG, hpH⟩ := hin hpA hpB
    rcases U_inter_cases hGΓ hHΓ hpG hpH with ⟨h₄, h₅⟩ | ⟨e, he₁, he₂, -⟩
    · exact Or.inr <| hfinish (tie_of_one_point hS hs hY hP hQ h₄ h₅ hAB hdis)
    · exact (hdis e he₁ he₂).elim
  · exact Or.inr <| hfinish (tie_of_disjoint hS hs hY hP hQ
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h₃)))


include hS in
/-- **(9.2)** of Graph Minors XI (page 105): "Let $a, b \in A(\Gamma)$ and let $Y$ be a restraint
with $a, b \subseteq Y$. Then there is a
tie $X$ with $a, b \subseteq X \subseteq Y$ and $l(X) \le l(Y)$." -/
theorem theorem_9_2_proof (hs : IsSlope Γ k ins) {a b : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A)
    (hY : IsRestraint Γ ins k Y) (haY : a ⊆ Y) (hbY : b ⊆ Y) :
    ∃ X, IsTie Γ ins k X ∧ a ⊆ X ∧ b ⊆ X ∧ X ⊆ Y ∧
      perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y := by
  rcases exists_pieces hS hs ha hb hY haY hbY with ⟨A, G, hP, haA, hbA⟩ | ⟨A, G, B, H, -, -, haA,
    hbB, ⟨X, h⟩, -⟩
  · obtain ⟨h₁, h₂, h₃⟩ := tie_of_piece hS hs hY hP
    exact ⟨A, h₁, haA, hbA, h₂, h₃⟩
  · exact ⟨X, h.1.1, haA.trans h.2.1, hbB.trans h.2.2, h.1.2.1, h.1.2.2⟩
end GraphMinor.GM11

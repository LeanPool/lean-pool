/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.DiscSides

/-!
# Sides of circuits

These are the facts about circuits of a radial drawing that the proofs of (8.5), (8.6) and (8.7)
use.
A *side* of a drawing `F` is a connected open set with frontier `U(F)`. The inside of a closed disc
bounded by `F` is a side, and so is the complement of that disc.

* `cover_sides`: sides that are pairwise disjoint along the edges of their drawings cover the
  surface.
* `path_side`: a path that meets a circuit only in its ends has all its interior on one side.
* `circuit_sup`: two paths with the same ends and nothing else in common form a circuit.
* `disc_split`, `disc_lambda`: the `λ`-order of the separation of a disc bounded by a circuit.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

section Walks

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- Two paths with the same ends and nothing else in common form a circuit. -/
theorem circuit_sup {G P Q : Drawing T} {u v : T} (hPG : P.IsSubdrawing G) (hQG : Q.IsSubdrawing G)
    (hp : P.IsPathBetween u v) (hq : Q.IsPathBetween u v) (huv : u ≠ v)
    (hV : P.V ∩ Q.V ⊆ {u, v}) (hE : Disjoint P.E Q.E) : (G.sup P Q).IsCircuit := by
  obtain ⟨W, hW, hWV, hWE⟩ := hp
  obtain ⟨X, hX, hXV, hXE⟩ := hq
  obtain ⟨W', hs, he⟩ := (Drawing.le_sup_left hPG hQG).exists_walk_up W
  obtain ⟨X', hs', he'⟩ := (Drawing.le_sup_right hPG hQG).exists_walk_up X
  have h₁ : W'.IsSimple := by
    change W'.support.Nodup
    rw [hs]
    exact hW
  have h₂ : X'.IsSimple := by
    change X'.support.Nodup
    rw [hs']
    exact hX
  have hc := GraphWalk.isSimpleClosed_append h₁ h₂.reverse (fun x hx hy ↦ by
    rw [GraphWalk.support_reverse, List.mem_reverse] at hy
    rw [hs] at hx
    rw [hs'] at hy
    have : x ∈ P.V ∩ Q.V := ⟨by rw [hWV]; exact hx, by rw [hXV]; exact hy⟩
    exact hV this) (fun e he₁ he₂ ↦ by
    rw [GraphWalk.edges_reverse, List.mem_reverse, he'] at he₂
    rw [he] at he₁
    exact disjoint_left.mp hE (by rw [hWE]; exact he₁) (by rw [hXE]; exact he₂))
  refine ⟨u, W'.append X'.reverse, hc, ?_, ?_, ?_⟩
  · rw [GraphWalk.length_append]
    by_contra hn
    have : W'.length = 0 := by omega
    exact huv (GraphWalk.eq_of_length_eq_zero this)
  · rw [Drawing.sup_V hPG hQG, hWV, hXV]
    ext x
    simp [GraphWalk.mem_support_append, GraphWalk.support_reverse, hs, hs']
  · rw [Drawing.sup_E hPG hQG, hWE, hXE]
    ext x
    simp [GraphWalk.edges_append, GraphWalk.edges_reverse, he, he']

omit [T2Space T] in
theorem U_union {C A B : Drawing T} (hV : C.V = A.V ∪ B.V) (hE : C.E = A.E ∪ B.E) :
    C.U = A.U ∪ B.U := by
  rw [Drawing.U_eq C, Drawing.U_eq A, Drawing.U_eq B, hV, hE]
  ext x
  simp only [mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro ((h | h) | ⟨e, he | he, h⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr ⟨e, he, h⟩)
    · exact Or.inr (Or.inr ⟨e, he, h⟩)
  · rintro ((h | ⟨e, he, h⟩) | (h | ⟨e, he, h⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨e, Or.inl he, h⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨e, Or.inr he, h⟩

theorem length_support {α β : Type*} {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    W.support.length = W.length + 1 := by
  induction W with
  | nil h => simp [GraphWalk.length, GraphWalk.edges, GraphWalk.support]
  | cons h r ih =>
    simp only [GraphWalk.support, List.length_cons, ih, GraphWalk.length, GraphWalk.edges]

omit [T2Space T] in
theorem IsCircuit.ncard_V {C : Drawing T} (hC : C.IsCircuit) : C.V.ncard = C.E.ncard := by
  classical
  obtain ⟨u, W, ⟨hnd, hed⟩, hpos, hV, hE⟩ := hC
  have hl : C.E.ncard = W.length := by
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set T)) := by
      ext x
      simp
    rw [hE, h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
    rfl
  have hVt : C.V = (W.support.tail.toFinset : Set T) := by
    rw [hV]
    ext x
    simp only [mem_ofPred_eq, List.coe_toFinset]
    constructor
    · intro hx
      rw [W.support_eq_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · cases W with
        | nil h => simp [GraphWalk.length] at hpos
        | cons h r => simpa using r.end_mem_support
      · exact hx
    · exact List.mem_of_mem_tail
  have hlen : W.support.tail.length = W.length := by
    rw [List.length_tail, length_support]
    rfl
  rw [hVt, ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen, hl]

omit [T2Space T] in
/-- A circuit in a bipartite drawing has exactly twice as many edges as vertices on one side. -/
theorem IsCircuit.ncard_E_eq {C : Drawing T} (hC : C.IsCircuit) {P : Set T}
    (halt : ∀ e x y, C.toGraph.IsLink e x y → (x ∈ P ↔ y ∉ P)) :
    C.E.ncard = 2 * (C.V ∩ P).ncard := by
  have h₁ := IsCircuit.ncard_le hC halt
  have h₂ := IsCircuit.ncard_le hC (P := Pᶜ) fun e x y hl ↦ by
    have := halt e x y hl
    simp only [mem_compl_iff, not_not]
    tauto
  have hsum : (C.V ∩ P).ncard + (C.V ∩ Pᶜ).ncard = C.V.ncard := by
    rw [← ncard_union_eq (disjoint_left.mpr fun x (hx : x ∈ C.V ∩ P) (hx' : x ∈ C.V ∩ Pᶜ) ↦ hx'.2
      hx.2) (C.finite_V.subset
      inter_subset_left) (C.finite_V.subset inter_subset_left), ← inter_union_distrib_left]
    simp
  have := IsCircuit.ncard_V hC
  omega

end Walks

section SideFacts

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]

/-- A connected open set with frontier `U(F)`. -/
structure IsSide (Ω : Set T) (F : Drawing T) : Prop where
  isOpen : IsOpen Ω
  frontier_eq : frontier Ω = F.U
  nonempty : Ω.Nonempty
  conn : IsPreconnected Ω

omit [ConnectedSpace T] in
theorem closure_discInt {Δ : Set T} (hΔ : IsClosedDisc Δ) : closure (discInt Δ) = Δ :=
  Subset.antisymm (closure_minimal (discInt_subset Δ) hΔ.isClosed) hΔ.subset_closure_discInt

omit [ConnectedSpace T] in
theorem isSide_int (hT : IsClosedSurface T) {Δ : Set T} {F : Drawing T} (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U) : IsSide (discInt Δ) F := by
  have hman : ∀ x : T, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have ho := hΔ.isOpen_discInt hman
  refine ⟨ho, ?_, hΔ.nonempty_discInt, hΔ.isPreconnected_discInt⟩
  rw [ho.frontier_eq, closure_discInt hΔ, ← hbd]
  ext x
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra hn
    exact h₂ ⟨h₁, hn⟩
  · intro h
    exact ⟨Surface.discBd_subset _ h, fun h' ↦ h'.2 h⟩

theorem isSide_out (hT : IsClosedSurface T) {Δ : Set T} {F : Drawing T} (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U) : IsSide Δᶜ F := by
  have hfr : frontier Δᶜ = F.U := by
    rw [frontier_compl, ← hbd, IsClosedDisc.frontier_eq_discBd hT hΔ]
  refine ⟨hΔ.isClosed.isOpen_compl, hfr, ?_, isPreconnected_compl_disc hT hΔ⟩
  by_contra hn
  have hemp : Δᶜ = ∅ := not_nonempty_iff_eq_empty.mp hn
  rw [hemp, frontier_empty, ← hbd] at hfr
  obtain ⟨φ⟩ := hΔ.isOArc_discBd
  exact eq_empty_iff_forall_notMem.mp hfr.symm _ (φ 1).2

variable {Ω : Set T} {F : Drawing T}

omit [T2Space T] [ConnectedSpace T] in
theorem IsSide.disjoint_U (h : IsSide Ω F) : Disjoint Ω F.U := by
  rw [← h.frontier_eq, h.isOpen.frontier_eq]
  exact disjoint_left.mpr fun x hx hx' ↦ hx'.2 hx

omit [T2Space T] [ConnectedSpace T] in
theorem IsSide.mem_of_closure (h : IsSide Ω F) {x : T} (hx : x ∈ closure Ω) (hn : x ∉ F.U) :
    x ∈ Ω := by
  by_contra hxΩ
  exact hn (h.frontier_eq ▸ (by rw [h.isOpen.frontier_eq]; exact ⟨hx, hxΩ⟩))

omit [T2Space T] [ConnectedSpace T] in
theorem IsSide.U_subset_closure (h : IsSide Ω F) : F.U ⊆ closure Ω := by
  rw [← h.frontier_eq]
  exact frontier_subset_closure

omit [T2Space T] [ConnectedSpace T] in
/-- A connected set that misses the frontier and meets `Ω` lies in `Ω`. -/
theorem IsSide.subset (h : IsSide Ω F) {s : Set T} (hs : IsPreconnected s)
    (hd : Disjoint s F.U) (hm : (s ∩ Ω).Nonempty) : s ⊆ Ω := by
  obtain ⟨y, hys, hyΩ⟩ := hm
  have := hs.subset_left_of_subset_union h.isOpen isClosed_closure.isOpen_compl
    (disjoint_left.mpr fun w hw hn ↦ hn (subset_closure hw)) (fun x hx ↦ ?_) ⟨y, hys, hyΩ⟩
  · exact this
  · by_cases hxc : x ∈ closure Ω
    · exact Or.inl (h.mem_of_closure hxc (disjoint_left.mp hd hx))
    · exact Or.inr hxc

variable {G : Drawing T}

theorem exists_region_near (hT : IsClosedSurface T) (G : Drawing T) {O : Set T} (hO : IsOpen O)
    {x : T} (hx : x ∈ closure O) : ∃ p ∈ G.R, x ∈ closure p ∧ (p ∩ O).Nonempty := by
  have hRfin : G.R.Finite := finite_R hT G
  have hd : x ∈ closure (⋃ p ∈ {p ∈ G.R | (p ∩ O).Nonempty}, p) := by
    rw [mem_closure_iff]
    intro Q hQ hxQ
    obtain ⟨y, hyQ, hyO⟩ := mem_closure_iff.mp hx Q hQ hxQ
    obtain ⟨z, ⟨hzQ, hzO⟩, hzU⟩ := exists_notMem_U (Γ := G) hT
      (hQ.inter hO) ⟨y, hyQ, hyO⟩
    obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzU
    exact ⟨z, hzQ, mem_biUnion (x := p) ⟨hp, z, hzp, hzO⟩ hzp⟩
  have hfinite : {p ∈ G.R | (p ∩ O).Nonempty}.Finite := hRfin.subset fun _ hp => hp.1
  rw [hfinite.closure_biUnion] at hd
  obtain ⟨p, ⟨hp, hpO⟩, hxp⟩ := mem_iUnion₂.mp hd
  exact ⟨p, hp, hxp, hpO⟩

omit [T2Space T] [ConnectedSpace T] in
theorem IsSide.region_subset (hΩ : IsSide Ω F) (hF : F.IsSubdrawing G) {s : Set T} (hs : s ∈ G.R)
    (hm : (s ∩ Ω).Nonempty) : s ⊆ Ω := by
  refine hΩ.subset ?_ ?_ hm
  · obtain ⟨y, hy, rfl⟩ := id hs
    exact isPreconnected_connectedComponentIn
  · exact disjoint_left.mpr fun x hx hxU ↦ GM11.region_subset hs hx (hF.U_subset hxU)

/-- **Sides that fit along their edges cover the surface.** Let `𝒪` be a finite set of sides of
subdrawings of `G`. Suppose that each edge of the drawing of a member is an edge of the drawing of a
member disjoint from it. An edge has only two regions next to it, and so a region of `G` in `𝒪` and
a region not in `𝒪` are never next to each other. So every region of `G` lies in a member. -/
theorem cover_sides (hT : IsClosedSurface T) {𝒪 : Set (Set T × Drawing T)} (hfin : 𝒪.Finite)
    (hne : 𝒪.Nonempty) (hs : ∀ o ∈ 𝒪, IsSide o.1 o.2 ∧ o.2.IsSubdrawing G)
    (hpair : ∀ o ∈ 𝒪, ∀ e ∈ o.2.E, ∃ o' ∈ 𝒪, e ∈ o'.2.E ∧ Disjoint o.1 o'.1) (x : T) :
    ∃ o ∈ 𝒪, x ∈ closure o.1 := by
  classical
  let Z : Set (Set T) := {s | s ∈ G.R ∧ ∃ o ∈ 𝒪, s ⊆ o.1}
  have hsub : ∀ s ∈ G.R, ∀ o ∈ 𝒪, (s ∩ o.1).Nonempty → s ∈ Z := fun s hs' o ho hm ↦
    ⟨hs', o, ho, (hs o ho).1.region_subset (hs o ho).2 hs' hm⟩
  have hall : ∀ s ∈ G.R, s ∈ Z := by
    intro s' hs'
    by_contra hnZ
    obtain ⟨o₀, ho₀⟩ := hne
    obtain ⟨y₀, hy₀⟩ := (hs o₀ ho₀).1.nonempty
    obtain ⟨s₀, hs₀, -, hm₀⟩ := exists_region_near hT G (hs o₀ ho₀).1.isOpen (subset_closure hy₀)
    obtain ⟨y₁, hy₁⟩ := region_nonempty hs₀
    obtain ⟨y₂, hy₂⟩ := region_nonempty hs'
    obtain ⟨e, he, -⟩ := exists_boundary_edge hT (X := univ) isOpen_univ isPreconnected_univ
      (hsub s₀ hs₀ o₀ ho₀ hm₀) (fun _ h ↦ h.1) ⟨hs', hnZ⟩ ⟨y₁, hy₁, mem_univ _⟩ ⟨y₂, hy₂, mem_univ
        _⟩
    obtain ⟨⟨s₁, hs₁Z, hi₁⟩, ⟨s₂, hs₂, hi₂⟩⟩ := mem_boundaryDrawing_E.mp he
    have heG := hi₁.1
    have he₁ := edge_subset_closure_of_incident hT heG hi₁.2.1 hi₁.2.2
    have he₂ := edge_subset_closure_of_incident hT heG hi₂.2.1 hi₂.2.2
    obtain ⟨hs₁, o, ho, hs₁o⟩ := hs₁Z
    obtain ⟨hside, hoG⟩ := hs o ho
    obtain ⟨z, hz⟩ := heG.1
    by_cases heo : e ∈ o.2.E
    · obtain ⟨o', ho', heo', hdis⟩ := hpair o ho e heo
      obtain ⟨hside', hoG'⟩ := hs o' ho'
      have hzcl : z ∈ closure o'.1 := hside'.U_subset_closure (o'.2.closure_subset_U heo'
        (subset_closure hz))
      obtain ⟨s₃, hs₃, hzs₃, hm₃⟩ := exists_region_near hT G hside'.isOpen hzcl
      have he₃ := edge_subset_closure_of_incident hT heG hs₃ ⟨z, hz, hzs₃⟩
      have hs₃o := hside'.region_subset hoG' hs₃ hm₃
      rcases region_incident_two hT heG hs₁ hs₃ hs₂.1 he₁ he₃ he₂ with
        h | h | h
      · obtain ⟨y, hy⟩ := region_nonempty hs₁
        exact disjoint_left.mp hdis (hs₁o hy) (hs₃o (h ▸ hy))
      · exact hs₂.2 ⟨hs₂.1, o, ho, h ▸ hs₁o⟩
      · exact hs₂.2 ⟨hs₂.1, o', ho', h ▸ hs₃o⟩
    · have hd := edge_disjoint_U hoG heG heo
      have hzo : z ∈ o.1 := hside.mem_of_closure (closure_mono hs₁o (he₁ hz))
        (disjoint_left.mp hd hz)
      obtain ⟨w, hwo, hws⟩ := mem_closure_iff.mp (he₂ hz) _ hside.isOpen hzo
      exact hs₂.2 (hsub s₂ hs₂.1 o ho ⟨w, hws, hwo⟩)
  have hd : x ∈ closure (⋃ o ∈ 𝒪, o.1) := by
    obtain ⟨s, hs₁, hxs, -⟩ := exists_region_near (O := univ) hT G isOpen_univ (by simp)
    obtain ⟨-, o, ho, hso⟩ := hall s hs₁
    exact closure_mono ((hso).trans (subset_biUnion_of_mem (u := fun o : Set T × Drawing T ↦ o.1)
      ho)) hxs
  rw [hfin.closure_biUnion] at hd
  obtain ⟨o, ho, hx⟩ := mem_iUnion₂.mp hd
  exact ⟨o, ho, hx⟩

theorem simple_self {α β : Type*} {H : Graph α β} {a : α} {r : GraphWalk H a a} (hs : r.IsSimple) :
    r.edges = [] ∧ r.support = [a] := by
  have hl := hs.length_eq_zero
  refine ⟨List.length_eq_zero_iff.mp hl, ?_⟩
  have hlen := length_support r
  rw [hl] at hlen
  have h := r.support_eq_cons
  rw [h] at hlen ⊢
  simp only [List.length_cons, zero_add, Nat.add_eq_right, List.length_eq_zero_iff] at hlen
  rw [hlen]

omit [T2Space T] [ConnectedSpace T] in
/-- A path that meets the frontier only in its ends lies on one side. -/
theorem walk_side (hF : F.IsSubdrawing G) (hΩ : IsSide Ω F) {P : Drawing T}
    (hP : P.IsSubdrawing G) (hE : Disjoint P.E F.E) {a b : T} (W : GraphWalk P.toGraph a b)
    (hs : W.IsSimple) (ha : a ∈ Ω) (hb : ∀ y ∈ W.support, y ∈ F.U → y = b) :
    (∀ e ∈ W.edges, e ⊆ Ω) ∧ ∀ y ∈ W.support, y ∈ Ω ∨ y = b := by
  induction W with
  | nil h =>
    simp only [GraphWalk.edges, GraphWalk.support, List.not_mem_nil, List.mem_singleton]
    exact ⟨fun e h ↦ h.elim, fun y hy ↦ Or.inr hy⟩
  | @cons a y b e h r ih =>
    have heP : e ∈ P.E := h.1
    have hed : Disjoint e F.U := edge_disjoint_U hF (hP.2 heP) (disjoint_left.mp hE heP)
    have hcl : closure e ∩ P.V = {a, y} := h.2.2.2
    have hac : a ∈ closure e := (hcl.symm ▸ Or.inl rfl : a ∈ closure e ∩ P.V).1
    have hyc : y ∈ closure e := (hcl.symm ▸ Or.inr rfl : y ∈ closure e ∩ P.V).1
    obtain ⟨z, hzΩ, hze⟩ := mem_closure_iff.mp hac _ hΩ.isOpen ha
    have heΩ : e ⊆ Ω := hΩ.subset heP.2.2.1.isConnected.isPreconnected hed ⟨z, hze, hzΩ⟩
    have hs' : r.IsSimple := hs.of_cons
    by_cases hyU : y ∈ F.U
    · have hyb : y = b := hb y (by simp [GraphWalk.support, r.start_mem_support]) hyU
      subst hyb
      obtain ⟨hre, hrs⟩ := simple_self hs'
      simp only [GraphWalk.edges, GraphWalk.support, hre, hrs, List.mem_cons, List.not_mem_nil,
        or_false]
      refine ⟨fun e' he' ↦ he' ▸ heΩ, ?_⟩
      rintro x (rfl | rfl)
      · exact Or.inl ha
      · exact Or.inr rfl
    · have hyΩ : y ∈ Ω := hΩ.mem_of_closure (closure_mono heΩ hyc) hyU
      obtain ⟨h₁, h₂⟩ := ih hs' hyΩ fun x hx ↦ hb x (by simp [GraphWalk.support, hx])
      simp only [GraphWalk.edges, GraphWalk.support, List.mem_cons]
      refine ⟨?_, ?_⟩
      · rintro e' (rfl | he')
        · exact heΩ
        · exact h₁ e' he'
      · rintro x (rfl | hx)
        · exact Or.inl ha
        · exact h₂ x hx

omit [T2Space T] [ConnectedSpace T] in
theorem mem_V_of_mem_U (hF : F.IsSubdrawing G) {x : T} (hxU : x ∈ F.U) (hxV : x ∈ G.V) : x ∈ F.V
  := by
  by_contra hn
  obtain ⟨e, he, hxe⟩ := F.exists_edge_of_mem hxU hn
  exact ((hF.2 he).2.1 hxe).2 hxV

omit [T2Space T] [ConnectedSpace T] in
/-- **A path meets only one side of a circuit.** Let `P` be a path between distinct vertices that
meets `F` only in its ends, and with no edge in `F`. Then all of `P` other than its ends lies in one
of two disjoint sides of `F` that cover the complement of `U(F)`. -/
theorem path_side (hF : F.IsSubdrawing G) {Ω Ω' : Set T} (hΩ : IsSide Ω F) (hΩ' : IsSide Ω' F)
    (hdis : Disjoint Ω Ω') (hcov : F.Uᶜ ⊆ Ω ∪ Ω') {P : Drawing T} (hP : P.IsSubdrawing G) {u v : T}
    (hpath : P.IsPathBetween u v) (huv : u ≠ v) (hV : P.V ∩ F.V ⊆ {u, v}) (hE : Disjoint P.E F.E) :
    (∀ x ∈ P.U, x ∈ Ω ∨ x = u ∨ x = v) ∨ ∀ x ∈ P.U, x ∈ Ω' ∨ x = u ∨ x = v := by
  obtain ⟨W, hW, hWV, hWE⟩ := hpath
  have hPF : ∀ y ∈ W.support, y ∈ F.U → y = u ∨ y = v := fun y hy hyU ↦ by
    have hyV : y ∈ P.V := by rw [hWV]; exact hy
    exact hV ⟨hyV, mem_V_of_mem_U hF hyU (hP.1 hyV)⟩
  cases W with
  | nil h => exact absurd rfl huv
  | @cons _ x _ e h r =>
    have heP : e ∈ P.E := h.1
    have hed : Disjoint e F.U := edge_disjoint_U hF (hP.2 heP) (disjoint_left.mp hE heP)
    have hcl : closure e ∩ P.V = {u, x} := h.2.2.2
    have hxc : x ∈ closure e := (hcl.symm ▸ Or.inr rfl : x ∈ closure e ∩ P.V).1
    have hs' : r.IsSimple := GraphWalk.IsSimple.of_cons hW
    have hunot : u ∉ r.support := (List.nodup_cons.mp hW).1
    have hb : ∀ y ∈ r.support, y ∈ F.U → y = v := fun y hy hyU ↦
      (hPF y (List.mem_cons_of_mem _ hy) hyU).resolve_left fun h ↦ hunot (h ▸ hy)
    have key : ∀ {Ξ : Set T}, IsSide Ξ F → e ⊆ Ξ → ∀ x' ∈ P.U, x' ∈ Ξ ∨ x' = u ∨ x' = v := by
      intro Ξ hΞ heΞ
      have hrest : (∀ e' ∈ r.edges, e' ⊆ Ξ) ∧ ∀ y ∈ r.support, y ∈ Ξ ∨ y = v := by
        by_cases hxU : x ∈ F.U
        · have hxv : x = v := hb x r.start_mem_support hxU
          subst hxv
          rw [(simple_self hs').1, (simple_self hs').2]
          simp
        · exact walk_side hF hΞ hP hE r hs' (hΞ.mem_of_closure (closure_mono heΞ hxc) hxU) hb
      intro y hy
      by_cases hyV : y ∈ P.V
      · rw [hWV] at hyV
        rcases List.mem_cons.mp hyV with rfl | hy'
        · exact Or.inr (Or.inl rfl)
        · rcases hrest.2 y hy' with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inr h')
      · obtain ⟨e', he', hye'⟩ := P.exists_edge_of_mem hy hyV
        rw [hWE] at he'
        rcases List.mem_cons.mp he' with rfl | he''
        · exact Or.inl (heΞ hye')
        · exact Or.inl (hrest.1 e' he'' hye')
    rcases heP.2.2.1.isConnected.isPreconnected.subset_or_subset hΩ.isOpen hΩ'.isOpen hdis
      (fun y hy ↦ hcov (disjoint_left.mp hed hy)) with h' | h'
    · exact Or.inl (key hΩ h')
    · exact Or.inr (key hΩ' h')

end SideFacts

section Theta

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]

/-- Graph Minors XIX, (8.5): `F₁, F₂` are the two paths of the circuit `F` between `u` and `v`, and
`P` is a path of `G` between `u` and `v` with no other vertex or edge in common with `F`. -/
structure TwoPaths (G F F₁ F₂ P : Drawing T) (u v : T) : Prop where
  ne : u ≠ v
  sub : F.IsSubdrawing G
  left : F₁.IsPathOf F u v
  right : F₂.IsPathOf F u v
  union_V : F.V = F₁.V ∪ F₂.V
  union_E : F.E = F₁.E ∪ F₂.E
  inter_V : F₁.V ∩ F₂.V ⊆ {u, v}
  disj_E : Disjoint F₁.E F₂.E
  path : P.IsPathOf G u v
  meet_V : P.V ∩ F.V ⊆ {u, v}
  meet_E : Disjoint P.E F.E

variable {G F F₁ F₂ P : Drawing T} {u v : T}

omit [ConnectedSpace T] in
omit [T2Space T] in
theorem TwoPaths.swap (h : TwoPaths G F F₁ F₂ P u v) : TwoPaths G F F₂ F₁ P u v :=
  ⟨h.ne, h.sub, h.right, h.left, by rw [h.union_V, Set.union_comm],
    by rw [h.union_E, Set.union_comm],
    by simpa only [Set.inter_comm] using h.inter_V,
    h.disj_E.symm, h.path, h.meet_V, h.meet_E⟩

omit [ConnectedSpace T] in
omit [T2Space T] in
theorem TwoPaths.sub₁ (h : TwoPaths G F F₁ F₂ P u v) : F₁.IsSubdrawing G := h.left.1.trans h.sub

omit [ConnectedSpace T] in
omit [T2Space T] in
theorem TwoPaths.sub₂ (h : TwoPaths G F F₁ F₂ P u v) : F₂.IsSubdrawing G := h.right.1.trans h.sub

omit [ConnectedSpace T] in
theorem TwoPaths.left_circuit (h : TwoPaths G F F₁ F₂ P u v) : (G.sup P F₂).IsCircuit := by
  refine circuit_sup h.path.1 h.sub₂ h.path.2 h.right.2 h.ne ?_ ?_
  · rintro x ⟨hx, hx'⟩
    exact h.meet_V ⟨hx, h.right.1.1 hx'⟩
  · exact disjoint_left.mpr fun e he he' ↦ disjoint_left.mp h.meet_E he (h.right.1.2 he')

omit [ConnectedSpace T] in
theorem TwoPaths.U_right (h : TwoPaths G F F₁ F₂ P u v) : (G.sup P F₂).U = P.U ∪ F₂.U :=
  U_union (Drawing.sup_V h.path.1 h.sub₂) (Drawing.sup_E h.path.1 h.sub₂)

omit [ConnectedSpace T] in
omit [T2Space T] in
theorem TwoPaths.U_eq (h : TwoPaths G F F₁ F₂ P u v) : F.U = F₁.U ∪ F₂.U :=
  U_union h.union_V h.union_E

omit [ConnectedSpace T] in
omit [T2Space T] in
theorem TwoPaths.exists_edge (h : TwoPaths G F F₁ F₂ P u v) : F₁.E.Nonempty := by
  obtain ⟨W, -, -, hWE⟩ := h.left.2
  cases W with
  | nil h' => exact absurd rfl h.ne
  | @cons _ x _ e h' r => exact ⟨e, h'.1⟩

omit [ConnectedSpace T] in
omit [T2Space T] in
theorem TwoPaths.mem_V (h : TwoPaths G F F₁ F₂ P u v) : u ∈ F.V ∧ v ∈ F.V := by
  obtain ⟨W, -, hWV, -⟩ := h.left.2
  have h₁ : u ∈ F₁.V := by rw [hWV]; exact W.start_mem_support
  have h₂ : v ∈ F₁.V := by rw [hWV]; exact W.end_mem_support
  exact ⟨h.left.1.1 h₁, h.left.1.1 h₂⟩

omit [ConnectedSpace T] in
omit [T2Space T] in
theorem TwoPaths.mem_V₁ (h : TwoPaths G F F₁ F₂ P u v) : u ∈ F₁.V ∧ v ∈ F₁.V := by
  obtain ⟨W, -, hWV, -⟩ := h.left.2
  exact ⟨by rw [hWV]; exact W.start_mem_support, by rw [hWV]; exact W.end_mem_support⟩

omit [ConnectedSpace T] in
/-- If `P` lies on one side of `F`, then the other side misses the circuit `P ∪ F₂`. -/
theorem TwoPaths.side_disjoint (h : TwoPaths G F F₁ F₂ P u v) {Ω Ω' : Set T} (hΩ : IsSide Ω F)
    (hdis : Disjoint Ω Ω') (hP : ∀ x ∈ P.U, x ∈ Ω' ∨ x = u ∨ x = v) :
    Disjoint Ω (G.sup P F₂).U := by
  refine disjoint_left.mpr fun x hx hxU ↦ ?_
  have hFU := disjoint_left.mp hΩ.disjoint_U hx
  rw [h.U_right] at hxU
  rcases hxU with hxP | hxF
  · rcases hP x hxP with h' | rfl | rfl
    · exact disjoint_left.mp hdis hx h'
    · exact hFU (F.V_subset_U h.mem_V.1)
    · exact hFU (F.V_subset_U h.mem_V.2)
  · exact hFU (h.U_eq ▸ Or.inr hxF)

omit [ConnectedSpace T] in
/-- A side that misses the boundary of a disc, and is not inside the disc, misses the disc. -/
theorem disjoint_disc (hT : IsClosedSurface T) {Ω Δ' : Set T} {F' C : Drawing T} (hΩ : IsSide Ω F')
    (hΔ' : IsClosedDisc Δ') (hbd : discBd Δ' = C.U) (hd : Disjoint Ω C.U)
    (hn : ¬ Ω ⊆ discInt Δ') : Disjoint Ω Δ' := by
  have hO := isSide_int hT hΔ' hbd
  refine disjoint_left.mpr fun x hx hxΔ ↦ ?_
  by_cases hxb : x ∈ discBd Δ'
  · exact disjoint_left.mp hd hx (hbd ▸ hxb)
  · exact hn (hO.subset hΩ.conn hd ⟨x, hx, hxΔ, hxb⟩)

/-- **The theta graph.** Suppose that `P` lies on one side `Ω'` of `F`, and that the other side `Ω`
misses both discs `Δ₁, Δ₂` bounded by `P ∪ F₁` and `P ∪ F₂`. Then `Ω` and the two discs cover the
surface. -/
theorem TwoPaths.theta_cover (hT : IsClosedSurface T) (h : TwoPaths G F F₁ F₂ P u v)
    {Ω : Set T} (hΩ : IsSide Ω F) {Δ₁ Δ₂ : Set T} (hΔ₁ : IsClosedDisc Δ₁) (hΔ₂ : IsClosedDisc Δ₂)
    (hbd₁ : discBd Δ₁ = (G.sup P F₁).U) (hbd₂ : discBd Δ₂ = (G.sup P F₂).U)
    (hd₁ : Disjoint Ω Δ₁) (hd₂ : Disjoint Ω Δ₂) (x : T) :
    x ∈ closure Ω ∨ x ∈ Δ₁ ∨ x ∈ Δ₂ := by
  have h' := h.swap
  have hO₁ := isSide_int hT hΔ₁ hbd₁
  have hO₂ := isSide_int hT hΔ₂ hbd₂
  have hcross : ∀ {F₃ Δ₃ : Set T} {K : Drawing T}, IsSide (discInt Δ₃) (G.sup P K) →
      Disjoint Ω Δ₃ → F₃ ⊆ F.U → Disjoint (discInt Δ₃) F₃ := by
    intro F₃ Δ₃ K hO hd hsub
    refine disjoint_left.mpr fun y hy hyF ↦ ?_
    obtain ⟨z, hzO, hzΩ⟩ := mem_closure_iff.mp (hΩ.U_subset_closure (hsub hyF)) _ hO.isOpen hy
    exact disjoint_left.mp hd hzΩ (discInt_subset _ hzO)
  have h₁₂ : Disjoint (discInt Δ₁) (G.sup P F₂).U := by
    rw [h.U_right]
    refine disjoint_union_right.mpr ⟨?_, hcross hO₁ hd₁ (h.U_eq ▸ subset_union_right)⟩
    have := hO₁.disjoint_U
    rw [h'.U_right] at this
    exact this.mono_right subset_union_left
  have h₂₁ : Disjoint (discInt Δ₂) (G.sup P F₁).U := by
    rw [h'.U_right]
    refine disjoint_union_right.mpr ⟨?_, hcross hO₂ hd₂ (h.U_eq ▸ subset_union_left)⟩
    have := hO₂.disjoint_U
    rw [h.U_right] at this
    exact this.mono_right subset_union_left
  have hne : (G.sup P F₁).U ≠ (G.sup P F₂).U := by
    intro heq
    obtain ⟨e, he⟩ := h.exists_edge
    have heG := h.sub₁.2 he
    have hnot : e ∉ (G.sup P F₂).E := by
      rw [Drawing.sup_E h.path.1 h.sub₂]
      rintro (hp | hr)
      · exact disjoint_left.mp h.meet_E hp (h.left.1.2 he)
      · exact disjoint_left.mp h.disj_E he hr
    have hd := edge_disjoint_U (G.sup_isSubdrawing P F₂) heG hnot
    obtain ⟨y, hy⟩ := heG.1
    have hyU : y ∈ (G.sup P F₁).U := by
      have heC : e ∈ (G.sup P F₁).E := by
        rw [Drawing.sup_E h.path.1 h.sub₁]
        exact Or.inr he
      exact Drawing.closure_subset_U _ heC (subset_closure hy)
    exact disjoint_left.mp hd hy (heq ▸ hyU)
  have hOO : Disjoint (discInt Δ₁) (discInt Δ₂) := by
    refine disjoint_left.mpr fun y hy₁ hy₂ ↦ hne ?_
    have s₁ := hO₂.subset hO₁.conn h₁₂ ⟨y, hy₁, hy₂⟩
    have s₂ := hO₁.subset hO₂.conn h₂₁ ⟨y, hy₂, hy₁⟩
    rw [← hO₁.frontier_eq, ← hO₂.frontier_eq, Subset.antisymm s₁ s₂]
  have hs₁ : Disjoint Ω (discInt Δ₁) := hd₁.mono_right (discInt_subset _)
  have hs₂ : Disjoint Ω (discInt Δ₂) := hd₂.mono_right (discInt_subset _)
  let 𝒪 : Set (Set T × Drawing T) :=
    {(Ω, F), (discInt Δ₁, G.sup P F₁), (discInt Δ₂, G.sup P F₂)}
  have hfin : 𝒪.Finite := by simp [𝒪]
  have mem₀ : (Ω, F) ∈ 𝒪 := Or.inl rfl
  have mem₁ : (discInt Δ₁, G.sup P F₁) ∈ 𝒪 := Or.inr (Or.inl rfl)
  have mem₂ : (discInt Δ₂, G.sup P F₂) ∈ 𝒪 := Or.inr (Or.inr rfl)
  have hC₁ : ∀ e, e ∈ F₁.E → e ∈ (G.sup P F₁).E := fun e he ↦ by
    rw [Drawing.sup_E h.path.1 h.sub₁]
    exact Or.inr he
  have hC₂ : ∀ e, e ∈ F₂.E → e ∈ (G.sup P F₂).E := fun e he ↦ by
    rw [Drawing.sup_E h.path.1 h.sub₂]
    exact Or.inr he
  have hP₁ : ∀ e, e ∈ P.E → e ∈ (G.sup P F₁).E := fun e he ↦ by
    rw [Drawing.sup_E h.path.1 h.sub₁]
    exact Or.inl he
  have hP₂ : ∀ e, e ∈ P.E → e ∈ (G.sup P F₂).E := fun e he ↦ by
    rw [Drawing.sup_E h.path.1 h.sub₂]
    exact Or.inl he
  have hcov := cover_sides (G := G) hT hfin ⟨_, mem₀⟩ (by
      rintro o (rfl | rfl | rfl)
      · exact ⟨hΩ, h.sub⟩
      · exact ⟨hO₁, G.sup_isSubdrawing P F₁⟩
      · exact ⟨hO₂, G.sup_isSubdrawing P F₂⟩) (by
      rintro o (rfl | rfl | rfl) e he
      · rw [h.union_E] at he
        rcases he with he | he
        · exact ⟨_, mem₁, hC₁ e he, hs₁⟩
        · exact ⟨_, mem₂, hC₂ e he, hs₂⟩
      · have he' : e ∈ P.E ∪ F₁.E := by
          rwa [← Drawing.sup_E h.path.1 h.sub₁]
        rcases he' with he' | he'
        · exact ⟨_, mem₂, hP₂ e he', hOO⟩
        · exact ⟨_, mem₀, h.left.1.2 he', hs₁.symm⟩
      · have he' : e ∈ P.E ∪ F₂.E := by
          rwa [← Drawing.sup_E h.path.1 h.sub₂]
        rcases he' with he' | he'
        · exact ⟨_, mem₁, hP₁ e he', hOO.symm⟩
        · exact ⟨_, mem₀, h.right.1.2 he', hs₂.symm⟩) x
  obtain ⟨o, ho, hx⟩ := hcov
  rcases ho with rfl | rfl | rfl
  · exact Or.inl hx
  · exact Or.inr (Or.inl (by rwa [closure_discInt hΔ₁] at hx))
  · exact Or.inr (Or.inr (by rwa [closure_discInt hΔ₂] at hx))

end Theta

end GraphMinor.GM19

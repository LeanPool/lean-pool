/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Theorem63
public import LeanPool.GraphMinor.GM14.Section7a
public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM11.CircuitRegions
public import LeanPool.GraphMinor.GM11.PaintingRegions
public import LeanPool.GraphMinor.GM11.Section5b

/-!
# Graph Minors XIX, (15.1)

Let `H` be a 2-cell drawing with a respectful tangle of order `θ`, and let `X` be a set of at most
`θ` vertices on the closure of one region `r`. A tangle separation of order `< |X|` with `X` on its
small side exists exactly when a short circuit of the radial drawing has `r*` on its inside and
more than half its length in vertices of `X`.

The proof of the paper takes all edges of the radial drawing split by the separation. We take the
union `G` of the circuits that (6.3) of XI gives for the separation. That is all the argument needs.
The circuits of `G` with maximal inside are confined, and (4.3) of XI shows that two of them through
`r*` meet only there. Counting vertices of `Γ` on these circuits then gives one with the property.

The result used later is `theorem_15_1_proof`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- In a 2-cell drawing with an edge, every vertex is an end of some edge. If `x` were not, each
region would have frontier missing `x`, since frontiers of open discs are connected, and a region
with frontier `{x}` would fill the connected set `Σ \ {x}`. So the closures of the regions and the
rest of `U(H)` form a closed set with complement `{x}`, and `{x}` would be open and closed. -/
theorem exists_edge_at_vertex_of_twoCell (hS : IsClosedSurface S) [ConnectedSpace S] {H : Drawing S}
    (hT : (PaintingOrDrawing.drawing H).IsTwoCell) (hE : H.E.Nonempty) {x : S} (hx : x ∈ H.V) :
    ∃ e ∈ H.E, x ∈ closure e := by
  by_contra hno
  push Not at hno
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hcpt : CompactSpace S := hS.1
  set T : Set S := (H.V \ {x}) ∪ ⋃ e ∈ H.E, closure e with hTdef
  have hTcl : IsClosed T :=
    ((H.finite_V.subset sdiff_subset).isClosed).union
      (Set.Finite.isClosed_biUnion H.finite_edges fun _ _ ↦ isClosed_closure)
  have hxT : x ∉ T := by
    rintro (h | h)
    · exact h.2 rfl
    · obtain ⟨e, he, h⟩ := mem_iUnion₂.mp h
      exact hno e he h
  have hUT : H.U ⊆ {x} ∪ T := by
    intro y hy
    rw [H.U_eq] at hy
    by_cases hyx : y = x
    · exact Or.inl hyx
    rcases hy with hy | hy
    · exact Or.inr (Or.inl ⟨hy, hyx⟩)
    · exact Or.inr (Or.inr hy)
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨y₀, hy₀⟩ := he₀.1
  have hy₀U : y₀ ∈ H.U := (he₀.2.1 hy₀).1
  have hy₀x : y₀ ≠ x := fun h ↦ (he₀.2.1 hy₀).2 (h ▸ hx)
  have hfrU : ∀ r ∈ H.R, frontier r ⊆ H.U := by
    intro r hr y hy
    have hyr : y ∉ r := by
      have := hy.2
      rwa [(region_isOpen hr).interior_eq] at this
    exact (closure_region_subset hr hy.1).resolve_left hyr
  have hY : IsPreconnected (univ \ {x} : Set S) :=
    GM11.isPreconnected_sdiff_finite hS isOpen_univ isPreconnected_univ (finite_singleton x)
  have hfx : ∀ r ∈ H.R, x ∉ closure r := by
    intro r hr hxc
    have hxr : x ∉ r := fun h ↦ region_subset hr h (H.V_subset_U hx)
    have hxf : x ∈ frontier r := ⟨hxc, by rwa [(region_isOpen hr).interior_eq]⟩
    have hcon : IsPreconnected (frontier r) := isPreconnected_frontier (hT.2 r hr)
    have hsingle : frontier r ⊆ {x} := by
      intro y hy
      by_contra hyx
      have hyT : y ∈ T := (hUT (hfrU r hr hy)).resolve_left hyx
      obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hcon {x} T isClosed_singleton hTcl
        ((hfrU r hr).trans hUT) ⟨x, hxf, rfl⟩ ⟨y, hy, hyT⟩
      exact hxT (hz₁ ▸ hz₂)
    obtain ⟨w, hw⟩ := region_nonempty hr
    have hwx : w ≠ x := fun h ↦ hxr (h ▸ hw)
    have hsplit : (univ \ {x} : Set S) ⊆ r ∪ (closure r)ᶜ := by
      intro y hy
      by_cases hyr : y ∈ r
      · exact Or.inl hyr
      refine Or.inr fun hyc ↦ hy.2 (hsingle ⟨hyc, ?_⟩)
      rwa [(region_isOpen hr).interior_eq]
    have hy₀c : y₀ ∈ (closure r)ᶜ := by
      refine (hsplit ⟨mem_univ _, hy₀x⟩).resolve_left fun h ↦ region_subset hr h hy₀U
    obtain ⟨z, -, hz₁, hz₂⟩ := hY r (closure r)ᶜ (region_isOpen hr) isClosed_closure.isOpen_compl
      hsplit ⟨w, ⟨mem_univ _, hwx⟩, hw⟩ ⟨y₀, ⟨mem_univ _, hy₀x⟩, hy₀c⟩
    exact hz₂ (subset_closure hz₁)
  have hRfin : H.R.Finite := finite_R hS H
  have hZcl : IsClosed (T ∪ ⋃ r ∈ H.R, closure r) :=
    hTcl.union (hRfin.isClosed_biUnion fun _ _ ↦ isClosed_closure)
  have hZ : T ∪ ⋃ r ∈ H.R, closure r = {x}ᶜ := by
    ext y
    constructor
    · rintro (h | h) (rfl : y = x)
      · exact hxT h
      · obtain ⟨r, hr, h⟩ := mem_iUnion₂.mp h
        exact hfx r hr h
    · intro (hy : y ≠ x)
      by_cases hyU : y ∈ H.U
      · exact Or.inl ((hUT hyU).resolve_left hy)
      obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
      exact Or.inr (mem_iUnion₂.mpr ⟨r, hr, subset_closure hyr⟩)
  have hopen : IsOpen ({x} : Set S) := by
    rw [← isClosed_compl_iff, ← hZ]
    exact hZcl
  have hclopen : IsClopen ({x} : Set S) := ⟨isClosed_singleton, hopen⟩
  have := hclopen.eq_univ ⟨x, rfl⟩
  have hy₀m : y₀ ∈ ({x} : Set S) := this ▸ mem_univ y₀
  exact hy₀x hy₀m

omit [T2Space S] in
/-- A vertex of a drawing that lies on `U(C)`, for a subdrawing `C`, is a vertex of `C`. -/
theorem mem_V_of_mem_U_sub {C K : Drawing S} (hCs : C.IsSubdrawing K) {x : S} (hxU : x ∈ C.U)
    (hxK : x ∈ K.V) : x ∈ C.V := by
  by_contra hxC
  obtain ⟨g, hg, hxg⟩ := C.exists_edge_of_mem hxU hxC
  exact ((hCs.2 hg).2.1 hxg).2 hxK

omit [T2Space S] in
/-- The ends in `K` of an edge of a subdrawing `C` are vertices of `C`. -/
theorem end_mem_V {C K : Drawing S} (hCs : C.IsSubdrawing K) {e : Set S} (he : e ∈ C.E) {x : S}
    (hxe : x ∈ closure e) (hxK : x ∈ K.V) : x ∈ C.V :=
  mem_V_of_mem_U_sub hCs (C.closure_subset_U he hxe) hxK

omit [T2Space S] in
/-- A region of `H` meets `U(C)`, for a subdrawing `C` of a radial drawing, only if the vertex of
the
radial drawing in that region is on `C`: the edges of the radial drawing in `r` all end at that
vertex. -/
theorem disjoint_region_U (hS : IsClosedSurface S) {H K : Drawing S}
    (hP : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) {r : Set S} (hr : r ∈ H.R) {w : S}
    (hw : w ∈ r) (hwV : w ∈ K.V) {C : Drawing S} (hCs : C.IsSubdrawing K) (hwU : w ∉ C.U) :
    Disjoint r C.U := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hP
  have huniq : ∀ {a b : S}, a ∈ r ∧ a ∈ K.V → b ∈ r ∧ b ∈ K.V → a = b := fun ha hb ↦
    (h3 r hr).unique ha hb
  refine disjoint_left.mpr fun y hyr hyU ↦ ?_
  by_cases hyV : y ∈ C.V
  · have : y = w := huniq ⟨hyr, hCs.1 hyV⟩ ⟨hw, hwV⟩
    exact hwU (this ▸ hyU)
  obtain ⟨f, hf, hyf⟩ := C.exists_edge_of_mem hyU hyV
  have hfK := hCs.2 hf
  obtain ⟨v, hv, w', hw', hcap⟩ := h5 f hfK
  have hfdis : Disjoint f H.U := by
    refine disjoint_left.mpr fun z hz hzU ↦ ?_
    have hzK := hfK.2.1 hz
    have : z ∈ H.V := by
      change z ∈ (PaintingOrDrawing.drawing H).V
      rw [← h1]
      exact ⟨hzU, hzK.1⟩
    exact hzK.2 (h2 this)
  have hfr : f ⊆ r := subset_region hr hfK.2.2.1.isConnected.isPreconnected hfdis hyf hyr
  have hw'cl : w' ∈ closure f := by
    have : w' ∈ closure f ∩ K.V := by rw [hcap]; simp
    exact this.1
  obtain ⟨r', hr', hw'r'⟩ := h4 w' hw'
  obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp (closure_mono hfr hw'cl) r' (region_isOpen hr') hw'r'
  have hrr : r' = r := region_eq_of_mem hr' hr hz₁ hz₂
  have hw'w : w' = w := huniq ⟨hrr ▸ hw'r', hw'.1⟩ ⟨hw, hwV⟩
  exact hwU (hw'w ▸ C.closure_subset_U hf hw'cl)

section Slope

variable {K : Drawing S} {k : ℕ} {ins : Drawing S → Set S}

/-- If `w ∉ ins(C)` and `r` is disjoint from `U(C)`, then the only points of `closure r` in `ins(C)`
are on `U(C)`. -/
theorem mem_U_of_mem_closure (hs : IsSlope K k ins) {C : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing K) (hl : C.length < k) {r : Set S} (hr : IsPreconnected r) {w : S}
    (hw : w ∈ r) (hwi : w ∉ ins C) (hdis : Disjoint r C.U) {x : S} (hx : x ∈ closure r)
    (hxi : x ∈ ins C) : x ∈ C.U := by
  have hcl : IsClosed (ins C) := (hs.isClosedDisc C hC hCs hl).isClosed
  have hfr : frontier (ins C) = C.U := by rw [subBd_eq_frontier', hs.subBd_eq C hC hCs hl]
  rcases GM11.subset_or_disjoint_of_frontier hcl hr (hfr ▸ hdis) with h | h
  · exact absurd (h hw) hwi
  by_contra hxU
  have hint : x ∈ interior (ins C) := by
    by_contra hni
    exact hxU (hfr ▸ (show x ∈ frontier (ins C) by rw [hcl.frontier_eq]; exact ⟨hxi, hni⟩))
  obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp hx _ isOpen_interior hint
  exact disjoint_left.mp h hz₂ (interior_subset hz₁)

/-- If `w` is inside `C` and off `U(C)`, then all of `closure r` is inside `C`. -/
theorem closure_subset_ins (hs : IsSlope K k ins) {C : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing K) (hl : C.length < k) {r : Set S} (hr : IsPreconnected r) {w : S}
    (hw : w ∈ r) (hwi : w ∈ ins C) (hdis : Disjoint r C.U) : closure r ⊆ ins C := by
  have hcl : IsClosed (ins C) := (hs.isClosedDisc C hC hCs hl).isClosed
  have hfr : frontier (ins C) = C.U := by rw [subBd_eq_frontier', hs.subBd_eq C hC hCs hl]
  rcases GM11.subset_or_disjoint_of_frontier hcl hr (hfr ▸ hdis) with h | h
  · exact closure_minimal h hcl
  · exact absurd hwi (disjoint_left.mp h hw)

/-- A circuit with two vertices on a circuit with maximal inside is inside it, by (4.3) of XI. -/
theorem ins_subset_of_two_common {Γ' C C' : Drawing S} (hs : IsSlope K k ins)
    (hsub : Γ'.IsSubdrawing K) (hconf : IsConfined k Γ') (hC : C.IsCircuit)
      (hCs : C.IsSubdrawing Γ')
    (hmax : ∀ C' : Drawing S, C'.IsCircuit → C'.IsSubdrawing Γ' → ins C ⊆ ins C' → ins C' ⊆ ins C)
    (hC' : C'.IsCircuit) (hC's : C'.IsSubdrawing Γ') {a b : S} (haC : a ∈ C.V) (haC' : a ∈ C'.V)
    (hbC : b ∈ C.V) (hbC' : b ∈ C'.V) (hab : a ≠ b) : ins C' ⊆ ins C := by
  have hs' := theorem_4_2_proof hs hsub
  obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, -, -, hsup⟩ := hC'.exists_two_paths haC' hbC' hab
  have hP' : P.U ⊆ ins C := path_U_subset hP (hPs.trans hC's) fun hW ↦
    theorem_4_3_i hs hsub hconf hC hCs hmax _ hW haC hbC
  have hQ' : Q.U ⊆ ins C := path_U_subset hQ (hQs.trans hC's) fun hW ↦
    theorem_4_3_i hs hsub hconf hC hCs hmax _ hW haC hbC
  have hU : C'.U ⊆ ins C := by
    rw [← hsup]
    intro z hz
    rw [Drawing.U_eq, Drawing.sup_V hPs hQs, Drawing.sup_E hPs hQs] at hz
    rcases hz with (hz | hz) | hz
    · exact hP' (P.V_subset_U hz)
    · exact hQ' (Q.V_subset_U hz)
    · obtain ⟨f, hf | hf, hz⟩ := mem_iUnion₂.mp hz
      · exact hP' (P.closure_subset_U hf hz)
      · exact hQ' (Q.closure_subset_U hf hz)
  exact hs'.monotone C' C hC' hC's (hconf C' hC' hC's) hC hCs (hconf C hC hCs) hU

/-- Two circuits with the same inside are equal: the inside gives `U(C)`, and `U(C)` gives the
vertices and the edges. -/
theorem eq_of_ins_eq (hs : IsSlope K k ins) {C C' : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing K) (hl : C.length < k) (hC' : C'.IsCircuit) (hCs' : C'.IsSubdrawing K)
    (hl' : C'.length < k) (h : ins C = ins C') : C = C' := by
  have hU : C.U = C'.U := by rw [← hs.subBd_eq C hC hCs hl, ← hs.subBd_eq C' hC' hCs' hl', h]
  have hedge : ∀ {D D' : Drawing S}, D.IsSubdrawing K → D'.IsSubdrawing K → D.U = D'.U →
      D.E ⊆ D'.E := by
    intro D D' hD hD' hUU e he
    by_contra he'
    obtain ⟨y, hy⟩ := (hD.2 he).1
    exact disjoint_left.mp (edge_disjoint_U hD' (hD.2 he) he') hy
      (hUU ▸ (he.2.1 hy).1)
  refine Drawing.ext_of_V_E ?_ ((hedge hCs hCs' hU).antisymm (hedge hCs' hCs hU.symm))
  ext x
  exact ⟨fun hx ↦ mem_V_of_mem_U_sub hCs' (hU ▸ C.V_subset_U hx) (hCs.1 hx),
    fun hx ↦ mem_V_of_mem_U_sub hCs (hU ▸ C'.V_subset_U hx) (hCs'.1 hx)⟩

end Slope

/-- The second statement of (15.1) implies the first, by (6.3) of XI. The side `A` is `Γ ∩ ins(C)`
with the vertices of `X` added, so its order is `½|E(C)| + |X \ ins(C)| < |X|`. -/
theorem exists_separation_of_circuit (_hS : IsClosedSurface S)
    {H K : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S} (hResp : IsRespectfulDrawingTangle H θ T)
    (hP : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) (hs : IsSlope K (2 * θ) ins)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hiff : ∀ A B : Hypergraph S (Set S), H.toHypergraph.IsSeparation A B → separationOrder A B < θ
      →
      ((A, B) ∈ T ↔ ∃ (k : ℕ) (C : Fin k → Drawing S),
        (∀ i : Fin k, (C i).IsCircuit ∧ (C i).IsSubdrawing K ∧ (C i).length < 2 * θ ∧
          (C i).V ∩ H.V ⊆ (A ∩ B).vertexSet) ∧ ∀ e ∈ A.edgeSet, ∃ i : Fin k, e ⊆ ins (C i)))
    {X : Set S} (hXV : X ⊆ H.V) (hXθ : X.ncard ≤ θ) {C : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing K) (hl : C.length < 2 * θ) (hlX : C.length < 2 * (X ∩ ins C).ncard) :
    ∃ A B, (A, B) ∈ T ∧ separationOrder A B < X.ncard ∧ X ⊆ A.vertexSet := by
  classical
  have hXfin : X.Finite := H.finite_V.subset hXV
  have hmem := hd C hC hCs hl
  set A₀ := (PaintingOrDrawing.drawing H).inter (ins C) with hA₀
  set B := (PaintingOrDrawing.drawing H).interOutside (ins C) with hB
  have hsep : H.toHypergraph.IsSeparation A₀ B := hResp.2.1.isSeparation hmem.2.2
  let A : Hypergraph S (Set S) :=
    { vertexSet := A₀.vertexSet ∪ X
      edgeSet := A₀.edgeSet
      Inc := A₀.Inc
      vertex_mem_of_inc := fun _ _ h ↦ Or.inl (A₀.vertex_mem_of_inc h)
      edge_mem_of_inc := fun _ _ h ↦ A₀.edge_mem_of_inc h
      vertexSet_finite := A₀.vertexSet_finite.union hXfin
      edgeSet_finite := A₀.edgeSet_finite }
  have hVeq : A₀.vertexSet ∪ B.vertexSet = H.V := congrArg Hypergraph.vertexSet hsep.union_eq
  have hunion : A ∪ B = A₀ ∪ B := by
    refine Hypergraph.ext ?_ rfl rfl
    change (A₀.vertexSet ∪ X) ∪ B.vertexSet = A₀.vertexSet ∪ B.vertexSet
    refine subset_antisymm (union_subset (union_subset subset_union_left ?_) subset_union_right)
      (union_subset_union_left _ subset_union_left)
    rw [hVeq]
    exact hXV
  have hsepA : H.toHypergraph.IsSeparation A B :=
    { left_le := ⟨union_subset hsep.left_le.vertexSet_subset hXV, hsep.left_le.edgeSet_subset,
        hsep.left_le.ends_eq⟩
      right_le := hsep.right_le
      union_eq := hunion.trans hsep.union_eq
      edgeSet_inter_eq := hsep.edgeSet_inter_eq }
  have hfr : frontier (ins C) = C.U := by rw [subBd_eq_frontier', hs.subBd_eq C hC hCs hl]
  have hcl : IsClosed (ins C) := hmem.1.isClosed
  have hcompl : (univ \ ins C : Set S) = (ins C)ᶜ := by ext; simp
  have hUin : C.U ⊆ ins C := fun z hz ↦ hcl.frontier_subset (hfr ▸ hz)
  have hbd : ∀ v, v ∈ H.V → v ∈ ins C → v ∈ B.vertexSet → v ∈ C.V := by
    intro v hvH hvi hvB
    have hvc : v ∈ closure (ins C)ᶜ := by
      have := hvB.2
      rwa [hcompl] at this
    have : v ∈ frontier (ins C) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hvi, hvc⟩
    exact mem_V_of_mem_U_sub hCs (hfr ▸ this) (hP.2.1 hvH)
  have hsub : (A ∩ B).vertexSet ⊆ (C.V ∩ H.V) ∪ (X \ ins C) := by
    rintro v ⟨hvA, hvB⟩
    have hvH : v ∈ H.V := hsepA.right_le.vertexSet_subset hvB
    by_cases hvi : v ∈ ins C
    · exact Or.inl ⟨hbd v hvH hvi hvB, hvH⟩
    · rcases hvA with hvA | hvX
      · exact absurd hvA.2 hvi
      · exact Or.inr ⟨hvX, hvi⟩
  have hord : separationOrder A B ≤ (C.V ∩ H.V).ncard + (X \ ins C).ncard :=
    (ncard_le_ncard hsub (((H.finite_V.subset inter_subset_right)).union
      (hXfin.subset sdiff_subset))).trans (ncard_union_le _ _)
  have hlen := (circuit_length_eq_two_mul_ncard hP hC hCs).1
  have hsum : (X ∩ ins C).ncard + (X \ ins C).ncard = X.ncard :=
    ncard_inter_add_ncard_sdiff_eq_ncard X (ins C) hXfin
  have hlt : separationOrder A B < X.ncard := by omega
  refine ⟨A, B, ?_, hlt, subset_union_right⟩
  refine (hiff A B hsepA (by omega)).mpr ⟨1, fun _ ↦ C, fun _ ↦ ⟨hC, hCs, hl, ?_⟩, fun e he ↦
    ⟨0, he.2⟩⟩
  rintro v ⟨hvC, hvH⟩
  have hvU : v ∈ C.U := C.V_subset_U hvC
  refine ⟨Or.inl ⟨hvH, hUin hvU⟩, hvH, ?_⟩
  have hvf : v ∈ frontier (ins C) := hfr.symm ▸ hvU
  rw [frontier_eq_closure_inter_closure] at hvf
  change v ∈ closure (univ \ ins C)
  rw [hcompl]
  exact hvf.2

/-- The core of (15.1). Let `G` be a subdrawing of the radial drawing whose vertices in `H` lie in a
set `Z` with `|Z| < |X|`. Every circuit of `G` is then short, since `Γ*` is bipartite. Suppose that
each `x ∈ X \ Z` is inside a circuit of `G`. Then some circuit of `G` has the second property of
(15.1). If a circuit of `G` with maximal inside has `w` strictly inside, it is that circuit, since
its inside includes `X`. Otherwise the maximal circuits with `w` inside go through `w`, and meet
only
there by (4.3) of XI, and a count of the vertices of `H` on them finds the circuit. -/
theorem exists_circuit_of_confined_in (hS : IsClosedSurface S) {H K G : Drawing S} {θ : ℕ}
    {ins : Drawing S → Set S} (hP : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    (hs : IsSlope K (2 * θ) ins) {r : Set S} (hr : r ∈ H.R) {w : S} (hw : w ∈ r) (hwV : w ∈ K.V)
    {X : Set S} (hXV : X ⊆ H.V) (hXr : X ⊆ closure r) (hXθ : X.ncard ≤ θ) (hGK : G.IsSubdrawing K)
    {Z : Set S} (hZfin : Z.Finite) (hGZ : ∀ v ∈ G.V, v ∈ H.V → v ∈ Z) (hZX : Z.ncard < X.ncard)
    (hcov : ∀ x ∈ X, x ∉ Z → ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing G ∧ x ∈ ins D) :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing G ∧ C.length < 2 * θ ∧
      C.length < 2 * (X ∩ ins C).ncard ∧ w ∈ ins C := by
  classical
  have hXfin : X.Finite := H.finite_V.subset hXV
  have hrc : IsPreconnected r := region_isPreconnected hr
  have hlen : ∀ D : Drawing S, D.IsCircuit → D.IsSubdrawing G → D.length = 2 * (D.V ∩ H.V).ncard :=
    fun D hD hDs ↦ (circuit_length_eq_two_mul_ncard hP hD (hDs.trans hGK)).1
  have hZsub : ∀ D : Drawing S, D.IsSubdrawing G → (D.V ∩ H.V).ncard ≤ Z.ncard := fun D hDs ↦
    ncard_le_ncard (fun v hv ↦ hGZ v (hDs.1 hv.1) hv.2) hZfin
  have hconf : IsConfined (2 * θ) G := by
    intro D hD hDs
    have := hlen D hD hDs
    have := hZsub D hDs
    omega
  let 𝒞 : Set (Drawing S) := {D | D.IsCircuit ∧ D.IsSubdrawing G}
  have h𝒞fin : 𝒞.Finite := by
    refine Set.Finite.of_injOn (f := fun D : Drawing S ↦ (D.V, D.E))
      (t := 𝒫 G.V ×ˢ 𝒫 G.E) ?_ ?_ (G.finite_V.finite_subsets.prod G.finite_edges.finite_subsets)
    · exact fun D hD ↦ ⟨hD.2.1, hD.2.2⟩
    · intro D _ D' _ h
      exact Drawing.ext_of_V_E (congrArg Prod.fst h) (congrArg Prod.snd h)
  let 𝓜 : Set (Drawing S) := {D | D ∈ 𝒞 ∧ ∀ D' ∈ 𝒞, ins D ⊆ ins D' → ins D' ⊆ ins D}
  have h𝓜fin : 𝓜.Finite := h𝒞fin.subset fun _ h ↦ h.1
  have hmaxex : ∀ D ∈ 𝒞, ∃ M ∈ 𝓜, ins D ⊆ ins M := by
    intro D hD
    obtain ⟨m, hle, hm⟩ := (h𝒞fin.image ins).exists_le_maximal (mem_image_of_mem ins hD)
    obtain ⟨M, hM, rfl⟩ := hm.1
    exact ⟨M, ⟨hM, fun D' hD' h ↦ hm.2 (mem_image_of_mem ins hD') h⟩, hle⟩
  have hshort : ∀ M ∈ 𝒞, (M : Drawing S).length < 2 * θ := fun M hM ↦ hconf M hM.1 hM.2
  have hsK : ∀ M ∈ 𝒞, (M : Drawing S).IsSubdrawing K := fun M hM ↦ hM.2.trans hGK
  by_cases hcase : ∃ M ∈ 𝓜, w ∈ ins M ∧ w ∉ (M : Drawing S).U
  · obtain ⟨M, hM, hwi, hwU⟩ := hcase
    have hsub := closure_subset_ins hs hM.1.1 (hsK M hM.1) (hshort M hM.1) hrc hw hwi
      (disjoint_region_U hS hP hr hw hwV (hsK M hM.1) hwU)
    have hXi : X ∩ ins M = X := inter_eq_left.mpr (hXr.trans hsub)
    refine ⟨M, hM.1.1, hM.1.2, hshort M hM.1, ?_, hwi⟩
    rw [hXi, hlen M hM.1.1 hM.1.2]
    have := hZsub M hM.1.2
    omega
  push Not at hcase
  have hUin : ∀ M ∈ 𝒞, (M : Drawing S).U ⊆ ins M := fun M hM ↦
    hs.U_subset_ins hM.1 (hsK M hM) (hshort M hM)
  have hwH : w ∉ H.U := region_subset hr hw
  let Mb : Finset (Drawing S) := h𝓜fin.toFinset.filter fun M ↦ w ∈ ins M
  have hMb : ∀ {M : Drawing S}, M ∈ Mb ↔ M ∈ 𝓜 ∧ w ∈ ins M := by
    intro M
    simp [Mb]
  let vv : Drawing S → Finset S := fun M ↦ H.finite_V.toFinset.filter (· ∈ M.V)
  have hvv : ∀ M : Drawing S, (vv M).card = (M.V ∩ H.V).ncard := by
    intro M
    rw [← ncard_coe_finset]
    congr 1
    ext y
    simp [vv, and_comm]
  have hmemvv : ∀ {M : Drawing S} {y : S}, y ∈ vv M ↔ y ∈ H.V ∧ y ∈ M.V := by
    intro M y
    simp [vv]
  let xx : Drawing S → Finset S := fun M ↦ hXfin.toFinset.filter (· ∈ ins M)
  have hxx : ∀ M : Drawing S, (xx M).card = (X ∩ ins M).ncard := by
    intro M
    rw [← ncard_coe_finset]
    congr 1
    ext y
    simp [xx]
  let X0 : Finset S := hXfin.toFinset.filter fun x ↦ ∀ M ∈ Mb, x ∉ ins M
  have hX0Z : ∀ x ∈ X0, x ∈ Z := by
    intro x hx
    have hxX : x ∈ X := by simpa using (Finset.mem_filter.mp hx).1
    have hx0 := (Finset.mem_filter.mp hx).2
    by_contra hxZ
    obtain ⟨D, hD, hDs, hxD⟩ := hcov x hxX hxZ
    obtain ⟨M, hM, hsub⟩ := hmaxex D ⟨hD, hDs⟩
    have hxM := hsub hxD
    have hwM : w ∉ ins M := fun h ↦ hx0 M (hMb.mpr ⟨hM, h⟩) hxM
    have hwU : w ∉ (M : Drawing S).U := fun h ↦ hwM (hUin M hM.1 h)
    have hxU := mem_U_of_mem_closure hs hM.1.1 (hsK M hM.1) (hshort M hM.1) hrc hw hwM
      (disjoint_region_U hS hP hr hw hwV (hsK M hM.1) hwU) (hXr hxX) hxM
    exact hxZ (hGZ x (hM.1.2.1 (mem_V_of_mem_U_sub (hsK M hM.1) hxU (hP.2.1 (hXV hxX)))) (hXV hxX))
  have hpd : ∀ M ∈ Mb, ∀ M' ∈ Mb, M ≠ M' → Disjoint (vv M) (vv M') := by
    intro M hM M' hM' hne
    refine Finset.disjoint_left.mpr fun a ha ha' ↦ hne ?_
    obtain ⟨hm, hwi⟩ := hMb.mp hM
    obtain ⟨hm', hwi'⟩ := hMb.mp hM'
    have hwM := mem_V_of_mem_U_sub (hsK M hm.1) (hcase M hm hwi) hwV
    have hwM' := mem_V_of_mem_U_sub (hsK M' hm'.1) (hcase M' hm' hwi') hwV
    obtain ⟨haH, haM⟩ := hmemvv.mp ha
    obtain ⟨-, haM'⟩ := hmemvv.mp ha'
    have haw : a ≠ w := fun h ↦ hwH (h ▸ H.V_subset_U haH)
    have hsk := fun (M₁ : Drawing S) (hm₁ : M₁ ∈ 𝓜) ↦ fun C' hC' hC's ↦ hm₁.2 C' ⟨hC', hC's⟩
    have h₁ : ins M' ⊆ ins M := ins_subset_of_two_common hs hGK hconf hm.1.1 hm.1.2 (hsk M hm)
      hm'.1.1 hm'.1.2 haM haM' hwM hwM' haw
    exact eq_of_ins_eq hs hm.1.1 (hsK M hm.1) (hshort M hm.1) hm'.1.1 (hsK M' hm'.1)
      (hshort M' hm'.1) (subset_antisymm (hm'.2 M hm.1 h₁) h₁)
  have hdisj : Disjoint (Mb.biUnion vv) X0 := by
    refine Finset.disjoint_left.mpr fun a ha ha₀ ↦ ?_
    obtain ⟨M, hM, haM⟩ := Finset.mem_biUnion.mp ha
    have hm := (hMb.mp hM).1
    exact (Finset.mem_filter.mp ha₀).2 M hM
      (hUin M hm.1 ((M : Drawing S).V_subset_U (hmemvv.mp haM).2))
  have hsubZ : Mb.biUnion vv ∪ X0 ⊆ hZfin.toFinset := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨M, hM, haM⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨haH, haV⟩ := hmemvv.mp haM
      simpa using hGZ a ((hMb.mp hM).1.1.2.1 haV) haH
    · simpa using hX0Z a ha
  have hc1 : ∑ M ∈ Mb, (vv M).card + X0.card ≤ hZfin.toFinset.card := by
    rw [← Finset.card_biUnion hpd, ← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsubZ
  have hc2 : hXfin.toFinset.card ≤ X0.card + ∑ M ∈ Mb, (xx M).card := by
    have hsub : hXfin.toFinset ⊆ X0 ∪ Mb.biUnion xx := by
      intro x hx
      by_cases h : ∀ M ∈ Mb, x ∉ ins M
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
      · push Not at h
        obtain ⟨M, hM, hxM⟩ := h
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨M, hM, Finset.mem_filter.mpr ⟨hx,
          hxM⟩⟩)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hZc : hZfin.toFinset.card < hXfin.toFinset.card := by
    rw [← ncard_eq_toFinset_card _ hZfin, ← ncard_eq_toFinset_card _ hXfin]
    exact hZX
  have hlt : ∑ M ∈ Mb, (vv M).card < ∑ M ∈ Mb, (xx M).card := by omega
  obtain ⟨M, hM, hltM⟩ := Finset.exists_lt_of_sum_lt hlt
  obtain ⟨hm, hwi⟩ := hMb.mp hM
  refine ⟨M, hm.1.1, hm.1.2, hshort M hm.1, ?_, hwi⟩
  rw [hlen M hm.1.1 hm.1.2, ← hxx, ← hvv]
  omega

/-- `exists_circuit_of_confined_in`, with the circuit read in the radial drawing. -/
theorem exists_circuit_of_confined (hS : IsClosedSurface S) {H K G : Drawing S} {θ : ℕ}
    {ins : Drawing S → Set S} (hP : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K)
    (hs : IsSlope K (2 * θ) ins) {r : Set S} (hr : r ∈ H.R) {w : S} (hw : w ∈ r) (hwV : w ∈ K.V)
    {X : Set S} (hXV : X ⊆ H.V) (hXr : X ⊆ closure r) (hXθ : X.ncard ≤ θ) (hGK : G.IsSubdrawing K)
    {Z : Set S} (hZfin : Z.Finite) (hGZ : ∀ v ∈ G.V, v ∈ H.V → v ∈ Z) (hZX : Z.ncard < X.ncard)
    (hcov : ∀ x ∈ X, x ∉ Z → ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing G ∧ x ∈ ins D) :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ ∧
      C.length < 2 * (X ∩ ins C).ncard ∧ w ∈ ins C := by
  obtain ⟨C, h₁, h₂, h₃⟩ := exists_circuit_of_confined_in hS hP hs hr hw hwV hXV hXr hXθ hGK hZfin
    hGZ hZX hcov
  exact ⟨C, h₁, h₂.trans hGK, h₃⟩

/-- **Graph Minors XIX, (15.1)** (page 379), for a respectful tangle of order `θ`.

"Let $\Gamma$ be a 2-cell drawing with $E(\Gamma) \ne
\emptyset$ in a surface $\Sigma$ with
$\text{bd}(\Sigma) = \emptyset$, and let $\mathscr{T}$ be a tangle in $\Gamma$ with
$\text{rep}(\mathscr{T}) \ge \theta$. Let $r$ be a region of $\Gamma$, and let $X \subseteq
V(\Gamma) \cap \bar{r}$ with $|X| \le \theta$. Then the following are equivalent:" the existence of
`(A, B) ∈ 𝒯` of order `< |X|` with `X ⊆ V(A)`, and the existence of a circuit `C` of `Γ*` of length
`< 2θ` such that `|X ∩ ins(C)| > ½|E(C)|` and `r* ∈ ins(C)`.

The Lean statement takes a respectful tangle of order exactly `θ` and its derived slope.
The radial vertex `w` represents the region `r`. With the paper's representativity bound, the
order-`θ` truncation retains the separations of order below `θ`. These include the orientations
that determine the inside of each circuit of length below `2 * θ` in Section 7. -/
theorem theorem_15_1_proof (hS : IsClosedSurface S) [ConnectedSpace S]
    {H K : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S} (hE : H.E.Nonempty) (hResp : IsRespectfulDrawingTangle H θ T)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins) {r : Set S} (hr : r ∈ H.R) {w : S}
    (hw : w ∈ r) (hwV : w ∈ K.V) {X : Set S} (hXV : X ⊆ H.V) (hXr : X ⊆ closure r)
    (hXθ : X.ncard ≤ θ) :
    (∃ A B, (A, B) ∈ T ∧ separationOrder A B < X.ncard ∧ X ⊆ A.vertexSet) ↔
      ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ ∧
        C.length < 2 * (X ∩ ins C).ncard ∧ w ∈ ins C := by
  classical
  have hP := hK.2.1
  have hs : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hResp.2.1.isPretangle hP.1 hd
  have hiff := (GM11.theorem_6_3_proof S hS inferInstance (PaintingOrDrawing.drawing H) K θ T ins
    hResp.1 hE
    hResp.2.1.isPretangle hResp.2.2 hK hd).1
  constructor
  · rintro ⟨A, B, hAB, hord, hXA⟩
    have hsep : H.toHypergraph.IsSeparation A B := hResp.2.1.isSeparation hAB
    obtain ⟨n, Cs, hCs, hcov⟩ := (hiff A B hsep (hResp.2.1.order_lt hAB)).mp hAB
    set G : Drawing S := K.span (⋃ i, (Cs i).V) (⋃ i, (Cs i).E) with hG
    have hGK : G.IsSubdrawing K :=
      ⟨K.spanV_subset _ _, by rw [hG, K.span_E]; exact inter_subset_right⟩
    have hCG : ∀ i, (Cs i).IsSubdrawing G := fun i ↦
      ⟨fun v hv ↦ Or.inl ⟨mem_iUnion.mpr ⟨i, hv⟩, (hCs i).2.1.1 hv⟩, fun e he ↦ by
        rw [hG, K.span_E]
        exact ⟨mem_iUnion.mpr ⟨i, he⟩, (hCs i).2.1.2 he⟩⟩
    refine exists_circuit_of_confined hS hP hs hr hw hwV hXV hXr hXθ hGK
      (Z := (A ∩ B).vertexSet) (A ∩ B).vertexSet_finite ?_ hord ?_
    · rintro v (⟨hv, -⟩ | hv) hvH
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
        exact (hCs i).2.2.2 ⟨hi, hvH⟩
      · obtain ⟨e, he, hve⟩ := mem_iUnion₂.mp hv
        obtain ⟨i, hi⟩ := mem_iUnion.mp he.1
        exact (hCs i).2.2.2 ⟨end_mem_V (hCs i).2.1 hi hve.1 hve.2, hvH⟩
    · intro x hxX hxZ
      have hxB : x ∉ B.vertexSet := fun h ↦ hxZ ⟨hXA hxX, h⟩
      obtain ⟨e, he, hxe⟩ := exists_edge_at_vertex_of_twoCell hS hResp.1 hE (hXV hxX)
      have hinc : (A ∪ B).Inc e x := by
        rw [hsep.union_eq]
        exact ⟨he, hXV hxX, hxe⟩
      rcases hinc with h | h
      · obtain ⟨i, hi⟩ := hcov e (A.edge_mem_of_inc h)
        have hclosed : IsClosed (ins (Cs i)) :=
          (hs.isClosedDisc _ (hCs i).1 (hCs i).2.1 (hCs i).2.2.1).isClosed
        exact ⟨Cs i, (hCs i).1, hCG i, closure_minimal hi hclosed hxe⟩
      · exact absurd (B.vertex_mem_of_inc h) hxB
  · rintro ⟨C, hC, hCs, hl, hlX, -⟩
    exact exists_separation_of_circuit hS hResp hP hs hd hiff hXV hXθ hC hCs hl hlX

end GraphMinor.GM19

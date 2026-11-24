/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section7b
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM11.Section6Pretangle

/-!
# A short circuit around each edge of a painting

Let `e` be an edge of `Γ`, and let `s` be the region of `Γ*` that contains `e`. The hypergraph `Γ`
has the
separation that splits off `e` with its ends. It has order at most 3, and the tangle holds it with
`e` on
the small side, by the third tangle axiom. The result of this file is
`TangleDatum.exists_circuit_around`:
some circuit of `Γ*` of length at most 6 has `s` in its inside. The proof is the proof of (6.3) of
Graph
Minors XI.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

theorem _root_.GraphMinor.GM10.IsTangle.toPretangle {α β : Type*} {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (h : IsTangle G θ T) : IsPretangle G θ T :=
  ⟨h.one_le, h.isSeparation, h.order_lt, h.axiom1, h.axiom2⟩

/-- The subhypergraph of `Γ` obtained by deleting the edge `g`, and keeping all vertices. -/
def Painting.deleteEdge (Γ : Painting S) (g : Set S) : Hypergraph S (Set S) where
  vertexSet := Γ.V
  edgeSet := Γ.E \ {g}
  Inc e v := (e ∈ Γ.E \ {g}) ∧ v ∈ Γ.V ∧ v ∈ tilde e
  vertex_mem_of_inc _ _ h := h.2.1
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := Γ.finite_V
  edgeSet_finite := Γ.finite_edges.subset sdiff_subset

omit [T2Space S] in
theorem Painting.deleteEdge_le (Γ : Painting S) (g : Set S) : Γ.deleteEdge g ≤ Γ.toHypergraph where
  vertexSet_subset := subset_rfl
  edgeSet_subset _ he := he.1
  ends_eq _ he := by
    ext v
    exact ⟨fun h ↦ ⟨he, h.2.1, h.2.2⟩, fun h ↦ ⟨he.1, h.2.1, h.2.2⟩⟩

omit [T2Space S] in
/-- An edge `e` of `Γ` lies in `closure g` only if it is `g`. -/
theorem Painting.eq_of_subset_closure (Γ : Painting S) {e g : Set S} (he : e ∈ Γ.E) (hg : g ∈ Γ.E)
    (hsub : e ⊆ closure g) : e = g := by
  obtain ⟨x, hx⟩ := he.1
  have hxg : x ∈ g := by
    by_contra hn
    exact Γ.disjoint_V he hx (Γ.tilde_subset_V hg ⟨hsub hx, hn⟩)
  exact arcComp_eq_of_mem he hg hx hxg

omit [T2Space S] in
/-- The separation of `Γ` that splits off the edge `g`. -/
theorem Painting.isSeparation_edge (Γ : Painting S) {g : Set S} (hg : g ∈ Γ.E) :
    Γ.toHypergraph.IsSeparation (Γ.restrict (closure g)) (Γ.deleteEdge g) ∧
      (Γ.restrict (closure g) ∩ Γ.deleteEdge g).vertexSet = tilde g := by
  have hcl : ∀ {x}, x ∈ Γ.V → x ∈ closure g → x ∈ tilde g := fun hx hc ↦
    ⟨hc, fun hxg ↦ Γ.disjoint_V hg hxg hx⟩
  constructor
  · rw [isSeparation_iff_of_le (Γ.restrict_le _) (Γ.deleteEdge_le g)]
    refine ⟨?_, ?_, ?_⟩
    · exact Subset.antisymm (union_subset inter_subset_left subset_rfl) subset_union_right
    · apply Subset.antisymm
      · exact union_subset (Γ.restrict_le _).edgeSet_subset (Γ.deleteEdge_le g).edgeSet_subset
      · intro e he
        by_cases heg : e = g
        · subst heg
          exact Or.inl ⟨he, subset_closure, fun x hx ↦ hx.1.1⟩
        · exact Or.inr ⟨he, heg⟩
    · refine eq_empty_of_forall_notMem ?_
      rintro e ⟨⟨he, hsub, -⟩, -, hn⟩
      exact hn (Γ.eq_of_subset_closure he hg hsub)
  · ext x
    constructor
    · rintro ⟨⟨hx, hc⟩, -⟩
      exact hcl hx hc
    · intro hx
      have hV := Γ.tilde_subset_V hg hx
      exact ⟨⟨hV, hx.1⟩, hV⟩

omit [T2Space S] in
theorem Painting.ncard_tilde_le (Γ : Painting S) {g : Set S} (hg : g ∈ Γ.E) : (tilde g).ncard ≤ 3
  := by
  rcases Γ.size_cases hg with h | h <;> omega

omit [T2Space S] [T2Space Shat] in
/-- `Γ*` is bipartite. -/
theorem RadialDrawing.bipartite {Γ : Painting S} (rad : RadialDrawing cap Γ) {D : Drawing Shat}
    (hV : D.V = Γ.hatV cap) : ∀ e x y, rad.G.toGraph.IsLink e x y → (x ∈ D.V ↔ y ∉ D.V) := by
  rw [hV]
  intro e x y hl
  obtain ⟨v, hv, w, ⟨-, hw⟩, hcap⟩ := rad.isPreRadial.2.2.2.2.1 e hl.1
  have heq : ({x, y} : Set Shat) = {v, w} := hl.2.2.2.symm.trans hcap
  have hx : x ∈ ({v, w} : Set Shat) := heq ▸ mem_insert x _
  have hy : y ∈ ({v, w} : Set Shat) := heq ▸ mem_insert_of_mem x rfl
  have hv' : v ∈ ({x, y} : Set Shat) := heq ▸ mem_insert v _
  have hw' : w ∈ ({x, y} : Set Shat) := heq ▸ mem_insert_of_mem v rfl
  rcases hx with rfl | rfl
  · rcases hw' with rfl | rfl
    · exact absurd hv hw
    · exact ⟨fun _ ↦ hw, fun _ ↦ hv⟩
  · rcases hy with rfl | rfl
    · exact ⟨fun h ↦ absurd h hw, fun h ↦ absurd hv h⟩
    · rcases hv' with rfl | rfl <;> exact absurd hv hw

namespace TangleDatum

/-- The inside of a short circuit `C` of `Γ*` gives a member of the tangle whose middle lies in
`tilde g`, if the vertices of `Γ` on `C` lie in `tilde g`. -/
theorem ins_middle (D : TangleDatum cap χ) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
    (hlt : C.E.ncard < 2 * D.rep) {g : Set S}
    (hV : ∀ v ∈ D.P.Γ.V, cap.emb v ∈ C.V → v ∈ tilde g) :
    ∀ v ∈ (D.P.Γ.restrict (cap.emb ⁻¹' D.ins C) ∩
      D.P.Γ.restrict (cap.emb ⁻¹' closure (D.ins C)ᶜ)).vertexSet, v ∈ tilde g := by
  have : ConnectedSpace Shat := cap.connected
  have hi := D.ins_spec hC hlt
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  intro v hv
  have hvU := (disc_facts hS h3 D.rad hC hi.2.2.1 hi.2.2.2.1).2.1 v hv
  have hvV : v ∈ D.P.Γ.V := hv.1.1
  refine hV v hvV (mem_V_of_mem_U hC.1 hvU ?_)
  exact D.rad.isPreRadial.2.1 (mem_image_of_mem _ hvV)

omit [T2Space S] [T2Space Shat] in
/-- An edge of `Γ` in the inside of a circuit is an edge of the part of `Γ` there. -/
theorem edge_mem_ins (D : TangleDatum cap χ) {e : Set S} (he : e ∈ D.P.Γ.E) {Δ : Set Shat}
    (hΔ : IsClosed Δ) (h : cap.emb '' e ⊆ Δ) :
    e ∈ (D.P.Γ.restrict (cap.emb ⁻¹' Δ)).edgeSet := by
  refine ⟨he, fun x hx ↦ h (mem_image_of_mem _ hx), fun v hv ↦ ?_⟩
  have h₁ : cap.emb v ∈ closure (cap.emb '' e) :=
    image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hv.1.1)
  exact closure_minimal h hΔ h₁

/-- **The circuit around an edge.** Let `s` be the region of `Γ*` that contains the edge `g` of `Γ`.
Then
some circuit of `Γ*` of length at most 6 has `s` in its inside. -/
theorem exists_circuit_around (D : TangleDatum cap χ) (hrep : 4 ≤ D.rep) {g : Set S}
    (hg : g ∈ D.P.Γ.E) {s : Set Shat} (hs : s ∈ D.rad.G.R) (hgs : cap.emb '' g ⊆ s) :
    ∃ F : Drawing Shat, F.IsCircuitOf D.rad.G ∧ F.E.ncard ≤ 6 ∧ s ⊆ D.ins F := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  set Γ := D.P.Γ with hΓ
  set G := D.rad.G with hG
  have hsl : IsSlope G (2 * D.rep) D.ins := D.isSlope (by omega)
  obtain ⟨hf₁, hf₂, hf₃⟩ := D.rad.region_facts hS h3
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap Γ
  have hbip := D.rad.bipartite hSk.hV
  have hVG : Sk.V ⊆ G.V := by
    rw [hSk.hV]
    exact D.rad.isPreRadial.2.1
  have hw : IsWeighting G (2 * D.rep) Sk.V D.rep :=
    isWeighting_radial (Γ := PaintingOrDrawing.drawing Sk) (by omega) hVG hbip
  -- A vertex of `Γ` on the boundary of `s` is an end of `g`.
  have hend : ∀ {x}, x ∈ Sk.V → x ∈ closure s → ∃ v ∈ tilde g, cap.emb v = x := by
    intro x hx hcl
    rw [hSk.hV] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, ⟨hf₃ s hs g hg hgs v hv hcl, fun h ↦ Γ.disjoint_V hg h hv⟩, rfl⟩
  have hNV : ∀ {x}, x ∈ Sk.V ∩ (boundaryDrawing G {s}).V → ∃ v ∈ tilde g, cap.emb v = x := by
    rintro x ⟨hx, hxN⟩
    obtain ⟨⟨r, hr, hir⟩, -⟩ := (mem_boundaryDrawing_V hT).mp hxN
    obtain rfl : r = s := hr
    exact hend hx hir.2.2
  have hNV' : ∀ {x}, x ∈ Sk.V ∩ (boundaryDrawing G (G.R \ {s})).V →
      ∃ v ∈ tilde g, cap.emb v = x := by
    rintro x ⟨hx, hxN⟩
    obtain ⟨-, r, ⟨hr, hrZ⟩, hir⟩ := (mem_boundaryDrawing_V hT).mp hxN
    have hrs : r = s := by
      by_contra hne
      exact hrZ ⟨hr, hne⟩
    obtain rfl := hrs
    exact hend hx hir.2.2
  have hfinT : (cap.emb '' tilde g).Finite := ((Γ.tilde_subset_V hg |>.trans Subset.rfl) |>
    Γ.finite_V.subset).image _
  have hcard : (cap.emb '' tilde g).ncard ≤ 3 :=
    (ncard_image_le (Γ.finite_V.subset (Γ.tilde_subset_V hg))).trans (Γ.ncard_tilde_le hg)
  have hlt : (Sk.V ∩ (boundaryDrawing G {s}).V).ncard < D.rep := by
    refine lt_of_le_of_lt (ncard_le_ncard ?_ hfinT) (by omega)
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hNV hx
    exact mem_image_of_mem _ hv
  rcases (theorem_5_2_proof hT hsl hw (Z := {s})
    (singleton_subset_iff.mpr hs) hlt).1 with hsm | hsm
  · obtain ⟨C, hC, hCN, hl, hin⟩ := hsm.2 s rfl
    refine ⟨C, ⟨hCN.trans (Drawing.span_isSubdrawing G _ _), hC⟩, ?_, hin⟩
    have halt : ∀ e x y, C.toGraph.IsLink e x y → (x ∈ Sk.V ↔ y ∉ Sk.V) := by
      intro e x y hl'
      have hCG := hCN.trans (Drawing.span_isSubdrawing G _ _)
      refine hbip e x y ⟨hCG.2 hl'.1, hCG.1 hl'.2.1, hCG.1 hl'.2.2.1, ?_⟩
      rw [← hCG.closure_inter_V hl'.1]
      exact hl'.2.2.2
    have h₁ := IsCircuit.ncard_le hC halt
    have h₂ : (C.V ∩ Sk.V).ncard ≤ (cap.emb '' tilde g).ncard := by
      refine ncard_le_ncard ?_ hfinT
      rintro x ⟨hxC, hxS⟩
      obtain ⟨v, hv, rfl⟩ := hNV ⟨hxS, hCN.1 hxC⟩
      exact mem_image_of_mem _ hv
    omega
  exfalso
  obtain ⟨hsep, hmid⟩ := Γ.isSeparation_edge hg
  have hord : Hypergraph.separationOrder (Γ.restrict (closure g)) (Γ.deleteEdge g) < D.ord := by
    have h₁ : Hypergraph.separationOrder (Γ.restrict (closure g)) (Γ.deleteEdge g) ≤ 3 := by
      rw [Hypergraph.separationOrder, hmid]
      exact Γ.ncard_tilde_le hg
    have h₂ := (tangleRep_spec D.rad D.ord D.𝒯).1
    change D.rep ≤ D.ord at h₂
    omega
  have hAB : (Γ.restrict (closure g), Γ.deleteEdge g) ∈ D.𝒯 := by
    rcases D.isTangle.axiom1 hsep hord with h | h
    · exact h
    · exact (D.isTangle.axiom3 h rfl).elim
  -- The region of each other edge has a circuit around it.
  have hcirc : ∀ e : Set S, e ∈ Γ.E \ {g} → ∃ C : Drawing Shat, C.IsCircuitOf G ∧
      C.E.ncard < 2 * D.rep ∧ (∀ v ∈ Γ.V, cap.emb v ∈ C.V → v ∈ tilde g) ∧
      cap.emb '' e ⊆ D.ins C := by
    rintro e ⟨he, heg⟩
    have hoff : Disjoint (cap.emb '' e) G.U := disc_edge_disjoint D.rad ⟨subset_rfl, subset_rfl⟩ he
    obtain ⟨x, hx⟩ := he.1
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem
      (disjoint_left.mp hoff (mem_image_of_mem _ hx))
    have her : cap.emb '' e ⊆ r := subset_region hr (he.2.2.1.isConnected.isPreconnected.image _
      cap.isEmbedding.continuous.continuousOn) hoff (mem_image_of_mem _ hx) hxr
    have hrs : r ≠ s := fun h ↦ heg (hf₂ s hs e he g hg (h ▸ her) hgs)
    obtain ⟨C, hC, hCN, hl, hin⟩ := hsm.2 r ⟨hr, hrs⟩
    refine ⟨C, ⟨hCN.trans (Drawing.span_isSubdrawing G _ _), hC⟩, hl, fun v hv hvC ↦ ?_,
      her.trans hin⟩
    have hvS : cap.emb v ∈ Sk.V := by
      rw [hSk.hV]
      exact mem_image_of_mem _ hv
    obtain ⟨v', hv', hvv⟩ := hNV' ⟨hvS, hCN.1 hvC⟩
    obtain rfl := cap.isEmbedding.injective hvv
    exact hv'
  have : Nonempty (Drawing Shat) := ⟨G⟩
  choose! C hC using hcirc
  let sepOf : Set S → Hypergraph S (Set S) × Hypergraph S (Set S) := fun e ↦
    (Γ.restrict (cap.emb ⁻¹' D.ins (C e)), Γ.restrict (cap.emb ⁻¹' closure (D.ins (C e))ᶜ))
  let L : List (Hypergraph S (Set S) × Hypergraph S (Set S)) :=
    (Γ.restrict (closure g), Γ.deleteEdge g) ::
      ((Γ.finite_edges.subset (sdiff_subset (t := {g}))).toFinset.toList.map sepOf)
  have hmem : ∀ {e}, e ∈ Γ.E \ {g} → sepOf e ∈ L := fun he ↦
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, Finset.mem_toList.mpr
      ((Set.Finite.mem_toFinset _).mpr he), rfl⟩)
  have hspec : ∀ {e}, e ∈ Γ.E \ {g} → IsInsOf D.rad D.ord D.𝒯 (C e) (D.ins (C e)) := fun he ↦
    D.ins_spec (hC _ he).1 (hC _ he).2.1
  refine theorem_6_2_proof D.isTangle.toPretangle hAB L ?_ ?_ ?_ ?_
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hAB
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
      have he' : e ∈ Γ.E \ {g} := (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp he)
      exact (hspec he').2.2.2.2
  · intro p hp x hx
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hx
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
      have he' : e ∈ Γ.E \ {g} := (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp he)
      rw [hmid]
      exact D.ins_middle (hC _ he').1 (hC _ he').2.1 (hC _ he').2.2.1 x hx
  · intro v hv
    by_cases hvg : v ∈ tilde g
    · exact ⟨_, List.mem_cons_self .., ⟨hv, hvg.1⟩⟩
    obtain ⟨c, hc, hvc⟩ := exists_edge_incident hS h3 D.rad hv
    have hcg : c ≠ g := fun h ↦ hvg ⟨h ▸ hvc, fun hxg ↦ Γ.disjoint_V hg hxg hv⟩
    have hc' : c ∈ Γ.E \ {g} := ⟨hc, hcg⟩
    refine ⟨_, hmem hc', hv, ?_⟩
    have h₁ : cap.emb v ∈ closure (cap.emb '' c) :=
      image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hvc)
    exact closure_minimal (hC _ hc').2.2.2 (hspec hc').2.2.1.isClosed h₁
  · intro e he
    exact ⟨_, hmem he, D.edge_mem_ins he.1 (hspec he).2.2.1.isClosed (hC _ he).2.2.2⟩

end TangleDatum

end GraphMinor.GM19

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.AnnulusRural
public import LeanPool.GraphMinor.GM14.DiscSlope

/-!
# Cutting a drawing along a circuit

Let `Y` be a drawing of a graph `A`, and let `C` be a circuit of `A` that is the boundary of a
closed
disc `E`. Each edge off `C` is inside `E` or outside `E`. This gives a separation of `A` with common
vertices `V(C)` (`exists_cut`). The edges of `C` go inside, except for a set `T` of them that we are
free to choose. This is the separation `(A, B)` of the proof of (8.4), page 42.

`exists_cut_society` then writes a society as the two compositions that the paper uses.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11
  GraphMinor.GM06

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]
variable {A C : Graph α β} {Y : GraphDrawing A S} {ν : α → S}

omit [T2Space S] in
theorem inj_of_drawing (hν : ∀ v : V(A), (Y.iso.vertexEquiv v).1 = ν v.1) : InjOn ν V(A) := by
  intro a ha b hb hab
  have h : (Y.iso.vertexEquiv ⟨a, ha⟩).1 = (Y.iso.vertexEquiv ⟨b, hb⟩).1 :=
    (hν ⟨a, ha⟩).trans (hab.trans (hν ⟨b, hb⟩).symm)
  exact congrArg Subtype.val (Y.iso.vertexEquiv.injective (Subtype.ext h))

omit [T2Space S] in
theorem mem_V_of_drawing (hν : ∀ v : V(A), (Y.iso.vertexEquiv v).1 = ν v.1) {v : α}
    (hv : v ∈ V(A)) : ν v ∈ Y.drawing.V := by
  rw [← hν ⟨v, hv⟩]
  exact (Y.iso.vertexEquiv ⟨v, hv⟩).2

omit [T2Space S] in
theorem edge_mem_of_drawing {e : β} (he : e ∈ E(A)) : graphDrawingEdgeSet Y e ∈ Y.drawing.E := by
  rw [graphDrawingEdgeSet_eq Y he]
  exact (Y.iso.edgeEquiv ⟨e, he⟩).2

omit [T2Space S] in
theorem ends_of_drawing (hν : ∀ v : V(A), (Y.iso.vertexEquiv v).1 = ν v.1) {e : β} {a b : α}
    (hl : A.IsLink e a b) : closure (graphDrawingEdgeSet Y e) ∩ Y.drawing.V = {ν a, ν b} := by
  have h := (Y.iso.isLink_iff ⟨e, hl.edge_mem⟩ ⟨a, hl.left_mem⟩ ⟨b, hl.right_mem⟩).mp hl
  rw [graphDrawingEdgeSet_eq Y hl.edge_mem, ← hν ⟨a, hl.left_mem⟩, ← hν ⟨b, hl.right_mem⟩]
  exact h.2.2.2

omit [T2Space S] in
theorem mem_subgraphU_iff (hν : ∀ v : V(A), (Y.iso.vertexEquiv v).1 = ν v.1) (hC : C ≤ A) {v : α}
    (hv : v ∈ V(A)) : ν v ∈ graphDrawingSubgraphU Y C ↔ v ∈ V(C) := by
  have hinj := inj_of_drawing hν
  constructor
  · rintro (h | h)
    · obtain ⟨w, hw, hx⟩ := mem_iUnion₂.mp h
      have hwA := hC.vertexSet_mono hw
      rw [graphDrawingVertexSet_eq_singleton Y hwA, hν ⟨w, hwA⟩] at hx
      exact hinj hv hwA hx ▸ hw
    · obtain ⟨e, he, hx⟩ := mem_iUnion₂.mp h
      obtain ⟨a, b, hl⟩ := C.exists_isLink_of_mem_edgeSet he
      have hm : ν v ∈ closure (graphDrawingEdgeSet Y e) ∩ Y.drawing.V :=
        ⟨hx, mem_V_of_drawing hν hv⟩
      rw [ends_of_drawing hν (hl.mono hC)] at hm
      rcases hm with h | h
      · exact hinj hv (hC.vertexSet_mono hl.left_mem) h ▸ hl.left_mem
      · exact hinj hv (hC.vertexSet_mono hl.right_mem) h ▸ hl.right_mem
  · intro h
    refine Or.inl (mem_iUnion₂.mpr ⟨v, h, ?_⟩)
    rw [graphDrawingVertexSet_eq_singleton Y hv, hν ⟨v, hv⟩]
    rfl

/-- An edge off the circuit is inside the disc or outside it. -/
theorem edge_sides (_hν : ∀ v : V(A), (Y.iso.vertexEquiv v).1 = ν v.1) (hS : IsClosedSurface S)
    {E' : Set S} (hE : IsClosedDisc E') (hC : C ≤ A) (hbd : discBd E' = graphDrawingSubgraphU Y C)
    {e : β} (he : e ∈ E(A)) (heC : e ∉ E(C)) :
    graphDrawingEdgeSet Y e ⊆ discInt E' ∨ Disjoint (graphDrawingEdgeSet Y e) E' := by
  have hmem := edge_mem_of_drawing (Y := Y) he
  have hpre : IsPreconnected (graphDrawingEdgeSet Y e) := hmem.2.2.1.isConnected.isPreconnected
  have hman : ∀ x : S, IsManifoldPoint x := (IsClosedSurface.isSurface hS).2.2
  have hoff : ∀ x ∈ graphDrawingEdgeSet Y e, x ∉ discBd E' := by
    intro x hx hxb
    have hxV : x ∉ Y.drawing.V := (hmem.2.1 hx).2
    rw [hbd] at hxb
    rcases hxb with h | h
    · obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp h
      have hwA := hC.vertexSet_mono hw
      rw [graphDrawingVertexSet_eq_singleton Y hwA] at hxw
      exact hxV (hxw ▸ (Y.iso.vertexEquiv ⟨w, hwA⟩).2)
    · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
      have hgA := hC.edgeSet_mono hg
      have hgm := edge_mem_of_drawing (Y := Y) hgA
      have hx' : x ∈ graphDrawingEdgeSet Y g := by
        rw [← Y.drawing.closure_diff_V hgm]
        exact ⟨hxg, hxV⟩
      have heq := Y.drawing.edge_eq_of_mem hmem hgm hx hx'
      rw [graphDrawingEdgeSet_eq Y he, graphDrawingEdgeSet_eq Y hgA] at heq
      have hne : e = g := congrArg Subtype.val (Y.iso.edgeEquiv.injective (Subtype.ext heq))
      exact heC (hne ▸ hg)
  have hsub : graphDrawingEdgeSet Y e ⊆ discInt E' ∪ E'ᶜ := by
    intro x hx
    by_cases h : x ∈ E'
    · exact Or.inl ⟨h, hoff x hx⟩
    · exact Or.inr h
  rcases hpre.subset_or_subset (hE.isOpen_discInt hman) hE.isClosed.isOpen_compl
    (disjoint_left.mpr fun x h₁ h₂ => h₂ h₁.1) hsub with h | h
  · exact Or.inl h
  · exact Or.inr (disjoint_left.mpr fun x h₁ h₂ => h h₁ h₂)

/-- See the module docstring. -/
theorem exists_cut (hν : ∀ v : V(A), (Y.iso.vertexEquiv v).1 = ν v.1) (hS : IsClosedSurface S)
    {E' : Set S} (hE : IsClosedDisc E') (hC : C ≤ A) (hbd : discBd E' = graphDrawingSubgraphU Y C)
    {T : Set β} (hT : T ⊆ E(C)) :
    ∃ I O : Graph α β, I ≤ A ∧ O ≤ A ∧ V(I) = {v ∈ V(A) | ν v ∈ E'} ∧
      V(O) = {v ∈ V(A) | ν v ∉ discInt E'} ∧ E(I) ∪ E(O) = E(A) ∧ Disjoint E(I) E(O) ∧
      (∀ e ∈ E(I), closure (graphDrawingEdgeSet Y e) ⊆ E') ∧
      (∀ e ∈ E(O), closure (graphDrawingEdgeSet Y e) ⊆ (discInt E')ᶜ) ∧
      E(C) \ T ⊆ E(I) ∧ T ⊆ E(O) ∧
      (∀ e ∈ E(O), e ∈ T ∨ ¬ graphDrawingEdgeSet Y e ⊆ E') := by
  classical
  have hman : ∀ x : S, IsManifoldPoint x := (IsClosedSurface.isSurface hS).2.2
  have hopen : IsOpen (discInt E') := hE.isOpen_discInt hman
  have hclE : IsClosed E' := hE.isClosed
  have hCbd : ∀ e ∈ E(C), closure (graphDrawingEdgeSet Y e) ⊆ discBd E' := fun e he => by
    rw [hbd]
    exact subset_union_right.trans' (subset_biUnion_of_mem
      (u := fun e => closure (graphDrawingEdgeSet Y e)) he)
  have hdisc : ∀ {P : Set S}, P ⊆ discBd E' → P ⊆ (discInt E')ᶜ := fun h x hx hxi => hxi.2 (h hx)
  have hbE : discBd E' ⊆ E' := GraphMinor.Surface.discBd_subset E'
  -- The two kinds of edge.
  let inE : Set β := {e | graphDrawingEdgeSet Y e ⊆ E' ∧ e ∉ T}
  let outE : Set β := {e | ¬ graphDrawingEdgeSet Y e ⊆ E' ∨ e ∈ T}
  have hin : ∀ e ∈ E(A), graphDrawingEdgeSet Y e ⊆ E' → closure (graphDrawingEdgeSet Y e) ⊆ E' :=
    fun e _ h => closure_minimal h hclE
  have hout : ∀ e ∈ E(A), e ∈ outE → closure (graphDrawingEdgeSet Y e) ⊆ (discInt E')ᶜ := by
    rintro e he (h | h)
    · by_cases heC : e ∈ E(C)
      · exact absurd (subset_closure.trans ((hCbd e heC).trans hbE)) h
      · rcases edge_sides hν hS hE hC hbd he heC with h' | h'
        · exact absurd (h'.trans sdiff_subset) h
        · refine closure_minimal ?_ hopen.isClosed_compl
          exact fun x hx hxi => disjoint_left.mp h' hx hxi.1
    · exact hdisc (hCbd e (hT h))
  let I : Graph α β := (A.induce {v ∈ V(A) | ν v ∈ E'}).restrict inE
  let O : Graph α β := (A.induce {v ∈ V(A) | ν v ∉ discInt E'}).restrict outE
  have hI : I ≤ A := restrict_le.trans (induce_le fun _ h => h.1)
  have hO : O ≤ A := restrict_le.trans (induce_le fun _ h => h.1)
  have hends : ∀ {e a b}, A.IsLink e a b → ν a ∈ closure (graphDrawingEdgeSet Y e) ∧
      ν b ∈ closure (graphDrawingEdgeSet Y e) := by
    intro e a b hl
    have h := ends_of_drawing hν hl
    have h₁ : ν a ∈ closure (graphDrawingEdgeSet Y e) ∩ Y.drawing.V := h.superset (mem_insert _ _)
    have h₂ : ν b ∈ closure (graphDrawingEdgeSet Y e) ∩ Y.drawing.V :=
      h.superset (mem_insert_of_mem _ rfl)
    exact ⟨h₁.1, h₂.1⟩
  have hIE : E(I) = E(A) ∩ inE := by
    ext e
    constructor
    · intro h
      exact ⟨hI.edgeSet_mono h, ((edgeSet_restrict _ _).subset h).2⟩
    · rintro ⟨he, hin'⟩
      obtain ⟨a, b, hl⟩ := A.exists_isLink_of_mem_edgeSet he
      have hc := hin e he hin'.1
      obtain ⟨h₁, h₂⟩ := hends hl
      have : I.IsLink e a b := ⟨hin', hl, ⟨hl.left_mem, hc h₁⟩, ⟨hl.right_mem, hc h₂⟩⟩
      exact this.edge_mem
  have hOE : E(O) = E(A) ∩ outE := by
    ext e
    constructor
    · intro h
      exact ⟨hO.edgeSet_mono h, ((edgeSet_restrict _ _).subset h).2⟩
    · rintro ⟨he, hout'⟩
      obtain ⟨a, b, hl⟩ := A.exists_isLink_of_mem_edgeSet he
      have hc := hout e he hout'
      obtain ⟨h₁, h₂⟩ := hends hl
      have : O.IsLink e a b := ⟨hout', hl, ⟨hl.left_mem, hc h₁⟩, ⟨hl.right_mem, hc h₂⟩⟩
      exact this.edge_mem
  refine ⟨I, O, hI, hO, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hIE, hOE]
    ext e
    simp only [mem_union, mem_inter_iff, inE, outE, mem_ofPred_eq]
    tauto
  · rw [hIE, hOE]
    refine disjoint_left.mpr ?_
    rintro e ⟨-, h₁, h₂⟩ ⟨-, h₃ | h₃⟩
    · exact h₃ h₁
    · exact h₂ h₃
  · intro e he
    rw [hIE] at he
    exact hin e he.1 he.2.1
  · intro e he
    rw [hOE] at he
    exact hout e he.1 he.2
  · rintro e ⟨he, heT⟩
    rw [hIE]
    exact ⟨hC.edgeSet_mono he, subset_closure.trans ((hCbd e he).trans hbE), heT⟩
  · intro e he
    rw [hOE]
    exact ⟨hC.edgeSet_mono (hT he), Or.inr he⟩
  · intro e he
    rw [hOE] at he
    exact he.2.symm

/-- See the module docstring. The society `(A ∪ G₂, Ω_E)` of the paper is `Sm`, the neighbourhood
outside `E'` is `Nout`, and the one inside is `Nin`. -/
theorem exists_cut_society (hS : IsClosedSurface S) {S_top S₂ : Society α β}
    {N : Neighborhood α β} (hcomp : S_top.IsComposition S₂ N) (Y : GraphDrawing N.G S) {ν : α → S}
    (hν : ∀ v : V(N.G), (Y.iso.vertexEquiv v).1 = ν v.1) {D D₂ E' : Set S} (_hD : IsClosedDisc D)
    (hE : IsClosedDisc E') (hD₂E : D₂ ⊆ E') (hED : E' ⊆ D)
    (hbarD : ∀ v ∈ N.Ω.bar, ν v ∈ discBd D) (hbarD₂ : ∀ v ∈ N.Ω₀.bar, ν v ∈ D₂)
    {C : Graph α β} (hC : C ≤ N.G) (hbd : discBd E' = graphDrawingSubgraphU Y C) {T : Set β}
    (hT : T ⊆ E(C)) (Ω_E : CyclicPerm α) (hΩE : Ω_E.bar = V(C)) :
    ∃ (Sm : Society α β) (Nout Nin : Neighborhood α β) (Yin : GraphDrawing Nin.G S)
      (Yout : GraphDrawing Nout.G S),
      Sm.Ω = Ω_E ∧ Nout.Ω = N.Ω ∧ Nout.Ω₀ = Ω_E ∧ Nin.Ω = Ω_E ∧ Nin.Ω₀ = N.Ω₀ ∧
      Nin.G ≤ N.G ∧ Nout.G ≤ N.G ∧ Sm.G ≤ S_top.G ∧
      V(Nin.G) = {v ∈ V(N.G) | ν v ∈ E'} ∧ V(Nout.G) = {v ∈ V(N.G) | ν v ∉ discInt E'} ∧
      E(C) \ T ⊆ E(Nin.G) ∧ T ⊆ E(Nout.G) ∧ E(Nin.G) ∪ E(Nout.G) = E(N.G) ∧
      (∀ e ∈ E(Nin.G), closure (graphDrawingEdgeSet Y e) ⊆ E') ∧
      (∀ e ∈ E(Nout.G), e ∈ T ∨ ¬ graphDrawingEdgeSet Y e ⊆ E') ∧
      V(Sm.G) = V(S₂.G) ∪ V(Nin.G) ∧ E(Sm.G) = E(S₂.G) ∪ E(Nin.G) ∧
      S_top.IsComposition Sm Nout ∧ Sm.IsComposition S₂ Nin ∧
      (∀ v : V(Nin.G), (Yin.iso.vertexEquiv v).1 = ν v.1) ∧
      (∀ v : V(Nout.G), (Yout.iso.vertexEquiv v).1 = ν v.1) ∧
      Yin.drawing.U ⊆ Y.drawing.U ∩ E' ∧ Yout.drawing.U ⊆ Y.drawing.U ∩ (discInt E')ᶜ ∧
      (∀ e ∈ E(Nin.G), graphDrawingEdgeSet Yin e = graphDrawingEdgeSet Y e) ∧
      (∀ e ∈ E(Nout.G), graphDrawingEdgeSet Yout e = graphDrawingEdgeSet Y e) ∧
      (∀ P ≤ Nin.G, graphDrawingSubgraphU Yin P = graphDrawingSubgraphU Y P) ∧
      (∀ P ≤ Nout.G, graphDrawingSubgraphU Yout P = graphDrawingSubgraphU Y P) := by
  classical
  obtain ⟨⟨⟨hS₂G, hNG, hVun, hEun, hEdis⟩, hbarN⟩, hΩeq, hΩ₀eq, hS₂bar⟩ := hcomp
  obtain ⟨I, O, hI, hO, hIV, hOV, hun, hdis, hIc, hOc, hCI, hTO, hOT⟩
    := exists_cut hν hS hE hC hbd hT
  have hman : ∀ x : S, IsManifoldPoint x := (IsClosedSurface.isSurface hS).2.2
  have hC₁ : ∀ {v}, v ∈ V(N.G) → (ν v ∈ discBd E' ↔ v ∈ V(C)) := fun hv => by
    rw [hbd]
    exact mem_subgraphU_iff hν hC hv
  have hCV : ∀ {v}, v ∈ V(C) → ν v ∈ discBd E' := fun hv =>
    (hC₁ (hC.vertexSet_mono hv)).mpr hv
  have hbE : discBd E' ⊆ E' := GraphMinor.Surface.discBd_subset E'
  have hCI' : V(C) ⊆ V(I) := fun v hv => by
    rw [hIV]
    exact ⟨hC.vertexSet_mono hv, hbE (hCV hv)⟩
  have hCO' : V(C) ⊆ V(O) := fun v hv => by
    rw [hOV]
    exact ⟨hC.vertexSet_mono hv, fun h => h.2 (hCV hv)⟩
  have hunV : V(I) ∪ V(O) = V(N.G) := by
    rw [hIV, hOV]
    ext v
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hv
      by_cases h : ν v ∈ E'
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, fun h' => h h'.1⟩
  have hbarO : N.Ω.bar ⊆ V(O) := by
    intro v hv
    rw [hOV]
    refine ⟨N.bar_subset hv, fun hi => ?_⟩
    exact (GraphMinor.Surface.discInt_mono hman hE hED hi).2 (hbarD v hv)
  have hbarI : N.Ω₀.bar ⊆ V(I) := by
    intro v hv
    rw [hIV]
    exact ⟨N.bar₀_subset hv, hD₂E (hbarD₂ v hv)⟩
  have hIG : I ≤ S_top.G := hI.trans hNG
  have hOG : O ≤ S_top.G := hO.trans hNG
  let U : Graph α β := subgraphUnion S_top.G S₂.G I
  have hU : U ≤ S_top.G := subgraphUnion_le hS₂G hIG
  have hUV : V(U) = V(S₂.G) ∪ V(I) := rfl
  have hUE : E(U) = E(S₂.G) ∪ E(I) := edgeSet_subgraphUnion hS₂G hIG
  let Sm : Society α β := ⟨U, Ω_E, S_top.finite_V.subset hU.vertexSet_mono,
    S_top.finite_E.subset hU.edgeSet_mono, by
      rw [hΩE]
      exact hCI'.trans subset_union_right⟩
  let Nout : Neighborhood α β := ⟨O, N.Ω, Ω_E, N.finite_V.subset hO.vertexSet_mono,
    N.finite_E.subset hO.edgeSet_mono, hbarO, by
      rw [hΩE]
      exact hCO'⟩
  let Nin : Neighborhood α β := ⟨I, Ω_E, N.Ω₀, N.finite_V.subset hI.vertexSet_mono,
    N.finite_E.subset hI.edgeSet_mono, by
      rw [hΩE]
      exact hCI', hbarI⟩
  have hcomp₁ : S_top.IsComposition Sm Nout := by
    refine ⟨⟨⟨hU, hOG, ?_, ?_, ?_⟩, hΩeq ▸ hbarO⟩, hΩeq, rfl, ?_⟩
    · change V(U) ∪ V(O) = V(S_top.G)
      rw [hUV, union_assoc, hunV, hVun]
    · change E(U) ∪ E(O) = E(S_top.G)
      rw [hUE, union_assoc, hun, hEun]
    · change Disjoint E(U) E(O)
      rw [hUE]
      exact disjoint_union_left.mpr ⟨hEdis.mono_right hO.edgeSet_mono, hdis⟩
    · change Ω_E.bar = V(U) ∩ V(O)
      rw [hΩE, hUV]
      refine Subset.antisymm (fun v hv => ⟨Or.inr (hCI' hv), hCO' hv⟩) ?_
      rintro v ⟨h | h, h'⟩
      · have hvN := hO.vertexSet_mono h'
        have hvb : v ∈ N.Ω₀.bar := by
          rw [hΩ₀eq, hS₂bar]
          exact ⟨h, hvN⟩
        rw [hOV] at h'
        refine (hC₁ hvN).mp ?_
        by_contra hn
        exact h'.2 ⟨hD₂E (hbarD₂ v hvb), hn⟩
      · rw [hIV] at h
        rw [hOV] at h'
        refine (hC₁ h.1).mp ?_
        by_contra hn
        exact h'.2 ⟨h.2, hn⟩
  have hcomp₂ : Sm.IsComposition S₂ Nin := by
    refine ⟨⟨⟨le_of_subset_of_subset hS₂G hU subset_union_left (by
      rw [hUE]
      exact subset_union_left), le_of_subset_of_subset hIG hU subset_union_right (by
      rw [hUE]
      exact subset_union_right), rfl, hUE.symm, ?_⟩, ?_⟩, rfl, hΩ₀eq, ?_⟩
    · exact hEdis.mono_right hI.edgeSet_mono
    · change Ω_E.bar ⊆ V(I)
      rw [hΩE]
      exact hCI'
    · change S₂.Ω.bar = V(S₂.G) ∩ V(I)
      refine Subset.antisymm (fun v hv => ⟨S₂.bar_subset hv, hbarI (hΩ₀eq ▸ hv)⟩) ?_
      rintro v ⟨h₁, h₂⟩
      rw [hS₂bar]
      exact ⟨h₁, hI.vertexSet_mono h₂⟩
  obtain ⟨Yin, hUi, hUs, -, hiv, -, hie, hip⟩ := GM09.GraphDrawing.ofSubgraph Y hI
  obtain ⟨Yout, hUo, hUs', -, hov, -, hoe, hop⟩ := GM09.GraphDrawing.ofSubgraph Y hO
  refine ⟨Sm, Nout, Nin, Yin, Yout, rfl, rfl, rfl, rfl, rfl, hI, hO, hU, hIV, hOV, hCI, hTO, hun,
    hIc,
    hOT, hUV, hUE, hcomp₁, hcomp₂, ?_, ?_, ?_, ?_, hie, hoe, hip, hop⟩
  · intro v
    rw [hiv v]
    exact hν ⟨v.1, hI.vertexSet_mono v.2⟩
  · intro v
    rw [hov v]
    exact hν ⟨v.1, hO.vertexSet_mono v.2⟩
  · refine subset_inter hUs ?_
    rw [hUi]
    refine union_subset (iUnion₂_subset fun v hv => ?_) (iUnion₂_subset fun e he => hIc e he)
    rw [graphDrawingVertexSet_eq_singleton Y (hI.vertexSet_mono hv), hν ⟨v, hI.vertexSet_mono hv⟩,
      singleton_subset_iff]
    exact (hIV.subset hv).2
  · refine subset_inter hUs' ?_
    rw [hUo]
    refine union_subset (iUnion₂_subset fun v hv => ?_) (iUnion₂_subset fun e he => hOc e he)
    rw [graphDrawingVertexSet_eq_singleton Y (hO.vertexSet_mono hv), hν ⟨v, hO.vertexSet_mono hv⟩,
      singleton_subset_iff]
    exact (hOV.subset hv).2

end GraphMinor.GM14

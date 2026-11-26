/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section10b
public import LeanPool.GraphMinor.GM09.ArcSides

/-!
# Graph Minors IX, (10.2): tools

A separation of a drawn graph from the two sides of an arc, and the two open arcs of an `O`-arc
between two of its points.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-- The open edge `e` has no point in `V(Γ)`. -/
theorem graphDrawingEdgeSet_subset_sdiff_V {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane)
    {e : β} (he : e ∈ E(G)) : graphDrawingEdgeSet Γ e ⊆ Γ.drawing.U \ Γ.drawing.V := by
  rw [graphDrawingEdgeSet_eq Γ he]
  exact (Γ.iso.edgeEquiv ⟨e, he⟩).2.2.1

/-- The open edge `e` lies off the drawing of any subgraph that does not contain `e`. -/
theorem disjoint_graphDrawingEdgeSet_subgraphU {G Q : Graph α β} (Γ : GraphDrawing G EuclideanPlane)
    (hQ : Q ≤ G) {e : β} (he : e ∈ E(G)) (heQ : e ∉ E(Q)) :
    Disjoint (graphDrawingEdgeSet Γ e) (graphDrawingSubgraphU Γ Q) := by
  rw [Set.disjoint_left]
  intro x hxe hxU
  have hP := singleEdgeSubgraph_le G e
  have hd : Disjoint E(Q) E(singleEdgeSubgraph G e) := by
    rw [edgeSet_singleEdgeSubgraph he, Set.disjoint_singleton_right]
    exact heQ
  have hmem : x ∈ graphDrawingSubgraphU Γ Q ∩ graphDrawingSubgraphU Γ (singleEdgeSubgraph G e) :=
    ⟨hxU, graphDrawingEdgeSet_subset_subgraphU_of_mem Γ
      (by rw [edgeSet_singleEdgeSubgraph he]; rfl) hxe⟩
  rw [graphDrawingSubgraphU_inter_of_disjoint_edgeSet Γ hQ hP hd] at hmem
  obtain ⟨v, ⟨hv, -⟩, hxv⟩ := mem_iUnion₂.mp hmem
  rw [graphDrawingVertexSet_eq_singleton Γ (hQ.vertexSet_mono hv)] at hxv
  exact (graphDrawingEdgeSet_subset_sdiff_V Γ he hxe).2
    (hxv ▸ (Γ.iso.vertexEquiv ⟨v, hQ.vertexSet_mono hv⟩).2)

theorem isPreconnected_graphDrawingEdgeSet {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane)
    {e : β} (he : e ∈ E(G)) : IsPreconnected (graphDrawingEdgeSet Γ e) := by
  rw [graphDrawingEdgeSet_eq Γ he]
  exact (Γ.iso.edgeEquiv ⟨e, he⟩).2.2.2.1.isConnected.isPreconnected

/-- A drawn vertex outside `Q` is off the drawing of `Q`. -/
theorem disjoint_graphDrawingVertexSet_subgraphU {G Q : Graph α β}
    (Γ : GraphDrawing G EuclideanPlane) (hQ : Q ≤ G) {v : α} (hv : v ∈ V(G)) (hvQ : v ∉ V(Q)) :
    Disjoint (graphDrawingVertexSet Γ v) (graphDrawingSubgraphU Γ Q) := by
  rw [Set.disjoint_left]
  intro x hx hxU
  rw [graphDrawingVertexSet_eq_singleton Γ hv] at hx
  have hxV : x ∈ Γ.drawing.V := hx ▸ (Γ.iso.vertexEquiv ⟨v, hv⟩).2
  obtain ⟨w, hw, hxw⟩ := graphDrawingSubgraphU_inter_V Γ hQ hxU hxV
  have : v = w := graphDrawingVertexSet_inj Γ
    (by rw [graphDrawingVertexSet_eq_singleton Γ hv]; exact hx) hxw
  exact hvQ (this ▸ hw)

/-- A separation of a drawn graph from the two sides of a subgraph drawn as an arc. -/
theorem exists_separation_of_sides {G Q : Graph α β} (Γ : GraphDrawing G EuclideanPlane)
    {Δ Y₁ Y₂ I₁ I₂ : Set EuclideanPlane} (hU : Γ.drawing.U ⊆ Δ) (hQ : Q ≤ G)
    (hs : IsArcSides Δ (graphDrawingSubgraphU Γ Q) I₁ I₂ Y₁ Y₂) :
    ∃ G₁ G₂ : Graph α β, IsGraphSeparation G G₁ G₂ ∧ V(G₁) ∩ V(G₂) = V(Q) ∧ Q ≤ G₁ ∧
      (∀ v ∈ V(G), graphDrawingVertexSet Γ v ⊆ Y₁ → v ∈ V(G₁)) ∧
      (∀ v ∈ V(G), graphDrawingVertexSet Γ v ⊆ Y₂ → v ∈ V(G₂)) ∧
      (∀ v ∈ V(G₁), v ∈ V(Q) ∨ graphDrawingVertexSet Γ v ⊆ Y₁) ∧
      (∀ v ∈ V(G₂), v ∈ V(Q) ∨ graphDrawingVertexSet Γ v ⊆ Y₂) ∧
      (∀ e ∈ E(G₁), e ∈ E(Q) ∨ graphDrawingEdgeSet Γ e ⊆ Y₁) ∧
      (∀ e ∈ E(G₂), graphDrawingEdgeSet Γ e ⊆ Y₂) := by
  classical
  have hVU : ∀ v ∈ V(G), graphDrawingVertexSet Γ v ⊆ Δ := by
    intro v hv
    rw [graphDrawingVertexSet_eq_singleton Γ hv, singleton_subset_iff]
    exact hU (Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, hv⟩).2)
  have hEU : ∀ e ∈ E(G), graphDrawingEdgeSet Γ e ⊆ Δ := fun e he =>
    (graphDrawingEdgeSet_subset_sdiff_V Γ he).trans (sdiff_subset.trans hU)
  have hVside : ∀ v ∈ V(G), v ∉ V(Q) →
      graphDrawingVertexSet Γ v ⊆ Y₁ ∨ graphDrawingVertexSet Γ v ⊆ Y₂ := by
    intro v hv hvQ
    refine hs.conn _ (fun x hx => ⟨hVU v hv hx, Set.disjoint_left.mp
      (disjoint_graphDrawingVertexSet_subgraphU Γ hQ hv hvQ) hx⟩) ?_
    rw [graphDrawingVertexSet_eq_singleton Γ hv]
    exact isPreconnected_singleton
  have hEsub : ∀ e ∈ E(G), e ∉ E(Q) → graphDrawingEdgeSet Γ e ⊆ Δ \ graphDrawingSubgraphU Γ Q :=
    fun e he heQ x hx => ⟨hEU e he hx, Set.disjoint_left.mp
      (disjoint_graphDrawingEdgeSet_subgraphU Γ hQ he heQ) hx⟩
  have hEside : ∀ e ∈ E(G), e ∉ E(Q) →
      graphDrawingEdgeSet Γ e ⊆ Y₁ ∨ graphDrawingEdgeSet Γ e ⊆ Y₂ := fun e he heQ =>
    hs.conn _ (hEsub e he heQ) (isPreconnected_graphDrawingEdgeSet Γ he)
  have hne : ∀ {X : Set EuclideanPlane}, X.Nonempty → X ⊆ Y₁ → X ⊆ Y₂ → False := by
    rintro X ⟨x, hx⟩ h₁ h₂
    exact Set.disjoint_left.mp hs.disj (h₁ hx) (h₂ hx)
  have hend : ∀ {e : β} {x y : α}, G.IsLink e x y → e ∉ E(Q) → x ∉ V(Q) →
      (∀ {Y Y' : Set EuclideanPlane}, (Y = Y₁ ∧ Y' = Y₂ ∨ Y = Y₂ ∧ Y' = Y₁) →
        graphDrawingEdgeSet Γ e ⊆ Y → graphDrawingVertexSet Γ x ⊆ Y) := by
    intro e x y hl heQ hxQ Y Y' hY hsub
    have hxG := hl.left_mem
    have he := hl.edge_mem
    have hcl := graphDrawingVertexSet_subset_closure_edge Γ hl
    have hp : IsPreconnected (graphDrawingEdgeSet Γ e ∪ graphDrawingVertexSet Γ x) :=
      (isPreconnected_graphDrawingEdgeSet Γ he).subset_closure subset_union_left
        (union_subset subset_closure hcl)
    have hZ : graphDrawingEdgeSet Γ e ∪ graphDrawingVertexSet Γ x ⊆
        Δ \ graphDrawingSubgraphU Γ Q := by
      refine union_subset (hEsub e he heQ) fun z hz => ⟨hVU x hxG hz, Set.disjoint_left.mp
        (disjoint_graphDrawingVertexSet_subgraphU Γ hQ hxG hxQ) hz⟩
    rcases hs.conn _ hZ hp with h' | h' <;> rcases hY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact subset_union_right.trans h'
    · exact (hne (graphDrawingEdgeSet_nonempty Γ he) (subset_union_left.trans h') hsub).elim
    · exact (hne (graphDrawingEdgeSet_nonempty Γ he) hsub (subset_union_left.trans h')).elim
    · exact subset_union_right.trans h'
  let V₁ : Set α := {v ∈ V(G) | v ∈ V(Q) ∨ graphDrawingVertexSet Γ v ⊆ Y₁}
  let V₂ : Set α := {v ∈ V(G) | v ∈ V(Q) ∨ graphDrawingVertexSet Γ v ⊆ Y₂}
  let E₁ : Set β := {e | e ∈ E(Q) ∨ graphDrawingEdgeSet Γ e ⊆ Y₁}
  let E₂ : Set β := {e | e ∉ E(Q) ∧ graphDrawingEdgeSet Γ e ⊆ Y₂}
  have hV₁ : V₁ ⊆ V(G) := fun v hv => hv.1
  have hV₂ : V₂ ⊆ V(G) := fun v hv => hv.1
  let G₁ := (G.induce V₁).restrict E₁
  let G₂ := (G.induce V₂).restrict E₂
  have hG₁ : G₁ ≤ G := restrict_le.trans (G.induce_le hV₁)
  have hG₂ : G₂ ≤ G := restrict_le.trans (G.induce_le hV₂)
  have hVG₁ : V(G₁) = V₁ := rfl
  have hVG₂ : V(G₂) = V₂ := rfl
  have hend₁ : ∀ e ∈ E₁, e ∈ E(G) → ∀ x y, G.IsLink e x y → x ∈ V₁ ∧ y ∈ V₁ := by
    intro e he₁ heG x y hl
    by_cases heQ : e ∈ E(Q)
    · obtain ⟨u, v, huv⟩ := Q.exists_isLink_of_mem_edgeSet heQ
      have hmem : ∀ z, z = u ∨ z = v → z ∈ V(Q) := by
        rintro z (rfl | rfl)
        · exact huv.left_mem
        · exact huv.right_mem
      exact ⟨⟨hl.left_mem, Or.inl (hmem x (hl.left_eq_or_eq (huv.mono hQ)))⟩,
        ⟨hl.right_mem, Or.inl (hmem y (hl.symm.left_eq_or_eq (huv.mono hQ)))⟩⟩
    · have hsub : graphDrawingEdgeSet Γ e ⊆ Y₁ := he₁.resolve_left heQ
      refine ⟨⟨hl.left_mem, ?_⟩, ⟨hl.right_mem, ?_⟩⟩
      · by_cases hx : x ∈ V(Q)
        · exact Or.inl hx
        · exact Or.inr (hend hl heQ hx (Or.inl ⟨rfl, rfl⟩) hsub)
      · by_cases hx : y ∈ V(Q)
        · exact Or.inl hx
        · exact Or.inr (hend hl.symm heQ hx (Or.inl ⟨rfl, rfl⟩) hsub)
  have hend₂ : ∀ e ∈ E₂, e ∈ E(G) → ∀ x y, G.IsLink e x y → x ∈ V₂ ∧ y ∈ V₂ := by
    rintro e ⟨heQ, hsub⟩ heG x y hl
    refine ⟨⟨hl.left_mem, ?_⟩, ⟨hl.right_mem, ?_⟩⟩
    · by_cases hx : x ∈ V(Q)
      · exact Or.inl hx
      · exact Or.inr (hend hl heQ hx (Or.inr ⟨rfl, rfl⟩) hsub)
    · by_cases hx : y ∈ V(Q)
      · exact Or.inl hx
      · exact Or.inr (hend hl.symm heQ hx (Or.inr ⟨rfl, rfl⟩) hsub)
  have hEG₁ : E(G₁) = E(G) ∩ E₁ := by
    apply Subset.antisymm
    · intro e he
      exact ⟨hG₁.edgeSet_mono he, he.2⟩
    · rintro e ⟨heG, he⟩
      obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heG
      obtain ⟨h₁, h₂⟩ := hend₁ e he heG x y hl
      exact ⟨by rw [edgeSet_induce]; exact ⟨x, y, hl, h₁, h₂⟩, he⟩
  have hEG₂ : E(G₂) = E(G) ∩ E₂ := by
    apply Subset.antisymm
    · intro e he
      exact ⟨hG₂.edgeSet_mono he, he.2⟩
    · rintro e ⟨heG, he⟩
      obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heG
      obtain ⟨h₁, h₂⟩ := hend₂ e he heG x y hl
      exact ⟨by rw [edgeSet_induce]; exact ⟨x, y, hl, h₁, h₂⟩, he⟩
  refine ⟨G₁, G₂, ⟨hG₁, hG₂, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun v hv => hv.2, fun v hv => hv.2,
    fun e he => he.2, fun e he => he.2.2⟩
  · rw [hVG₁, hVG₂]
    apply Subset.antisymm (union_subset hV₁ hV₂)
    intro v hv
    by_cases hvQ : v ∈ V(Q)
    · exact Or.inl ⟨hv, Or.inl hvQ⟩
    · rcases hVside v hv hvQ with h' | h'
      · exact Or.inl ⟨hv, Or.inr h'⟩
      · exact Or.inr ⟨hv, Or.inr h'⟩
  · rw [hEG₁, hEG₂]
    apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
    intro e he
    by_cases heQ : e ∈ E(Q)
    · exact Or.inl ⟨he, Or.inl heQ⟩
    · rcases hEside e he heQ with h' | h'
      · exact Or.inl ⟨he, Or.inr h'⟩
      · exact Or.inr ⟨he, heQ, h'⟩
  · rw [hEG₁, hEG₂, Set.disjoint_left]
    rintro e ⟨heG, he₁⟩ ⟨-, heQ, h₂⟩
    exact hne (graphDrawingEdgeSet_nonempty Γ heG) (he₁.resolve_left heQ) h₂
  · rw [hVG₁, hVG₂]
    apply Subset.antisymm
    · rintro v ⟨⟨hv, h₁⟩, ⟨-, h₂⟩⟩
      by_contra hvQ
      exact hne (graphDrawingVertexSet_nonempty Γ hv) (h₁.resolve_left hvQ) (h₂.resolve_left hvQ)
    · intro v hv
      exact ⟨⟨hQ.vertexSet_mono hv, Or.inl hv⟩, ⟨hQ.vertexSet_mono hv, Or.inl hv⟩⟩
  · rw [(Compatible.of_le_le hQ hG₁).le_iff, hVG₁, hEG₁]
    exact ⟨fun v hv => ⟨hQ.vertexSet_mono hv, Or.inl hv⟩,
      fun e he => ⟨hQ.edgeSet_mono he, Or.inl he⟩⟩
  · exact fun v hv h => ⟨hv, Or.inr h⟩
  · exact fun v hv h => ⟨hv, Or.inr h⟩

theorem eq_of_circleExp_eq {c x y : ℝ} (hx : x ∈ Ico c (c + 2 * Real.pi))
    (hy : y ∈ Ico c (c + 2 * Real.pi)) (h : Circle.exp x = Circle.exp y) : x = y :=
  Circle.exp_injOn_Ico (a := c) (b := c + 2 * Real.pi) (by simp) hx hy h

theorem exists_mem_Ico_circleExp (c : ℝ) (z : Circle) :
    ∃ t ∈ Ico c (c + 2 * Real.pi), Circle.exp t = z :=
  GraphMinor.Surface.exists_circleExp_mem_Ico c z

/-- The two open arcs of an `O`-arc `C` between two distinct points `a, b`, read off from a
parametrisation `φ`. A point between `a` and `b` in the sense of `φ` lies in `I₁`, and a point
between `b` and `a` lies in `I₂`. -/
theorem exists_open_arcs {C : Set EuclideanPlane} (φ : Circle ≃ₜ C) {a b : EuclideanPlane}
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    ∃ I₁ I₂ : Set EuclideanPlane, IsPreconnected I₁ ∧ IsPreconnected I₂ ∧ Disjoint I₁ I₂ ∧
      I₁ ∪ I₂ = C \ {a, b} ∧
      (∀ t₁ t₂ t₃ : ℝ, t₁ < t₂ → t₂ < t₃ → t₃ < t₁ + 2 * Real.pi →
        (φ (Circle.exp t₁)).1 = a → (φ (Circle.exp t₃)).1 = b → (φ (Circle.exp t₂)).1 ∈ I₁) ∧
      (∀ t₁ t₂ t₃ : ℝ, t₁ < t₂ → t₂ < t₃ → t₃ < t₁ + 2 * Real.pi →
        (φ (Circle.exp t₁)).1 = b → (φ (Circle.exp t₃)).1 = a → (φ (Circle.exp t₂)).1 ∈ I₂) ∧
      IsLineWithEnds (I₁ ∪ {a, b}) a b ∧ IsLineWithEnds (I₂ ∪ {a, b}) b a := by
  have hpi := Real.pi_pos
  let f : ℝ → EuclideanPlane := fun t => (φ (Circle.exp t)).1
  have hf : Continuous f :=
    continuous_subtype_val.comp (φ.continuous.comp Circle.exp.continuous)
  have hf_exp : ∀ {s t : ℝ}, f s = f t → Circle.exp s = Circle.exp t := fun h =>
    φ.injective (Subtype.ext h)
  obtain ⟨ta, -, hta⟩ := exists_mem_Ico_circleExp 0 (φ.symm ⟨a, ha⟩)
  obtain ⟨tb, htb, htb'⟩ := exists_mem_Ico_circleExp ta (φ.symm ⟨b, hb⟩)
  have hfa : f ta = a := by simp [f, hta]
  have hfb : f tb = b := by simp [f, htb']
  have hab' : ta ≠ tb := fun e => hab (by rw [← hfa, ← hfb, e])
  have htb1 : ta < tb := lt_of_le_of_ne htb.1 hab'
  have hfa2 : f (ta + 2 * Real.pi) = a := by
    simp only [f, Circle.exp_add_two_pi]
    exact hfa
  have shift : ∀ {t u : ℝ}, Circle.exp t = Circle.exp u → ∃ m : ℤ, t = u + m * (2 * Real.pi) ∧
      ∀ s : ℝ, f (s - m * (2 * Real.pi)) = f s := by
    intro t u h
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
    refine ⟨m, hm, fun s => ?_⟩
    have : Circle.exp (s - m * (2 * Real.pi)) = Circle.exp s :=
      Circle.exp_eq_exp.mpr ⟨-m, by push_cast; ring⟩
    simp only [f, this]
  have key : ∀ s₀ s₁ : ℝ, s₀ < s₁ → s₁ < s₀ + 2 * Real.pi →
      IsLineWithEnds (f '' Ioo s₀ s₁ ∪ {f s₀, f s₁}) (f s₀) (f s₁) := by
    intro s₀ s₁ h₀ h₁
    let e : unitInterval → EuclideanPlane := fun s => f (s₀ + s * (s₁ - s₀))
    have hpos : 0 < s₁ - s₀ := by linarith
    have hmem : ∀ s : unitInterval, s₀ + s * (s₁ - s₀) ∈ Ico s₀ (s₀ + 2 * Real.pi) := by
      intro s
      have h₂ := s.2.1
      have h₃ := s.2.2
      have h₄ : (s : ℝ) * (s₁ - s₀) ≤ 1 * (s₁ - s₀) := by gcongr
      constructor <;> nlinarith
    have hearc : IsArcMap e := by
      refine ⟨hf.comp (by fun_prop), fun s u h => ?_⟩
      have := eq_of_circleExp_eq (hmem s) (hmem u) (hf_exp h)
      have h' : (s : ℝ) * (s₁ - s₀) = u * (s₁ - s₀) := by linarith
      exact Subtype.ext (mul_right_cancel₀ hpos.ne' h')
    have hline := hearc.isLineWithEnds
    have he₀ : e 0 = f s₀ := by simp [e]
    have he₁ : e 1 = f s₁ := by simp [e]
    rw [he₀, he₁] at hline
    have hrange : range e = f '' Ioo s₀ s₁ ∪ {f s₀, f s₁} := by
      ext x
      constructor
      · rintro ⟨s, rfl⟩
        by_cases h₂ : (s : ℝ) = 0
        · exact Or.inr (Or.inl (by simp [e, h₂]))
        by_cases h₃ : (s : ℝ) = 1
        · exact Or.inr (Or.inr (by simp [e, h₃]))
        have hs₀ : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm h₂)
        have hs₁ : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 h₃
        refine Or.inl ⟨_, ⟨?_, ?_⟩, rfl⟩ <;> nlinarith
      · rintro (⟨t, ht, rfl⟩ | (rfl | rfl))
        · have hs : (t - s₀) / (s₁ - s₀) ∈ Icc (0 : ℝ) 1 := by
            constructor
            · exact div_nonneg (by linarith [ht.1]) hpos.le
            · rw [div_le_one hpos]
              linarith [ht.2]
          refine ⟨⟨_, hs⟩, ?_⟩
          simp only [e]
          congr 1
          field_simp
          ring
        · exact ⟨0, he₀⟩
        · exact ⟨1, he₁⟩
    rwa [hrange] at hline
  refine ⟨f '' Ioo ta tb, f '' Ioo tb (ta + 2 * Real.pi), isPreconnected_Ioo.image _
    hf.continuousOn,
    isPreconnected_Ioo.image _ hf.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
    have := eq_of_circleExp_eq (c := ta) ⟨ht.1.trans' htb1 |>.le, ht.2⟩
      ⟨hs.1.le, hs.2.trans htb.2⟩ (hf_exp he)
    linarith [hs.2, ht.1]
  · apply Subset.antisymm
    · have hne : ∀ t ∈ Ico ta (ta + 2 * Real.pi), t ≠ ta → t ≠ tb → f t ≠ a ∧ f t ≠ b := by
        intro t ht h₁ h₂
        constructor
        · intro e
          exact h₁ (eq_of_circleExp_eq ht ⟨le_rfl, by linarith⟩ (hf_exp (e.trans hfa.symm)))
        · intro e
          exact h₂ (eq_of_circleExp_eq ht htb (hf_exp (e.trans hfb.symm)))
      rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · have h := hne t ⟨ht.1.le, ht.2.trans htb.2⟩ ht.1.ne' ht.2.ne
        refine ⟨(φ _).2, ?_⟩
        rintro (e | e)
        · exact h.1 e
        · exact h.2 e
      · have h := hne t ⟨(htb1.trans ht.1).le, ht.2⟩ (htb1.trans ht.1).ne' ht.1.ne'
        refine ⟨(φ _).2, ?_⟩
        rintro (e | e)
        · exact h.1 e
        · exact h.2 e
    · rintro x ⟨hx, hne⟩
      obtain ⟨t, ht, hte⟩ := exists_mem_Ico_circleExp ta (φ.symm ⟨x, hx⟩)
      have hfx : f t = x := by simp [f, hte]
      have h1 : t ≠ ta := fun e => hne (Or.inl (by rw [← hfx, e, hfa]))
      have h2 : t ≠ tb := fun e => hne (Or.inr (show x = b by rw [← hfx, e, hfb]))
      rcases lt_or_gt_of_ne h2 with h | h
      · exact Or.inl ⟨t, ⟨lt_of_le_of_ne ht.1 h1.symm, h⟩, hfx⟩
      · exact Or.inr ⟨t, ⟨h, ht.2⟩, hfx⟩
  · intro t₁ t₂ t₃ h₁₂ h₂₃ h₃₁ ea eb
    obtain ⟨m, hm, hs⟩ := shift (t := t₁) (u := ta) (hf_exp (ea.trans hfa.symm))
    refine ⟨t₂ - m * (2 * Real.pi), ?_, hs t₂⟩
    have hb2 : Circle.exp (t₃ - m * (2 * Real.pi)) = Circle.exp tb :=
      hf_exp ((hs t₃).trans (eb.trans hfb.symm))
    have h3 : t₃ - m * (2 * Real.pi) = tb :=
      eq_of_circleExp_eq (c := ta) ⟨by linarith, by linarith⟩ htb hb2
    exact ⟨by linarith, by linarith⟩
  · intro t₁ t₂ t₃ h₁₂ h₂₃ h₃₁ eb ea
    obtain ⟨m, hm, hs⟩ := shift (t := t₁) (u := tb) (hf_exp (eb.trans hfb.symm))
    refine ⟨t₂ - m * (2 * Real.pi), ?_, hs t₂⟩
    have hb2 : Circle.exp (t₃ - m * (2 * Real.pi)) = Circle.exp (ta + 2 * Real.pi) :=
      hf_exp ((hs t₃).trans (ea.trans hfa2.symm))
    have h3 : t₃ - m * (2 * Real.pi) = ta + 2 * Real.pi :=
      eq_of_circleExp_eq (c := tb) ⟨by linarith, by linarith⟩
        ⟨by linarith [htb.2], by linarith⟩ hb2
    exact ⟨by linarith, by linarith⟩
  · refine ⟨?_, ?_⟩
    · have := key ta tb htb1 (by linarith [htb.2])
      rwa [hfa, hfb] at this
    · have := key tb (ta + 2 * Real.pi) (by linarith [htb.2]) (by linarith)
      rwa [hfb, hfa2, pair_comm b a] at this

theorem IsGraphPathWithEnds.eq_of_same_ends {G P : Graph α β} {a : α}
    (h : IsGraphPathWithEnds G P a a) : V(P) = {a} ∧ E(P) = ∅ := by
  obtain ⟨-, W, hW, hV, hE⟩ := h
  cases W with
  | nil _ =>
    exact ⟨by rw [hV]; ext x; simp, by rw [hE]; ext x; simp⟩
  | cons hl rest =>
    exfalso
    have hnd : (rest.support).Nodup ∧ a ∉ rest.support := by
      have : (a :: rest.support).Nodup := hW
      rw [List.nodup_cons] at this
      exact ⟨this.2, this.1⟩
    exact hnd.2 rest.end_mem_support

/-- The drawing of a path `R` from `a ∈ ΩBar` that meets a circuit `C` only at its last vertex `y`
meets the closed disc of `C` only at `y`. -/
theorem subgraphU_inter_disc {N : Neighborhood α β} (P_pres : Presentation N) {C R : Graph α β}
    {D : Set EuclideanPlane} {a y : α} (hCG : C ≤ N.G) (hD : IsClosedDisc D)
    (hDΔ : D ⊆ P_pres.Δ) (hbd : subBd D = graphDrawingSubgraphU P_pres.Γ C)
    (ha : a ∈ N.Ω.bar) (hR : IsGraphPathWithEnds N.G R a y) (hV : V(R) ∩ V(C) = {y}) :
    graphDrawingSubgraphU P_pres.Γ R ∩ D = graphDrawingVertexSet P_pres.Γ y := by
  set Γ := P_pres.Γ
  have hyG : y ∈ V(N.G) := hR.le.vertexSet_mono hR.right_mem
  have hyR : y ∈ V(R) := hR.right_mem
  have hyC : y ∈ V(C) := (hV.symm ▸ mem_singleton y : y ∈ V(R) ∩ V(C)).2
  have hsub : graphDrawingVertexSet Γ y ⊆ graphDrawingSubgraphU Γ R ∩ D := by
    intro x hx
    refine ⟨graphDrawingVertexSet_subset_subgraphU_of_mem Γ hyR hx, ?_⟩
    have : x ∈ subBd D := hbd ▸ graphDrawingVertexSet_subset_subgraphU_of_mem Γ hyC hx
    rw [subBd_eq_discBd_plane hD] at this
    exact Surface.discBd_subset D this
  apply Subset.antisymm _ hsub
  have hE : Disjoint E(R) E(C) := by
    rw [Set.disjoint_left]
    intro e heR heC
    obtain ⟨u, v, huv⟩ := R.exists_isLink_of_mem_edgeSet heR
    obtain ⟨u', v', huv'⟩ := C.exists_isLink_of_mem_edgeSet heC
    have hG := huv.mono hR.le
    have hG' := huv'.mono hCG
    have hmem : ∀ z, z = u' ∨ z = v' → z ∈ V(C) := by
      rintro z (rfl | rfl)
      · exact huv'.left_mem
      · exact huv'.right_mem
    have h₁ : u ∈ V(R) ∩ V(C) := ⟨huv.left_mem, hmem u (hG.left_eq_or_eq hG')⟩
    have h₂ : v ∈ V(R) ∩ V(C) := ⟨huv.right_mem, hmem v (hG.symm.left_eq_or_eq hG')⟩
    rw [hV] at h₁ h₂
    have e₁ : u = y := h₁
    have e₂ : v = y := h₂
    subst e₁
    subst e₂
    exact hR.not_isLoopAt heR _ hG
  have hinter : graphDrawingSubgraphU Γ R ∩ graphDrawingSubgraphU Γ C =
      graphDrawingVertexSet Γ y := by
    rw [graphDrawingSubgraphU_inter_of_disjoint_edgeSet Γ hR.le hCG hE, hV]
    simp
  have hfr : frontier D = graphDrawingSubgraphU Γ C := by
    rw [frontier_eq_discBd_plane hD, ← subBd_eq_discBd_plane hD, hbd]
  by_cases hay : a = y
  · subst hay
    obtain ⟨hVR, hER⟩ := hR.eq_of_same_ends
    rintro x ⟨hx | hx, -⟩
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      rw [hVR] at hv
      exact (show v = a from hv) ▸ hxv
    · obtain ⟨e, he, -⟩ := mem_iUnion₂.mp hx
      rw [hER] at he
      exact he.elim
  have hay' : (Γ.iso.vertexEquiv ⟨a, hR.le.vertexSet_mono hR.left_mem⟩).1 ≠
      (Γ.iso.vertexEquiv ⟨y, hyG⟩).1 := (isLineWithEnds_graphDrawingSubgraphU Γ hR hay).2
  have hl := (isLineWithEnds_graphDrawingSubgraphU Γ hR hay).1
  set pa := (Γ.iso.vertexEquiv ⟨a, hR.le.vertexSet_mono hR.left_mem⟩).1
  set py := (Γ.iso.vertexEquiv ⟨y, hyG⟩).1
  have hy_set : graphDrawingVertexSet Γ y = {py} := graphDrawingVertexSet_eq_singleton Γ hyG
  rw [hy_set] at hinter ⊢
  have hZ : IsPreconnected (graphDrawingSubgraphU Γ R \ {py}) := hl.isPreconnected_diff_right
  rintro x ⟨hxR, hxD⟩
  by_contra hxy
  have hxne : x ≠ py := hxy
  have hpa_R : pa ∈ graphDrawingSubgraphU Γ R := hl.left_mem
  have hpa_bd : pa ∈ subBd P_pres.Δ := by
    have := (P_pres.mem_bd_Δ_iff a (hR.le.vertexSet_mono hR.left_mem)).mpr ha
    rw [graphDrawingVertexSet_eq_singleton Γ (hR.le.vertexSet_mono hR.left_mem)] at this
    exact this rfl
  have hpa_D : pa ∉ D := by
    intro hm
    have hnf : pa ∉ frontier D := by
      rw [hfr]
      intro h
      have : pa ∈ graphDrawingSubgraphU Γ R ∩ graphDrawingSubgraphU Γ C := ⟨hpa_R, h⟩
      rw [hinter] at this
      exact hay' this
    have hint : pa ∈ interior D := by
      by_contra h
      exact hnf ⟨subset_closure hm, h⟩
    have hint' : pa ∈ interior P_pres.Δ := interior_mono hDΔ hint
    rw [subBd_eq_discBd_plane P_pres.isClosedDisc_Δ, ← frontier_eq_discBd_plane
      P_pres.isClosedDisc_Δ]
      at hpa_bd
    exact hpa_bd.2 hint'
  obtain ⟨z, ⟨hzR, hzne⟩, hzf⟩ := inter_frontier_nonempty_of_isPreconnected hZ
    (U := D) ⟨x, ⟨hxR, hxne⟩, hxD⟩ ⟨pa, ⟨hpa_R, hay'⟩, hpa_D⟩
  rw [hfr] at hzf
  have : z ∈ graphDrawingSubgraphU Γ R ∩ graphDrawingSubgraphU Γ C := ⟨hzR, hzf⟩
  rw [hinter] at this
  exact hzne this

end GraphMinor.GM09

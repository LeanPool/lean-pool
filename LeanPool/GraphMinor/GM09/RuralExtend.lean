/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.RuralAdd

/-!
# Adding an edge or a vertex to a rural neighborhood

The proof of (6.1) deletes an edge or a vertex from a counterexample, and uses that the smaller
society has small sophistication. To go back we must add the edge or the vertex to the rural
neighborhood of a composition. Here we do so in the four cases that arise: an edge parallel to an
edge of the neighborhood, a loop at a vertex off the inner disc, an edge joining two consecutive
vertices of `ΩBar`, and a new isolated vertex of `ΩBar`.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-- The edge of a drawing that represents a link has the two vertices as the ends of its closure. -/
theorem closure_inter_V_of_isLink {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) {f : β}
    {u w : α} (hl : G.IsLink f u w) :
    graphDrawingEdgeSet Γ f ∈ Γ.drawing.E ∧
      closure (graphDrawingEdgeSet Γ f) ∩ Γ.drawing.V = {vertexPt Γ u, vertexPt Γ w} := by
  have he : f ∈ E(G) := hl.edge_mem
  have hu : u ∈ V(G) := hl.left_mem
  have hw : w ∈ V(G) := hl.right_mem
  have hlink := (Γ.iso.isLink_iff ⟨f, he⟩ ⟨u, hu⟩ ⟨w, hw⟩).mp hl
  rw [graphDrawingEdgeSet_eq Γ he]
  refine ⟨(Γ.iso.edgeEquiv ⟨f, he⟩).2, ?_⟩
  rw [← vertexEquiv_eq_vertexPt Γ ⟨u, hu⟩, ← vertexEquiv_eq_vertexPt Γ ⟨w, hw⟩]
  exact hlink.2.2.2

namespace Neighborhood

/-- Adding one edge, drawn as `C`, to a neighborhood with a presentation. -/
theorem isRural_add_edge {N N' : Neighborhood α β} (P : Presentation N) (hΩ : N'.Ω = N.Ω)
    (hΩ₀ : N'.Ω₀ = N.Ω₀) (hle : N.G ≤ N'.G) (hV : V(N'.G) = V(N.G)) {e : β} {u w : α}
    (hE : E(N'.G) = insert e E(N.G)) (he : e ∉ E(N.G)) (hl : N'.G.IsLink e u w)
    {C : Set EuclideanPlane}
    (hC : (u ≠ w ∧ IsLineWithEnds C (vertexPt P.Γ u) (vertexPt P.Γ w)) ∨
      (u = w ∧ IsOArc C ∧ vertexPt P.Γ u ∈ C))
    (hCs : C ⊆ P.Δ \ interior P.Δ₀) (hmeet : P.Γ.drawing.U ∩ C ⊆ {vertexPt P.Γ u, vertexPt P.Γ w}) :
    N'.IsRural := by
  classical
  let Γ := P.Γ
  let ν := vertexPt Γ
  let H : Graph α β := (N'.G.induce {u, w}).restrict {e}
  have huV : u ∈ V(N'.G) := hl.left_mem
  have hwV : w ∈ V(N'.G) := hl.right_mem
  have hVH : V(H) = {u, w} := by simp [H]
  have hEH : E(H) = {e} := by
    ext f
    simp only [H, edgeSet_restrict, mem_inter_iff, mem_singleton_iff, edgeSet_induce,
      mem_ofPred_eq]
    refine ⟨fun h => h.2, fun h => ?_⟩
    subst h
    exact ⟨⟨u, w, hl, Or.inl rfl, Or.inr rfl⟩, rfl⟩
  have hHle : H ≤ N'.G := Graph.restrict_le.trans (N'.G.induce_le (pair_subset huV hwV))
  have hlH : H.IsLink e u w := ⟨rfl, hl, Or.inl rfl, Or.inr rfl⟩
  have hH : ∃ ΓH : GraphDrawing H EuclideanPlane, ΓH.drawing.U = C ∧
      ∀ x : V(H), (ΓH.iso.vertexEquiv x).1 = ν x.1 := by
    rcases hC with ⟨hne, hK⟩ | ⟨rfl, hF, hm⟩
    · have hνne : ν u ≠ ν w := fun h => hne (vertexPt_injOn Γ (hV ▸ huV) (hV ▸ hwV) h)
      exact GraphDrawing.of_single_edge hVH hEH hlH hνne hK
    · have hVH' : V(H) = {u} := by rw [hVH, pair_eq_singleton]
      exact GraphDrawing.of_single_loop hVH' hEH hlH hF hm
  obtain ⟨ΓH, hUH, hνH⟩ := hH
  have hinj : InjOn ν V(N'.G) := hV ▸ vertexPt_injOn Γ
  obtain ⟨Γ', hU', hν'⟩ := GraphDrawing.glue hle hHle
    (by rw [hV, hVH, union_eq_left]; exact pair_subset (hV ▸ huV) (hV ▸ hwV))
    (by rw [hEH, hE, union_singleton])
    (by rw [hEH]; exact disjoint_singleton_right.mpr he)
    hinj Γ ΓH (fun x => vertexEquiv_eq_vertexPt Γ x) hνH (by
      rw [hUH, hVH]
      rintro x hx
      rcases hmeet hx with h | h
      · exact ⟨u, ⟨hV ▸ huV, Or.inl rfl⟩, h.symm⟩
      · exact ⟨w, ⟨hV ▸ hwV, Or.inr rfl⟩, (mem_singleton_iff.mp h).symm⟩)
  have hset : ∀ x, graphDrawingVertexSet Γ' x = graphDrawingVertexSet Γ x := by
    intro x
    by_cases hx : x ∈ V(N.G)
    · rw [graphDrawingVertexSet_eq_singleton Γ' (hV ▸ hx), hν' ⟨x, hV ▸ hx⟩,
        vertexSet_eq_vertexPt Γ hx]
    · ext y
      constructor
      · rintro ⟨h, -⟩
        exact (hx (hV ▸ h)).elim
      · rintro ⟨h, -⟩
        exact (hx h).elim
  have hag := P.agrees_Δ
  have hag₀ := P.agrees_Δ₀
  obtain ⟨φ, hφ_cw, hφ⟩ := hag
  unfold IsRural
  rw [hΩ, hΩ₀]
  refine ⟨Γ', P.Δ, P.Δ₀, P.isClosedDisc_Δ, P.Δ₀_subset_Δ, ?_, ?_, ?_,
    ⟨φ, hφ_cw, hφ.congr fun v _ => hset v⟩, ?_⟩
  · rw [hU', hUH]
    exact union_subset P.U_subset hCs
  · intro v hv
    rw [hset v]
    exact P.mem_bd_Δ_iff v (hV ▸ hv)
  · intro v hv
    rw [hset v]
    exact P.mem_bd_Δ₀_iff v (hV ▸ hv)
  · rcases hag₀ with h | ⟨hd, φ₀, hφ₀_cw, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hd, φ₀, hφ₀_cw, h.congr fun v _ => hset v⟩

theorem isClosed_Δ₀ {N : Neighborhood α β} (P : Presentation N) : IsClosed P.Δ₀ := by
  rcases P.agrees_Δ₀ with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
    exact isClosed_empty
  · exact h.isCompact.isClosed

theorem region_subset {X X₀ : Set EuclideanPlane} (_hX₀ : X₀ ⊆ X) :
    interior X \ X₀ ⊆ X \ interior X₀ := fun _ hx =>
  ⟨interior_subset hx.1, fun h => hx.2 (interior_subset h)⟩

private theorem curve_subset {N : Neighborhood α β} (P : Presentation N) {C : Set EuclideanPlane}
    {s : Set EuclideanPlane} (hs : s ⊆ P.Γ.drawing.U) (hC : C \ s ⊆ interior P.Δ \ P.Δ₀) :
    C ⊆ P.Δ \ interior P.Δ₀ := by
  intro x hx
  by_cases h : x ∈ s
  · exact P.U_subset (hs h)
  · exact region_subset P.Δ₀_subset_Δ (hC ⟨hx, h⟩)

private theorem curve_meet {U C s : Set EuclideanPlane} (h : Disjoint (C \ s) U) : U ∩ C ⊆ s := by
  rintro x ⟨hxU, hxC⟩
  by_contra hn
  exact disjoint_left.mp h ⟨hxC, hn⟩ hxU

private theorem clean_inter {N : Neighborhood α β} (P : Presentation N)
    (hc₁ : P.Γ.drawing.U ∩ subBd P.Δ = (⋃ v ∈ N.Ω.bar, graphDrawingVertexSet P.Γ v))
    (hc₃ : P.Γ.drawing.U ∩ subBd P.Δ₀ ⊆ (⋃ v ∈ N.Ω₀.bar, graphDrawingVertexSet P.Γ v)) :
    P.Γ.drawing.U ∩ (subBd P.Δ ∪ subBd P.Δ₀) ⊆ P.Γ.drawing.V := by
  have key : ∀ (Y : Set α), Y ⊆ V(N.G) → ∀ x ∈ ⋃ v ∈ Y, graphDrawingVertexSet P.Γ v,
      x ∈ P.Γ.drawing.V := by
    intro Y hY x hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    rw [graphDrawingVertexSet_eq_singleton P.Γ (hY hv)] at hxv
    rw [hxv]
    exact (P.Γ.iso.vertexEquiv ⟨v, hY hv⟩).2
  rintro x ⟨hxU, h | h⟩
  · exact key _ N.bar_subset x (hc₁ ▸ ⟨hxU, h⟩)
  · exact key _ N.bar₀_subset x (hc₃ ⟨hxU, h⟩)

/-- A rural neighborhood stays rural when we add an edge parallel to one of its edges with two
different ends. -/
theorem IsRural.add_parallel {N N' : Neighborhood α β} (hr : N.IsRural) (hΩ : N'.Ω = N.Ω)
    (hΩ₀ : N'.Ω₀ = N.Ω₀) (hle : N.G ≤ N'.G) (hV : V(N'.G) = V(N.G)) {e f : β} {u w : α}
    (hE : E(N'.G) = insert e E(N.G)) (he : e ∉ E(N.G)) (hl : N'.G.IsLink e u w)
    (hf : N.G.IsLink f u w) (huw : u ≠ w) : N'.IsRural := by
  obtain ⟨P, hc₁, -, hc₃⟩ := hr.exists_clean
  obtain ⟨hfE, hcap⟩ := closure_inter_V_of_isLink P.Γ hf
  have hne : vertexPt P.Γ u ≠ vertexPt P.Γ w := fun h =>
    huw (vertexPt_injOn P.Γ hf.left_mem hf.right_mem h)
  obtain ⟨K, hK, hr', hd⟩ := exists_parallel_line P.isClosedDisc_Δ.isCompact.isClosed
    (isClosed_Δ₀ P)
    P.U_subset (clean_inter P hc₁ hc₃) hfE hne hcap
  refine isRural_add_edge P hΩ hΩ₀ hle hV hE he hl (Or.inl ⟨huw, hK⟩)
    (curve_subset P (pair_subset (vertexPt_mem_U P.Γ hf.left_mem)
      (vertexPt_mem_U P.Γ hf.right_mem)) hr') (curve_meet hd)

/-- A rural neighborhood stays rural when we add a loop at a vertex that is not in `ΩBar₀`. -/
theorem IsRural.add_loop {N N' : Neighborhood α β} (hr : N.IsRural) (hΩ : N'.Ω = N.Ω)
    (hΩ₀ : N'.Ω₀ = N.Ω₀) (hle : N.G ≤ N'.G) (hV : V(N'.G) = V(N.G)) {e : β} {v : α}
    (hE : E(N'.G) = insert e E(N.G)) (he : e ∉ E(N.G)) (hl : N'.G.IsLink e v v)
    (hvV : v ∈ V(N.G)) (hv₀ : v ∉ N.Ω₀.bar) : N'.IsRural := by
  classical
  obtain ⟨P, hc₁, -, hc₃⟩ := hr.exists_clean
  have hXc := P.isClosedDisc_Δ.isCompact.isClosed
  have hX₀c := isClosed_Δ₀ P
  have hclean := clean_inter P hc₁ hc₃
  have hvU := vertexPt_mem_U P.Γ hvV
  have hF : ∃ F : Set EuclideanPlane, IsOArc F ∧ vertexPt P.Γ v ∈ F ∧
      F \ {vertexPt P.Γ v} ⊆ interior P.Δ \ P.Δ₀ ∧
      Disjoint (F \ {vertexPt P.Γ v}) P.Γ.drawing.U := by
    by_cases hex : ∃ f w, N.G.IsLink f v w
    · obtain ⟨f, w, hf⟩ := hex
      obtain ⟨hfE, hcap⟩ := closure_inter_V_of_isLink P.Γ hf
      have ha : vertexPt P.Γ v ∈ closure (graphDrawingEdgeSet P.Γ f) ∩ P.Γ.drawing.V :=
        hcap ▸ Or.inl rfl
      exact exists_oArc_of_edge hXc hX₀c P.U_subset hclean hfE ha
    · have hno : ∀ e' ∈ P.Γ.drawing.E, vertexPt P.Γ v ∉ closure e' := by
        intro e' he' hae
        let g := P.Γ.iso.edgeEquiv.symm ⟨e', he'⟩
        have hge : graphDrawingEdgeSet P.Γ g.1 = e' := by
          rw [graphDrawingEdgeSet_eq P.Γ g.2]
          simp [g]
        obtain ⟨x, y, hg⟩ := N.G.exists_isLink_of_mem_edgeSet g.2
        obtain ⟨-, hcap⟩ := closure_inter_V_of_isLink P.Γ hg
        rw [hge] at hcap
        have hmem : vertexPt P.Γ v ∈ ({vertexPt P.Γ x, vertexPt P.Γ y} : Set EuclideanPlane) :=
          hcap ▸ ⟨hae, by rw [← vertexEquiv_eq_vertexPt P.Γ ⟨v, hvV⟩]; exact
            (P.Γ.iso.vertexEquiv _).2⟩
        rcases hmem with h | h
        · obtain rfl := vertexPt_injOn P.Γ hvV hg.left_mem h
          exact hex ⟨_, _, hg⟩
        · obtain rfl := vertexPt_injOn P.Γ hvV hg.right_mem h
          exact hex ⟨_, _, hg.symm⟩
      have hoff : vertexPt P.Γ v ∉ P.Δ₀ := by
        intro h
        have hb : vertexPt P.Γ v ∈ subBd P.Δ₀ := by
          rw [subBd_eq_of_isClosed hX₀c]
          exact ⟨h, (P.U_subset hvU).2⟩
        apply hv₀
        refine (P.mem_bd_Δ₀_iff v hvV).mp ?_
        rw [vertexSet_eq_vertexPt P.Γ hvV]
        exact singleton_subset_iff.mpr hb
      exact exists_oArc_of_isolated P.isClosedDisc_Δ hX₀c (P.U_subset hvU).1 hoff hno
  obtain ⟨F, hF, ha, hr', hd⟩ := hF
  refine isRural_add_edge P hΩ hΩ₀ hle hV hE he hl (Or.inr ⟨rfl, hF, ha⟩)
    (curve_subset P (singleton_subset_iff.mpr hvU) hr') ?_
  rw [pair_eq_singleton]
  exact curve_meet hd

/-- A rural neighborhood stays rural when we add an edge joining two vertices that are consecutive
in `Ω`. The new edge runs along `bd(Δ)`. -/
theorem IsRural.add_boundary_edge {N N' : Neighborhood α β} (hr : N.IsRural) (hΩ : N'.Ω = N.Ω)
    (hΩ₀ : N'.Ω₀ = N.Ω₀) (hle : N.G ≤ N'.G) (hV : V(N'.G) = V(N.G)) {e : β} {u w : α}
    (hE : E(N'.G) = insert e E(N.G)) (he : e ∉ E(N.G)) (hl : N'.G.IsLink e u w)
    (hu : u ∈ N.Ω.bar) (hw : w ∈ N.Ω.bar) (huw : u ≠ w) (hgap : N.Ω.interval u w = ∅) :
    N'.IsRural := by
  classical
  obtain ⟨P, hc₁, -, -⟩ := hr.exists_clean
  obtain ⟨φ, _, hφ⟩ := P.agrees_Δ
  have huG := N.bar_subset hu
  have hwG := N.bar_subset hw
  have hne : vertexPt P.Γ u ≠ vertexPt P.Γ w := fun h => huw (vertexPt_injOn P.Γ huG hwG h)
  have hmem : ∀ x ∈ N.Ω.bar, vertexPt P.Γ x ∈ subBd P.Δ := fun x hx =>
    hφ.1 x hx (by rw [vertexSet_eq_vertexPt P.Γ (N.bar_subset hx)]; rfl)
  obtain ⟨I₁, I₂, -, -, hd, hun, -, hsnd, hl₁, -⟩ := exists_open_arcs φ (hmem u hu) (hmem w hw) hne
  have hI₁ : I₁ ⊆ subBd P.Δ \ {vertexPt P.Γ u, vertexPt P.Γ w} := hun ▸ subset_union_left
  refine isRural_add_edge P hΩ hΩ₀ hle hV hE he hl (Or.inl ⟨huw, hl₁⟩) ?_ ?_
  · have hb : subBd P.Δ ⊆ P.Δ \ interior P.Δ₀ := by
      rw [subBd_eq_of_isClosed P.isClosedDisc_Δ.isCompact.isClosed]
      exact fun x hx => ⟨hx.1, fun h => hx.2 (interior_mono P.Δ₀_subset_Δ h)⟩
    rintro x (h | rfl | rfl)
    · exact hb (hI₁ h).1
    · exact hb (hmem u hu)
    · exact hb (hmem w hw)
  · rintro x ⟨hxU, h | h⟩
    · exfalso
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hc₁ ▸ ⟨hxU, (hI₁ h).1⟩ :
        x ∈ ⋃ v ∈ N.Ω.bar, graphDrawingVertexSet P.Γ v)
      rw [vertexSet_eq_vertexPt P.Γ (N.bar_subset hz)] at hxz
      obtain rfl : x = vertexPt P.Γ z := hxz
      have hzu : z ≠ u := fun h' => (hI₁ h).2 (Or.inl (by rw [h']))
      have hzw : z ≠ w := fun h' => (hI₁ h).2 (Or.inr (by rw [h']; rfl))
      have hcw : z ∈ N.Ω.interval w u := by
        rcases N.Ω.mem_interval_or_interval_swap hu hw hz huw hzu hzw with h' | h'
        · rw [hgap] at h'
          exact h'.elim
        · exact h'
      obtain ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, m₁, m₂, m₃⟩ := hφ.2 _ _ _ hcw.2
      rw [vertexSet_eq_vertexPt P.Γ hwG] at m₁
      rw [vertexSet_eq_vertexPt P.Γ (N.bar_subset hz)] at m₂
      rw [vertexSet_eq_vertexPt P.Γ huG] at m₃
      have := hsnd t₁ t₂ t₃ h₁₂ h₂₃ h₃₁ m₁ m₃
      rw [show (φ (Circle.exp t₂)).1 = vertexPt P.Γ z from m₂] at this
      exact disjoint_left.mp hd h this
    · exact h

/-- Given a cyclic permutation of a finite set with `v` in it, and points in an `O`-arc for the
other elements in the order of `Ω`, there are valid angles for all of `ΩBar` that give those points,
and the angle of `v` gives a point different from them. -/
theorem exists_angles_with_gap {S : Type*} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    {Ω : CyclicPerm α} {v : α} (hv : v ∈ Ω.bar) {ν : α → S} (hinj : InjOn ν (Ω.bar \ {v}))
    (hmem : ∀ w ∈ Ω.bar \ {v}, ν w ∈ C)
    (hag : ∀ v₁ v₂ v₃ : α, Ω.IsClockwise3 v₁ v₂ v₃ → v₁ ≠ v → v₂ ≠ v → v₃ ≠ v →
      ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₁ + 2 * Real.pi ∧
        (φ (Circle.exp t₁)).1 = ν v₁ ∧ (φ (Circle.exp t₂)).1 = ν v₂ ∧
        (φ (Circle.exp t₃)).1 = ν v₃) :
    ∃ (L : List α) (θ : α → ℝ), Ω.IsOrbitList L ∧ IsValidAngle L θ ∧
      (∀ w ∈ Ω.bar \ {v}, (φ (Circle.exp (θ w))).1 = ν w) ∧
      ∀ w ∈ Ω.bar \ {v}, (φ (Circle.exp (θ v))).1 ≠ ν w := by
  classical
  have hpi := Real.pi_pos
  obtain ⟨L, hL, hL0⟩ := Ω.exists_isOrbitList_starting_at hv
  have hbar : ∀ i (hi : i < L.length), L[i]'hi ∈ Ω.bar := fun i hi => by
    rw [← hL.2.2.1]
    exact List.getElem_mem hi
  have hpos : 0 < L.length := List.length_pos_of_ne_nil hL.2.1
  have hne0 : ∀ i (hi : i < L.length), 0 < i → L[i]'hi ≠ v := by
    intro i hi h0 h
    have h₂ : L[i]'hi = L[0]'hpos := h.trans (hL0 hpos).symm
    have := (List.Nodup.getElem_inj_iff hL.1).mp h₂
    omega
  have hmemL : ∀ w ∈ Ω.bar \ {v}, ∃ i, ∃ hi : i < L.length, 0 < i ∧ L[i]'hi = w := by
    rintro w ⟨hw, hne⟩
    rw [← hL.2.2.1] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
    refine ⟨i, hi, Nat.pos_of_ne_zero fun h => hne ?_, rfl⟩
    subst h
    exact hL0 hi
  by_cases hone : L.length = 1
  · refine ⟨L, 0, hL, ⟨fun i j hi hj hij => by omega, fun i hi => by simpa using hpi⟩, ?_, ?_⟩
    · intro w hw
      obtain ⟨i, hi, h0, -⟩ := hmemL w hw
      omega
    · intro w hw
      obtain ⟨i, hi, h0, -⟩ := hmemL w hw
      omega
  have h1 : 1 < L.length := by omega
  let w₀ := L[1]'h1
  have hw₀ : w₀ ∈ Ω.bar \ {v} := ⟨hbar 1 h1, hne0 1 h1 one_pos⟩
  let pt' : α → Circle := fun w => if h : ν w ∈ C then φ.symm ⟨ν w, h⟩ else 1
  have hpt' : ∀ w ∈ Ω.bar \ {v}, (φ (pt' w)).1 = ν w := by
    intro w hw
    simp only [pt', hmem w hw, ↓reduceDIte, Homeomorph.apply_symm_apply]
  obtain ⟨t₀, -, ht₀⟩ := exists_mem_Ico_circleExp 0 (pt' w₀)
  choose s hsI hse using fun w => exists_mem_Ico_circleExp t₀ (pt' w)
  have hsv : ∀ w ∈ Ω.bar \ {v}, (φ (Circle.exp (s w))).1 = ν w := fun w hw => by
    rw [hse w, hpt' w hw]
  have huniq : ∀ w ∈ Ω.bar \ {v}, ∀ t ∈ Ico t₀ (t₀ + 2 * Real.pi),
      (φ (Circle.exp t)).1 = ν w → t = s w := by
    intro w hw t ht h
    refine eq_of_circleExp_eq ht (hsI w) ?_
    apply φ.injective
    exact Subtype.ext (h.trans (hsv w hw).symm)
  have hs₀ : s w₀ = t₀ := (huniq w₀ hw₀ t₀ ⟨le_rfl, by linarith⟩ (by rw [ht₀, hpt' w₀ hw₀])).symm
  have hidx : ∀ i (hi : i < L.length), 0 < i → L[i]'hi ∈ Ω.bar \ {v} := fun i hi h =>
    ⟨hbar i hi, hne0 i hi h⟩
  have hmono : ∀ i j (hi : i < L.length) (hj : j < L.length), 0 < i → i < j →
      s (L[i]'hi) < s (L[j]'hj) := by
    intro i j hi hj h0 hij
    rcases Nat.lt_or_ge 1 i with h1i | hi1
    · have hin := Ω.isOrbitList_mem_interval_of_lt hL h1i hij hj
      obtain ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, m₁, m₂, m₃⟩ :=
        hag _ _ _ hin.2 (hne0 1 h1 one_pos) (hne0 i hi h0) (hne0 j hj (by omega))
      have hexp : Circle.exp t₁ = Circle.exp t₀ := by
        apply φ.injective
        apply Subtype.ext
        rw [m₁, ht₀, hpt' _ hw₀]
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
      have hshift : ∀ t : ℝ, Circle.exp (t - m * (2 * Real.pi)) = Circle.exp t := fun t =>
        Circle.exp_eq_exp.mpr ⟨-m, by push_cast; ring⟩
      have e₂ : s (L[i]'hi) = t₂ - m * (2 * Real.pi) :=
        (huniq _ (hidx i hi h0) _ ⟨by linarith, by linarith⟩ (by rw [hshift, m₂])).symm
      have e₃ : s (L[j]'hj) = t₃ - m * (2 * Real.pi) :=
        (huniq _ (hidx j hj (by omega)) _ ⟨by linarith, by linarith⟩ (by rw [hshift, m₃])).symm
      rw [e₂, e₃]
      linarith
    · obtain rfl : i = 1 := by omega
      have hge := (hsI (L[j]'hj)).1
      change s w₀ < _
      rw [hs₀]
      refine lt_of_le_of_ne hge fun h => ?_
      have hν : ν w₀ = ν (L[j]'hj) := by
        rw [← hsv _ hw₀, ← hsv _ (hidx j hj (by omega)), hs₀, ← h]
      have := (List.Nodup.getElem_inj_iff hL.1).mp (hinj hw₀ (hidx j hj (by omega)) hν)
      omega
  let last := L[L.length - 1]'(by omega)
  have hle : ∀ i (hi : i < L.length), 0 < i → s (L[i]'hi) ≤ s last := by
    intro i hi h0
    rcases Nat.lt_or_ge i (L.length - 1) with h | h
    · exact (hmono i _ hi (by omega) h0 h).le
    · obtain rfl : i = L.length - 1 := by omega
      exact le_rfl
  have hlast := (hsI last).2
  let θv : ℝ := (s last - 2 * Real.pi + t₀) / 2
  have hθ1 : θv < t₀ := by simp only [θv]; linarith
  have hθ2 : s last < θv + 2 * Real.pi := by simp only [θv]; linarith
  have hθ3 : t₀ ≤ θv + 2 * Real.pi := by
    have := (hsI last).1
    simp only [θv]
    linarith
  have hθ4 : θv + 2 * Real.pi < t₀ + 2 * Real.pi := by linarith
  let θ : α → ℝ := fun w => if w = v then θv else s w
  have hθs : ∀ i (hi : i < L.length), 0 < i → θ (L[i]'hi) = s (L[i]'hi) := fun i hi h => by
    simp only [θ, hne0 i hi h, ↓reduceIte]
  have hθv : θ v = θv := by simp [θ]
  have hθL0 : θ (L[0]'hpos) = θv := by rw [hL0 hpos, hθv]
  refine ⟨L, θ, hL, ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [hθL0, hθs j hj (by omega)]
      exact lt_of_lt_of_le hθ1 (hsI _).1
    · rw [hθs i hi h0, hθs j hj (by omega)]
      exact hmono i j hi hj h0 hij
  · rcases Nat.eq_zero_or_pos i with rfl | h0
    · linarith
    · rw [hθs i hi h0, hθL0]
      exact lt_of_le_of_lt (hle i hi h0) hθ2
  · intro w hw
    have hwv : w ≠ v := hw.2
    simp only [θ, hwv, ↓reduceIte]
    exact hsv w hw
  · intro w hw he
    rw [hθv] at he
    have hexp : Circle.exp (θv + 2 * Real.pi) = Circle.exp θv := by
      simp only [circle_exp_add_two_pi]
    obtain ⟨i, hi, h0, rfl⟩ := hmemL w hw
    have e := huniq _ hw (θv + 2 * Real.pi) ⟨hθ3, hθ4⟩ (by rw [hexp]; exact he)
    have := hle i hi h0
    linarith

/-- A rural neighborhood stays rural when we add a new isolated vertex to `ΩBar`. It goes on
`bd(Δ)` in the gap between its two neighbours in `Ω`. -/
theorem IsRural.add_boundary_vertex {N N' : Neighborhood α β} (hr : N.IsRural)
    (hΩ₀ : N'.Ω₀ = N.Ω₀) (hle : N.G ≤ N'.G) {v : α} (hvN : v ∉ V(N.G))
    (hV : V(N'.G) = insert v V(N.G)) (hE : E(N'.G) = E(N.G)) (hvb : v ∈ N'.Ω.bar)
    (hbar : N.Ω.bar = N'.Ω.bar \ {v})
    (hcw : ∀ v₁ v₂ v₃ : α, N'.Ω.IsClockwise3 v₁ v₂ v₃ → v₁ ≠ v → v₂ ≠ v → v₃ ≠ v →
      N.Ω.IsClockwise3 v₁ v₂ v₃) : N'.IsRural := by
  classical
  obtain ⟨P, hc₁, hc₂, -⟩ := hr.exists_clean
  obtain ⟨φ, hφ_cw, hφ⟩ := P.agrees_Δ
  have hXc := P.isClosedDisc_Δ.isCompact.isClosed
  let Γ := P.Γ
  let ν₀ := vertexPt Γ
  have hsub : N'.Ω.bar \ {v} ⊆ V(N.G) := hbar ▸ N.bar_subset
  have hset₀ : ∀ {w}, w ∈ N'.Ω.bar \ {v} → graphDrawingVertexSet Γ w = {ν₀ w} := fun h =>
    vertexSet_eq_vertexPt Γ (hsub h)
  obtain ⟨L, θ, hL, hθ, hνθ, hgap⟩ := exists_angles_with_gap φ hvb (ν := ν₀)
    ((vertexPt_injOn Γ).mono hsub)
    (fun w hw => hφ.1 w (hbar ▸ hw) (by rw [hset₀ hw]; rfl))
    (fun v₁ v₂ v₃ h h₁ h₂ h₃ => by
      have hm := CyclicPerm.isClockwise3_iff.mp h
      have hm₁ : v₁ ∈ N'.Ω.bar \ {v} := ⟨hm.2.2.2.1, h₁⟩
      have hm₂ : v₂ ∈ N'.Ω.bar \ {v} := ⟨hm.2.2.2.2.1, h₂⟩
      have hm₃ : v₃ ∈ N'.Ω.bar \ {v} := ⟨hm.2.2.2.2.2.1, h₃⟩
      obtain ⟨t₁, t₂, t₃, a, b, c, m₁, m₂, m₃⟩ := hφ.2 _ _ _ (hcw _ _ _ h h₁ h₂ h₃)
      rw [hset₀ hm₁] at m₁
      rw [hset₀ hm₂] at m₂
      rw [hset₀ hm₃] at m₃
      exact ⟨t₁, t₂, t₃, a, b, c, m₁, m₂, m₃⟩)
  let x : EuclideanPlane := (φ (Circle.exp (θ v))).1
  have hxb : x ∈ subBd P.Δ := (φ _).2
  have hnot : ∀ y ∈ ⋃ w ∈ N.Ω.bar, graphDrawingVertexSet P.Γ w, y ≠ x := by
    rintro y hy rfl
    obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hy
    rw [hbar] at hw
    rw [show P.Γ = Γ from rfl, hset₀ hw] at hyw
    exact hgap w hw hyw
  have hxU : x ∉ Γ.drawing.U := fun h => hnot x (hc₁ ▸ ⟨h, hxb⟩) rfl
  have hxΔ₀ : x ∉ P.Δ₀ := fun h => hnot x (hc₂ ⟨h, hxb⟩) rfl
  let ν : α → EuclideanPlane := update ν₀ v x
  have hνv : ν v = x := update_self _ _ _
  have hνo : ∀ w, w ≠ v → ν w = ν₀ w := fun w h => update_of_ne h _ _
  let H : Graph α β := (N'.G.induce {v}).restrict ∅
  have hvV : v ∈ V(N'.G) := hV ▸ mem_insert _ _
  have hVH : V(H) = {v} := by simp [H]
  have hEH : E(H) = ∅ := by simp [H]
  have hHle : H ≤ N'.G := Graph.restrict_le.trans (N'.G.induce_le (singleton_subset_iff.mpr hvV))
  obtain ⟨ΓH, hUH, hνH⟩ := GraphDrawing.of_edgeless (ν := ν) (by rw [hVH]; exact finite_singleton v)
    hEH (by rw [hVH]; exact injOn_singleton _ _)
  have hUH' : ΓH.drawing.U = {x} := by rw [hUH, hVH, image_singleton, hνv]
  have hne : ∀ w ∈ V(N.G), w ≠ v := fun w hw h => hvN (h ▸ hw)
  have hinj : InjOn ν V(N'.G) := by
    rw [hV]
    rintro a (rfl | ha) b (rfl | hb) hab
    · rfl
    · rw [hνv, hνo b (hne b hb)] at hab
      exact (hxU (hab ▸ vertexPt_mem_U Γ hb)).elim
    · rw [hνv, hνo a (hne a ha)] at hab
      exact (hxU (hab ▸ vertexPt_mem_U Γ ha)).elim
    · rw [hνo a (hne a ha), hνo b (hne b hb)] at hab
      exact vertexPt_injOn Γ ha hb hab
  obtain ⟨Γ', hU', hν'⟩ := GraphDrawing.glue (ν := ν) hle hHle
    (by rw [hV, hVH, union_comm, ← insert_eq])
    (by rw [hEH, hE, union_empty]) (by rw [hEH]; exact disjoint_bot_right)
    hinj Γ ΓH
    (fun w => by rw [hνo w.1 (hne w.1 w.2)]; exact vertexEquiv_eq_vertexPt Γ w) hνH (by
      rw [hUH']
      rintro _ ⟨hu, rfl⟩
      exact (hxU hu).elim)
  have hsetO : ∀ w, w ≠ v → graphDrawingVertexSet Γ' w = graphDrawingVertexSet Γ w := by
    intro w hw
    by_cases hx : w ∈ V(N.G)
    · have hx' : w ∈ V(N'.G) := hV ▸ mem_insert_of_mem _ hx
      rw [graphDrawingVertexSet_eq_singleton Γ' hx', hν' ⟨w, hx'⟩, vertexSet_eq_vertexPt Γ hx]
      exact congrArg _ (hνo w hw)
    · ext y
      constructor
      · rintro ⟨h, -⟩
        rcases (hV ▸ h : w ∈ insert v V(N.G)) with h' | h'
        · exact (hw h').elim
        · exact (hx h').elim
      · rintro ⟨h, -⟩
        exact (hx h).elim
  have hsetV : graphDrawingVertexSet Γ' v = {x} := by
    rw [graphDrawingVertexSet_eq_singleton Γ' hvV, hν' ⟨v, hvV⟩]
    exact congrArg _ hνv
  have hX₀ : ∀ y, y ∈ subBd P.Δ₀ → y ∈ P.Δ₀ := fun y hy => by
    rw [subBd_eq_of_isClosed (isClosed_Δ₀ P)] at hy
    exact hy.1
  have hag₀ := P.agrees_Δ₀
  unfold IsRural
  rw [hΩ₀]
  have hv₀ : v ∉ N.Ω₀.bar := fun h => hvN (N.bar₀_subset h)
  refine ⟨Γ', P.Δ, P.Δ₀, P.isClosedDisc_Δ, P.Δ₀_subset_Δ, ?_, ?_, ?_,
    ⟨φ, hφ_cw, drawingAgrees_of_angles hL hθ φ ?_ ?_⟩, ?_⟩
  · rw [hU', hUH']
    refine union_subset P.U_subset (singleton_subset_iff.mpr ?_)
    rw [subBd_eq_of_isClosed hXc] at hxb
    exact ⟨hxb.1, fun h => hxΔ₀ (interior_subset h)⟩
  · intro w hw
    rcases eq_or_ne w v with rfl | hne'
    · rw [hsetV]
      exact ⟨fun _ => hvb, fun _ => singleton_subset_iff.mpr hxb⟩
    · have hwN : w ∈ V(N.G) := (hV ▸ hw : w ∈ insert v V(N.G)).resolve_left hne'
      rw [hsetO w hne', P.mem_bd_Δ_iff w hwN, hbar]
      exact ⟨fun h => h.1, fun h => ⟨h, hne'⟩⟩
  · intro w hw
    rcases eq_or_ne w v with rfl | hne'
    · rw [hsetV, singleton_subset_iff]
      exact ⟨fun h => (hxΔ₀ (hX₀ _ h)).elim, fun h => (hv₀ h).elim⟩
    · have hwN : w ∈ V(N.G) := (hV ▸ hw : w ∈ insert v V(N.G)).resolve_left hne'
      rw [hsetO w hne']
      exact P.mem_bd_Δ₀_iff w hwN
  · intro w hw
    rcases eq_or_ne w v with rfl | hne'
    · rw [hsetV]
      exact singleton_subset_iff.mpr hxb
    · rw [hsetO w hne']
      exact hφ.1 w (hbar ▸ ⟨hw, hne'⟩)
  · intro w hw
    rcases eq_or_ne w v with rfl | hne'
    · rw [hsetV]
      rfl
    · have hw' : w ∈ N'.Ω.bar \ {v} := ⟨hw, hne'⟩
      rw [hsetO w hne', hset₀ hw']
      exact hνθ w hw'
  · have hcong : ∀ w ∈ N.Ω₀.bar, graphDrawingVertexSet Γ' w = graphDrawingVertexSet Γ w :=
      fun w hw => hsetO w (fun h => hv₀ (h ▸ hw))
    rcases hag₀ with h | ⟨hd, φ₀, hφ₀_cw, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hd, φ₀, hφ₀_cw, h.congr hcong⟩

end Neighborhood

end GraphMinor.GM09

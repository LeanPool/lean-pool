/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section10f

/-!
# Graph Minors IX, (10.4)

We follow the proof of the paper. We first delete edges at `ΩBar` and apply (10.1), so that the nest
misses `ΩBar` and each linking path meets `ΩBar` only at its first vertex. The last circuit `K` of
the
nest bounds a disc `D`. The drawing of `G` splits at `K` into the part `H₁` in `D` and the part
`H₂` outside. We apply (9.1) and (10.3) to the part in `D`, and then extend the paths we get along
the linking paths.

The paper says that the extended paths form a crooked transaction but gives no reason. Their ends
cross if and only if the old ends cross, by `crosses_outer_iff_crosses_inner_of_disjoint_paths`
applied to the rural neighborhood `(H₂, Ω, Ω₁)`. Then `Society.isCrookedTransaction_image` applies.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-- Agreement with a circle depends only on where the vertices of `ΩBar` are drawn. -/
theorem DrawingAgreesWithOArcHomeo.congr {G G' : Graph α β} {Γ : GraphDrawing G EuclideanPlane}
    {Γ' : GraphDrawing G' EuclideanPlane} {Ω : CyclicPerm α} {F : Set EuclideanPlane}
    {φ : Circle ≃ₜ F} (h : DrawingAgreesWithOArcHomeo Γ Ω F φ)
    (hv : ∀ v ∈ Ω.bar, graphDrawingVertexSet Γ' v = graphDrawingVertexSet Γ v) :
    DrawingAgreesWithOArcHomeo Γ' Ω F φ := by
  refine ⟨fun v hv' => ?_, fun v₁ v₂ v₃ hc => ?_⟩
  · rw [hv v hv']
    exact h.1 v hv'
  · have hm := CyclicPerm.isClockwise3_iff.mp hc
    rw [hv v₁ hm.2.2.2.1, hv v₂ hm.2.2.2.2.1, hv v₃ hm.2.2.2.2.2.1]
    exact h.2 _ _ _ hc

/-- A presentation of a neighborhood whose graph is a subgraph of `G`, read off from a presentation
with graph `G`. -/
theorem Presentation.exists_of_le {N N' : Neighborhood α β} (P_pres : Presentation N)
    (hG : N'.G ≤ N.G) {Δ' Δ₀' : Set EuclideanPlane} (hΔ' : IsClosedDisc Δ') (hsub : Δ₀' ⊆ Δ')
    (hU : graphDrawingSubgraphU P_pres.Γ N'.G ⊆ Δ' \ interior Δ₀')
    (hbd : ∀ v ∈ V(N'.G), (graphDrawingVertexSet P_pres.Γ v ⊆ subBd Δ' ↔ v ∈ N'.Ω.bar))
    (hbd₀ : ∀ v ∈ V(N'.G), (graphDrawingVertexSet P_pres.Γ v ⊆ subBd Δ₀' ↔ v ∈ N'.Ω₀.bar))
    (hag : ∃ φ : Circle ≃ₜ subBd Δ',
      IsClockwiseDiscHomeo Δ' φ ∧ DrawingAgreesWithOArcHomeo P_pres.Γ N'.Ω (subBd Δ') φ)
    (hag₀ : (Δ₀' = ∅ ∧ N'.Ω₀.bar = ∅) ∨ (IsClosedDisc Δ₀' ∧ ∃ φ₀ : Circle ≃ₜ subBd Δ₀',
      IsClockwiseDiscHomeo Δ₀' φ₀ ∧ DrawingAgreesWithOArcHomeo P_pres.Γ N'.Ω₀ (subBd Δ₀') φ₀)) :
    ∃ P' : Presentation N', P'.Δ = Δ' ∧ P'.Δ₀ = Δ₀' ∧
      (∀ v ∈ V(N'.G), graphDrawingVertexSet P'.Γ v = graphDrawingVertexSet P_pres.Γ v) ∧
      ∀ R ≤ N'.G, graphDrawingSubgraphU P'.Γ R = graphDrawingSubgraphU P_pres.Γ R := by
  obtain ⟨Γ', hU'_eq, -, -, -, hvert, -, hsubg⟩ := GraphDrawing.ofSubgraph P_pres.Γ hG
  obtain ⟨φ, hφ_cw, hφ⟩ := hag
  refine ⟨⟨Γ', Δ', Δ₀', hΔ', hsub, hU'_eq ▸ hU, fun v hv => ?_, fun v hv => ?_,
    ⟨φ, hφ_cw, ?_⟩, ?_⟩, rfl, rfl, hvert, hsubg⟩
  · rw [hvert v hv]
    exact hbd v hv
  · rw [hvert v hv]
    exact hbd₀ v hv
  · exact hφ.congr fun v hv => hvert v (N'.bar_subset hv)
  · rcases hag₀ with h | ⟨h, φ₀, hφ₀_cw, hφ₀⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, φ₀, hφ₀_cw, hφ₀.congr fun v hv => hvert v (N'.bar₀_subset hv)⟩

/-- With two circuits in a nest, no vertex is on both boundaries. -/
theorem disjoint_bar_bar₀_of_isNest {N : Neighborhood α β} {P_pres : Presentation N} {m : ℕ}
    {C : Fin m → Graph α β} (hC : N.IsNest P_pres C) (hm : 2 ≤ m) :
    Disjoint N.Ω.bar N.Ω₀.bar := by
  rw [Set.disjoint_left]
  intro v hv hv₀
  have hlt : (⟨0, by omega⟩ : Fin m) < ⟨1, by omega⟩ := by simp [Fin.lt_def]
  have hdis := disjoint_vertexSet_bar_of_isNest_lt hC hlt
  obtain ⟨hcir, -, D, hDd, hDs, -⟩ := hC
  set j : Fin m := ⟨0, by omega⟩
  have hvG := N.bar_subset hv
  have hbdΔ := (P_pres.mem_bd_Δ_iff v hvG).mpr hv
  have hD : graphDrawingVertexSet P_pres.Γ v ⊆ D j := by
    rw [graphDrawingVertexSet_eq_singleton P_pres.Γ hvG, singleton_subset_iff]
    exact (hDs j).1 (isClosedDisc_Δ₀_and_mem_of_mem_bar₀ P_pres hv₀).2
  have hbdD : graphDrawingVertexSet P_pres.Γ v ⊆ graphDrawingSubgraphU P_pres.Γ (C j) := by
    rw [← (hDd j).2]
    exact (subset_inter hD hbdΔ).trans (inter_subBd_subset_subBd (hDs j).2)
  exact Set.disjoint_left.mp hdis
    (mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU P_pres.Γ (hcir j).1 hvG hbdD) hv

/-- A circuit has an edge. -/
theorem IsGraphCircuit.edgeSet_nonempty {G C : Graph α β} (hC : IsGraphCircuit G C) :
    E(C).Nonempty := by
  obtain ⟨-, u, W, -, hlen, -, -⟩ := hC
  cases W with
  | nil _ => simp at hlen
  | cons hlink rest => exact ⟨_, hlink.edge_mem⟩

/-- The nest and the linking paths of the proof of (10.4). The nest misses `ΩBar` and each path
meets
`ΩBar` only in its first vertex. -/
theorem exists_clean_paths_of_nest {N : Neighborhood α β} (P_pres : Presentation N)
    {n : ℕ} (hn : 1 ≤ n)
    {C' : Fin (n + 1) → Graph α β} (hC' : N.IsNest P_pres C') {X : Set α} (hX : N.IsLinked X) :
    ∃ (C : Fin n → Graph α β) (P : Fin X.ncard → Graph α β) (x t : Fin X.ncard → α),
      N.IsNest P_pres C ∧ (∀ j, Disjoint V(C j) N.Ω.bar) ∧
      (∀ i, IsFromToPathWithEnds N.G (P i) X N.Ω₀.bar (x i) (t i) ∧ V(P i) ∩ N.Ω.bar = {x i}) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i j, ∃ I, IsGraphPath N.G I ∧ I ≤ P i ∧ I ≤ C j ∧ V(I) = V(P i) ∩ V(C j) := by
  classical
  obtain ⟨hXb, P₀, hP₀, hd₀⟩ := hX
  have hd_bar := disjoint_bar_bar₀_of_isNest hC' (by omega)
  choose x₀ hx₀ y₀ hy₀ hP₀' using hP₀
  have hPV : ∀ i, V(P₀ i) ∩ N.Ω.bar = {x₀ i} := fun i => (hP₀' i).2.1
  let F : Set β := {e | ∀ a b, N.G.IsLink e a b → a ∉ N.Ω.bar ∧ b ∉ N.Ω.bar} ∪ ⋃ i, E(P₀ i)
  let G' := N.G.restrict F
  have hG' : G' ≤ N.G := Graph.restrict_le
  have hVG' : V(G') = V(N.G) := rfl
  have hEG' : E(G') = E(N.G) ∩ F := rfl
  let N' : Neighborhood α β :=
    { G := G', Ω := N.Ω, Ω₀ := N.Ω₀, finite_V := N.finite_V,
      finite_E := N.finite_E.subset hG'.edgeSet_mono, bar_subset := N.bar_subset,
      bar₀_subset := N.bar₀_subset }
  obtain ⟨P', hPΔ, hPΔ₀, hPv, hPU⟩ := Presentation.exists_of_le (N' := N') P_pres hG'
    P_pres.isClosedDisc_Δ P_pres.Δ₀_subset_Δ
    ((graphDrawingSubgraphU_subset_U P_pres.Γ _).trans P_pres.U_subset) P_pres.mem_bd_Δ_iff
    P_pres.mem_bd_Δ₀_iff P_pres.agrees_Δ P_pres.agrees_Δ₀
  let C₀ : Fin n → Graph α β := fun j => C' j.castSucc
  have hC₀d : ∀ j, Disjoint V(C₀ j) N.Ω.bar := fun j =>
    disjoint_vertexSet_bar_of_isNest_lt hC' (Fin.castSucc_lt_last j)
  have hC₀G : ∀ j, C₀ j ≤ N.G := fun j => (hC'.1 _).1
  have hC₀le : ∀ j, C₀ j ≤ G' := by
    intro j
    refine (Compatible.of_le_le (hC₀G j) hG').le_iff.mpr
      ⟨(hC₀G j).vertexSet_mono, fun e he => ⟨(hC₀G j).edgeSet_mono he, Or.inl ?_⟩⟩
    intro a b hab
    obtain ⟨u, w, hl⟩ : ∃ u w, (C₀ j).IsLink e u w := exists_isLink_of_mem_edgeSet he
    have hlG := hl.mono (hC₀G j)
    have hm : ∀ {z}, z = u ∨ z = w → z ∈ V(C₀ j) := by
      rintro z (rfl | rfl)
      · exact hl.left_mem
      · exact hl.right_mem
    exact ⟨Set.disjoint_left.mp (hC₀d j) (hm (hab.left_eq_or_eq hlG)),
      Set.disjoint_left.mp (hC₀d j) (hm (hab.symm.left_eq_or_eq hlG))⟩
  have hP₀le : ∀ i, P₀ i ≤ G' := by
    intro i
    refine (Compatible.of_le_le (hP₀' i).1.le hG').le_iff.mpr
      ⟨(hP₀' i).1.le.vertexSet_mono, fun e he =>
        ⟨(hP₀' i).1.le.edgeSet_mono he, Or.inr (mem_iUnion.mpr ⟨i, he⟩)⟩⟩
  have hnest : N'.IsNest P' C₀ := by
    obtain ⟨hcir, hdisj, D, hDd, hDs, hDm⟩ := hC'
    refine ⟨fun j => ⟨hC₀le j, (hcir _).2⟩, fun i j hij => hdisj fun e => hij
      (Fin.castSucc_injective _ e), fun j => D j.castSucc, fun j => ⟨(hDd _).1, ?_⟩, fun j => ?_,
      fun i j hij => hDm _ _ (Fin.castSucc_le_castSucc_iff.mpr hij)⟩
    · rw [hPU _ (hC₀le j)]
      exact (hDd _).2
    · rw [hPΔ, hPΔ₀]
      exact hDs _
  have hweak : N'.IsWeaklyLinked X := by
    refine ⟨hXb, P₀, fun i => ⟨x₀ i, y₀ i, (hP₀' i).1.of_le (hP₀le i), ?_, (hP₀' i).2.2⟩, hd₀⟩
    apply Subset.antisymm
    · rintro v ⟨hv, hvX⟩
      have : v ∈ V(P₀ i) ∩ N.Ω.bar := ⟨hv, hXb hvX⟩
      rwa [hPV] at this
    · rintro _ rfl
      exact ⟨(hP₀' i).1.left_mem, hx₀ i⟩
  obtain ⟨C, P, hC, hP, hPd, hPC⟩ := theorem_10_1_proof P' ⟨C₀, hnest⟩ hweak
  choose x t hP₁ using hP
  have hin : ∀ {e v w}, G'.IsLink e v w → v ∈ N.Ω.bar →
      ∃ i, e ∈ E(P₀ i) ∧ v = x₀ i ∧ (P₀ i).Inc e v := by
    intro e v w hl hv
    have he : e ∈ F := (show e ∈ E(G') from hl.edge_mem).2
    rcases he with he | he
    · exact absurd hv (he v w (hl.mono hG')).1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp he
      obtain ⟨a, b, hab⟩ : ∃ a b, (P₀ i).IsLink e a b := exists_isLink_of_mem_edgeSet hi
      have hlG := hl.mono hG'
      have hvP : v ∈ V(P₀ i) ∧ (P₀ i).Inc e v := by
        rcases hlG.left_eq_or_eq (hab.mono (hP₀' i).1.le) with rfl | rfl
        · exact ⟨hab.left_mem, ⟨_, hab⟩⟩
        · exact ⟨hab.right_mem, ⟨_, hab.symm⟩⟩
      have : v ∈ V(P₀ i) ∩ N.Ω.bar := ⟨hvP.1, hv⟩
      rw [hPV] at this
      exact ⟨i, hi, this, hvP.2⟩
  have huniq : ∀ {e₁ e₂ v w₁ w₂}, G'.IsLink e₁ v w₁ → G'.IsLink e₂ v w₂ → v ∈ N.Ω.bar →
      e₁ = e₂ := by
    intro e₁ e₂ v w₁ w₂ h₁ h₂ hv
    obtain ⟨i₁, he₁, hx₁, hi₁⟩ := hin h₁ hv
    obtain ⟨i₂, he₂, hx₂, hi₂⟩ := hin h₂ hv
    have hi : i₁ = i₂ := by
      by_contra hne
      have hm₂ : v ∈ V(P₀ i₂) := hx₂ ▸ (hP₀' i₂).1.left_mem
      have hm₁ : v ∈ V(P₀ i₁) := hx₁ ▸ (hP₀' i₁).1.left_mem
      exact Set.disjoint_left.mp (hd₀ hne) hm₁ hm₂
    subst hi
    rw [hx₁] at hi₁ hi₂
    exact (hP₀' i₁).1.inc_left_unique he₁ he₂ hi₁ hi₂
  have hCbar : ∀ j, Disjoint V(C j) N.Ω.bar := by
    intro j
    rw [Set.disjoint_left]
    intro v hv hvb
    have hc := hC.1 j
    by_cases h : ∃ v' ∈ V(C j), v ≠ v'
    · obtain ⟨v', hv', hne⟩ := h
      obtain ⟨Q₁, Q₂, -, -, hQ₁, hQ₂, -, -, -, hE, -⟩ := hc.exists_two_paths hv hv' hne
      obtain ⟨e₁, he₁, w₁, hl₁⟩ := hQ₁.exists_inc_of_mem_of_ne hne hQ₁.left_mem
      obtain ⟨e₂, he₂, w₂, hl₂⟩ := hQ₂.exists_inc_of_mem_of_ne hne hQ₂.left_mem
      have e' := huniq (hl₁.mono hQ₁.le) (hl₂.mono hQ₂.le) hvb
      exact Set.disjoint_left.mp hE he₁ (e' ▸ he₂)
    · push Not at h
      obtain ⟨e, he⟩ := hc.edgeSet_nonempty
      obtain ⟨u, w, hl⟩ : ∃ u w, (C j).IsLink e u w := exists_isLink_of_mem_edgeSet he
      obtain rfl := (h u hl.left_mem).symm
      obtain rfl := (h w hl.right_mem).symm
      obtain ⟨i, hi, -, -⟩ := hin (hl.mono hc.1) hvb
      exact (hP₀' i).1.not_isLoopAt hi _ ((hl.mono hc.1).mono hG')
  have hPbar : ∀ i, V(P i) ∩ N.Ω.bar = {x i} := by
    intro i
    obtain ⟨hpath, hVX, hV₀⟩ := hP₁ i
    have hxX : x i ∈ X := (hVX.symm ▸ mem_singleton _ : x i ∈ V(P i) ∩ X).2
    have ht₀ : t i ∈ N.Ω₀.bar := (hV₀.symm ▸ mem_singleton _ : t i ∈ V(P i) ∩ N'.Ω₀.bar).2
    apply Subset.antisymm
    · rintro w ⟨hw, hwb⟩
      by_contra hne
      have hne' : x i ≠ w := fun e => hne e.symm
      have hwt : w ≠ t i := fun e =>
        Set.disjoint_left.mp hd_bar hwb (e.symm ▸ ht₀)
      obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hp₁, hp₂, -, -, hE⟩ := hpath.exists_split_at hw
      obtain ⟨e₁, he₁, w₁, hl₁⟩ := hp₁.exists_inc_of_mem_of_ne hne' hp₁.right_mem
      obtain ⟨e₂, he₂, w₂, hl₂⟩ := hp₂.exists_inc_of_mem_of_ne hwt hp₂.left_mem
      have hle₁ : Q₁ ≤ G' := hQ₁.trans hpath.le
      have hle₂ : Q₂ ≤ G' := hQ₂.trans hpath.le
      have e' := huniq (hl₁.mono hle₁) (hl₂.mono hle₂) hwb
      exact Set.disjoint_left.mp hE he₁ (e' ▸ he₂)
    · rintro _ rfl
      exact ⟨hpath.left_mem, hXb hxX⟩
  refine ⟨C, P, x, t, ?_, hCbar, fun i => ⟨?_, hPbar i⟩, hPd, fun i j => ?_⟩
  · obtain ⟨hcir, hdisj, D, hDd, hDs, hDm⟩ := hC
    refine ⟨fun j => ⟨(hcir j).1.trans hG', (hcir j).2⟩, hdisj, D, fun j => ⟨(hDd j).1, ?_⟩,
      fun j => ?_, hDm⟩
    · rw [← hPU _ (hcir j).1]
      exact (hDd j).2
    · rw [← hPΔ, ← hPΔ₀]
      exact hDs j
  · obtain ⟨hpath, hVX, hV₀⟩ := hP₁ i
    exact ⟨hpath.mono hG', hVX, hV₀⟩
  · obtain ⟨u, w, hI⟩ := hPC i j
    have hle₁ : P i ≤ G' := (hP₁ i).1.le
    have hle₂ : C j ≤ G' := (hC.1 j).1
    exact ⟨_, ⟨u, w, hI.mono hG'⟩, subgraphInter_le_left hle₁ hle₂,
      subgraphInter_le_right hle₁ hle₂,
      vertexSet_subgraphInter _ _ _⟩

/-- The clean nest used in the proof of Graph Minors IX (10.4). -/
theorem exists_clean_paths {N : Neighborhood α β} (P_pres : Presentation N) {p : ℕ}
    {C' : Fin (p + 5) → Graph α β} (hC' : N.IsNest P_pres C') {X : Set α} (hX : N.IsLinked X) :
    ∃ (C : Fin (p + 4) → Graph α β) (P : Fin X.ncard → Graph α β) (x t : Fin X.ncard → α),
      N.IsNest P_pres C ∧ (∀ j, Disjoint V(C j) N.Ω.bar) ∧
      (∀ i, IsFromToPathWithEnds N.G (P i) X N.Ω₀.bar (x i) (t i) ∧ V(P i) ∩ N.Ω.bar = {x i}) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i j, ∃ I, IsGraphPath N.G I ∧ I ≤ P i ∧ I ≤ C j ∧ V(I) = V(P i) ∩ V(C j) :=
  exists_clean_paths_of_nest P_pres (n := p + 4) (by omega) hC' hX

/-- The union of a path with a path at each end. -/
theorem exists_extended_path {G P A B : Graph α β} {a b a' b' : α}
    (hP : IsGraphPathWithEnds G P a b) (hA : IsGraphPathWithEnds G A a' a)
    (hB : IsGraphPathWithEnds G B b' b) (hAP : V(A) ∩ V(P) = {a}) (hBP : V(B) ∩ V(P) = {b})
    (hAB : Disjoint V(A) V(B)) :
    ∃ Q, IsGraphPathWithEnds G Q a' b' ∧ V(Q) = V(A) ∪ V(P) ∪ V(B) := by
  have h₁ := hP.subgraphUnion hB.symm (by rw [inter_comm]; exact hBP)
  have hV₁ : V(A) ∩ V(subgraphUnion G P B) = {a} := by
    rw [vertexSet_subgraphUnion, inter_union_distrib_left, hAP, hAB.inter_eq, union_empty]
  refine ⟨_, hA.subgraphUnion h₁ hV₁, ?_⟩
  rw [vertexSet_subgraphUnion, vertexSet_subgraphUnion, union_assoc]

/-- Every circuit in a nest lies on the inner side of the last circuit. -/
theorem nestedCircuitsOnInnerSide
    {N : Neighborhood α β} (Γ : GraphDrawing N.G EuclideanPlane)
    {m : ℕ} {C : Fin m → Graph α β} {D : Fin m → Set EuclideanPlane} {last : Fin m}
    (hcir : ∀ j, IsGraphCircuit N.G (C j))
    (hdisj : Pairwise fun i j => Disjoint V(C i) V(C j))
    (hDd : ∀ j, IsClosedDisc (D j) ∧ subBd (D j) = graphDrawingSubgraphU Γ (C j))
    (hDm : ∀ (i j : Fin m), i ≤ j → D i ⊆ D j) (hlast : ∀ j : Fin m, j ≤ last)
    {H₁ H₂ : Graph α β} (hsep : IsGraphSeparation N.G H₁ H₂)
    (hcut : V(H₁) ∩ V(H₂) = V(C last)) (hKH₁ : C last ≤ H₁)
    (hY₁ : ∀ v ∈ V(N.G), graphDrawingVertexSet Γ v ⊆ D last \ subBd (D last) → v ∈ V(H₁))
    (hpt : ∀ v ∈ V(N.G), ∃ q, graphDrawingVertexSet Γ v = {q})
    (hbdK : ∀ v ∈ V(N.G), graphDrawingVertexSet Γ v ⊆ subBd (D last) ↔ v ∈ V(C last))
    (j : Fin m) : C j ≤ H₁ := by
  classical
  by_cases hj : j = last
  · subst hj
    exact hKH₁
  refine IsGraphSeparation.le_left_of_disjoint hsep (hcir j).1 (Set.disjoint_left.mpr ?_)
  intro v hv hv₂
  have hvG := (hcir j).1.vertexSet_mono hv
  have hnK : v ∉ V(C last) := fun h => Set.disjoint_left.mp (hdisj hj) hv h
  have hv₁ : v ∈ V(H₁) := by
    obtain ⟨q, hq⟩ := hpt v hvG
    refine hY₁ v hvG ?_
    have hqm : q ∈ graphDrawingVertexSet Γ v := hq ▸ mem_singleton q
    have hjle : j ≤ last := hlast j
    have hqD : q ∈ D last := by
      refine hDm j last hjle (subBd_subset_of_isClosed (isClosed_of_isClosedDisc (hDd j).1) ?_)
      rw [(hDd j).2]
      exact graphDrawingVertexSet_subset_subgraphU_of_mem Γ hv hqm
    rw [hq, singleton_subset_iff]
    refine ⟨hqD, fun hb => hnK ((hbdK v hvG).mp ?_)⟩
    rw [hq, singleton_subset_iff]
    exact hb
  exact hnK (hcut ▸ ⟨hv₁, hv₂⟩)

private theorem splitPathAtInnerCircuit {G H₁ H₂ K P I : Graph α β}
    (hsep : IsGraphSeparation G H₁ H₂) (hcut : V(H₁) ∩ V(H₂) = V(K)) (hKH₁ : K ≤ H₁)
    {x t : α} (hP : IsGraphPathWithEnds G P x t) (hI : IsGraphPath G I)
    (hIP : I ≤ P) (hIK : I ≤ K) (hVI : V(I) = V(P) ∩ V(K))
    (hx : x ∈ V(H₂)) (ht : t ∈ V(H₁)) :
    ∃ (y : α) (R W : Graph α β), y ∈ V(K) ∧
      IsGraphPathWithEnds H₂ R x y ∧ V(R) ⊆ V(P) ∧ V(R) ∩ V(K) = {y} ∧
      IsGraphPathWithEnds H₁ W y t ∧ V(W) ⊆ V(P) := by
  classical
  obtain ⟨u, w, hIp⟩ := hI
  have hne : (V(P) ∩ V(K)).Nonempty := ⟨u, hVI ▸ hIp.left_mem⟩
  have hne' := hne
  obtain ⟨y, hy, R, -, hRP, -, hRp, -, -, -, -, hRd⟩ :=
    hP.exists_first_split_at_mem hne
  obtain ⟨z, hz, T, -, hTP, -, hTp, -, -, -, -, hTd⟩ :=
    hP.symm.exists_first_split_at_mem hne'
  have hinter : ∀ {Q : Graph α β} {q : α}, q ∈ V(Q) → q ∈ V(K) →
      Disjoint (V(Q) \ {q}) V(K) → V(Q) ∩ V(K) = {q} := by
    intro Q q hq hqK hd
    apply Subset.antisymm
    · rintro v ⟨hv, hvK⟩
      by_contra hne
      exact Set.disjoint_left.mp hd ⟨hv, hne⟩ hvK
    · rintro _ rfl
      exact ⟨hq, hqK⟩
  have hRV := hinter hRp.right_mem hy.2 hRd
  have hTV := hinter hTp.right_mem hz.2 hTd
  have hRN : IsGraphPathWithEnds G R x y := hRp.mono hP.le
  have hTN : IsGraphPathWithEnds G T t z := hTp.mono hP.le
  have hRH₂ : R ≤ H₂ := hRN.le_right_of_inter_subset hsep
    (by rw [hcut, hRV]) hx (hcut.symm ▸ hy.2 : y ∈ V(H₁) ∩ V(H₂)).2
  have hTH₁ : T ≤ H₁ := hTN.le_right_of_inter_subset (IsGraphSeparation.symm hsep)
    (by rw [inter_comm V(H₂), hcut, hTV]) ht (hKH₁.vertexSet_mono hz.2)
  have hyI : y ∈ V(I) := hVI ▸ hy
  have hzI : z ∈ V(I) := hVI ▸ hz
  obtain ⟨M, hMI, hMp, -⟩ := hIp.exists_subpath hyI hzI
  have hMH₁ : IsGraphPathWithEnds H₁ M y z := hMp.mono (hIK.trans hKH₁)
  have hTH : IsGraphPathWithEnds H₁ T z t := (hTN.of_le hTH₁).symm
  have hMT : V(M) ∩ V(T) = {z} := by
    apply Subset.antisymm
    · rintro v ⟨hv, hvT⟩
      have : v ∈ V(T) ∩ V(K) := ⟨hvT, (hMI.trans hIK).vertexSet_mono hv⟩
      rwa [hTV] at this
    · rintro _ rfl
      exact ⟨hMp.right_mem, hTp.right_mem⟩
  refine ⟨y, R, _, hy.2, hRN.of_le hRH₂, hRP.vertexSet_mono, hRV, hMH₁.subgraphUnion hTH hMT, ?_⟩
  rw [vertexSet_subgraphUnion]
  exact union_subset (hMI.trans hIP).vertexSet_mono hTP.vertexSet_mono

private theorem weakLinkingAlongOuterPaths {N₁ : Neighborhood α β} {n : ℕ}
    {P R W : Fin n → Graph α β} {y t : Fin n → α} (hYcard : (range y).ncard = n)
    (hybar : ∀ i, y i ∈ N₁.Ω.bar)
    (hW : ∀ i, IsGraphPathWithEnds N₁.G (W i) (y i) (t i))
    (hPd : Pairwise fun i j => Disjoint V(P i) V(P j))
    (hWP : ∀ i, V(W i) ⊆ V(P i)) (hRP : ∀ i, V(R i) ⊆ V(P i))
    (hyR : ∀ i, y i ∈ V(R i)) (htbar : ∀ i, V(P i) ∩ N₁.Ω₀.bar = {t i}) :
    N₁.IsWeaklyLinked (range y) := by
  classical
  refine ⟨by rintro _ ⟨i, rfl⟩; exact hybar i,
    fun j => W (Fin.cast hYcard j), fun j => ?_, fun i j hij => ?_⟩
  · set i := Fin.cast hYcard j
    refine ⟨y i, t i, hW i, ?_, ?_⟩
    · apply Subset.antisymm
      · rintro v ⟨hv, ⟨k, rfl⟩⟩
        by_cases hik : i = k
        · subst hik
          rfl
        · exact (Set.disjoint_left.mp (hPd hik) (hWP i hv) (hRP k (hyR k))).elim
      · rintro _ rfl
        exact ⟨(hW i).left_mem, mem_range_self i⟩
    · apply Subset.antisymm
      · rintro v ⟨hv, hv₀⟩
        have : v ∈ V(P i) ∩ N₁.Ω₀.bar := ⟨hWP i hv, hv₀⟩
        rwa [htbar i] at this
      · rintro _ rfl
        have : t i ∈ V(P i) ∩ N₁.Ω₀.bar := (htbar i).symm ▸ mem_singleton _
        exact ⟨(hW i).right_mem, this.2⟩
  · refine (hPd fun e => hij ?_).mono (hWP _) (hWP _)
    exact Fin.cast_injective hYcard e

private theorem extendTransactionAcrossNeighborhood
    {S_comp S₁ : Society α β} {N₂ : Neighborhood α β} {K : Graph α β} {X : Set α} {p : ℕ}
    (hXpos : 0 < X.ncard) (hInner : S₁.G ≤ S_comp.G) (hOuter : N₂.G ≤ S_comp.G)
    (hcutU : V(N₂.G) ∩ V(S₁.G) = V(K)) (hΩ : N₂.Ω = S_comp.Ω) (hΩ₀ : N₂.Ω₀ = S₁.Ω)
    (hrural₂ : N₂.IsRural) (hbarH₂ : S_comp.Ω.bar ⊆ V(N₂.G))
    (hKbar : Disjoint V(K) S_comp.Ω.bar)
    {R : Fin X.ncard → Graph α β} {x y : Fin X.ncard → α}
    (hR : ∀ i, IsGraphPathWithEnds N₂.G (R i) (x i) (y i))
    (hRK : ∀ i, V(R i) ∩ V(K) = {y i})
    (hy_inj : Injective y) (hx_inj : Injective x)
    (hRd : ∀ {i j}, i ≠ j → Disjoint V(R i) V(R j))
    (hybar : ∀ i, y i ∈ S₁.Ω.bar) (hxb : ∀ i, x i ∈ S_comp.Ω.bar)
    (hxX : ∀ i, x i ∈ X) (hRbar : ∀ i, V(R i) ∩ S_comp.Ω.bar = {x i})
    {T : Set (Graph α β)} (hT : S₁.IsCrookedTransaction T) (hpT : p ≤ T.ncard)
    (hTends : S₁.transactionEnds T ⊆ range y) :
    ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ p ≤ P'.ncard ∧
      S_comp.transactionEnds P' ⊆ X ∧
      ∀ Q ∈ P', Disjoint (pathInternalVerts S_comp.G Q) S_comp.Ω.bar := by
  classical
  have hyR (i : Fin X.ncard) : y i ∈ V(R i) := (hR i).right_mem
  have hne_idx : Nonempty (Fin X.ncard) := ⟨⟨0, hXpos⟩⟩
  let ψ : α → α := fun v => x (invFun y v)
  have hψ : ∀ i, ψ (y i) = x i := fun i => congrArg x (leftInverse_invFun hy_inj i)
  have hS₁T : ∀ Q ∈ T, Q ≤ S₁.G := by
    intro Q hQ
    obtain ⟨A, B, hf⟩ := hT.1
    obtain ⟨a, -, b, -, hQp⟩ := hf.2.2 Q hQ
    exact hQp.1.le
  have hRS : ∀ {i v}, v ∈ V(R i) → v ∈ V(S₁.G) → v = y i := by
    intro i v hv hv₁
    have : v ∈ V(R i) ∩ V(K) := ⟨hv, hcutU ▸ ⟨(hR i).le.vertexSet_mono hv, hv₁⟩⟩
    rwa [hRK] at this
  have hRSN : ∀ i, IsGraphPathWithEnds S_comp.G (R i) (x i) (y i) := fun i =>
    (hR i).mono hOuter
  have hRV : ∀ {Q : Graph α β} {i}, Q ≤ S₁.G → y i ∈ V(Q) → V(R i) ∩ V(Q) = {y i} := by
    intro Q i hQ hyQ
    apply Subset.antisymm
    · rintro v ⟨hv, hvQ⟩
      exact hRS hv (hQ.vertexSet_mono hvQ)
    · rintro _ rfl
      exact ⟨hyR i, hyQ⟩
  have hTY : ∀ {Q a b}, Q ∈ T → S₁.IsOmegaPathWithEnds Q a b → ∃ i j, a = y i ∧ b = y j ∧ i ≠ j
    := by
    intro Q a b hQ hab
    obtain ⟨i, rfl⟩ := hTends ⟨Q, hQ, b, hab⟩
    obtain ⟨j, rfl⟩ := hTends ⟨Q, hQ, _, Society.IsOmegaPathWithEnds.symm S₁ hab⟩
    exact ⟨i, j, rfl, rfl, fun e => hab.2.1 (congrArg y e)⟩
  have hex : ∀ Q ∈ T, ∃ Qe : Graph α β, ∀ i j, S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      IsGraphPathWithEnds S_comp.G Qe (x i) (x j) ∧ V(Qe) = V(R i) ∪ V(Q) ∪ V(R j) := by
    intro Q hQ
    obtain ⟨A, B, hf⟩ := hT.1
    obtain ⟨a, -, b, -, hQp⟩ := hf.2.2 Q hQ
    obtain ⟨i₀, j₀, rfl, rfl, hne⟩ := hTY hQ hQp
    have hQS : Q ≤ S₁.G := hS₁T Q hQ
    have hpS : IsGraphPathWithEnds S_comp.G Q (y i₀) (y j₀) :=
      hQp.1.mono hInner
    obtain ⟨Qe, hQe, hVQ⟩ := exists_extended_path hpS (hRSN i₀) (hRSN j₀)
      (hRV hQS hQp.1.left_mem) (hRV hQS hQp.1.right_mem) (hRd hne)
    refine ⟨Qe, fun i j hij => ?_⟩
    rcases Society.IsOmegaPathWithEnds.ends_eq S₁ hQp hij with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · obtain rfl := hy_inj e₁
      obtain rfl := hy_inj e₂
      exact ⟨hQe, hVQ⟩
    · obtain rfl := hy_inj e₁
      obtain rfl := hy_inj e₂
      refine ⟨hQe.symm, ?_⟩
      rw [hVQ]
      ext v
      simp only [mem_union]
      tauto
  choose! f hf using hex
  have hTdisj : ∀ {Q Q'}, Q ∈ T → Q' ∈ T → Q ≠ Q' → Disjoint V(Q) V(Q') := by
    intro Q Q' hQ hQ' hne
    obtain ⟨A, B, hfence⟩ := hT.1
    exact hfence.1.2 hQ hQ' hne
  have hendsT : ∀ Q ∈ T, ∀ i j, S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      S_comp.IsOmegaPathWithEnds (f Q) (x i) (x j) := fun Q hQ i j hij =>
    ⟨(hf Q hQ i j hij).1, fun e => hij.2.1 (congrArg y (hx_inj e)), hxb i, hxb j⟩
  have hRQ : ∀ {Q Q' i j}, Q ∈ T → Q' ∈ T → Q ≠ Q' → S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      Disjoint V(R i) V(Q') := by
    intro Q Q' i j hQ hQ' hne hij
    rw [Set.disjoint_left]
    intro v hv hvQ
    have e := hRS hv ((hS₁T Q' hQ').vertexSet_mono hvQ)
    subst e
    exact Set.disjoint_left.mp (hTdisj hQ hQ' hne) hij.1.left_mem hvQ
  have hd : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Disjoint V(f Q) V(f Q') := by
    intro Q hQ Q' hQ' hne
    obtain ⟨A, B, hfence⟩ := hT.1
    obtain ⟨a, -, b, -, hQp⟩ := hfence.2.2 Q hQ
    obtain ⟨a', -, b', -, hQ'p⟩ := hfence.2.2 Q' hQ'
    obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hQp
    obtain ⟨i', j', rfl, rfl, -⟩ := hTY hQ' hQ'p
    rw [(hf Q hQ i j hQp).2, (hf Q' hQ' i' j' hQ'p).2]
    have hdQ := hTdisj hQ hQ' hne
    have h₁ := hRQ hQ hQ' hne hQp
    have h₂ := hRQ hQ hQ' hne (Society.IsOmegaPathWithEnds.symm S₁ hQp)
    have h₃ := hRQ hQ' hQ hne.symm hQ'p
    have h₄ := hRQ hQ' hQ hne.symm (Society.IsOmegaPathWithEnds.symm S₁ hQ'p)
    have hne' : ∀ {u w}, y u ∈ V(Q) → y w ∈ V(Q') → u ≠ w := by
      rintro u w hu hw rfl
      exact Set.disjoint_left.mp hdQ hu hw
    have hu₁ := hQp.1.left_mem
    have hu₂ := hQp.1.right_mem
    have hw₁ := hQ'p.1.left_mem
    have hw₂ := hQ'p.1.right_mem
    rw [Set.disjoint_left]
    rintro v ((h | h) | h) ((h' | h') | h')
    · exact Set.disjoint_left.mp (hRd (hne' hu₁ hw₁)) h h'
    · exact Set.disjoint_left.mp h₁ h h'
    · exact Set.disjoint_left.mp (hRd (hne' hu₁ hw₂)) h h'
    · exact Set.disjoint_left.mp h₃ h' h
    · exact Set.disjoint_left.mp hdQ h h'
    · exact Set.disjoint_left.mp h₄ h' h
    · exact Set.disjoint_left.mp (hRd (hne' hu₂ hw₁)) h h'
    · exact Set.disjoint_left.mp h₂ h h'
    · exact Set.disjoint_left.mp (hRd (hne' hu₂ hw₂)) h h'
  have hcrook : S_comp.IsCrookedTransaction (f '' T) := by
    refine Society.isCrookedTransaction_image (ψ := ψ) hT ?_ hd ?_ ?_
    · intro Q hQ a b hab
      obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hab
      rw [hψ, hψ]
      exact hendsT Q hQ i j hab
    · intro a ha b hb e
      obtain ⟨i, rfl⟩ := hTends ha
      obtain ⟨j, rfl⟩ := hTends hb
      rw [hψ, hψ] at e
      exact congrArg y (hx_inj e)
    · intro a ha b hb c hc d' hd' h12 h13 h14 h23 h24 h34
      obtain ⟨i₁, rfl⟩ := hTends ha
      obtain ⟨i₂, rfl⟩ := hTends hb
      obtain ⟨i₃, rfl⟩ := hTends hc
      obtain ⟨i₄, rfl⟩ := hTends hd'
      have hne : ∀ {u w}, y u ≠ y w → u ≠ w := fun h e => h (congrArg y e)
      have hN : ∀ k, x k ∈ N₂.Ω.bar := fun k => hΩ.symm ▸ hxb k
      have hO : ∀ k, y k ∈ N₂.Ω₀.bar := fun k => hΩ₀.symm ▸ hybar k
      have h := crosses_outer_iff_crosses_inner_of_disjoint_paths hrural₂ (hR i₁) (hN i₁) (hO i₁)
        (hR i₃) (hN i₃) (hO i₃) (hR i₂) (hN i₂) (hO i₂) (hR i₄) (hN i₄) (hO i₄)
        (hRd (hne h13)) (hRd (hne h12)) (hRd (hne h14)) (hRd (hne h23.symm)) (hRd (hne h34))
        (hRd (hne h24))
      rw [hψ, hψ, hψ, hψ]
      rw [hΩ, hΩ₀] at h
      exact h.symm
  have hnonempty : ∀ Q ∈ T, V(f Q).Nonempty := by
    intro Q hQ
    obtain ⟨A, B, hfence⟩ := hT.1
    obtain ⟨a, -, b, -, hQp⟩ := hfence.2.2 Q hQ
    obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hQp
    exact ⟨_, (hf Q hQ i j hQp).1.left_mem⟩
  have hinjf : InjOn f T := by
    intro Q hQ Q' hQ' e
    by_contra hne
    obtain ⟨v, hv⟩ := hnonempty Q hQ
    exact Set.disjoint_left.mp (hd Q hQ Q' hQ' hne) hv (e ▸ hv)
  refine ⟨f '' T, hcrook, ?_, ?_, ?_⟩
  · rw [hinjf.ncard_image]
    exact hpT
  · rintro v ⟨_, ⟨Q, hQ, rfl⟩, b, hvb⟩
    obtain ⟨A, B, hfence⟩ := hT.1
    obtain ⟨a', -, b', -, hQp⟩ := hfence.2.2 Q hQ
    obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hQp
    rcases Society.IsOmegaPathWithEnds.ends_eq S_comp (hendsT Q hQ i j hQp) hvb with ⟨e, -⟩ | ⟨e, -⟩
    · exact e ▸ hxX i
    · exact e ▸ hxX j
  · rintro _ ⟨Q, hQ, rfl⟩
    rw [Set.disjoint_left]
    rintro v ⟨hv, hvE⟩ hvb
    obtain ⟨A, B, hfence⟩ := hT.1
    obtain ⟨a', -, b', -, hQp⟩ := hfence.2.2 Q hQ
    obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hQp
    obtain ⟨hpath, hVe⟩ := hf Q hQ i j hQp
    have hend : ∀ {k}, v ∈ V(R k) → v = x k := fun hk =>
      mem_singleton_iff.mp (hRbar _ ▸ ⟨hk, hvb⟩)
    rw [hVe] at hv
    rcases hv with (h | h) | h
    · exact hvE ⟨_, hend h ▸ hpath⟩
    · have hK : v ∈ V(N₂.G) ∩ V(S₁.G) := ⟨hbarH₂ hvb, (hS₁T Q hQ).vertexSet_mono h⟩
      rw [hcutU] at hK
      exact Set.disjoint_left.mp hKbar hK hvb
    · exact hvE ⟨_, hend h ▸ hpath.symm⟩

/-- Cut a presentation at a nested circuit, keeping its inner and outer boundaries on
their respective sides. -/
theorem Presentation.separate_at_circuit {N : Neighborhood α β} (P_pres : Presentation N)
    {m : ℕ} (C : Fin m → Graph α β) (D : Fin m → Set EuclideanPlane) (last : Fin m)
    (hCircuit : IsGraphCircuit N.G (C last)) (hDisc : IsClosedDisc (D last))
    (hBoundary : subBd (D last) = graphDrawingSubgraphU P_pres.Γ (C last))
    (hInner : P_pres.Δ₀ ⊆ D last) (hOuter : D last ⊆ P_pres.Δ)
    (hDisjoint : Disjoint V(C last) N.Ω.bar) :
    let Γ := P_pres.Γ
    (∀ v ∈ V(N.G), graphDrawingVertexSet Γ v ⊆ subBd (D last) ↔ v ∈ V(C last)) ∧
      ∃ H₁ H₂ : Graph α β, IsGraphSeparation N.G H₁ H₂ ∧
        V(H₁) ∩ V(H₂) = V(C last) ∧ C last ≤ H₁ ∧
        (∀ v ∈ V(N.G), graphDrawingVertexSet Γ v ⊆ D last \ subBd (D last) → v ∈ V(H₁)) ∧
        graphDrawingSubgraphU Γ H₁ ⊆ D last ∧
        graphDrawingSubgraphU Γ H₂ ⊆ P_pres.Δ \ interior (D last) ∧
        N.Ω.bar ⊆ V(H₂) ∧ N.Ω₀.bar ⊆ V(H₁) := by
  let Γ := P_pres.Γ
  have hKG := hCircuit.1
  have hUΔ : Γ.drawing.U ⊆ P_pres.Δ := P_pres.U_subset.trans sdiff_subset
  obtain ⟨H₁, H₂, hsep, hcut, hKH₁, hY₁, hY₂, hUH₁, hUH₂⟩ := exists_separation_of_disc Γ
    (isClosed_of_isClosedDisc P_pres.isClosedDisc_Δ) hUΔ hKG hDisc hOuter hBoundary
  have hpt : ∀ v ∈ V(N.G), ∃ q, graphDrawingVertexSet Γ v = {q} := fun v hv =>
    ⟨_, graphDrawingVertexSet_eq_singleton Γ hv⟩
  have hbdK : ∀ v ∈ V(N.G), (graphDrawingVertexSet Γ v ⊆ subBd (D last) ↔ v ∈ V(C last)) := by
    intro v hv
    rw [hBoundary]
    exact ⟨mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hKG hv,
      graphDrawingVertexSet_subset_subgraphU_of_mem Γ⟩
  have hbarH₂ : N.Ω.bar ⊆ V(H₂) := by
    intro v hv
    have hvG := N.bar_subset hv
    obtain ⟨q, hq⟩ := hpt v hvG
    refine hY₂ v hvG ?_
    rw [hq, singleton_subset_iff]
    have hb := (P_pres.mem_bd_Δ_iff v hvG).mpr hv
    have hqm : q ∈ graphDrawingVertexSet Γ v := hq ▸ mem_singleton q
    refine ⟨subBd_subset_of_isClosed (isClosed_of_isClosedDisc P_pres.isClosedDisc_Δ) (hb hqm),
      fun hqD => ?_⟩
    have : graphDrawingVertexSet Γ v ⊆ subBd (D last) := by
      rw [hq, singleton_subset_iff]
      refine inter_subBd_subset_subBd hOuter ⟨hqD, hb hqm⟩
    exact Set.disjoint_left.mp hDisjoint ((hbdK v hvG).mp this) hv
  have hbar₀H₁ : N.Ω₀.bar ⊆ V(H₁) := by
    intro v hv
    have hvG := N.bar₀_subset hv
    by_cases hvK : v ∈ V(C last)
    · exact hKH₁.vertexSet_mono hvK
    obtain ⟨q, hq⟩ := hpt v hvG
    refine hY₁ v hvG ?_
    rw [hq, singleton_subset_iff]
    have hq' := singleton_injective (hq.symm.trans (graphDrawingVertexSet_eq_singleton Γ hvG))
    refine ⟨hInner (hq' ▸ (isClosedDisc_Δ₀_and_mem_of_mem_bar₀ P_pres hv).2),
      fun hb => hvK ?_⟩
    exact (hbdK v hvG).mp (by rw [hq, singleton_subset_iff]; exact hb)
  exact ⟨hbdK, H₁, H₂, hsep, hcut, hKH₁, hY₁, hUH₁, hUH₂, hbarH₂, hbar₀H₁⟩

/-- The last circuit of a nest cuts a rural composition into two rural neighborhoods and
an intermediate society. The initial nest remains available on the inner side. -/
theorem exists_nested_neighborhood_composition {S_comp S₀ : Society α β}
    {N : Neighborhood α β} {m : ℕ} (P_pres : Presentation N) (C : Fin m → Graph α β)
    (D : Fin m → Set EuclideanPlane) (last : Fin m) (hlast : ∀ j, j ≤ last)
    (hcir : ∀ j, IsGraphCircuit N.G (C j))
    (hdisj : Pairwise fun i j => Disjoint V(C i) V(C j))
    (hDd : ∀ j, IsClosedDisc (D j) ∧ subBd (D j) = graphDrawingSubgraphU P_pres.Γ (C j))
    (hDs : ∀ j, P_pres.Δ₀ ⊆ D j ∧ D j ⊆ P_pres.Δ)
    (hDm : ∀ i j, i ≤ j → D i ⊆ D j)
    (hDisjoint : Disjoint V(C last) N.Ω.bar) (hcomp : S_comp.IsComposition S₀ N) :
    ∃ (N₁ N₂ : Neighborhood α β) (P₁ : Presentation N₁) (S₁ : Society α β),
      IsGraphSeparation N.G N₁.G N₂.G ∧ V(N₁.G) ∩ V(N₂.G) = V(C last) ∧
      C last ≤ N₁.G ∧ N₁.Ω.bar = V(C last) ∧
      N.Ω.bar ⊆ V(N₂.G) ∧ N.Ω₀.bar ⊆ V(N₁.G) ∧
      N₁.IsRural ∧ N₂.IsRural ∧ N₁.IsNest P₁ C ∧
      S₁.G ≤ S_comp.G ∧ V(N₂.G) ∩ V(S₁.G) = V(C last) ∧
      S₁.IsComposition S₀ N₁ ∧ S_comp.IsComposition S₁ N₂ := by
  classical
  have hΩ : N.Ω = S_comp.Ω := hcomp.2.1
  have hNG : N.G ≤ S_comp.G := hcomp.1.1.2.1
  let Γ := P_pres.Γ
  have hKG : C last ≤ N.G := (hcir last).1
  obtain ⟨hbdK, H₁, H₂, hsep, hcut, hKH₁, hY₁, hUH₁, hUH₂, hbarH₂, hbar₀H₁⟩ :=
    P_pres.separate_at_circuit C D last (hcir last) (hDd last).1 (hDd last).2
      (hDs last).1 (hDs last).2 hDisjoint
  have hpt : ∀ v ∈ V(N.G), ∃ q, graphDrawingVertexSet Γ v = {q} := fun v hv =>
    ⟨_, graphDrawingVertexSet_eq_singleton Γ hv⟩
  have hK₂ : V(C last) ⊆ V(H₂) := fun v hv => (hcut.symm ▸ hv : v ∈ V(H₁) ∩ V(H₂)).2
  have hCH₁ : ∀ j, C j ≤ H₁ := by
    intro j
    exact nestedCircuitsOnInnerSide Γ hcir hdisj hDd hDm hlast
      hsep hcut hKH₁ hY₁ hpt hbdK j
  have hKne : V(C last).Nonempty := by
    obtain ⟨e, he⟩ := (hcir last).edgeSet_nonempty
    obtain ⟨u, w, hl⟩ : ∃ u w, (C last).IsLink e u w := exists_isLink_of_mem_edgeSet he
    exact ⟨u, hl.left_mem⟩
  have hKfin : V(C last).Finite := N.finite_V.subset hKG.vertexSet_mono
  obtain ⟨φ, hφ_cw⟩ := exists_isClockwiseDiscHomeo (hDd last).1
  let ν : α → EuclideanPlane := fun v =>
    if h : v ∈ V(N.G) then (Γ.iso.vertexEquiv ⟨v, h⟩).1 else 0
  have hν : ∀ v (h : v ∈ V(N.G)), graphDrawingVertexSet Γ v = {ν v} := by
    intro v h
    rw [graphDrawingVertexSet_eq_singleton Γ h]
    simp only [ν, h, ↓reduceDIte]
  obtain ⟨Ω₁, hΩ₁, hagK⟩ := exists_cyclicPerm_agrees_of_injOn φ ν hKfin hKne
    (fun u hu w hw e => graphDrawingVertexSet_inj Γ (x := ν u)
      (by rw [hν u (hKG.vertexSet_mono hu)]; rfl)
      (by rw [hν w (hKG.vertexSet_mono hw), e]; rfl))
    (fun v hv => by
      have := (hbdK v (hKG.vertexSet_mono hv)).mpr hv
      rw [hν v (hKG.vertexSet_mono hv), singleton_subset_iff] at this
      exact this)
  have hbarK : ∀ {v}, v ∈ Ω₁.bar → v ∈ V(N.G) := fun hv =>
    hKG.vertexSet_mono (hΩ₁ ▸ hv)
  have hag : DrawingAgreesWithOArcHomeo Γ Ω₁ (subBd (D last)) φ := by
    refine ⟨fun v hv => ?_, fun v₁ v₂ v₃ hc => ?_⟩
    · rw [hν v (hbarK hv), singleton_subset_iff]
      exact hagK.1 v hv
    · have hm := CyclicPerm.isClockwise3_iff.mp hc
      obtain ⟨t₁, t₂, t₃, h₁, h₂, h₃, e₁, e₂, e₃⟩ := hagK.2 v₁ v₂ v₃ hc
      refine ⟨t₁, t₂, t₃, h₁, h₂, h₃, ?_, ?_, ?_⟩
      · rw [hν v₁ (hbarK hm.2.2.2.1), e₁]
        rfl
      · rw [hν v₂ (hbarK hm.2.2.2.2.1), e₂]
        rfl
      · rw [hν v₃ (hbarK hm.2.2.2.2.2.1), e₃]
        rfl
  let N₁ : Neighborhood α β :=
    { G := H₁, Ω := Ω₁, Ω₀ := N.Ω₀, finite_V := N.finite_V.subset hsep.1.vertexSet_mono,
      finite_E := N.finite_E.subset hsep.1.edgeSet_mono,
      bar_subset := hΩ₁.subset.trans hKH₁.vertexSet_mono, bar₀_subset := hbar₀H₁ }
  let N₂ : Neighborhood α β :=
    { G := H₂, Ω := N.Ω, Ω₀ := Ω₁, finite_V := N.finite_V.subset hsep.2.1.vertexSet_mono,
      finite_E := N.finite_E.subset hsep.2.1.edgeSet_mono, bar_subset := hbarH₂,
      bar₀_subset := hΩ₁.subset.trans hK₂ }
  have hbdΩ₁ : ∀ G' : Graph α β, G' ≤ N.G → ∀ v ∈ V(G'),
      (graphDrawingVertexSet Γ v ⊆ subBd (D last) ↔ v ∈ Ω₁.bar) := by
    intro G' hG' v hv
    rw [hΩ₁]
    exact hbdK v (hG'.vertexSet_mono hv)
  obtain ⟨P₁, hP₁Δ, hP₁Δ₀, -, hP₁U⟩ := Presentation.exists_of_le (N' := N₁) P_pres hsep.1
    (hDd last).1 (hDs last).1
    (fun q hq => ⟨hUH₁ hq, (P_pres.U_subset (graphDrawingSubgraphU_subset_U Γ _ hq)).2⟩)
    (hbdΩ₁ H₁ hsep.1) (fun v hv => P_pres.mem_bd_Δ₀_iff v (hsep.1.vertexSet_mono hv))
    ⟨φ, hφ_cw, hag⟩ P_pres.agrees_Δ₀
  obtain ⟨P₂, -, -, -, -⟩ := Presentation.exists_of_le (N' := N₂) P_pres hsep.2.1
    P_pres.isClosedDisc_Δ (hDs last).2 hUH₂
    (fun v hv => P_pres.mem_bd_Δ_iff v (hsep.2.1.vertexSet_mono hv))
    (hbdΩ₁ H₂ hsep.2.1) P_pres.agrees_Δ (Or.inr ⟨(hDd last).1, φ, hφ_cw, hag⟩)
  have hrural₁ : N₁.IsRural := ⟨P₁.Γ, P₁.Δ, P₁.Δ₀, P₁.isClosedDisc_Δ, P₁.Δ₀_subset_Δ, P₁.U_subset,
    P₁.mem_bd_Δ_iff, P₁.mem_bd_Δ₀_iff, P₁.agrees_Δ, P₁.agrees_Δ₀⟩
  have hrural₂ : N₂.IsRural := ⟨P₂.Γ, P₂.Δ, P₂.Δ₀, P₂.isClosedDisc_Δ, P₂.Δ₀_subset_Δ, P₂.U_subset,
    P₂.mem_bd_Δ_iff, P₂.mem_bd_Δ₀_iff, P₂.agrees_Δ, P₂.agrees_Δ₀⟩
  have hnest₁ : N₁.IsNest P₁ C := by
    refine ⟨fun j => ⟨hCH₁ j, (hcir j).2⟩, hdisj, D, fun j => ⟨(hDd j).1, ?_⟩, fun j => ?_, hDm⟩
    · rw [hP₁U _ (hCH₁ j)]
      exact (hDd j).2
    · rw [hP₁Δ, hP₁Δ₀]
      exact ⟨(hDs j).1, hDm j last (hlast j)⟩
  have hH₁S : H₁ ≤ S_comp.G := hsep.1.trans hNG
  obtain ⟨hsU, hVU⟩ := hcomp.isGraphSeparation_union (IsGraphSeparation.symm hsep) hbar₀H₁
  have hsU' : IsGraphSeparation S_comp.G H₂ (subgraphUnion S_comp.G H₁ S₀.G) := hsU
  have hS₀S : S₀.G ≤ S_comp.G := hcomp.1.1.1
  let S₁ : Society α β :=
    { G := subgraphUnion S_comp.G H₁ S₀.G, Ω := Ω₁,
      finite_V := S_comp.finite_V.subset (subgraphUnion_le hH₁S hS₀S).vertexSet_mono,
      finite_E := S_comp.finite_E.subset (subgraphUnion_le hH₁S hS₀S).edgeSet_mono,
      bar_subset := fun v hv => Or.inl (hKH₁.vertexSet_mono (hΩ₁ ▸ hv)) }
  have hcutU : V(H₂) ∩ V(S₁.G) = V(C last) := by
    rw [show V(H₂) ∩ V(S₁.G) = V(H₂) ∩ V(H₁) from hVU, inter_comm, hcut]
  have hcomp₂ : S_comp.IsComposition S₁ N₂ := by
    refine ⟨⟨IsGraphSeparation.symm hsU', hΩ ▸ hbarH₂⟩, hΩ, rfl, ?_⟩
    change Ω₁.bar = V(S₁.G) ∩ V(H₂)
    rw [hΩ₁, inter_comm, hcutU]
  have hcomp₁ : S₁.IsComposition S₀ N₁ := by
    obtain ⟨⟨hs₀, -⟩, -, hΩ₀, hbar₀⟩ := hcomp
    have hUle₀ : S₀.G ≤ S₁.G := le_subgraphUnion_right hH₁S hS₀S
    have hUle₁ : H₁ ≤ S₁.G := le_subgraphUnion_left hH₁S hS₀S
    refine ⟨⟨⟨hUle₀, hUle₁, ?_, ?_, ?_⟩, ?_⟩, rfl, hΩ₀, ?_⟩
    · change V(S₀.G) ∪ V(H₁) = V(H₁) ∪ V(S₀.G)
      exact union_comm _ _
    · rw [show E(S₁.G) = E(H₁) ∪ E(S₀.G) from edgeSet_subgraphUnion hH₁S hS₀S]
      exact union_comm _ _
    · exact hs₀.2.2.2.2.mono_right hsep.1.edgeSet_mono
    · change Ω₁.bar ⊆ V(H₁)
      exact hΩ₁.subset.trans hKH₁.vertexSet_mono
    · change S₀.Ω.bar = V(S₀.G) ∩ V(H₁)
      apply Subset.antisymm
      · intro v hv
        refine ⟨S₀.bar_subset hv, hbar₀H₁ ?_⟩
        rw [hΩ₀]
        exact hv
      · rintro v ⟨hv₀, hv₁⟩
        rw [hbar₀]
        exact ⟨hv₀, hsep.1.vertexSet_mono hv₁⟩
  exact ⟨N₁, N₂, P₁, S₁, hsep, hcut, hKH₁, hΩ₁, hbarH₂, hbar₀H₁, hrural₁, hrural₂,
    hnest₁, subgraphUnion_le hH₁S hS₀S, hcutU, hcomp₁, hcomp₂⟩

/-- **Graph Minors IX, (10.4)** (page 65):
"Let $p \ge 2$ with $p \ne 3$. Let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth
$\ge p + 5$, and let $X \subseteq \bar{\Omega}$ be linked with $|X| \ge 2p + 8$." -/
theorem theorem_10_4_proof {S_comp S₀ : Society α β} {N : Neighborhood α β} {p : ℕ} {X : Set α}
    (hp2 : 2 ≤ p) (hp3 : p ≠ 3) (hbreadth : N.HasBreadthGe (p + 5))
    (hX : N.IsLinked X) (hcard : 2 * p + 8 ≤ X.ncard) (hcomp : S_comp.IsComposition S₀ N)
    {P₀ : Set (Graph α β)} (hP₀ : S_comp.IsCrookedTransaction P₀) (hp : p ≤ P₀.ncard) :
    ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ p ≤ P'.ncard ∧
      S_comp.transactionEnds P' ⊆ X ∧
      ∀ P ∈ P', Disjoint (pathInternalVerts S_comp.G P) S_comp.Ω.bar := by
  classical
  obtain ⟨P_pres, C', hC'⟩ := hbreadth
  obtain ⟨C, P, x, t, hC, hCbar, hP, hPd, hI⟩ := exists_clean_paths P_pres hC' hX
  have hΩ : N.Ω = S_comp.Ω := hcomp.2.1
  have hNG : N.G ≤ S_comp.G := hcomp.1.1.2.1
  let last : Fin (p + 4) := ⟨p + 3, by omega⟩
  obtain ⟨hcir, hdisj, D, hDd, hDs, hDm⟩ := hC
  obtain ⟨N₁, N₂, P₁, S₁, hsep, hcut, hKH₁, hΩ₁, hbarH₂, hbar₀H₁, hrural₁, hrural₂,
      hnest₁, hS₁S, hcutU, hcomp₁, hcomp₂⟩ :=
    exists_nested_neighborhood_composition P_pres C D last (fun j => Fin.mk_le_mk.mpr (by omega))
      hcir hdisj hDd hDs hDm (hCbar last) hcomp
  let H₁ := N₁.G
  let H₂ := N₂.G
  have hsplit : ∀ i, ∃ (y : α) (R W : Graph α β), y ∈ V(C last) ∧
      IsGraphPathWithEnds H₂ R (x i) y ∧ V(R) ⊆ V(P i) ∧ V(R) ∩ V(C last) = {y} ∧
      IsGraphPathWithEnds H₁ W y (t i) ∧ V(W) ⊆ V(P i) := by
    intro i
    obtain ⟨I, hIp, hIP, hIK, hVI⟩ := hI i last
    exact splitPathAtInnerCircuit hsep hcut hKH₁ (hP i).1.1 hIp hIP hIK hVI
      (hbarH₂ ((hP i).2.symm ▸ (mem_singleton _ : x i ∈ {x i})).2)
      (hbar₀H₁ ((hP i).1.2.2.symm ▸ (mem_singleton _ : t i ∈ {t i})).2)
  choose y R W hyK hR hRP hRK hW hWP using hsplit
  have hyR : ∀ i, y i ∈ V(R i) := fun i => (hR i).right_mem
  have hy_inj : Injective y := by
    intro i j e
    by_contra hne
    exact Set.disjoint_left.mp (hPd hne) (hRP i (hyR i)) (e ▸ hRP j (hyR j))
  have hx_inj : Injective x := by
    intro i j e
    by_contra hne
    exact Set.disjoint_left.mp (hPd hne) (hP i).1.1.left_mem (e ▸ (hP j).1.1.left_mem)
  have hRd : ∀ {i j}, i ≠ j → Disjoint V(R i) V(R j) := fun hne =>
    (hPd hne).mono (hRP _) (hRP _)
  have hYcard : (range y).ncard = X.ncard := by
    rw [← image_univ, ncard_image_of_injective _ hy_inj, ncard_univ, Nat.card_fin]
  have hΩ₀ : N₁.Ω₀ = N.Ω₀ := hcomp₁.2.2.1.trans hcomp.2.2.1.symm
  have hweak : N₁.IsWeaklyLinked (range y) := by
    exact weakLinkingAlongOuterPaths (N₁ := N₁) hYcard
      (fun i => hΩ₁.symm ▸ hyK i) hW hPd hWP hRP hyR (fun i => hΩ₀.symm ▸ (hP i).1.2.2)
  obtain ⟨T₀, hT₀, hpT₀⟩ := theorem_9_1_proof hcomp₂ hrural₂ hP₀ hp
  obtain ⟨T, hT, hpT, hTends⟩ := theorem_10_3_proof hp2 hp3 hrural₁ ⟨P₁, C, hnest₁⟩ hweak
    (by rw [hYcard]; exact hcard) hcomp₁ hT₀ hpT₀
  refine extendTransactionAcrossNeighborhood (N₂ := N₂) (K := C last) (by omega)
    hS₁S (hsep.2.1.trans hNG) hcutU hcomp₂.2.1 hcomp₂.2.2.1
    hrural₂ (fun v hv => hbarH₂ (hΩ ▸ hv)) (hΩ ▸ hCbar last)
    hR hRK hy_inj hx_inj hRd (fun i => hcomp₁.2.1 ▸ (hΩ₁.symm ▸ hyK i)) ?_ ?_ ?_ hT hpT hTends
  · intro i
    have hx : x i ∈ V(P i) ∩ N.Ω.bar := (hP i).2.symm ▸ mem_singleton _
    exact hΩ ▸ hx.2
  · intro i
    exact ((hP i).1.2.1.symm ▸ mem_singleton _ : x i ∈ V(P i) ∩ X).2
  · intro i
    apply Subset.antisymm
    · intro v hv
      have hmem : v ∈ V(P i) ∩ N.Ω.bar := ⟨hRP i hv.1, hΩ ▸ hv.2⟩
      rwa [(hP i).2] at hmem
    · rintro _ rfl
      exact ⟨(hR i).left_mem, hΩ ▸ ((hP i).2.symm ▸ mem_singleton _ :
        x i ∈ V(P i) ∩ N.Ω.bar).2⟩

end GraphMinor.GM09

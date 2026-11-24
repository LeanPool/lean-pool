/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.TreeStep
public import LeanPool.GraphMinor.GM07.ForestParts

/-!
# Graph Minors VII, (4.4): a forest that avoids the cut

Graph Minors VII states (4.4) on page 223 with no proof, and offers an induction on `|E(L)|` as an
example. Here we do the following instead.

First a move takes the finitely many points that the parts of `L` shrink to away from `H₀`
(`exists_move_off`), except for the vertices of `H₀` on `bd(Σ)`. Then one move shrinks each part of
`L` near its point (`exists_gather`). In the end, a part of `L` meets the forest only if it has a
vertex `z` of `H₀` on `bd(Σ)`, and only near `z`. At each such `z` the edges are moved to one side
of the part by `exists_root_step` (`exists_root_steps`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- A flat set stays flat when pulled back by a homeomorphism. -/
theorem Flat.preimage_homeo {A : Set S} (h : Flat A) (G : S ≃ₜ S) : Flat (G ⁻¹' A)
  := fun a b p q hp hq => by
  obtain ⟨F⟩ := h (p.map G.continuous) (q.map G.continuous) hp hq
  refine ⟨⟨⟨⟨fun w => G.symm (F w), by fun_prop⟩, fun x => ?_, fun x => ?_⟩, fun t x hx => ?_⟩⟩
  · simp
  · simp
  · rcases hx with rfl | hx
    · simp
    · obtain rfl : x = 1 := hx
      simp

/-- The steps of (4.4) at all roots. They do not interfere, because each one takes place in its own
flat set. -/
theorem exists_root_steps (hS : IsSurface S) {L : Drawing S} {φ : S' → S}
  (hJ : IsCutAlongGraph L S' φ) (hNo : NoArcs L) {Z : Set S} (hZ : Z.Finite) (T F : S → Set S)
    (l : S → S')
    (hT : ∀ z ∈ Z, IsPreconnected (T z) ∧ IsClosed (T z) ∧ IsClosed (L.U \ T z) ∧ T z ⊆ L.U
      ∧ z ∈ T z ∧ z ∈ bd S ∧ φ (l z) = z ∧ IsOpen (F z) ∧ Flat (F z) ∧ T z ⊆ F z)
    (hd : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → Disjoint (F z) (F z')) {H : Drawing S}
      (hH : IsSurfaceForest H) (hV : ∀ z ∈ Z, ∀ v ∈ H.V, v ≠ z → v ∉ T z)
        (hE : ∀ z ∈ Z, ∀ e ∈ H.E, SplitEdge (closure e) (F z) z (T z)) :
    ∃ P : Drawing S, P.V = H.V ∧ IsSurfaceForest P ∧ ForestsHomotopic P H ∧
      (∀ z ∈ Z, P.U ∩ T z ⊆ {z}) ∧ P.U ⊆ H.U ∪ ⋃ z ∈ Z, F z ∧ ∀ z ∈ Z, ∀ z' ∈ φ ⁻¹' {z}, z' ≠ l z
        → z' ∉ closure (φ ⁻¹' (P.U \ P.V)) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hφ := hJ.quotientMap.continuous
  have key : ∀ J : Set S, J.Finite → J ⊆ Z → ∃ P : Drawing S, P.V = H.V ∧ IsSurfaceForest P
    ∧ ForestsHomotopic P H ∧ (∀ z ∈ J, P.U ∩ T z ⊆ {z}) ∧ P.U ⊆ H.U ∪ ⋃ z ∈ J, F z ∧
      (∀ z ∈ J, ∀ z' ∈ φ ⁻¹' {z}, z' ≠ l z → z' ∉ closure (φ ⁻¹' (P.U \ P.V))) ∧ ∀ z ∈ Z, z ∉ J
        → ∀ e ∈ P.E, SplitEdge (closure e) (F z) z (T z) := by
    intro J hJ
    induction J, hJ using Set.Finite.induction_on with
    | empty =>
      refine fun _ => ⟨H, rfl, hH, ?_, by simp, ?_, by simp, fun z hz _ e he => hE z hz e he⟩
      · have h0 := forestsHomotopic_of_move (α := Homeomorph.refl S) IsMove.refl hH
        rwa [mapDrawingHomeo_refl] at h0
      · simp
    | @insert z₀ J hz₀ _ ih =>
      intro hsub
      obtain ⟨P, hPV, hPf, hPh, h1, h2, h3, h4⟩ := ih fun x hx => hsub (mem_insert_of_mem _ hx)
      have hz₀Z := hsub (mem_insert _ _)
      obtain ⟨hp, hc, hr, hU, hmem, hb, hl, ho, hfl, hTF⟩ := hT z₀ hz₀Z
      obtain ⟨Pn, Y, hYc, hYF, hnV, hnf, hnh, hnT, hnE, hnU, hnC⟩ := exists_root_step hS hJ hNo hp
        hc hr hU hmem hb hl (H := P) hPf ho hfl hTF (fun v hv => hV z₀ hz₀Z v (hPV ▸ hv))
          (h4 z₀ hz₀Z hz₀)
      have hdz : ∀ z ∈ J, Disjoint (F z) (F z₀) := fun z hz => hd z (hsub
        (mem_insert_of_mem _ hz)) z₀ hz₀Z fun h => hz₀ (h ▸ hz)
      have hYT : ∀ z ∈ J, Disjoint Y (T z) := fun z hz => ((hdz z hz).symm.mono_left
        hYF).mono_right (hT z (hsub (mem_insert_of_mem _ hz))).2.2.2.2.2.2.2.2.2
      refine ⟨Pn, hnV.trans hPV, hnf, ForestsHomotopic.trans hnh hPh, fun z hz q hq => ?_,
        fun q hq => ?_, fun z hz z' hz' hne hin => ?_, fun z hzZ hzn e he => ?_⟩
      · rcases hz with rfl | hz
        · exact hnT hq
        · rcases hnU hq.1 with h | h
          · exact h1 z hz ⟨h, hq.2⟩
          · exact (disjoint_left.mp (hYT z hz) h hq.2).elim
      · rcases hnU hq with h | h
        · rcases h2 h with h' | h'
          · exact .inl h'
          · obtain ⟨z, hz, h'⟩ := mem_iUnion₂.mp h'
            exact .inr (mem_iUnion₂.mpr ⟨z, mem_insert_of_mem _ hz, h'⟩)
        · exact .inr (mem_iUnion₂.mpr ⟨z₀, mem_insert _ _, hYF h⟩)
      · rcases hz with rfl | hz
        · exact hnC z' hz' hne hin
        · have hsub' : φ ⁻¹' (Pn.U \ Pn.V) ⊆ closure (φ ⁻¹' (P.U \ P.V)) ∪ φ ⁻¹' Y := by
            rintro q ⟨hq1, hq2⟩
            rcases hnU hq1 with h | h
            · exact .inl (subset_closure ⟨h, fun h' => hq2 (by rw [hnV]; exact h')⟩)
            · exact .inr h
          rcases closure_minimal hsub' (isClosed_closure.union (hYc.preimage hφ)) hin with h | h
          · exact h3 z hz z' hz' hne h
          · have h5 : φ z' = z := hz'
            have h6 : z ∈ T z := (hT z (hsub (mem_insert_of_mem _ hz))).2.2.2.2.1
            exact disjoint_left.mp (hYT z hz) h (h5 ▸ h6)
      · have hzJ : z ∉ J := fun h => hzn (mem_insert_of_mem _ h)
        have hne : z ≠ z₀ := fun h => hzn (h ▸ mem_insert _ _)
        obtain ⟨e₀, he₀, hs1, hs2⟩ := hnE e he
        have hTz := (hT z hzZ).2.2.2.2.2.2.2.2.2
        exact (h4 z hzZ hzJ e₀ he₀).change isClosed_closure hYc (hd z hzZ z₀ hz₀Z hne)
          ((hd z hzZ z₀ hz₀Z hne).symm.mono_left hYF |>.mono_right hTz) hs1 hs2
  obtain ⟨P, h1, h2, h3, h4, h5, h6, -⟩ := key Z hZ subset_rfl
  exact ⟨P, h1, h2, h3, h4, h5, h6⟩

/-- A finite connected set has at most one point. -/
theorem eq_of_finite_preconnected [T1Space S] {A : Set S} (hf : A.Finite)
  (hp : IsPreconnected A) {a b : S} (ha : a ∈ A) (hb : b ∈ A) : a = b := by
  classical
  by_contra hne
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hp {a} (A \ {a}) isClosed_singleton
    (hf.subset sdiff_subset).isClosed (fun x hx => by
      by_cases h : x = a
      · exact .inl h
      · exact .inr ⟨hx, h⟩) (by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff, mem_sdiff, mem_empty_iff_false, iff_false]
      tauto) with h | h
  · exact hne (h hb).symm
  · exact (h ha).2 rfl

private theorem split_forest_edge_near_boundary_vertex
    {S : Type}
    [TopologicalSpace S]
    (H₀ : Drawing S)
    [T2Space S]
    (H₁ : Drawing S)
    (hH₁ : IsSurfaceForest H₁)
    (hX : H₁.V ∩ bd S = H₀.V ∩ bd S)
    (Z : Set S)
    (base : S → Set S)
    (F : S → Set S)
    (hF : ∀ z ∈ Z, F z ⊆ base z ∧ z ∈ F z ∧ IsOpen (F z) ∧ IsFlat (F z))
    (z : S)
    (hz : z ∈ Z)
    (hzBd : z ∈ H₀.V ∩ bd S)
    (e : Set S)
    (he : e ∈ H₁.E) :
    ∃ Q₂ Q₁ : Set S, IsClosed Q₂ ∧ closure e = Q₁ ∪ Q₂ ∧ Q₁ ⊆ F z ∧ IsPreconnected Q₁ ∧
      (Q₁.Nonempty → z ∈ Q₁) ∧ z ∉ Q₂ := by
  by_cases hze : z ∈ closure e
  · have hzV : z ∈ H₁.V := by
      have : z ∈ H₁.V ∩ bd S := hX ▸ hzBd
      exact this.1
    obtain ⟨u, v, -, hcap, hline⟩ := edge_line_of_forest hH₁.2 he
    have hzc : z ∈ ({u, v} : Set S) := by rw [← hcap]; exact ⟨hze, hzV⟩
    obtain ⟨y, hline'⟩ : ∃ y, IsLineWithEnds (closure e) z y := by
      rcases hzc with rfl | h
      · exact ⟨v, hline⟩
      · obtain rfl : z = v := h
        exact ⟨u, hline.symm⟩
    obtain ⟨f, hf0, -⟩ := hline'
    let a : unitInterval → S := fun t => (f t).1
    have hac : Continuous a := by fun_prop
    have hai : Function.Injective a := fun s t h => f.injective (Subtype.ext h)
    have hr : range a = closure e := by
      ext q
      exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hq => ⟨f.symm ⟨q, hq⟩, by simp [a]⟩⟩
    have ha0 : a 0 = z := hf0
    obtain ⟨t, ht0, -, htN⟩ := exists_initial hac (hF z hz).2.2.1
      (show a 0 ∈ F z by rw [ha0]; exact (hF z hz).2.1)
    refine ⟨a '' Ici t, a '' Iic t, (isClosed_Ici.isCompact.image hac).isClosed, ?_, ?_,
      isPreconnected_Iic.image a hac.continuousOn, fun _ => ⟨0, unitInterval.nonneg t, ha0⟩, ?_⟩
    · rw [← hr, ← image_univ, ← image_union, Iic_union_Ici]
    · rintro _ ⟨s, hs, rfl⟩
      exact htN s hs
    · rintro ⟨s, hs, he'⟩
      have h1 : s = 0 := hai (he'.trans ha0.symm)
      rw [h1] at hs
      exact absurd (show t.1 ≤ 0 from hs) (not_le.mpr ht0)
  · exact ⟨closure e, ∅, isClosed_closure, by simp, empty_subset _, isPreconnected_empty,
      by simp, hze⟩

private theorem boundary_vertex_avoids_far_edge_pieces
    {S : Type}
    [TopologicalSpace S]
    (H₁ : Drawing S) :
    ∀ (Z : Set S),
    ∀ (F : S → Set S),
    ∀ (Q₂ : S → Set S → Set S),
    ∀ (Q₁ : S → Set S → Set S),
    (∀ z ∈ Z, ∀ e ∈ H₁.E, IsClosed (Q₂ z e) ∧ closure e = Q₁ z e ∪ Q₂ z e ∧ Q₁ z e ⊆ F z ∧
      IsPreconnected (Q₁ z e) ∧ ((Q₁ z e).Nonempty → z ∈ Q₁ z e) ∧ z ∉ Q₂ z e) →
    let Cz : S → Set S := fun z => (⋃ e ∈ H₁.E, Q₂ z e) ∪ H₁.V \ {z}
    ∀ (z : S),
    (z ∈ Z) →
    z ∉ Cz z := by
  intro Z F Q₂ Q₁ hQ Cz z hz
  rintro (h | h)
  · obtain ⟨e, he, h⟩ := mem_iUnion₂.mp h
    exact (hQ z hz e he).2.2.2.2.2 h
  · exact h.2 rfl

private theorem move_boundary_components_into_local_neighbourhoods
    {S : Type}
    [TopologicalSpace S]
    (L : Drawing S)
    (H₀ : Drawing S)
    (K : Set (Set S))
    (hparts : ∀ C ∈ K, IsPreconnected C ∧ IsClosed C ∧ IsClosed (L.U \ C) ∧ C ⊆ L.U)
    (Rall : Set S) :
    let Z : Set S := H₀.V ∩ bd S ∩ L.U
    let Y₁ : Set S := Rall ∪ Z
    ∀ (cmp : S → Set S),
    (∀ y ∈ L.U, cmp y ∈ K) →
    (∀ y ∈ L.U, y ∈ cmp y) →
    ∀ (O : S → Set S),
    (Y₁.PairwiseDisjoint O) →
    let base : S → Set S := fun y => O y ∩ (L.U \ cmp y)ᶜ
    ∀ (N : S → Set S),
    (∀ y ∈ Y₁, IsOpen (N y)) →
    (∀ y ∈ Y₁, y ∈ N y) →
    (∀ y ∈ Y₁, N y ⊆ base y) →
    let NP : Set S → Set S := fun C => ⋃ y ∈ Y₁ ∩ C, N y
    ∀ (G : S ≃ₜ S),
    (∀ C ∈ K, ∀ z ∈ C, G z ∈ NP C) →
    (∀ z ∈ bd S, G z = z) →
    ∀ (z : S),
    (z ∈ Z) →
    ∀ q ∈ cmp z, G q ∈ N z := by
  intro Z Y₁ cmp hcmpK hcmpM O hOd base N hNo hyN hNb NP G hGN hGb z hz
  have hzU : z ∈ L.U := hz.2
  have hC := hcmpK z hzU
  have hzY : z ∈ Y₁ := .inr hz
  have hconn : IsPreconnected (G '' cmp z) := (hparts _ hC).1.image G G.continuous.continuousOn
  let v : Set S := ⋃ y ∈ (Y₁ ∩ cmp z) \ {z}, N y
  have hsub : G '' cmp z ⊆ N z ∪ v := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨y, hy, h1⟩ := mem_iUnion₂.mp (hGN _ hC q hq)
    by_cases hyz : y = z
    · exact .inl (hyz ▸ h1)
    · exact .inr (mem_iUnion₂.mpr ⟨y, ⟨hy, hyz⟩, h1⟩)
  have hd' : Disjoint (N z) v := by
    rw [disjoint_left]
    intro q h1 h2
    obtain ⟨y, hy, h3⟩ := mem_iUnion₂.mp h2
    exact disjoint_left.mp (hOd hzY hy.1.1 (Ne.symm hy.2)) (hNb z hzY h1).1 (hNb y hy.1.1 h3).1
  have hvOpen : IsOpen v := isOpen_biUnion fun y hy => hNo y hy.1.1
  have hmain := hconn.subset_left_of_subset_union (hNo z hzY) hvOpen hd' hsub
    ⟨z, ⟨z, hcmpM z hzU, hGb z hz.1.2⟩, hyN z hzY⟩
  exact fun q hq => hmain (mem_image_of_mem G hq)

/-- **(4.4) of Graph Minors VII** (page 223). Let `L` be a proper graph with no isolated vertices in
`Σ`, such that no subset of `U(L)` is an `O`-arc or an `I`-arc, and let `φ` be the map of the cut
along `U(L)`. Let `H₀` be a forest in `Σ`, and for each vertex `z` of `H₀` on `bd(Σ)` let `l z` be a
point of `φ⁻¹(z)`. Then there is a forest `H` homotopic to `H₀` with `U(H) ∩ U(L) ⊆ bd(Σ)`, such
that every point of `φ⁻¹(z)` other than `l z` is an isolated vertex of `φ⁻¹(H)`. -/
theorem theorem_4_4_proof (hS : IsSurface S) (L : Drawing S) (φ : S' → S)
  (hJ : IsCutAlongGraph L S' φ) (hNoArc : ∀ F : Set S, F ⊆ L.U → ¬ IsOArc F ∧ ¬ IsIArc F)
    (H₀ : Drawing S) (l : S → S') (hH₀ : IsSurfaceForest H₀) (hl : ∀ z ∈ H₀.V ∩ bd S, φ (l z) = z) :
    ∃ (H : Drawing S) (H' : Drawing S'), IsSurfaceForest H ∧ ForestsHomotopic H H₀
      ∧ H.U ∩ L.U ⊆ bd S ∧ IsPullbackDrawing φ H H' ∧ ∀ z ∈ H₀.V ∩ bd S, ∀ z' ∈ φ ⁻¹' {z} \ {l z},
        IsIsolatedVertex H' z' := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hNoA : NoArcs L := ⟨fun F hF => (hNoArc F hF).1, fun F hF => (hNoArc F hF).2⟩
  have hY := hJ.isSurface
  have : T2Space S' := hY.2.1
  have hφ := hJ.quotientMap.continuous
  have hP := hJ.isProper
  have hn := hJ.noIsolated
  obtain ⟨K, hK, hparts, hcover, hdis, hdich⟩ := exists_parts hn
  obtain ⟨R, hR, hgather⟩ := exists_gather hS hP hn hNoA hK hparts hcover hdis hdich
  -- The roots off the boundary leave `H₀`.
  let Rall : Set S := ⋃ C ∈ K, R C
  have hRf : Rall.Finite := hK.biUnion fun C hC => (hR C hC).1
  have hRU : Rall ⊆ L.U := fun r hr => by
    obtain ⟨C, hC, h⟩ := mem_iUnion₂.mp hr
    exact (hparts C hC).2.2.2 ((hR C hC).2 h)
  obtain ⟨M, hM, hMoff⟩ := exists_move_off hS hH₀.2 (hRf.subset (sdiff_subset (t
    := bd S))) fun a ha => ha.2
  let H₁ : Drawing S := mapDrawingHomeo M.symm H₀
  have hH₁h : ForestsHomotopic H₁ H₀ := forestsHomotopic_of_move hM.symm hH₀
  have hH₁ : IsSurfaceForest H₁ := ⟨hH₁h.1, hH₁h.2.2.1⟩
  have hX : H₁.V ∩ bd S = H₀.V ∩ bd S := hH₁h.2.2.2.2.1
  have hoff1 : ∀ r ∈ Rall, r ∉ bd S → r ∉ H₁.U := fun r hr hb hU => by
    obtain ⟨q, hq, he⟩ := hU
    refine hMoff r ⟨hr, hb⟩ ?_
    have : M r = q := by rw [← he]; simp
    rw [this]
    exact hq
  -- The points, and disjoint open sets around them.
  let Z : Set S := (H₀.V ∩ bd S) ∩ L.U
  have hZf : Z.Finite := (H₀.finite_V.subset inter_subset_left).subset inter_subset_left
  let Y₁ : Set S := Rall ∪ Z
  have hY₁f : Y₁.Finite := hRf.union hZf
  have hY₁U : Y₁ ⊆ L.U := union_subset hRU inter_subset_right
  have hcmp : ∀ y, y ∈ L.U → ∃ C ∈ K, y ∈ C := hcover
  choose! cmp hcmpK hcmpM using hcmp
  have hcmpU : ∀ C ∈ K, ∀ y ∈ C, cmp y = C := fun C hC y hy => by
    have hyU := (hparts C hC).2.2.2 hy
    by_contra hne
    exact disjoint_left.mp (hdis _ (hcmpK y hyU) C hC hne) (hcmpM y hyU) hy
  obtain ⟨O, hO, hOd⟩ := hY₁f.t2_separation
  let base : S → Set S := fun y => O y ∩ (L.U \ cmp y)ᶜ
  have hbaseo : ∀ y ∈ Y₁, IsOpen (base y) := fun y hy => (hO y).2.inter (hparts _ (hcmpK y
    (hY₁U hy))).2.2.1.isOpen_compl
  have hybase : ∀ y ∈ Y₁, y ∈ base y := fun y hy => ⟨(hO y).1, fun h => h.2 (hcmpM y (hY₁U hy))⟩
  have hflat : ∀ z, z ∈ Z → ∃ W : Set S, W ⊆ base z ∧ z ∈ W ∧ IsOpen W ∧ IsFlat W := fun z hz => by
    obtain ⟨W, h1, h2, h3, -, h4, -⟩ := exists_chart_ball_subset hS z (hbaseo z (.inr hz))
      (hybase z (.inr hz))
    exact ⟨W, h1, h2, h3, h4⟩
  choose! F hF using hflat
  -- Each edge at a root splits near the root.
  have hsplit : ∀ z, z ∈ Z → ∀ e, e ∈ H₁.E → ∃ Q₂ Q₁ : Set S, IsClosed Q₂ ∧ closure e = Q₁ ∪ Q₂
    ∧ Q₁ ⊆ F z ∧ IsPreconnected Q₁ ∧ (Q₁.Nonempty → z ∈ Q₁) ∧ z ∉ Q₂ := fun z hz e he => by
    exact split_forest_edge_near_boundary_vertex (S := S) H₀ H₁ hH₁ hX Z base F hF z hz hz.1 e he
  choose! Q₂ Q₁ hQ using hsplit
  let Cz : S → Set S := fun z => (⋃ e ∈ H₁.E, Q₂ z e) ∪ (H₁.V \ {z})
  have hEfin : H₁.E.Finite := H₁.finite_edges
  have hCzc : ∀ z ∈ Z, IsClosed (Cz z) := fun z hz => (hEfin.isClosed_biUnion fun e he =>
    (hQ z hz e he).1).union (H₁.finite_V.subset sdiff_subset).isClosed
  have hzCz : ∀ z ∈ Z, z ∉ Cz z := fun z hz => by
    exact boundary_vertex_avoids_far_edge_pieces (S := S) H₁ Z F Q₂ Q₁ hQ z hz
  let N : S → Set S := fun y => if y ∈ Z then F y ∩ (Cz y)ᶜ else base y ∩ H₁.Uᶜ
  have hNZ : ∀ y ∈ Z, N y = F y ∩ (Cz y)ᶜ := fun y hy => ite_eq_left hy
  have hNn : ∀ y, y ∉ Z → N y = base y ∩ H₁.Uᶜ := fun y hy => ite_eq_right hy
  have hNo : ∀ y ∈ Y₁, IsOpen (N y) := fun y hy => by
    by_cases hyZ : y ∈ Z
    · rw [hNZ y hyZ]
      exact (hF y hyZ).2.2.1.inter (hCzc y hyZ).isOpen_compl
    · rw [hNn y hyZ]
      exact (hbaseo y hy).inter H₁.isClosed_U.isOpen_compl
  have hyN : ∀ y ∈ Y₁, y ∈ N y := fun y hy => by
    by_cases hyZ : y ∈ Z
    · rw [hNZ y hyZ]
      exact ⟨(hF y hyZ).2.1, hzCz y hyZ⟩
    · rw [hNn y hyZ]
      refine ⟨hybase y hy, fun hU => ?_⟩
      have hyR : y ∈ Rall := by
        rcases hy with h | h
        · exact h
        · exact (hyZ h).elim
      by_cases hb : y ∈ bd S
      · have h1 : y ∈ H₁.V ∩ bd S := ⟨hH₁.1 ⟨hb, hU⟩, hb⟩
        exact hyZ ⟨hX ▸ h1, hRU hyR⟩
      · exact hoff1 y hyR hb hU
  have hNb : ∀ y, y ∈ Y₁ → N y ⊆ base y := fun y hy q hq => by
    by_cases hyZ : y ∈ Z
    · rw [hNZ y hyZ] at hq
      exact (hF y hyZ).1 hq.1
    · rw [hNn y hyZ] at hq
      exact hq.1
  let NP : Set S → Set S := fun C => ⋃ y ∈ Y₁ ∩ C, N y
  obtain ⟨G, hG, hGN⟩ := hgather NP (fun C hC => ⟨isOpen_biUnion fun y hy => hNo y hy.1, fun r hr
    => mem_iUnion₂.mpr ⟨r, ⟨.inl (mem_iUnion₂.mpr ⟨C, hC, hr⟩), (hR C hC).2 hr⟩, hyN r (.inl
      (mem_iUnion₂.mpr ⟨C, hC, hr⟩))⟩⟩) (fun C hC D hD hne => by
    constructor
    · rw [disjoint_left]
      intro q hq hq'
      obtain ⟨y, hy, h1⟩ := mem_iUnion₂.mp hq
      obtain ⟨y', hy', h2⟩ := mem_iUnion₂.mp hq'
      have hyy : y ≠ y' := fun h => disjoint_left.mp (hdis C hC D hD hne) hy.2 (h ▸ hy'.2)
      exact disjoint_left.mp (hOd hy.1 hy'.1 hyy) (hNb y hy.1 h1).1 (hNb y' hy'.1 h2).1
    · rw [disjoint_left]
      intro q hq hqD
      obtain ⟨y, hy, h1⟩ := mem_iUnion₂.mp hq
      refine (hNb y hy.1 h1).2 ⟨(hparts D hD).2.2.2 hqD, ?_⟩
      rw [hcmpU C hC y hy.2]
      exact disjoint_right.mp (hdis C hC D hD hne) hqD)
  let H₂ : Drawing S := mapDrawingHomeo G.symm H₁
  have hH₂h : ForestsHomotopic H₂ H₁ := forestsHomotopic_of_move hG.symm hH₁
  have hH₂ : IsSurfaceForest H₂ := ⟨hH₂h.1, hH₂h.2.2.1⟩
  have hGb : ∀ z ∈ bd S, G z = z := hG.1
  have hGs : ∀ z ∈ bd S, G.symm z = z := fun z hz => by rw [Homeomorph.symm_apply_eq, hGb z hz]
  -- A part with a root stays near the root.
  have hNz : ∀ z ∈ Z, ∀ q ∈ cmp z, G q ∈ N z := fun z hz => by
    exact move_boundary_components_into_local_neighbourhoods (S := S) L H₀ K hparts Rall cmp
      hcmpK hcmpM O hOd  N hNo hyN hNb  G hGN hGb z hz
  have hNF : ∀ z ∈ Z, N z ⊆ F z := fun z hz q hq => by
    rw [hNZ z hz] at hq
    exact hq.1
  obtain ⟨P, hPV, hPf, hPh, hPT, hPU, hPC⟩ := exists_root_steps hS hJ hNoA hZf cmp (fun z
    => G ⁻¹' F z) l (fun z hz => by
      have hzU : z ∈ L.U := hz.2
      obtain ⟨h1, h2, h3, h4⟩ := hparts _ (hcmpK z hzU)
      exact ⟨h1, h2, h3, h4, hcmpM z hzU, hz.1.2, hl z hz.1, (hF z hz).2.2.1.preimage G.continuous,
        Flat.preimage_homeo (IsFlat.flat (hF z hz).2.2.2) G, fun q hq => hNF z hz (hNz z hz q hq)⟩)
          (fun z hz z' hz' hne => by
      rw [disjoint_left]
      intro q h1 h2
      exact disjoint_left.mp (hOd (.inr hz) (.inr hz') hne) ((hF z hz).1 h1).1
        ((hF z' hz').1 h2).1) hH₂ (fun z hz v hv hne hvT => by
      obtain ⟨v₁, hv₁, rfl⟩ := hv
      have h1 := hNz z hz _ hvT
      rw [Homeomorph.apply_symm_apply, hNZ z hz] at h1
      have hv₁z : v₁ = z := by
        by_contra hn
        exact h1.2 (.inr ⟨hv₁, hn⟩)
      rw [hv₁z] at hne
      exact hne (hGs z hz.1.2)) (fun z hz e he => by
      have he' : e ∈ (image G.symm) '' H₁.E := by
        rw [← mapDrawingHomeo_E]
        exact he
      obtain ⟨e₁, he₁, rfl⟩ := he'
      obtain ⟨hc₂, hc, hsub, hp, h0, hzq⟩ := hQ z hz e₁ he₁
      refine ⟨G.symm '' Q₁ z e₁, G.symm '' Q₂ z e₁, (G.symm.isClosed_image).mpr hc₂, ?_, ?_,
        hp.image _ G.symm.continuous.continuousOn, ?_, ?_⟩
      · rw [← G.symm.image_closure, hc, image_union]
      · rintro _ ⟨q, hq, rfl⟩
        change G (G.symm q) ∈ F z
        rw [Homeomorph.apply_symm_apply]
        exact hsub hq
      · rintro ⟨_, q, hq, rfl⟩
        exact ⟨z, h0 ⟨q, hq⟩, hGs z hz.1.2⟩
      · rw [disjoint_left]
        rintro _ ⟨q, hq, rfl⟩ hT
        have h1 := hNz z hz _ hT
        rw [Homeomorph.apply_symm_apply, hNZ z hz] at h1
        exact h1.2 (.inl (mem_iUnion₂.mpr ⟨e₁, he₁, hq⟩)))
  have hhom : ForestsHomotopic P H₀ := ForestsHomotopic.trans hPh (ForestsHomotopic.trans hH₂h hH₁h)
  -- The forest meets `U(L)` only at roots.
  have hcross : ∀ q ∈ P.U ∩ L.U, q ∈ Z := by
    rintro q ⟨hqP, hqL⟩
    have hC := hcmpK q hqL
    by_cases hroot : ∃ z ∈ Z, cmp z = cmp q
    · obtain ⟨z, hz, he⟩ := hroot
      have h1 := hPT z hz ⟨hqP, he ▸ hcmpM q hqL⟩
      rw [mem_singleton_iff.mp h1]
      exact hz
    · exfalso
      obtain ⟨y, hy, h1⟩ := mem_iUnion₂.mp (hGN _ hC q (hcmpM q hqL))
      have hyZ : y ∉ Z := fun h => hroot ⟨y, h, hcmpU _ hC y hy.2⟩
      rw [hNn y hyZ] at h1
      rcases hPU hqP with h | h
      · obtain ⟨q₁, hq₁, rfl⟩ := h
        rw [Homeomorph.apply_symm_apply] at h1
        exact h1.2 hq₁
      · obtain ⟨z, hz, h⟩ := mem_iUnion₂.mp h
        have hne : y ≠ z := fun h' => hyZ (h' ▸ hz)
        exact disjoint_left.mp (hOd hy.1 (.inr hz) hne) h1.1.1 ((hF z hz).1 h).1
  have hPVbd : ∀ z ∈ Z, z ∈ P.V := fun z hz => by
    have h1 : z ∈ H₁.V ∩ bd S := hX ▸ hz.1
    rw [hPV]
    exact ⟨z, h1.1, hGs z hz.1.2⟩
  have hPn : P.IsNormal L.U := fun q hq => hPVbd q (hcross q ⟨hq.2, hq.1⟩)
  obtain ⟨H', hp, -, -⟩ := exists_pullback hS hJ hPf hPn
  refine ⟨P, H', hPf, hhom, fun q hq => (hcross q hq).1.2, hp, fun z hz z' hz' => ?_⟩
  have hφz : φ z' = z := hz'.1
  have hzPV : z ∈ P.V := by
    have h1 : z ∈ P.V ∩ bd S := by rw [hhom.2.2.2.2.1]; exact hz
    exact h1.1
  refine ⟨by rw [hp.2]; change φ z' ∈ P.V; rw [hφz]; exact hzPV, fun e' he' hinc => ?_⟩
  have hin : z' ∈ closure e' := hinc.2.2
  by_cases hzL : z ∈ L.U
  · refine hPC z ⟨hz, hzL⟩ z' hz'.1 (fun h => hz'.2 h) (closure_mono (fun q hq => ?_) hin)
    have h1 := he'.2.1 hq
    rw [hp.1, hp.2] at h1
    exact h1
  · have hconn := isPreconnected_preimage_tree hS hJ hNoA isPreconnected_singleton
      isClosed_singleton (T := {z}) (by
      have : L.U \ {z} = L.U := sdiff_singleton_eq_self hzL
      rw [this]
      exact L.isClosed_U)
    exact hz'.2 (eq_of_finite_preconnected (hJ.finite_fiber z) hconn hz'.1 (hl z hz))

end GraphMinor.GM07

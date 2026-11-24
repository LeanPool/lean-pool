/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Cited
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.Section4c

/-!
# Graph Minors XIV, Section 3: tangles, zones, and clearing

This file formalizes Section 3 of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50
(pages 27–29):

- `theorem_3_1`: Graph Minors XIV, (3.1) (page 28), showing that for a closed walk `W` of a radial
  drawing `K` of `H` with length `< 2θ` and an atom `x ∈ A(H)` with corresponding atom `x'` of `K`,
  `x' ⊆ ins(W)` if and only if `x ∩ ins(W) ≠ ∅`.
- `clearedSubdrawing_isTwoCell`: for a `λ`-zone `Λ` around `z` in a 2-cell drawing `H`, the cleared
  subdrawing `H' = H ∩ (Σ - Λ)` has `Λ` as a region and every other region of `H'` is a region of
  `H`, so `H'` is a 2-cell subdrawing of `H`.
- `theorem_3_2`: Graph Minors XIV, (3.2) (page 28), existence and uniqueness of a tangle of order
  `θ - 4λ - 2` obtained by clearing a `λ`-zone `Λ`, proved from Graph Minors XII, (7.10)
  (`GM12Theorem710Statement`), in `Section3Proved.lean`.
- `freeSet_subset`: any subset of a free set is free (Graph Minors X, (12.2), cited on page 28).
-/

public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-! ## Proof of (3.1) -/

omit [T1Space S] in
/-- If a subdrawing `L` of `K` has a point in a region `c` of `H`, it has the vertex of `K` in `c`:
an edge of `K` in `c` has an end off `V(H)`, and that end lies in `c`. -/
private theorem vertex_of_mem_region [LocallyConnectedSpace S] {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsPreRadialDrawing K) {c : Set S} (hc : c ∈ H.R)
    {L : Drawing S} (hL : L.IsSubdrawing K) {x w : S} (hxL : x ∈ L.U) (hxc : x ∈ c) (hw : w ∈ c)
    (hwK : w ∈ K.V) : w ∈ L.V := by
  obtain ⟨hUU, hVV, huniq, -, hbip, -⟩ := hK
  have hUU' : H.U ∩ K.U = H.V := hUU
  have hVV' : H.V ⊆ K.V := hVV
  have huniq' : ∀ r ∈ H.R, ∃! w, w ∈ r ∧ w ∈ K.V := huniq
  have heq : ∀ y ∈ c, y ∈ K.V → y = w := fun y hy hyK =>
    (huniq' c hc).unique ⟨hy, hyK⟩ ⟨hw, hwK⟩
  by_cases hxV : x ∈ L.V
  · rw [← heq x hxc (hL.1 hxV)]
    exact hxV
  obtain ⟨e, he, hxe⟩ := L.exists_edge_of_mem hxL hxV
  have heK := hL.2 he
  obtain ⟨v, hv, w', hw', hcap⟩ := hbip e heK
  have hedis : Disjoint e H.U := disjoint_left.mpr fun y hy hyU => by
    have hyK : y ∈ K.U := (heK.2.1 hy).1
    have : y ∈ H.U ∩ K.U := ⟨hyU, hyK⟩
    rw [hUU'] at this
    exact (heK.2.1 hy).2 (hVV' this)
  have hsub : e ⊆ c := subset_region hc
    (show IsPathConnected e from heK.2.2.1).isConnected.isPreconnected hedis hxe hxc
  have hw'mem : w' ∈ closure e ∩ K.V := by rw [hcap]; simp
  have hw'U : w' ∉ H.U := fun h => by
    have : w' ∈ H.U ∩ K.U := ⟨h, K.V_subset_U hw'mem.2⟩
    rw [hUU'] at this
    exact hw'.2 this
  have hw'c : w' ∈ c := by
    rcases closure_region_subset hc (closure_mono hsub hw'mem.1) with h | h
    · exact h
    · exact absurd h hw'U
  rw [← heq w' hw'c hw'mem.2]
  exact ((hL.closure_inter_V he).symm ▸ hw'mem : w' ∈ closure e ∩ L.V).2

omit [T1Space S] in
/-- A preconnected set that meets a closed set `D` and misses its frontier lies in `D`. -/
theorem subset_of_disjoint_frontier {A D : Set S} (hA : IsPreconnected A) (hD : IsClosed D)
    (hdis : Disjoint A (frontier D)) {x : S} (hx : x ∈ A) (hxD : x ∈ D) : A ⊆ D := by
  have hcov : A ⊆ interior D ∪ Dᶜ := by
    intro y hy
    by_cases hyD : y ∈ D
    · refine Or.inl ?_
      by_contra h
      exact disjoint_left.mp hdis hy ⟨subset_closure hyD, h⟩
    · exact Or.inr hyD
  have hxi : x ∈ interior D := (hcov hx).resolve_right (fun h => h hxD)
  intro y hy
  by_contra hyD
  obtain ⟨z, -, hz₁, hz₂⟩ := hA _ _ isOpen_interior hD.isOpen_compl hcov ⟨x, hx, hxi⟩ ⟨y, hy, hyD⟩
  exact hz₂ (interior_subset hz₁)

/-- Graph Minors XIV, (3.1) (page 28):
"If $W$ is a closed walk of $K$ with length $<2\theta$ (so that $ins(W)$ is defined), and $x
\in A(H)$, and $x'$ is the corresponding atom of $K$, then $x' \subseteq ins(W)$ if and only
if $x \cap ins(W) \ne \emptyset$." -/
theorem theorem_3_1_proof {H K : Drawing S} (hS : IsClosedSurface S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins) {x x' : Set S}
    (hx : IsCorrespondingAtom H K x x') {u : S} (W : GraphWalk K.toGraph u u)
    (hl : W.length < 2 * θ) :
    x' ⊆ insWalk ins K W ↔ (x ∩ insWalk ins K W).Nonempty := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have : T2Space S := hS.2.1
  have hP := hK.2.1
  have hLs : (walkDrawing K W).IsSubdrawing K := walkDrawing_isSubdrawing K W
  have hdisc : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing (walkDrawing K W) →
      IsClosed (ins C) ∧ frontier (ins C) = C.U ∧ C.U ⊆ ins C := by
    intro C hC hCs
    have hlen : C.length < 2 * θ := by
      refine lt_of_le_of_lt ?_ hl
      have hsub : C.E ⊆ {e | e ∈ W.edges} := by
        have := hCs.2
        rwa [walkDrawing_E] at this
      calc C.E.ncard ≤ ({e | e ∈ W.edges} : Set (Set S)).ncard :=
            Set.ncard_le_ncard hsub (List.finite_toSet _)
        _ ≤ W.edges.length := by
            rw [show ({e | e ∈ W.edges} : Set (Set S)) = ↑W.edges.toFinset by ext; simp,
              Set.ncard_coe_finset]
            exact List.toFinset_card_le _
        _ = W.length := rfl
    obtain ⟨h₁, h₂, -⟩ := hd C hC (hCs.trans hLs) hlen
    have hcl : IsClosed (ins C) := h₁.isClosed
    have hfr : frontier (ins C) = C.U := by rw [subBd_eq_frontier', h₂]
    exact ⟨hcl, hfr, hfr ▸ hcl.frontier_subset⟩
  constructor
  · intro h
    obtain ⟨-, -, hcase⟩ := hx
    rcases hcase with ⟨v, -, rfl, rfl⟩ | ⟨he, hr, hsub⟩ | ⟨hr, v, hv, rfl⟩
    · exact ⟨v, rfl, h rfl⟩
    · obtain ⟨y, hy⟩ := he.1
      exact ⟨y, hy, h (hsub hy)⟩
    · exact ⟨v, hv.2, h rfl⟩
  · rintro ⟨y, hyx, hyW⟩
    obtain ⟨-, -, hcase⟩ := hx
    rcases hcase with ⟨v, -, rfl, rfl⟩ | ⟨he, hr, hsub⟩ | ⟨hr, w, hw, rfl⟩
    · exact singleton_subset_iff.mpr (by rwa [mem_singleton_iff.mp hyx] at hyW)
    · have hUU : H.U ∩ K.U = H.V := hP.1
      have hyK : y ∉ K.U := fun h => by
        have hyU : y ∈ H.U := (he.2.1 hyx).1
        have : y ∈ H.U ∩ K.U := ⟨hyU, h⟩
        rw [hUU] at this
        exact (he.2.1 hyx).2 this
      have hdisr : Disjoint x' K.U := disjoint_left.mpr fun z hz hzU => region_subset hr hz hzU
      rcases hyW with hy | hy
      · exact absurd (hLs.U_subset hy) hyK
      · obtain ⟨C, ⟨hC, hCs⟩, hyC⟩ := mem_iUnion₂.mp hy
        obtain ⟨hcl, hfr, -⟩ := hdisc C hC hCs
        have hd' : Disjoint x' (frontier (ins C)) := by
          rw [hfr]
          exact hdisr.mono_right (hCs.trans hLs).U_subset
        have hin := subset_of_disjoint_frontier (region_isPreconnected hr) hcl hd' (hsub hyx) hyC
        exact fun z hz => Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hin hz⟩)
    · refine singleton_subset_iff.mpr ?_
      rcases hyW with hy | hy
      · exact Or.inl ((walkDrawing K W).V_subset_U
          (vertex_of_mem_region hP hr hLs hy hyx hw.2 hw.1))
      · obtain ⟨C, ⟨hC, hCs⟩, hyC⟩ := mem_iUnion₂.mp hy
        obtain ⟨hcl, hfr, hUin⟩ := hdisc C hC hCs
        refine Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, ?_⟩)
        by_cases hwC : w ∈ C.V
        · exact hUin (C.V_subset_U hwC)
        · refine subset_of_disjoint_frontier (region_isPreconnected hr) hcl ?_ hyx hyC hw.2
          rw [hfr]
          refine disjoint_left.mpr fun z hz hzC => hwC ?_
          exact vertex_of_mem_region hP hr (hCs.trans hLs) hzC hz hw.2 hw.1

/-! ## Regions of `H ∩ (Σ - Λ)` and Proof of (3.2) -/

omit [T1Space S] in
/-- An `O`-arc in a Hausdorff space is closed. -/
theorem IsOArc.isClosed [T2Space S] {F : Set S} (hF : IsOArc F) : IsClosed F := by
  obtain ⟨φ⟩ := hF
  have : CompactSpace F := φ.compactSpace
  exact (isCompact_iff_compactSpace.mpr this).isClosed

omit [T1Space S] in
private theorem exists_circle_arc_in_edge [T2Space S] {H : Drawing S} {F e : Set S}
    (φ : Circle ≃ₜ F) (hFU : F ⊆ H.U) (he : e ∈ H.E)
    {p : S} (hpF : p ∈ F) (hpe : p ∈ e) :
    ∃ (g : ℝ → S) (ε : ℝ), Continuous g ∧ g 0 = p ∧ 0 < ε ∧
      (∀ t ∈ Icc (-ε) ε, g t ∈ e) ∧ InjOn g (Icc (-ε) ε) ∧ range g ⊆ F := by
  let z₀ : Circle := φ.symm ⟨p, hpF⟩
  let g : ℝ → S := fun θ => (φ (z₀ * Circle.exp θ)).1
  have hg : Continuous g := by fun_prop
  have hg0 : g 0 = p := by simp [g, z₀]
  have hge : IsOpen {θ : ℝ | g θ ∈ e} := by
    have hEq : {θ : ℝ | g θ ∈ e} = g ⁻¹' (H.U \ e)ᶜ := by
      ext θ
      simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, mem_sdiff, not_and, not_not]
      exact ⟨fun h _ => h, fun h => h (hFU (φ _).2)⟩
    rw [hEq]
    exact (isClosed_U_sdiff_edge H he).isOpen_compl.preimage hg
  have hg0e : (0 : ℝ) ∈ {θ : ℝ | g θ ∈ e} := by
    change g 0 ∈ e
    rwa [hg0]
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hge 0 hg0e
  have hpi := Real.pi_pos
  let ε : ℝ := min (δ₀ / 2) (Real.pi / 2)
  have hε : 0 < ε := lt_min (half_pos hδ₀) (half_pos hpi)
  have hεpi : ε ≤ Real.pi / 2 := min_le_right _ _
  let J : Set ℝ := Icc (-ε) ε
  have hJe : ∀ x ∈ J, g x ∈ e := by
    intro x hx
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_lt]
    have hlt : ε < δ₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₀)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hginj : InjOn g J := by
    intro x hx y hy hxy
    have h₁ : z₀ * Circle.exp x = z₀ * Circle.exp y := φ.injective (Subtype.ext hxy)
    have h₂ : Circle.exp x = Circle.exp y := mul_left_cancel h₁
    have hb : ε - (-ε) < 2 * Real.pi := by linarith
    exact Circle.exp_injOn_Icc hb hx hy h₂
  exact ⟨g, ε, hg, hg0, hε, hJe, hginj, by rintro _ ⟨t, rfl⟩; exact (φ _).2⟩

omit [T1Space S] in
/-- For an `O`-arc `F ⊆ U(H)` and an edge `e ∈ E(H)`, either `e ⊆ F` or `e` is disjoint from `F`.
Every point of `e ∩ F` has a small arc of `F` around it inside `e`, whose preimage in the open
unit interval is open by the intermediate value theorem; since `e` is connected and `F` is closed,
`e ∩ F` is clopen in `e`. -/
theorem edge_subset_or_disjoint_of_isOArc [T2Space S] {H : Drawing S} {F e : Set S}
    (hF : IsOArc F) (hFU : F ⊆ H.U) (he : e ∈ H.E) : e ⊆ F ∨ Disjoint e F := by
  by_cases hdis : Disjoint e F
  · exact Or.inr hdis
  refine Or.inl ?_
  by_contra hnot
  obtain ⟨p, hpe, hpF⟩ := not_disjoint_iff.mp hdis
  obtain ⟨q, hqe, hqF⟩ := not_subset.mp hnot
  obtain ⟨γ, hγ, hγ0, hγ1, hinj, hγe⟩ := exists_edge_param H he
  have hFcl : IsClosed F := IsOArc.isClosed hF
  obtain ⟨φ⟩ := hF
  -- `γ ⁻¹' F` is closed in `unitInterval`, and we show `Ioo 0 1 ∩ γ ⁻¹' F` is open in `Ioo 0 1`.
  let T : Set unitInterval := {t ∈ Ioo (0 : unitInterval) 1 | γ t ∈ F}
  have hTopen : ∃ U : Set unitInterval, IsOpen U ∧ T = Ioo (0 : unitInterval) 1 ∩ U := by
    have hstep : ∀ t₀ ∈ T, ∃ U : Set unitInterval, IsOpen U ∧ t₀ ∈ U ∧
        Ioo (0 : unitInterval) 1 ∩ U ⊆ T := by
      rintro t₀ ⟨ht₀, ht₀F⟩
      have ht₀e : γ t₀ ∈ e := by rw [← hγe]; exact mem_image_of_mem γ ht₀
      obtain ⟨g, ε, hg, hg0, hε, hJe, hginj, hgF⟩ := exists_circle_arc_in_edge φ hFU he ht₀F ht₀e
      let J : Set ℝ := Icc (-ε) ε
      -- Pull `g '' J` back along `γ` to `Ioo 0 1`.
      let Y : Set S := g '' J
      have hYcpt : IsCompact Y := isCompact_Icc.image hg
      let K : Set unitInterval := γ ⁻¹' Y
      have hKcpt : IsCompact K := (hYcpt.isClosed.preimage hγ).isCompact
      have : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
      have hKIoo : K ⊆ Ioo 0 1 := by
        intro t ⟨x, hxJ, hxt⟩
        have hte : γ t ∈ e := hxt ▸ hJe x hxJ
        refine ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩
        · rintro rfl; exact (he.2.1 hte).2 hγ0
        · rintro rfl; exact (he.2.1 hte).2 hγ1
      let γK : K → S := fun t => γ t.1
      have hγK : Continuous γK := hγ.comp continuous_subtype_val
      have hγKinj : Function.Injective γK := fun s t h =>
        Subtype.ext (hinj (hKIoo s.2) (hKIoo t.2) h)
      have hγKemb : IsClosedEmbedding γK := hγK.isClosedEmbedding hγKinj
      have hch : ∀ x : J, ∃ t : K, γK t = g x.1 := by
        intro x
        have hmem : g x.1 ∈ e := hJe x.1 x.2
        rw [← hγe] at hmem
        obtain ⟨t, ht, htx⟩ := hmem
        exact ⟨⟨t, ⟨x.1, x.2, htx.symm⟩⟩, htx⟩
      choose τ hτ using hch
      have hτc : Continuous τ := by
        refine hγKemb.isInducing.continuous_iff.mpr ?_
        have : γK ∘ τ = fun x : J => g x.1 := funext hτ
        rw [this]
        exact hg.comp continuous_subtype_val
      let τR : J → ℝ := fun x => (τ x).1.1
      have hτRc : Continuous τR :=
        continuous_subtype_val.comp (continuous_subtype_val.comp hτc)
      have hτRinj : Function.Injective τR := by
        intro x y hxy
        have h₁ : τ x = τ y := Subtype.ext (Subtype.ext hxy)
        have h₂ : g x.1 = g y.1 := by rw [← hτ, ← hτ, h₁]
        exact Subtype.ext (hginj x.2 y.2 h₂)
      let xL : J := ⟨-ε, by simp [J, hε.le]⟩
      let xM : J := ⟨0, by simp [J, hε.le]⟩
      let xR : J := ⟨ε, by simp [J, hε.le]⟩
      have hτM : (τ xM).1 = t₀ := by
        apply hinj (hKIoo (τ xM).2) ht₀
        change γK (τ xM) = γ t₀
        rw [hτ xM]
        exact hg0
      have hτMR : τR xM = (t₀ : ℝ) := congrArg Subtype.val hτM
      -- By IVT on `[-ε, 0]` and `[0, ε]`, `τR xM` lies strictly between `τR xL` and `τR xR`.
      let JL : Set J := {x : J | x.1 ≤ 0}
      let JR : Set J := {x : J | 0 ≤ x.1}
      have hJL : IsPreconnected JL := by
        have hEq : JL = Subtype.val ⁻¹' Icc (-ε) 0 := by
          ext x; simp [JL, x.2.1]
        rw [hEq]
        refine (IsInducing.subtypeVal : IsInducing (Subtype.val : J → ℝ)).isPreconnected_image.mp ?_
        rw [Subtype.image_preimage_coe, inter_eq_right.mpr (Icc_subset_Icc_right hε.le)]
        exact isPreconnected_Icc
      have hJR : IsPreconnected JR := by
        have hEq : JR = Subtype.val ⁻¹' Icc 0 ε := by
          ext x; simp [JR, x.2.2]
        rw [hEq]
        refine (IsInducing.subtypeVal : IsInducing (Subtype.val : J → ℝ)).isPreconnected_image.mp ?_
        rw [Subtype.image_preimage_coe, inter_eq_right.mpr (Icc_subset_Icc_left (by linarith))]
        exact isPreconnected_Icc
      have hivL : Icc (min (τR xL) (τR xM)) (max (τR xL) (τR xM)) ⊆ τR '' JL := by
        rcases le_total (τR xL) (τR xM) with h | h
        · rw [min_eq_left h, max_eq_right h]
          exact hJL.intermediate_value (by simp [JL, xL, hε.le]) (by simp [JL,
            xM]) hτRc.continuousOn
        · rw [min_eq_right h, max_eq_left h]
          exact hJL.intermediate_value (by simp [JL, xM]) (by simp [JL, xL,
            hε.le]) hτRc.continuousOn
      have hivR : Icc (min (τR xM) (τR xR)) (max (τR xM) (τR xR)) ⊆ τR '' JR := by
        rcases le_total (τR xM) (τR xR) with h | h
        · rw [min_eq_left h, max_eq_right h]
          exact hJR.intermediate_value (by simp [JR, xM]) (by simp [JR, xR,
            hε.le]) hτRc.continuousOn
        · rw [min_eq_right h, max_eq_left h]
          exact hJR.intermediate_value (by simp [JR, xR, hε.le]) (by simp [JR,
            xM]) hτRc.continuousOn
      have hbetween : (τR xL < τR xM ∧ τR xM < τR xR) ∨ (τR xR < τR xM ∧ τR xM < τR xL) := by
        let f := τR ∘ Set.projIcc (-ε) ε (by linarith : -ε ≤ ε)
        have hfc : Continuous f := hτRc.comp continuous_projIcc
        have hfi : InjOn f J := by
          intro x hx y hy hxy
          change τR (Set.projIcc _ _ _ x) = τR (Set.projIcc _ _ _ y) at hxy
          have h := congrArg Subtype.val (hτRinj hxy)
          simpa only [Set.projIcc_of_mem _ hx, Set.projIcc_of_mem _ hy] using h
        have hval (x : J) : f x = τR x := by
          change τR (Set.projIcc _ _ _ (x : ℝ)) = τR x
          rw [Set.projIcc_val]
        have hLM : (xL : ℝ) < xM := by change -ε < 0; linarith
        have hMR : (xM : ℝ) < xR := hε
        rcases hfc.continuousOn.strictMonoOn_of_injOn_Icc' (by linarith : -ε ≤ ε) hfi with h | h
        · left
          simpa only [hval] using And.intro
            (h xL.2 xM.2 hLM) (h xM.2 xR.2 hMR)
        · right
          simpa only [hval] using And.intro
            (h xM.2 xR.2 hMR) (h xL.2 xM.2 hLM)
      let aR : ℝ := min (τR xL) (τR xR)
      let bR : ℝ := max (τR xL) (τR xR)
      refine ⟨Subtype.val ⁻¹' Ioo aR bR, isOpen_Ioo.preimage continuous_subtype_val, ?_, ?_⟩
      · change aR < (t₀ : ℝ) ∧ (t₀ : ℝ) < bR
        rw [← hτMR]
        rcases hbetween with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact ⟨lt_of_le_of_lt (min_le_left _ _) h₁, lt_of_lt_of_le h₂ (le_max_right _ _)⟩
        · exact ⟨lt_of_le_of_lt (min_le_right _ _) h₁, lt_of_lt_of_le h₂ (le_max_left _ _)⟩
      · rintro t ⟨htI, hta, htb⟩
        have hta' : min (τR xL) (τR xR) < (t : ℝ) := hta
        have htb' : (t : ℝ) < max (τR xL) (τR xR) := htb
        refine ⟨htI, ?_⟩
        have hcov : (t : ℝ) ∈ τR '' JL ∪ τR '' JR := by
          rcases le_total (t : ℝ) (τR xM) with hle | hle
          · rcases hbetween with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · refine Or.inl (hivL ⟨?_, ?_⟩)
              · rw [min_eq_left h₁.le]
                rw [min_eq_left (h₁.trans h₂).le] at hta'
                exact hta'.le
              · rw [max_eq_right h₁.le]
                exact hle
            · refine Or.inr (hivR ⟨?_, ?_⟩)
              · rw [min_eq_right h₁.le]
                rw [min_eq_right (h₁.trans h₂).le] at hta'
                exact hta'.le
              · rw [max_eq_left h₁.le]
                exact hle
          · rcases hbetween with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · refine Or.inr (hivR ⟨?_, ?_⟩)
              · rw [min_eq_left h₂.le]
                exact hle
              · rw [max_eq_right h₂.le]
                rw [max_eq_right (h₁.trans h₂).le] at htb'
                exact htb'.le
            · refine Or.inl (hivL ⟨?_, ?_⟩)
              · rw [min_eq_right h₂.le]
                exact hle
              · rw [max_eq_left h₂.le]
                rw [max_eq_left (h₁.trans h₂).le] at htb'
                exact htb'.le
        have hmem : ∃ x : J, τR x = (t : ℝ) := by
          rcases hcov with ⟨x, -, hx⟩ | ⟨x, -, hx⟩ <;> exact ⟨x, hx⟩
        obtain ⟨x, hx⟩ := hmem
        have htx : t = (τ x).1 := Subtype.ext hx.symm
        rw [htx]
        change γK (τ x) ∈ F
        rw [hτ x]
        exact hgF (mem_range_self _)
    choose! U hUo htU hUs using hstep
    refine ⟨⋃ t ∈ T, U t, isOpen_biUnion fun t ht => hUo t ht, ?_⟩
    ext t
    constructor
    · intro ht
      exact ⟨ht.1, mem_iUnion₂.mpr ⟨t, ht, htU t ht⟩⟩
    · rintro ⟨htI, htU'⟩
      obtain ⟨s, hs, hts⟩ := mem_iUnion₂.mp htU'
      exact hUs s hs ⟨htI, hts⟩
  obtain ⟨U, hUo, hTU⟩ := hTopen
  have hcov : Ioo (0 : unitInterval) 1 ⊆ U ∪ (γ ⁻¹' F)ᶜ := by
    intro t ht
    by_cases htF : γ t ∈ F
    · have htT : t ∈ T := ⟨ht, htF⟩
      rw [hTU] at htT
      exact Or.inl htT.2
    · exact Or.inr htF
  obtain ⟨t₁, ht₁, rfl⟩ : p ∈ γ '' Ioo 0 1 := by rwa [hγe]
  obtain ⟨t₂, ht₂, rfl⟩ : q ∈ γ '' Ioo 0 1 := by rwa [hγe]
  have ht₁U : t₁ ∈ U := by
    have : t₁ ∈ T := ⟨ht₁, hpF⟩
    rw [hTU] at this
    exact this.2
  obtain ⟨t, htI, htU, htF⟩ := isPreconnected_Ioo U (γ ⁻¹' F)ᶜ hUo
    (hFcl.preimage hγ).isOpen_compl hcov ⟨t₁, ht₁, ht₁U⟩ ⟨t₂, ht₂, hqF⟩
  have htT : t ∈ T := by rw [hTU]; exact ⟨htI, htU⟩
  exact htF htT.2

omit [T1Space S] in
/-- For an open set `Λ ⊆ Σ`, `Λ` is disjoint from `subBd Λ`, and `closure Λ = Λ ∪ subBd Λ`. -/
theorem isOpen_disjoint_subBd_and_closure_eq {Λ : Set S} (hΛ : IsOpen Λ) :
    Disjoint Λ (subBd Λ) ∧ closure Λ = Λ ∪ subBd Λ := by
  have hdis : Disjoint Λ (subBd Λ) := by
    refine disjoint_left.mpr fun x hx ⟨_, hxout⟩ => ?_
    obtain ⟨y, hyΛ, hyn⟩ := mem_closure_iff.mp hxout Λ hΛ hx
    exact hyn.2 hyΛ
  refine ⟨hdis, subset_antisymm ?_ (union_subset subset_closure fun _ h => h.1)⟩
  intro x hx
  by_cases hxΛ : x ∈ Λ
  · exact Or.inl hxΛ
  · exact Or.inr ⟨hx, subset_closure ⟨mem_univ _, hxΛ⟩⟩

omit [T1Space S] in
/-- Every edge of `H` either lies in `Λ` or lies in `Σ - Λ`, when `Λ` is a `λ`-zone around `z`. -/
theorem edge_subset_or_subset_compl_of_zone [T2Space S] {H : Drawing S}
    {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ e : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ) (he : e ∈ H.E) :
    e ⊆ Λ ∨ e ⊆ univ \ Λ := by
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
  rcases edge_subset_or_disjoint_of_isOArc hZone.isOArc_bd hZone.bd_subset_U he with hsub | hdis
  · exact Or.inr fun x hx => ⟨mem_univ _, fun hxΛ => disjoint_left.mp hdisL hxΛ (hsub hx)⟩
  · have hcov : e ⊆ Λ ∪ (closure Λ)ᶜ := by
      intro x hx
      by_cases hxcl : x ∈ closure Λ
      · rw [hclL] at hxcl
        exact Or.inl (hxcl.resolve_right (disjoint_left.mp hdis hx))
      · exact Or.inr hxcl
    have hdisO : Disjoint Λ (closure Λ)ᶜ :=
      disjoint_left.mpr fun x hx hxc => hxc (subset_closure hx)
    by_cases hmeet : (e ∩ Λ).Nonempty
    · obtain ⟨x, hxe, hxΛ⟩ := hmeet
      exact Or.inl ((he.2.2.1.isConnected.isPreconnected).subset_left_of_subset_union
        hZone.isOpenDisc.1 isClosed_closure.isOpen_compl hdisO hcov ⟨x, hxe, hxΛ⟩)
    · refine Or.inr fun x hxe => ⟨mem_univ _, fun hxΛ => hmeet ⟨x, hxe, hxΛ⟩⟩

/-- `clearedSubdrawing H Λ` is a subdrawing of `H`. -/
theorem clearedSubdrawing_isSubdrawing (H : Drawing S) (Λ : Set S) :
    (clearedSubdrawing H Λ).IsSubdrawing H :=
  Drawing.span_isSubdrawing H _ _

/-- For a `λ`-zone `Λ` around `z`, the point set of `H' = H ∩ (Σ - Λ)` is `U(H) \ Λ`. -/
theorem clearedSubdrawing_U [T2Space S] {H : Drawing S}
    {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ) :
    (clearedSubdrawing H Λ).U = H.U \ Λ := by
  have hcl_compl : IsClosed (univ \ Λ) := by
    rw [← compl_eq_univ_sdiff]
    exact hZone.isOpenDisc.1.isClosed_compl
  have hE : (clearedSubdrawing H Λ).E = {e | e ∈ H.E ∧ e ⊆ univ \ Λ} := by
    change (H.span _ _).E = _
    rw [H.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  apply subset_antisymm
  · rw [(clearedSubdrawing H Λ).U_eq]
    refine union_subset ?_ (iUnion₂_subset fun e he => ?_)
    · rintro x (⟨hx, hxV⟩ | hx)
      · exact ⟨H.V_subset_U hxV, hx.2.2⟩
      · obtain ⟨e, he', hxe, hxV⟩ := mem_iUnion₂.mp hx
        exact ⟨H.V_subset_U hxV, (hcl_compl.closure_subset_iff.mpr he'.1.2 hxe).2⟩
    · rw [hE] at he
      exact fun x hx => ⟨H.closure_subset_U he.1 hx,
        (hcl_compl.closure_subset_iff.mpr he.2 hx).2⟩
  · rintro x ⟨hxU, hxΛ⟩
    by_cases hxV : x ∈ H.V
    · refine (clearedSubdrawing H Λ).V_subset_U ?_
      exact Or.inl ⟨⟨hxV, mem_univ _, hxΛ⟩, hxV⟩
    · obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxU hxV
      rcases edge_subset_or_subset_compl_of_zone hZone he with heΛ | hec
      · exact absurd (heΛ hxe) hxΛ
      · have he' : e ∈ (clearedSubdrawing H Λ).E := by
          rw [hE]
          exact ⟨he, hec⟩
        exact (clearedSubdrawing H Λ).closure_subset_U he' (subset_closure hxe)

/-- Graph Minors XIV, Section 3 (page 28):
"Let $\Lambda$ be a $\lambda$-zone around $z$ and let $H' = H \cap (\Sigma - \Lambda)$. Since
$H \cap bd(\Lambda)$ is a circuit it follows that $\Lambda$ is a region of $H'$, and every
other region of $H'$ is a region of $H$. Consequently $H'$ is a 2-cell drawing in $\Sigma$." -/
theorem clearedSubdrawing_region_eq_or_mem_R [T2Space S] {H : Drawing S}
    {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ) {r' : Set S}
    (hr' : r' ∈ (clearedSubdrawing H Λ).R) :
    r' = Λ ∨ r' ∈ H.R := by
  have hU := clearedSubdrawing_U hZone
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
  have hbdU' : subBd Λ ⊆ (clearedSubdrawing H Λ).U := by
    rw [hU]
    exact fun x hx => ⟨hZone.bd_subset_U hx, disjoint_right.mp hdisL hx⟩
  let O₂ : Set S := univ \ (H.U ∪ closure Λ)
  have hO₂ : IsOpen O₂ := isOpen_univ.sdiff (H.isClosed_U.union isClosed_closure)
  have hdisO : Disjoint Λ O₂ :=
    disjoint_left.mpr fun x hx hxO => hxO.2 (Or.inr (subset_closure hx))
  have hcompl : univ \ (clearedSubdrawing H Λ).U = Λ ∪ O₂ := by
    rw [hU]
    ext x
    constructor
    · rintro ⟨_, hx⟩
      by_cases hxΛ : x ∈ Λ
      · exact Or.inl hxΛ
      · refine Or.inr ⟨mem_univ _, ?_⟩
        rintro (hxU | hxcl)
        · exact hx ⟨hxU, hxΛ⟩
        · rw [hclL] at hxcl
          exact hx ⟨hZone.bd_subset_U (hxcl.resolve_left hxΛ), hxΛ⟩
    · rintro (hxΛ | ⟨_, hx⟩)
      · exact ⟨mem_univ _, fun h => h.2 hxΛ⟩
      · exact ⟨mem_univ _, fun h => hx (Or.inl h.1)⟩
  obtain ⟨x, hxU', rfl⟩ := (mem_R_iff (clearedSubdrawing H Λ)).mp hr'
  have hx_mem : x ∈ univ \ (clearedSubdrawing H Λ).U := ⟨mem_univ _, hxU'⟩
  have hcov' : connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) x ⊆ Λ ∪ O₂ := by
    rw [← hcompl]
    exact connectedComponentIn_subset _ _
  rcases hcompl ▸ hx_mem with hxΛ | hxO₂
  · refine Or.inl (subset_antisymm ?_ ?_)
    · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
        hZone.isOpenDisc.1 hO₂ hdisO hcov' ⟨x, mem_connectedComponentIn hx_mem, hxΛ⟩
    · refine hZone.isOpenDisc.isPathConnected.isConnected.isPreconnected.subset_connectedComponentIn
        hxΛ ?_
      rw [hcompl]
      exact subset_union_left
  · refine Or.inr ?_
    have hxHU : x ∉ H.U := fun h => hxO₂.2 (Or.inl h)
    refine (mem_R_iff H).mpr ⟨x, hxHU, subset_antisymm ?_ ?_⟩
    · have hsubO₂ : connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) x ⊆ O₂ :=
        isPreconnected_connectedComponentIn.subset_right_of_subset_union
          hZone.isOpenDisc.1 hO₂ hdisO hcov' ⟨x, mem_connectedComponentIn hx_mem, hxO₂⟩
      refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hx_mem) ?_
      exact hsubO₂.trans fun y hy => ⟨mem_univ _, fun h => hy.2 (Or.inl h)⟩
    · have hrH : connectedComponentIn (univ \ H.U) x ∈ H.R :=
        (mem_R_iff H).mpr ⟨x, hxHU, rfl⟩
      have hcovH : connectedComponentIn (univ \ H.U) x ⊆ Λ ∪ O₂ := by
        intro y hy
        have hyU : y ∉ H.U := (connectedComponentIn_subset _ _ hy).2
        by_cases hycl : y ∈ closure Λ
        · rw [hclL] at hycl
          exact Or.inl (hycl.resolve_right fun hbd => hyU (hZone.bd_subset_U hbd))
        · exact Or.inr ⟨mem_univ _, fun h => h.elim hyU hycl⟩
      have hsubO₂ : connectedComponentIn (univ \ H.U) x ⊆ O₂ :=
        isPreconnected_connectedComponentIn.subset_right_of_subset_union
          hZone.isOpenDisc.1 hO₂ hdisO hcovH
          ⟨x, mem_connectedComponentIn ⟨mem_univ _, hxHU⟩, hxO₂⟩
      refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn ⟨mem_univ _, hxHU⟩) ?_
      rw [hcompl]
      exact hsubO₂.trans subset_union_right

/-- If `H` is a 2-cell drawing and `Λ` is a `λ`-zone around `z`, then `H ∩ (Σ - Λ)` is a 2-cell
drawing in `Σ` (Graph Minors XIV, Section 3, page 28). -/
theorem clearedSubdrawing_isTwoCell [T2Space S] {H : Drawing S}
    {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ : Set S}
    (h2cell : (PaintingOrDrawing.drawing H).IsTwoCell)
    (hZone : IsLambdaZoneAround H d lam z Λ) :
    (PaintingOrDrawing.drawing (clearedSubdrawing H Λ)).IsTwoCell := by
  refine ⟨h2cell.1, fun r' hr' => ?_⟩
  rcases clearedSubdrawing_region_eq_or_mem_R hZone hr' with rfl | hr'H
  · exact hZone.isOpenDisc
  · exact h2cell.2 r' hr'H

/-- Graph Minors XIV, Section 3 (page 28):
"It is easy to see and was shown in [4, theorem (12.2)] that any subset of a free set is free." -/
theorem freeSet_subset {α β : Type*} {G : Hypergraph α β}
    {T : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ} {X X' : Set α}
    (hT : IsTangle G θ T) (hX : IsFreeSet G T θ X) (hsub : X' ⊆ X) : IsFreeSet G T θ X' :=
  hX.subset hT hsub

end GraphMinor.GM14

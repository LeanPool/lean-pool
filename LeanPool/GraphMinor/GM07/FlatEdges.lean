/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section35
public import LeanPool.GraphMinor.GM07.Section41
public import LeanPool.GraphMinor.GM07.CutBounds
public import LeanPool.GraphMinor.GM11.FlatCover
public import LeanPool.GraphMinor.GM14.Section6c

/-!
# Adding lines to a flat set

This file is the first half of the proof of (4.3) of Graph Minors VII (pages 222 and 223). The paper
picks a set `Y` maximal among the unions of
regions, edges and vertices all of whose `O`-arcs are null-homotopic, and says that it is "easy to
see" that `Y` contains every edge at a vertex of `Y`.
Here is the reason (`IsFlat.union_line`, `IsFlat.union_edge`). A line `L` with an end in `Y` has a
thin closed disc around it, the disc of
`exists_edge_lens`. Its boundary lies in `Y`, except possibly for the other end of `L`, so by (11.3)
adding the inside of the disc keeps `Y` flat.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

theorem IsFlat.mono {Y Y' : Set S} (h : IsFlat Y) (hs : Y' ⊆ Y) : IsFlat Y' := fun φ hφ => h φ
  (hφ.trans hs)

/-- A line without one end joins each of its points to the other end. -/
theorem joinedIn_line_sdiff {R : Set S} {u x a : S} (hR : IsLineWithEnds R u x) (ha : a ∈ R)
  (hne : a ≠ u) : JoinedIn (R \ {u}) a x := by
  obtain ⟨f, h0, h1⟩ := hR
  let g : unitInterval → S := fun t => (f t).1
  have hg : Continuous g := continuous_subtype_val.comp f.continuous
  have hconv : IsPathConnected (Ioc (0 : ℝ) 1) :=
    (convex_Ioc 0 1).isPathConnected ⟨1, by norm_num, le_rfl⟩
  have hu : ∀ t : unitInterval, 0 < (t : ℝ) → g t ≠ u := fun t ht e => by
    have : f t = f 0 := Subtype.ext (e.trans h0.symm)
    have h2 := f.injective this
    rw [h2] at ht
    simp at ht
  let s := f.symm ⟨a, ha⟩
  have hs : g s = a := by simp [g, s]
  have hs0 : 0 < (s : ℝ) := by
    rcases eq_or_lt_of_le (s.2.1 : (0 : ℝ) ≤ s) with h | h
    · have : s = 0 := Subtype.ext h.symm
      rw [this] at hs
      exact (hne (hs.symm.trans h0)).elim
    · exact h
  have hmem : ∀ t ∈ Ioc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨ht.1.le, ht.2⟩
  obtain ⟨γ, hγ⟩ := hconv.joinedIn _ ⟨hs0, s.2.2⟩ 1 ⟨by norm_num, le_rfl⟩
  let c : C(unitInterval, unitInterval) := ⟨fun t => ⟨γ t, hmem _ (hγ t)⟩, Continuous.subtype_mk
    γ.continuous _⟩
  refine ⟨⟨⟨fun t => g (c t), hg.comp c.continuous⟩, ?_, ?_⟩, fun t => ?_⟩
  · have : c 0 = s := Subtype.ext (by simp [c])
    change g (c 0) = a
    rw [this, hs]
  · have : c 1 = 1 := Subtype.ext (by simp [c])
    change g (c 1) = x
    rw [this]
    exact h1
  · exact ⟨(f (c t)).2, hu _ (hγ t).1⟩

/-- A set that holds an `O`-arc except for at most one point, and a point `x` of the `O`-arc, is
arc-connected. -/
theorem isArcConnected_oArc_part [T2Space S] {C W : Set S} (hC : IsOArc C) {x u : S} (hx : x ∈ C)
  (hu : u ∈ C) (hne : x ≠ u) (hW : W ⊆ C) (hrest : C \ {u} ⊆ W) :
    IsArcConnected W := by
  obtain ⟨P, Q, hP, hQ, hPQ, -⟩ := hC.lines hu hx hne.symm
  have hJ : ∀ a ∈ W, JoinedIn W a x := fun a ha => by
    have hline : ∀ {R : Set S}, IsLineWithEnds R u x → R ⊆ C → a ∈ R → JoinedIn W a x
      := fun {R} hR hRC haR => by
      by_cases h : a = u
      · have hRW : R ⊆ W := fun z hz => by
          by_cases hzu : z = u
          · rw [hzu, ← h]
            exact ha
          · exact hrest ⟨hRC hz, hzu⟩
        rw [h]
        exact ((joinedIn_iff_eq_or_exists_isLineWithEnds hR.left_mem hR.right_mem).mpr (.inr ⟨R,
          subset_rfl, hR⟩)).mono hRW
      · exact (joinedIn_line_sdiff hR haR h).mono fun z hz => hrest ⟨hRC hz.1, hz.2⟩
    have : a ∈ P ∪ Q := hPQ ▸ hW ha
    rcases this with h | h
    · exact hline hP (hPQ ▸ subset_union_left) h
    · exact hline hQ (hPQ ▸ subset_union_right) h
  intro a ha b hb hab
  have h := (hJ a ha).trans (hJ b hb).symm
  exact ((joinedIn_iff_eq_or_exists_isLineWithEnds ha hb).mp h).resolve_left hab

/-- A connected set of a capped surface that misses the cuffs, with a point of the inside of the
surface in its closure, lies in the surface. -/
theorem subset_range_of_side {T : Type} [TopologicalSpace T] {j : S → T} {K : Set T}
  (hT : IsClosedSurface T) (hj : IsClosedEmbedding j) (hK : IsClosed K) (hu : range j ∪ K = univ)
    (hi : range j ∩ K = j '' bd S) {A : Set T} (hA : IsPreconnected A) (hbd : Disjoint A
      (j '' bd S)) {x₀ : S} (hx₀ : x₀ ∉ bd S) (hcl : j x₀ ∈ closure A) : A ⊆ range j := by
  have hfr : frontier (range j) = j '' bd S := cap_frontier hT hj hK hu hi
  refine subset_of_preconnected_frontier hA hj.isClosed_range (hfr ▸ hbd) ?_
  have h1 : j x₀ ∈ interior (range j) := by
    have h2 : j x₀ ∉ frontier (range j) := by
      rw [hfr]
      rintro ⟨x, hx, e⟩
      rw [hj.injective e] at hx
      exact hx₀ hx
    by_contra h3
    exact h2 ⟨subset_closure ⟨x₀, rfl⟩, h3⟩
  obtain ⟨z, hz, hzA⟩ := mem_closure_iff.mp hcl _ isOpen_interior h1
  exact ⟨z, hzA, interior_subset hz⟩

/-- A thin closed disc `Δ` around a line `L` that meets a closed set `W` and the boundary of the
surface only at its ends. The inside of `Δ` is `L` without its ends together with two
path-connected open-side sets `A` and `B`, and each point of `L` other than its ends lies in the
closure of both sides. We get `Δ` from `exists_edge_lens_sides` in the capped surface. Both
sides lie in the surface, because they are connected, they miss the cuffs and they touch the inside
of the surface along `L`. -/
theorem exists_line_lens (hS : IsSurface S) {L W : Set S} {x u : S} (hL : IsLineWithEnds L x u)
  (hW : IsClosed W) (hLW : L ∩ W ⊆ {x, u}) (hLb : L ∩ bd S ⊆ {x, u}) :
    ∃ Δ A B : Set S, IsClosedDisc Δ ∧ L ⊆ Δ ∧ Δ ∩ (W ∪ bd S) ⊆ {x, u} ∧ x ∈ discBd Δ ∧ u ∈ discBd Δ
      ∧ discBd Δ ∩ L ⊆ {x, u} ∧ IsOpen (Δ \ discBd Δ) ∧ Δ \ discBd Δ ⊆ A ∪ B ∪ L ∧
      A ⊆ Δ \ discBd Δ ∧ B ⊆ Δ \ discBd Δ ∧ Disjoint A B ∧ Disjoint A L ∧ Disjoint B L
        ∧ IsPathConnected A ∧ IsPathConnected B ∧ L \ {x, u} ⊆ closure A ∧ L \ {x, u} ⊆ closure B
          := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hS2 : CompactSpace S := hS.1
  have hbc : IsClosed (bd S) := (cuff_statement.{0} S hS).1
  obtain ⟨T, tT, j, K, hT, hj, hK, hu, hi, -⟩ := exists_capAll S hS
  have ht2T : T2Space T := hT.2.1
  have hman : ∀ z : T, IsManifoldPoint z := fun z => (hT.2.2 z).isManifoldPoint
  have hne : x ≠ u := fun e => by
    obtain ⟨f, h0, h1⟩ := hL
    have : f 0 = f 1 := Subtype.ext (h0.trans (e.trans h1.symm))
    exact zero_ne_one (f.injective this)
  have hl' := hL.map_of_embedding hj.isEmbedding
  have hne' : j x ≠ j u := fun e => hne (hj.injective e)
  let Zl : Set T := j '' (W ∪ bd S)
  have hZl : IsClosed Zl := hj.isClosedMap _ (hW.union hbc)
  have hLZ : (j '' L) ∩ Zl ⊆ {j x, j u} := by
    rintro _ ⟨⟨z, hz, rfl⟩, z', hz', e⟩
    obtain rfl := hj.injective e
    have : z' ∈ ({x, u} : Set S) := by
      rcases hz' with h | h
      · exact hLW ⟨hz, h⟩
      · exact hLb ⟨hz, h⟩
    rcases this with rfl | h
    · exact .inl rfl
    · exact .inr (congrArg j h)
  obtain ⟨D, A, B, hD, hLD, hDZ, hxD, huD, hDL, hDeq, hAc, hBc, -, -, hAL, hBL, hLA, hLB, -, -,
    hAB, hA', hB'⟩ := exists_edge_lens_sides hT hl' hne' hZl hLZ
  obtain ⟨x₀, hx₀, hx₀e⟩ : ∃ x₀ ∈ L, x₀ ∉ ({x, u} : Set S) := by
    obtain ⟨z, hz⟩ := GM14.IsLineWithEnds.nonempty_sdiff_pair hL
    exact ⟨z, hz.1, hz.2⟩
  have hx₀b : x₀ ∉ bd S := fun h => hx₀e (hLb ⟨hx₀, h⟩)
  have hside : ∀ {A' : Set T}, A' ⊆ D → IsPreconnected A' → Disjoint A' (j '' L)
    → j '' L ⊆ closure A' → A' ⊆ range j := fun {A'} hs hc hd hcl => by
    refine subset_range_of_side hT hj hK hu hi hc (disjoint_left.mpr ?_) hx₀b (hcl ⟨x₀, hx₀, rfl⟩)
    rintro z hz ⟨y, hy, rfl⟩
    have h1 : j y ∈ Zl := ⟨y, .inr hy, rfl⟩
    have h2 := hDZ ⟨hs hz, h1⟩
    refine disjoint_left.mp hd hz ?_
    rcases h2 with h3 | h3
    · exact h3 ▸ hl'.left_mem
    · exact (mem_singleton_iff.mp h3) ▸ hl'.right_mem
  have hAD : A ⊆ D := fun z hz => hDeq ▸ .inl (.inl hz)
  have hBD : B ⊆ D := fun z hz => hDeq ▸ .inl (.inr hz)
  have hDr : D ⊆ range j := by
    rw [hDeq]
    refine union_subset (union_subset (hside hAD hAc hAL hLA) (hside hBD hBc hBL hLB)) ?_
    exact image_subset_range _ _
  have hΔ : IsClosedDisc (j ⁻¹' D) := isClosedDisc_preimage_of_subset_range hj.continuous
    hj.injective hD hDr
  have him := hΔ.image_injOn hj.continuous.continuousOn hj.injective.injOn
  have hDim : j '' (j ⁻¹' D) = D := image_preimage_eq_of_subset hDr
  have hbdeq : j ⁻¹' discBd D = discBd (j ⁻¹' D) := by
    rw [hDim] at him
    rw [him.2, preimage_image_eq _ hj.injective]
  have hin : j ⁻¹' D \ discBd (j ⁻¹' D) = j ⁻¹' (D \ discBd D) := by
    rw [← hbdeq]
    rfl
  have hopen : IsOpen (j ⁻¹' D \ discBd (j ⁻¹' D)) := by
    rw [hin]
    exact (hD.isOpen_discInt hman).preimage hj.continuous
  have hpc : ∀ {A₀ : Set T}, A₀ ⊆ D → IsPathConnected (A₀ \ discBd D) → IsPathConnected (j ⁻¹'
    (A₀ \ discBd D)) := fun {A₀} hs hc => by
    rw [hj.isInducing.isPathConnected_iff, image_preimage_eq_of_subset (sdiff_subset.trans
      (hs.trans hDr))]
    exact hc
  have hend : ∀ z ∈ L \ {x, u}, j z ∉ discBd D := fun z hz h => by
    rcases hDL ⟨h, z, hz.1, rfl⟩ with h2 | h2
    · exact hz.2 (.inl (hj.injective h2))
    · exact hz.2 (.inr (hj.injective h2))
  have hcl : ∀ {A₀ : Set T}, A₀ ⊆ D → j '' L ⊆ closure A₀ → L \ {x, u} ⊆ closure (j ⁻¹'
    (A₀ \ discBd D)) := fun {A₀} hs hc z hz => by
    rw [mem_closure_iff]
    intro O hO hzO
    obtain ⟨O', hO', rfl⟩ := hj.isInducing.isOpen_iff.mp hO
    have h1 : j z ∈ O' ∩ (D \ discBd D) := ⟨hzO, hLD ⟨z, hz.1, rfl⟩, hend z hz⟩
    obtain ⟨y, hy, hyA⟩ := mem_closure_iff.mp (hc ⟨z, hz.1, rfl⟩) _ (hO'.inter
      (hD.isOpen_discInt hman)) h1
    obtain ⟨y', rfl⟩ := hDr hy.2.1
    exact ⟨y', hy.1, hyA, hy.2.2⟩
  refine ⟨j ⁻¹' D, j ⁻¹' (A \ discBd D), j ⁻¹' (B \ discBd D), hΔ, fun z hz
    => hLD ⟨z, hz, rfl⟩, ?_, ?_, ?_, ?_, hopen, ?_, ?_, ?_, ?_, ?_, ?_, hpc hAD hA', hpc hBD hB',
      hcl hAD hLA, hcl hBD hLB⟩
  · rintro z ⟨hz, hz'⟩
    rcases hDZ ⟨hz, z, hz', rfl⟩ with h | h
    · exact .inl (hj.injective h)
    · exact .inr (hj.injective h)
  · rw [← hbdeq]
    exact hxD
  · rw [← hbdeq]
    exact huD
  · rintro z ⟨hz, hzL⟩
    rw [← hbdeq] at hz
    rcases hDL ⟨hz, z, hzL, rfl⟩ with h | h
    · exact .inl (hj.injective h)
    · exact .inr (hj.injective h)
  · rw [hin]
    rintro z ⟨hz, hz'⟩
    have : j z ∈ A ∪ B ∪ j '' L := hDeq ▸ hz
    rcases this with (h | h) | ⟨z', hz'', e⟩
    · exact .inl (.inl ⟨h, hz'⟩)
    · exact .inl (.inr ⟨h, hz'⟩)
    · exact .inr (hj.injective e ▸ hz'')
  · rw [hin]
    exact fun z hz => ⟨hAD hz.1, hz.2⟩
  · rw [hin]
    exact fun z hz => ⟨hBD hz.1, hz.2⟩
  · exact disjoint_left.mpr fun z hz hz' => disjoint_left.mp hAB hz.1 hz'.1
  · exact disjoint_left.mpr fun z hz hz' => disjoint_left.mp hAL hz.1 ⟨z, hz', rfl⟩
  · exact disjoint_left.mpr fun z hz hz' => disjoint_left.mp hBL hz.1 ⟨z, hz', rfl⟩

/-- **Adding a line to a flat set.** Let `Y` be flat and let `L` be a line with an end `x` in `Y`,
such that everything off `L`, a closed set `W` and `bd(Σ)` lies in `Y`. Then
`Y` stays flat when we add `L` without its ends. The proof is in the module docstring. -/
theorem IsFlat.union_line (hS : IsSurface S) {Y W L : Set S} {x u : S} (hY : IsFlat Y)
  (hL : IsLineWithEnds L x u) (hW : IsClosed W) (hLW : L ∩ W ⊆ {x, u}) (hLb : L ∩ bd S ⊆ {x, u})
    (hxY : x ∈ Y) (hrest : ∀ z, z ∉ W → z ∉ bd S → z ∉ L → z ∈ Y) : IsFlat (Y ∪ (L \ {x, u})) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hne : x ≠ u := fun e => by
    obtain ⟨f, h0, h1⟩ := hL
    have : f 0 = f 1 := Subtype.ext (h0.trans (e.trans h1.symm))
    exact zero_ne_one (f.injective this)
  obtain ⟨Δ, -, -, hΔ, hLD, hDZ, hxC, huC, hDL, -⟩ := exists_line_lens hS hL hW hLW hLb
  have hnotin : ∀ z ∈ discBd Δ, z ≠ x → z ≠ u → z ∉ W ∧ z ∉ bd S ∧ z ∉ L := fun z hz h1 h2 => by
    have hzD : z ∈ Δ := GM11.discBd_subset _ hz
    have hend : z ∉ ({x, u} : Set S) := by
      rintro (h | h)
      · exact h1 h
      · exact h2 h
    exact ⟨fun h => hend (hDZ ⟨hzD, .inl h⟩), fun h => hend (hDZ ⟨hzD, .inr h⟩),
      fun h => hend (hDL ⟨hz, h⟩)⟩
  have harc : IsArcConnected (Y ∩ discBd Δ) := isArcConnected_oArc_part
    (IsClosedDisc.isOArc_discBd hΔ) hxC huC hne inter_subset_right fun z hz => by
    by_cases hzx : z = x
    · exact ⟨hzx ▸ hxY, hz.1⟩
    · obtain ⟨h1, h2, h3⟩ := hnotin z hz.1 hzx hz.2
      exact ⟨hrest z h1 h2 h3, hz.1⟩
  refine IsFlat.mono ((theorem_11_3_proof hS hΔ harc).2 hY) (union_subset_union_right _ fun z hz
    => ?_)
  refine ⟨hLD hz.1, fun hb => hz.2 ?_⟩
  exact hDL ⟨hb, hz.1⟩

/-- In a flat set, paths with the same ends are homotopic. -/
theorem IsFlat.flat {A : Set S} (hA : IsFlat A) : Flat A := fun a b p q hp hq => by
  obtain ⟨ψ, -, h0, h1, h2, -, h3, -⟩ := IsFlat.curvesHomotopic hA (φ₁ := p.toContinuousMap) (φ₂
    := q.toContinuousMap)
    (by rintro _ ⟨u, rfl⟩; exact hp u) (by rintro _ ⟨u, rfl⟩; exact hq u) (by simp) (by simp)
  refine ⟨⟨⟨⟨fun w => ψ (w.2, w.1), by fun_prop⟩, fun x => ?_, fun x => ?_⟩, fun t x hx => ?_⟩⟩
  · exact h0 x
  · exact h1 x
  · rcases hx with rfl | hx
    · exact h2 t
    · obtain rfl : x = 1 := hx
      exact h3 t

/-- A flat set in the sense of paths is flat. -/
theorem Flat.isFlat {A : Set S} (hA : Flat A) : IsFlat A := fun φ hφ => by
  have hK' := flat_univ_iff.mpr hA
  let a : (univ : Set S) := ⟨φ (arcParam 1 0), trivial⟩
  let γ : Path a a :=
    ⟨⟨fun t => ⟨φ (arcParam 1 t), trivial⟩, by fun_prop⟩, rfl, Subtype.ext (by simp [a])⟩
  have hγ : ∀ u, γ u ∈ (Subtype.val ⁻¹' A : Set (univ : Set S)) := fun u => hφ ⟨_, rfl⟩
  have hh : γ.Homotopic (Path.refl a) := hK' _ _ hγ fun _ => by simpa using hγ 0
  exact ⟨a.1, a.2, closedCurvesHomotopicIn_of_path 1 φ (ContinuousMap.const _ a.1) γ (Path.refl a)
    (fun _ => rfl) (fun _ => rfl) hh⟩

/-- **Adding a disc that joins two pieces of a flat open set.** Let `c₁` and `c₂` be disjoint
path-connected open subsets of a flat open set `Y`, and let `N` be the inside of a closed
disc. Suppose that `N` meets `Y` only in two path-connected sets, one in `c₁` and one in `c₂`. Then
`Y ∪ N` is flat. This is the step of the proof of (4.3) of Graph Minors VII (page 222) in which an
edge
between two components of `Y` is added to `Y`, and the proof is the van Kampen argument in
`flat_iUnion_cover`. A closed curve lies either in `Y` without `c₁`, `c₂`, or in `c₁ ∪ c₂ ∪ N`. -/
theorem IsFlat.union_bridge {Y Δ A B c₁ c₂ : Set S} (hY : IsFlat Y) (h1Y : c₁ ⊆ Y) (h2Y : c₂ ⊆ Y)
  (h1o : IsOpen c₁) (h2o : IsOpen c₂) (h1p : IsPathConnected c₁) (h2p : IsPathConnected c₂)
    (hd : Disjoint c₁ c₂) (hrest : IsOpen (Y \ (c₁ ∪ c₂))) (hΔ : IsClosedDisc Δ) (hNo : IsOpen
      (Δ \ discBd Δ)) (hA : IsPathConnected A) (hB : IsPathConnected B) (hAe : A = c₁ ∩
        (Δ \ discBd Δ)) (hBe : B = c₂ ∩ (Δ \ discBd Δ))
    (hYN : Y ∩ (Δ \ discBd Δ) ⊆ c₁ ∪ c₂) : IsFlat (Y ∪ (Δ \ discBd Δ)) := by
  classical
  set N := Δ \ discBd Δ with hN
  have hAN : A ⊆ N := hAe ▸ inter_subset_right
  have hBN : B ⊆ N := hBe ▸ inter_subset_right
  have hNp : IsPathConnected N := by
    obtain ⟨h, g, c⟩ := hΔ.exists_isChart
    have e : N = g '' Metric.ball 0 1 := c.discInt_eq
    rw [e]
    exact ((convex_ball 0 1).isPathConnected ⟨0, by simp⟩).image'
      (c.gc.mono Metric.ball_subset_closedBall)
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨b, hb⟩ := hB.nonempty
  have hNf : Flat N := IsFlat.flat (fun φ hφ => ?_)
  rotate_left
  · obtain ⟨c, hc, h⟩ := null_of_disc φ.continuous hΔ (fun w => (hφ ⟨w, rfl⟩).1)
    exact ⟨c, trivial, h.mono (subset_univ _)⟩
  let O : Fin 3 → Set S := ![c₁, c₂, N]
  let bs : Fin 3 → S := ![a, b, a]
  have hOo : ∀ i, IsOpen (O i) := by
    intro i
    fin_cases i
    · exact h1o
    · exact h2o
    · exact hNo
  have hOp : ∀ i, IsPathConnected (O i) := by
    intro i
    fin_cases i
    · exact h1p
    · exact h2p
    · exact hNp
  have hOb : ∀ i, bs i ∈ O i := by
    intro i
    fin_cases i
    · exact (hAe.subset ha).1
    · exact (hBe.subset hb).1
    · exact hAN ha
  have hOf : ∀ i, Flat (O i) := by
    intro i
    fin_cases i
    · exact IsFlat.flat (IsFlat.mono hY h1Y)
    · exact IsFlat.flat (IsFlat.mono hY h2Y)
    · exact hNf
  have hNs : ∀ {P : Set S}, P ⊆ N → ∀ z ∈ P, ∀ w ∈ P, IsPathConnected P
    → ∃ f : GM11.Cl z w, GM11.Arw N f := fun hs z hz w hw hc => by
    have hj := hc.joinedIn z hz w hw
    exact ⟨GM11.Cl.mk hj.somePath, hj.somePath, fun u => hs (hj.somePath_mem u), rfl⟩
  have hF : Flat (⋃ i, O i) := by
    refine flat_iUnion_cover hNf O bs hOo hOb hOp hOf fun i j y hi hj => ?_
    have hto : ∀ i, y ∈ O i → y ∈ N → ∃ f : GM11.Cl (bs i) y, GM11.Arw (O i) f ∧ GM11.Arw N f := by
      intro i hi hyN
      fin_cases i
      · have hyA : y ∈ A := hAe.symm.subset ⟨hi, hyN⟩
        have hj := hA.joinedIn a ha y hyA
        have hm : ∀ u, hj.somePath u ∈ c₁ ∩ N := fun u => hAe.subset (hj.somePath_mem u)
        exact ⟨GM11.Cl.mk hj.somePath, ⟨hj.somePath, fun u => (hm u).1, rfl⟩, hj.somePath,
          fun u => (hm u).2, rfl⟩
      · have hyB : y ∈ B := hBe.symm.subset ⟨hi, hyN⟩
        have hj := hB.joinedIn b hb y hyB
        have hm : ∀ u, hj.somePath u ∈ c₂ ∩ N := fun u => hBe.subset (hj.somePath_mem u)
        exact ⟨GM11.Cl.mk hj.somePath, ⟨hj.somePath, fun u => (hm u).1, rfl⟩, hj.somePath,
          fun u => (hm u).2, rfl⟩
      · have hj := hNp.joinedIn a (hAN ha) y hyN
        exact ⟨GM11.Cl.mk hj.somePath, ⟨hj.somePath, hj.somePath_mem, rfl⟩, hj.somePath,
          hj.somePath_mem, rfl⟩
    by_cases hyN : y ∈ N
    · obtain ⟨f, hf, hf'⟩ := hto i hi hyN
      obtain ⟨g, hg, hg'⟩ := hto j hj hyN
      exact ⟨f, g.symm, hf, hg.symm, hf'.trans hg'.symm⟩
    · have hsame : i = j := by
        fin_cases i <;> fin_cases j <;> first
          | rfl
          | exact (hyN hi).elim
          | exact (hyN hj).elim
          | exact (disjoint_left.mp hd hi hj).elim
          | exact (disjoint_left.mp hd hj hi).elim
      subst hsame
      have hjn := (hOp i).joinedIn (bs i) (hOb i) y hi
      have hf : GM11.Arw (O i) (GM11.Cl.mk hjn.somePath) := ⟨hjn.somePath, hjn.somePath_mem, rfl⟩
      refine ⟨_, _, hf, hf.symm, ?_⟩
      rw [GM11.cl_trans_symm]
      have hbN : bs i ∈ N := by
        fin_cases i
        · exact hAN ha
        · exact hBN hb
        · exact hAN ha
      exact GM11.arw_refl hbN
  have hIF : IsFlat (⋃ i, O i) := Flat.isFlat hF
  intro φ hφ
  have hpre : IsPreconnected (range φ) := isPreconnected_range φ.continuous
  have hunion : (⋃ i, O i) = c₁ ∪ c₂ ∪ N := by
    ext z
    simp only [mem_iUnion, Fin.exists_fin_succ, O, mem_union]
    simp
    tauto
  have hWo : IsOpen (⋃ i, O i) := isOpen_iUnion hOo
  have hdis : Disjoint (⋃ i, O i) (Y \ (c₁ ∪ c₂)) := by
    rw [hunion, disjoint_left]
    rintro z (h | h) hz
    · exact hz.2 h
    · exact hz.2 (hYN ⟨hz.1, h⟩)
  have hcov : range φ ⊆ (⋃ i, O i) ∪ (Y \ (c₁ ∪ c₂)) := fun z hz => by
    by_cases h : z ∈ c₁ ∪ c₂
    · refine .inl ?_
      rw [hunion]
      exact .inl h
    · rcases hφ hz with h1 | h1
      · exact .inr ⟨h1, h⟩
      · refine .inl ?_
        rw [hunion]
        exact .inr h1
  rcases hpre.subset_or_subset hWo hrest hdis hcov with h | h
  · exact hIF φ h
  · exact hY φ (h.trans sdiff_subset)

/-- An `O`-arc cut into two lines at `x` and `w`. Near `w` it has a third line `R` between two
points `a`, `b` of the two lines. It holds `w` and not `x`, and the rest of the `O`-arc is a closed
set `R'`. -/
theorem exists_piece_around [T2Space S] {C P Q : Set S} {x w a b : S} (hO : IsOArc C)
  (hP : IsLineWithEnds P x w) (hQ : IsLineWithEnds Q x w) (hPQ : P ∪ Q = C) (hPQi : P ∩ Q = {x, w})
    (ha : a ∈ P \ {x, w}) (hb : b ∈ Q \ {x, w}) : ∃ R R' : Set S, IsLineWithEnds R a b
      ∧ IsClosed R' ∧ R ∪ R' = C ∧ R ∩ R' ⊆ {a, b} ∧ w ∈ R ∧ x ∉ R := by
  have hPs : P ⊆ C := hPQ ▸ subset_union_left
  have hQs : Q ⊆ C := hPQ ▸ subset_union_right
  have hab : a ≠ b := fun h => ha.2 (hPQi ▸ ⟨ha.1, h ▸ hb.1⟩)
  obtain ⟨R₀, R₁, hR₀, hR₁, hRu, hRi⟩ := hO.lines (hPs ha.1) (hQs hb.1) hab
  have hxa : x ≠ a := fun h => ha.2 (.inl h.symm)
  have hxb : x ≠ b := fun h => hb.2 (.inl h.symm)
  have hwa : w ≠ a := fun h => ha.2 (.inr h.symm)
  have hwb : w ≠ b := fun h => hb.2 (.inr h.symm)
  have hsep : ∀ {R₂ : Set S}, IsLineWithEnds R₂ a b → R₂ ⊆ C → x ∉ R₂ → w ∉ R₂ → False
    := fun {R₂} hR₂ hs hx' hw' => by
    have hc := (isConnected_line hR₂).isPreconnected
    have hcov : R₂ ⊆ P ∪ Q := hPQ ▸ hs
    obtain ⟨z, hz, h1⟩ := isPreconnected_closed_iff.mp hc P Q hP.isCompact.isClosed
      hQ.isCompact.isClosed hcov ⟨a, hR₂.left_mem, ha.1⟩ ⟨b, hR₂.right_mem, hb.1⟩
    have : z ∈ ({x, w} : Set S) := hPQi ▸ h1
    rcases this with rfl | h
    · exact hx' hz
    · exact hw' ((mem_singleton_iff.mp h) ▸ hz)
  have hwm : w ∈ R₀ ∪ R₁ := hRu ▸ hPs hP.right_mem
  have hRs₀ : R₀ ⊆ C := hRu ▸ subset_union_left
  have hRs₁ : R₁ ⊆ C := hRu ▸ subset_union_right
  have hnot : ∀ z, z ≠ a → z ≠ b → z ∈ R₀ → z ∉ R₁ := fun z h1 h2 h3 h4 => by
    rcases (hRi ▸ ⟨h3, h4⟩ : z ∈ ({a, b} : Set S)) with h | h
    · exact h1 h
    · exact h2 h
  rcases hwm with h | h
  · exact ⟨R₀, R₁, hR₀, hR₁.isCompact.isClosed, hRu, hRi.subset, h,
      fun h2 => hsep hR₁ hRs₁ (hnot x hxa hxb h2) (hnot w hwa hwb h)⟩
  · exact ⟨R₁, R₀, hR₁, hR₀.isCompact.isClosed, by rwa [union_comm],
      by rw [inter_comm]; exact hRi.subset, h,
      fun h2 => hsep hR₀ hRs₀ (fun h3 => hnot x hxa hxb h3 h2) (fun h3 => hnot w hwa hwb h3 h)⟩

/-- Let `e` be a loop of a proper graph, cut into two lines `P` and `Q` at `s` and `t`. If `s` lies
in a flat set `Y` that holds all of `Σ` off `U(G)` and `bd(Σ)`, then `Y` stays flat when we add both
lines. -/
theorem IsFlat.union_pair (hS : IsSurface S) {G : Drawing S} (hG : G.IsProper) {Y : Set S}
  (hY : IsFlat Y) (hrest : ∀ z, z ∉ G.U → z ∉ bd S → z ∈ Y) {e : Set S} (he : e ∈ G.E) {u : S}
    (hcap : closure e ∩ G.V = {u}) {P Q : Set S} {s t : S} (hP : IsLineWithEnds P s t)
      (hQ : IsLineWithEnds Q s t) (hPQ : P ∪ Q = closure e) (hPQi : P ∩ Q = {s, t}) (hu : u ∈
        ({s, t} : Set S)) (hsY : s ∈ Y) :
    IsFlat (Y ∪ (P \ {s, t}) ∪ (Q \ {s, t})) := by
  have ht2 : T2Space S := hS.2.1
  have hW0 : IsClosed (G.U \ e) := isClosed_U_sdiff_edge G he
  have hclU : closure e ⊆ G.U := G.closure_subset_U he
  have hdiff : closure e \ G.V = e := G.closure_diff_V he
  have hinV : ∀ z ∈ closure e, z ∉ e → z = u := fun z h1 h2 => by
    have h3 : z ∈ G.V := by
      by_contra h3
      apply h2
      rw [← hdiff]
      exact ⟨h1, h3⟩
    have hm : z ∈ closure e ∩ G.V := ⟨h1, h3⟩
    rw [hcap] at hm
    exact hm
  have hbV : ∀ z ∈ closure e, z ∈ bd S → z = u := fun z h1 h2 => by
    have hm : z ∈ closure e ∩ G.V := ⟨h1, hG ⟨h2, hclU h1⟩⟩
    rw [hcap] at hm
    exact hm
  have hmain : ∀ {Y' R R' : Set S}, IsFlat Y' → Y ⊆ Y' → s ∈ Y' → IsLineWithEnds R s t
    → IsLineWithEnds R' s t → R ∪ R' = closure e → R ∩ R' = {s, t} → IsFlat (Y' ∪ (R \ {s, t}))
      := fun {Y' R R'} hF hs hsY' hR hR' hu' hi => by
    have hRs : R ⊆ closure e := hu' ▸ subset_union_left
    refine IsFlat.union_line hS hF hR (hW0.union hR'.isCompact.isClosed) ?_ ?_ hsY' fun z h1 h2 h3
      => hs (hrest z (fun h => ?_) h2)
    · rintro z ⟨hz, h | h⟩
      · have := hinV z (hRs hz) h.2
        exact this ▸ hu
      · have : z ∈ R ∩ R' := ⟨hz, h⟩
        rwa [hi] at this
    · rintro z ⟨hz, hb⟩
      have := hbV z (hRs hz) hb
      exact this ▸ hu
    · by_cases h4 : z ∈ e
      · have : z ∈ R ∪ R' := hu' ▸ subset_closure h4
        rcases this with h5 | h5
        · exact h3 h5
        · exact h1 (.inr h5)
      · exact h1 (.inl ⟨h, h4⟩)
  have hF1 := hmain hY subset_rfl hsY hP hQ hPQ hPQi
  exact hmain hF1 subset_union_left (.inl hsY) hQ hP
    (by rwa [union_comm]) (by rwa [inter_comm])

/-- A flat set that holds all of `Σ` off `U(G)` and `bd(Σ)`, and a point of a loop `e`, stays flat
when we add `e`. -/
theorem IsFlat.union_loop (hS : IsSurface S) {G : Drawing S} (hG : G.IsProper) {Y : Set S}
  (hY : IsFlat Y) (hrest : ∀ z, z ∉ G.U → z ∉ bd S → z ∈ Y) {e : Set S} (he : e ∈ G.E) {u : S}
    (hcap : closure e ∩ G.V = {u}) (hO : IsOArc (closure e)) {w : S} (hwe : w ∈ e)
      (hwY : w ∈ Y) : IsFlat (Y ∪ e) := by
  have ht2 : T2Space S := hS.2.1
  have hu : u ∈ closure e ∩ G.V := by
    rw [hcap]
    rfl
  have hoff : ∀ z ∈ e, z ∉ G.V := fun z hz => by
    have h : z ∈ closure e \ G.V := by
      rw [G.closure_diff_V he]
      exact hz
    exact h.2
  have hwu : w ≠ u := fun h => hoff w hwe (h ▸ hu.2)
  obtain ⟨P, Q, hP, hQ, hPQ, hPQi⟩ := hO.lines (subset_closure hwe) hu.1 hwu
  refine IsFlat.mono (IsFlat.union_pair hS hG hY hrest he hcap hP hQ hPQ hPQi
    (.inr rfl) hwY) fun z hz => ?_
  rcases hz with hz | hz
  · exact .inl (.inl hz)
  by_cases hzw : z = w
  · exact .inl (.inl (hzw ▸ hwY))
  have hzu : z ≠ u := fun h => hoff z hz (h ▸ hu.2)
  have : z ∈ P ∪ Q := hPQ ▸ subset_closure hz
  rcases this with h | h
  · exact .inl (.inr ⟨h, by simp [hzw, hzu]⟩)
  · exact .inr ⟨h, by simp [hzw, hzu]⟩

/-- **Adding an edge at a vertex of a flat set.** Let `Y` be flat, hold all of `Σ` off `U(G)` and
`bd(Σ)`, and hold an end of the edge `e` of the proper graph `G`.
Then `Y ∪ e` is flat. For a loop we cut `ē` at a point `w` into two lines, add them in turn by
`IsFlat.union_line`, and then add `w` with a line around it. -/
theorem IsFlat.union_edge (hS : IsSurface S) {G : Drawing S} (hG : G.IsProper) {Y : Set S}
  (hY : IsFlat Y) (hrest : ∀ z, z ∉ G.U → z ∉ bd S → z ∈ Y) {e : Set S} (he : e ∈ G.E) {x : S}
    (hx : x ∈ closure e) (hxV : x ∈ G.V) (hxY : x ∈ Y) : IsFlat (Y ∪ e) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hW0 : IsClosed (G.U \ e) := isClosed_U_sdiff_edge G he
  have hclU : closure e ⊆ G.U := G.closure_subset_U he
  have hdiff : closure e \ G.V = e := G.closure_diff_V he
  have hoff : ∀ z ∈ e, z ∉ G.V := fun z hz => by
    have h : z ∈ closure e \ G.V := by
      rw [hdiff]
      exact hz
    exact h.2
  have hinV : ∀ z ∈ closure e, z ∉ e → z ∈ G.V := fun z h1 h2 => by
    by_contra h3
    apply h2
    rw [← hdiff]
    exact ⟨h1, h3⟩
  have hbV : ∀ z ∈ closure e, z ∈ bd S → z ∈ G.V := fun z h1 h2 => hG ⟨h2, hclU h1⟩
  rcases G.edge_cond e he with ⟨u, v, huv, hcap, hl⟩ | ⟨u, hcap, hO⟩
  · -- `e` is a line.
    have hxe : x ∈ ({u, v} : Set S) := hcap ▸ ⟨hx, hxV⟩
    obtain ⟨u', hu', hl'⟩ : ∃ u', closure e ∩ G.V = {x, u'} ∧ IsLineWithEnds (closure e) x u' := by
      rcases hxe with rfl | h
      · exact ⟨v, hcap, hl⟩
      · obtain rfl : x = v := h
        exact ⟨u, by rw [hcap, pair_comm], hl.symm⟩
    have hW : closure e ∩ (G.U \ e) ⊆ {x, u'} := fun z hz => hu' ▸ ⟨hz.1, hinV z hz.1 hz.2.2⟩
    have hb : closure e ∩ bd S ⊆ {x, u'} := fun z hz => hu' ▸ ⟨hz.1, hbV z hz.1 hz.2⟩
    refine IsFlat.mono (IsFlat.union_line hS hY hl' hW0 hW hb hxY fun z h1 h2 h3 => hrest z (fun h
      => h3 ?_) h2) (union_subset_union_right _ fun z hz => ?_)
    · by_contra h4
      exact h1 ⟨h, fun h5 => h4 (subset_closure h5)⟩
    · refine ⟨subset_closure hz, fun h => ?_⟩
      have h1 : z ∈ closure e ∩ G.V := hu' ▸ h
      exact hoff z hz h1.2
  · -- `e` is a loop at `x`.
    have hxu : x = u := by
      have : x ∈ ({u} : Set S) := hcap ▸ ⟨hx, hxV⟩
      exact this
    subst hxu
    obtain ⟨w, hwe⟩ : e.Nonempty := he.2.2.1.nonempty
    have hwx : x ≠ w := fun h => hoff w hwe (h ▸ hxV)
    obtain ⟨P, Q, hP, hQ, hPQ, hPQi⟩ := hO.lines hx (subset_closure hwe) hwx
    have hF2 := IsFlat.union_pair hS hG hY hrest he hcap hP hQ hPQ hPQi (.inl rfl) hxY
    obtain ⟨a, ha⟩ := GM14.IsLineWithEnds.nonempty_sdiff_pair hP
    obtain ⟨b, hb⟩ := GM14.IsLineWithEnds.nonempty_sdiff_pair hQ
    have hmem : a ∈ e := by
      by_contra h
      have hm : a ∈ closure e ∩ G.V := ⟨hPQ ▸ .inl ha.1, hinV a (hPQ ▸ .inl ha.1) h⟩
      rw [hcap] at hm
      exact ha.2 (.inl hm)
    refine IsFlat.mono (IsFlat.union_loop hS hG hF2 (fun z h1 h2 => .inl (.inl
      (hrest z h1 h2))) he hcap hO hmem (.inl (.inr ha))) ?_
    exact union_subset_union_left _ (subset_union_left.trans subset_union_left)

end GraphMinor.GM07

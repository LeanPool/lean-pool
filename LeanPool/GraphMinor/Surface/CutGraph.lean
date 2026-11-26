/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Classification

/-!
# Dissections that contain a given arc

To cut a surface along an arc or an `O`-arc `F`, we first dissect the surface so that `F` lies in
the graph of the
dissection. We add `F` to the graph of the cuffs and run the proof of `exists_surface_dissection`
(`exists_dissection_with`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

variable {X : Type u} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
/-- Adding a line with two distinct ends in a set keeps it connected after removing a point. -/
theorem TwoConn.add_line {G L : Set X} (hG : TwoConn G) {s t : X} (hl : IsLineWithEnds L s t)
  (hs : s ∈ G) (ht : t ∈ G)
    (hne : s ≠ t) : TwoConn (G ∪ L) := by
  classical
  intro p
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hl.exists_arc
  have hemb := fun (I : Set 𝕀) (hI : IsPreconnected I) => hI.image a ha.1.continuousOn
  have hbase : ((G \ {p})).Nonempty := by
    by_cases h : a 0 = p
    · exact ⟨a 1, ht, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨a 0, hs, fun h' => h h'⟩
  have hB : ∀ z ∈ (G ∪ range a) \ {p}, ∃ B : Set X, IsPreconnected B ∧ z ∈ B ∧ B ⊆
    (G ∪ range a) \ {p} ∧
      (B ∩ (G \ {p})).Nonempty := by
    rintro z ⟨hz | ⟨r, rfl⟩, hzp⟩
    · exact ⟨G \ {p}, hG p, ⟨hz, hzp⟩, fun y hy => ⟨.inl hy.1, hy.2⟩, ⟨z, ⟨hz, hzp⟩, hz, hzp⟩⟩
    · by_cases hp : ∃ c, a c = p
      · obtain ⟨c, rfl⟩ := hp
        have hrc : r ≠ c := fun h => hzp (by rw [h]; rfl)
        rcases lt_or_gt_of_ne hrc with h | h
        · refine ⟨a '' Iic r, hemb _ isPreconnected_Iic, ⟨r, le_rfl, rfl⟩, ?_, ⟨a 0, ⟨0,
            unitInterval.nonneg', rfl⟩, hs, ?_⟩⟩
          · rintro _ ⟨y, hy, rfl⟩
            exact ⟨.inr ⟨y, rfl⟩, fun he => (lt_of_le_of_lt hy h).ne (congrArg Subtype.val
              (ha.2 he))⟩
          · intro he
            have hzero : (0 : 𝕀) ≤ r := unitInterval.nonneg'
            exact (lt_of_le_of_lt hzero h).ne (ha.2 he)
        · refine ⟨a '' Ici r, hemb _ isPreconnected_Ici, ⟨r, le_rfl, rfl⟩, ?_, ⟨a 1, ⟨1,
            unitInterval.le_one', rfl⟩, ht, ?_⟩⟩
          · rintro _ ⟨y, hy, rfl⟩
            exact ⟨.inr ⟨y, rfl⟩, fun he => (lt_of_lt_of_le h hy).ne' (ha.2 he)⟩
          · exact fun he => (lt_of_lt_of_le h (show r ≤ 1 from unitInterval.le_one')).ne' (ha.2 he)
      · refine ⟨range a, ?_, ⟨r, rfl⟩, ?_, ⟨a 0, ⟨0, rfl⟩, hs, fun he => hp ⟨0, he⟩⟩⟩
        · rw [← image_univ]
          exact hemb _ isPreconnected_univ
        · rintro _ ⟨y, rfl⟩
          exact ⟨.inr ⟨y, rfl⟩, fun he => hp ⟨y, he⟩⟩
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := hB x hx
  obtain ⟨B', hB1', hB2', hB3', hB4'⟩ := hB y hy
  have hsub : G \ {p} ⊆ (G ∪ range a) \ {p} := fun z hz => ⟨.inl hz.1, hz.2⟩
  refine ⟨B ∪ (G \ {p}) ∪ B', union_subset (union_subset hB3 hsub) hB3', .inl (.inl hB2),
    .inr hB2', ?_⟩
  refine IsPreconnected.union' ?_ (hB1.union' hB4 (hG p)) hB1'
  obtain ⟨w, hw1, hw2⟩ := hB4'
  exact ⟨w, .inr hw2, hw1⟩

section pull

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T] [T2Space S] [T2Space T] {j : S
  → T}

omit [T2Space S] in
omit [T2Space T] in
/-- A point of the surface on an edge of a dissection of the closed surface lies on a pulled edge or
vertex. -/
theorem mem_pull_gr (hj : IsClosedEmbedding j) {K : Set T} (hK : IsClosed K) (hu : range j ∪ K
  = univ)
    (hi : range j ∩ K = j '' bd S) {V : Set T} {E 𝓕 : Set (Set T)} (hd : IsDissection V E 𝓕)
    (hb : j '' bd S ⊆ ⋃₀ {e ∈ E | e ⊆ range j}) {x : S} (hx : j x ∈ gr V E) :
    x ∈ gr (j ⁻¹' V) ((fun e => j ⁻¹' e) '' {e ∈ E | e ⊆ range j}) := by
  rcases hx with hx | ⟨e, he, hxe⟩
  · exact .inl hx
  by_cases hxV : j x ∈ V
  · exact .inl hxV
  have hg := hd.graph
  have hconn := hg.isPreconnected_open he
  have hin : e ⊆ range j := by
    by_cases hmeet : ∃ y ∈ e \ V, y ∈ range j ∩ K
    · obtain ⟨y, hy, hyr⟩ := hmeet
      rw [hi] at hyr
      obtain ⟨e', he', hye'⟩ := hb hyr
      have hee : e = e' := by
        by_contra hc
        exact hy.2 (hg.disj e he e' he'.1 hc ⟨hy.1, hye'⟩)
      rw [hee]
      exact he'.2
    · have hsub : e \ V ⊆ range j := by
        intro z hz
        by_contra hzr
        have hzK : z ∈ K := (hu ▸ mem_univ z : z ∈ range j ∪ K).resolve_left hzr
        obtain ⟨w, hw, hw1, hw2⟩ := isPreconnected_closed_iff.mp hconn _ _ hj.isClosed_range hK
          (fun y _ => hu ▸ mem_univ y) ⟨j x, ⟨hxe, hxV⟩, x, rfl⟩ ⟨z, hz, hzK⟩
        exact hmeet ⟨w, hw, hw1, hw2⟩
      exact (hg.subset_closure_open he).trans (closure_minimal hsub hj.isClosed_range)
  exact .inr ⟨_, ⟨e, ⟨he, hin⟩, rfl⟩, hxe⟩

end pull

variable {S : Type u} [TopologicalSpace S]

/-- A dissection containing a graph whose edges cover a finite family of circles and lines.
The circles contain the cuffs, and each line has two distinct endpoints on the circles. -/
theorem exists_dissection_with_lines (hS : IsSurface S) [ConnectedSpace S]
    {V₀ : Set S} {E₀ 𝓐 𝓛 : Set (Set S)} (hg : IsGraph V₀ E₀)
    (hV₀ : V₀ ⊆ ⋃₀ E₀) (h𝓐 : 𝓐.Finite) (h𝓛 : 𝓛.Finite)
    (hO𝓐 : ∀ C ∈ 𝓐, IsOArc C) (hcu : cuffs S ⊆ 𝓐)
    (hline : ∀ L ∈ 𝓛, ∃ s t, s ≠ t ∧ IsLineWithEnds L s t ∧ s ∈ ⋃₀ 𝓐 ∧ t ∈ ⋃₀ 𝓐)
    (hc : ⋃₀ E₀ = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛) :
    ∃ (V : Set S) (E 𝓕 : Set (Set S)), IsDissection V E 𝓕 ∧ V₀ ⊆ V ∧ ⋃₀ E₀ ⊆ gr V E := by
  classical
  obtain ⟨hcpt, ht2, hman⟩ := id hS
  obtain ⟨T, _, j, K, hT, hj, hK, hu, hi, hconn⟩ := exists_capAll S hS
  have := hconn inferInstance
  have : T2Space T := hT.2.1
  have hgT := hg.map hj.isEmbedding
  have hsU : ⋃₀ ((fun e => j '' e) '' E₀) = j '' ⋃₀ E₀ := by
    rw [sUnion_image, sUnion_eq_biUnion, image_iUnion₂]
  have hsA : ⋃₀ ((fun C => j '' C) '' 𝓐) = j '' ⋃₀ 𝓐 := by
    rw [sUnion_image, sUnion_eq_biUnion, image_iUnion₂]
  obtain ⟨ρ, hρ, hl⟩ := exists_inv_of_compactOn (isCompact_univ (X := S)) hj.continuous.continuousOn
    hj.injective.injOn
  have hOT : ∀ C ∈ 𝓐, IsOArc (j '' C) := fun C hC =>
    (hO𝓐 C hC).image hj.continuous.continuousOn (hρ.mono (image_mono (subset_univ _)))
      (fun x _ => hl (mem_univ x))
  obtain ⟨V, E, 𝓕, hVV, hsub, hd⟩ := exists_dissection hT hgT (image_mono hV₀ |>.trans (by
      rintro _ ⟨y, ⟨e, he, hy⟩, rfl⟩
      exact ⟨_, ⟨e, he, rfl⟩, mem_image_of_mem j hy⟩)) (𝓒c := (fun C => j '' C) '' 𝓐)
    (h𝓐.image _)
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact (hOT C hC).twoConn)
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact (hOT C hC).exists_three)
    (by
      intro G hG hm
      have h1 := hG.sUnion_add (h𝓐.image _) (by
        rintro _ ⟨C, hC, rfl⟩
        exact (hOT C hC).twoConn) hm
      rw [hsU]
      rw [hsA] at h1
      have key : ∀ 𝓛' : Set (Set S), 𝓛'.Finite → 𝓛' ⊆ 𝓛 → TwoConn (G ∪ j '' ⋃₀ 𝓐 ∪ j '' ⋃₀ 𝓛') := by
        intro 𝓛' h𝓛'
        induction 𝓛', h𝓛' using Set.Finite.induction_on with
        | empty =>
          intro _
          simpa using h1
        | @insert L 𝓛' hL hfin ih =>
          intro hsub
          obtain ⟨s, t, hne, hl, hs, ht⟩ := hline L (hsub (mem_insert _ _))
          have h2 := (ih ((subset_insert _ _).trans hsub)).add_line (hl.map_of_embedding
            hj.isEmbedding)
            (.inl (.inr (mem_image_of_mem j hs))) (.inl (.inr (mem_image_of_mem j ht)))
            (fun he => hne (hj.injective he))
          rw [sUnion_insert, union_comm L, image_union, ← union_assoc]
          exact h2
      have h3 := key 𝓛 h𝓛 subset_rfl
      rw [hc, image_union, ← union_assoc]
      exact h3)
  rw [hsU] at hsub
  have hbd : bd S ⊆ ⋃₀ 𝓐 := by
    rw [← sUnion_cuffs]
    exact sUnion_mono hcu
  have hsub2 : ⋃₀ 𝓐 ⊆ ⋃₀ E₀ := by
    rw [hc]
    exact subset_union_left
  have hb0 : j '' bd S ⊆ ⋃₀ E := (image_mono (hbd.trans hsub2)).trans hsub
  have hb1 : j '' bd S ⊆ ⋃₀ {e ∈ E | e ⊆ range j} := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ ⋃₀ cuffs S := sUnion_cuffs (S := S) ▸ hx
    obtain ⟨C, hC, hxC⟩ := hx'
    have hne : Nonempty T := ⟨j x⟩
    have hC' := hOT C (hcu hC)
    have hsubC : j '' C ⊆ ⋃₀ E :=
      (image_mono (subset_sUnion_of_mem (hcu hC) |>.trans hsub2)).trans hsub
    obtain ⟨e, he, hxe⟩ := hd.graph.subset_edges hC' hsubC (mem_image_of_mem j hxC)
    exact ⟨e, ⟨he.1, he.2.trans (image_subset_range _ _)⟩, hxe⟩
  refine ⟨_, _, _, pull_dissection hman hj hK hu hi hd hb0, ?_, ?_⟩
  · intro x hx
    exact hVV (mem_image_of_mem j hx)
  · intro x hx
    exact mem_pull_gr hj hK hu hi hd hb1 (.inr (hsub (mem_image_of_mem j hx)))

/-- A dissection of a connected surface whose graph contains the union of some `O`-arcs and possibly
one line. -/
theorem exists_dissection_with (hS : IsSurface S) [ConnectedSpace S] {V₀ : Set S} {E₀ 𝓐 : Set
  (Set S)} (hg : IsGraph V₀ E₀)
    (hV₀ : V₀ ⊆ ⋃₀ E₀) (h𝓐 : 𝓐.Finite) (hO𝓐 : ∀ C ∈ 𝓐, IsOArc C) (hcu : cuffs S ⊆ 𝓐)
    (hcase : ⋃₀ E₀ = ⋃₀ 𝓐 ∨ ∃ L s t, ⋃₀ E₀ = ⋃₀ 𝓐 ∪ L ∧ IsLineWithEnds L s t ∧ s ≠ t ∧ s ∈ ⋃₀ 𝓐
      ∧ t ∈ ⋃₀ 𝓐) :
    ∃ (V : Set S) (E 𝓕 : Set (Set S)), IsDissection V E 𝓕 ∧ V₀ ⊆ V ∧ ⋃₀ E₀ ⊆ gr V E := by
  rcases hcase with hE | ⟨L, s, t, hE, hline, hne, hs, ht⟩
  · refine exists_dissection_with_lines (𝓛 := ∅) hS hg hV₀ h𝓐 finite_empty hO𝓐 hcu ?_ ?_
    · exact fun _ h => h.elim
    · simpa using hE
  · refine exists_dissection_with_lines (𝓛 := {L}) hS hg hV₀ h𝓐 (finite_singleton L) hO𝓐 hcu ?_ ?_
    · intro M hM
      obtain rfl := mem_singleton_iff.mp hM
      exact ⟨s, t, hne, hline, hs, ht⟩
    · simpa using hE

end GraphMinor.Surface

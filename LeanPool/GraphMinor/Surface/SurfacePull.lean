/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.EdgeLoop

/-!
# Dissections of surfaces with boundary

A surface with boundary sits in a closed surface, by capping its cuffs. If the cuffs lie in the
graph of a dissection
of the closed surface, each cell lies in the surface or in the caps, since its interior is
connected. The cells in the
surface, with the edges in the surface, form a dissection of the surface (`pull_dissection`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

section dense

variable {S : Type u} [TopologicalSpace S]

/-- Points that are not on the boundary are dense. -/
theorem mem_closure_compl_bd {x : S} (hx : IsManifoldPoint x) : x ∈ closure (bd S)ᶜ := by
  obtain ⟨U, O, j, k, hU, hO, hxU, hj, hk, hm, hk', hl, hr⟩ := hx.exists_chart
  rw [_root_.mem_closure_iff]
  intro N hN hxN
  have hcw : ContinuousWithinAt k (O ∩ halfPlane) (j x) := hk _ (hm hxU)
  have hA : U ∩ N ∈ 𝓝 (k (j x)) := by
    rw [hl hxU]
    exact (hU.inter hN).mem_nhds ⟨hxU, hxN⟩
  have h1 := hcw hA
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.mp h1
  obtain ⟨ρ', hρ', hball'⟩ := Metric.isOpen_iff.mp hO _ (hm hxU).1
  let r : ℝ := min ρ ρ' / 2
  have hr0 : 0 < r := by positivity
  have hr1 : r < ρ := by
    have := min_le_left ρ ρ'
    simp only [r]
    linarith [lt_min hρ hρ']
  have hr2 : r < ρ' := by
    have := min_le_right ρ ρ'
    simp only [r]
    linarith [lt_min hρ hρ']
  let z : ℂ := j x + (r : ℂ)
  have hzd : dist z (j x) = r := by
    simp [z, dist_eq_norm, abs_of_pos hr0]
  have hzH : z ∈ O ∩ halfPlane := by
    refine ⟨hball' (by simpa [hzd] using hr2), ?_⟩
    have := (hm hxU).2
    have h' : 0 ≤ (j x).re := this
    change 0 ≤ (j x + (r : ℂ)).re
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hkz : k z ∈ U ∩ N := hball ⟨by simpa [hzd] using hr1, hzH⟩
  refine ⟨k z, hkz.2, ?_⟩
  have hre : 0 < (j (k z)).re := by
    rw [hr hzH]
    have h' : 0 ≤ (j x).re := (hm hxU).2
    simp only [z, Complex.add_re, Complex.ofReal_re]
    linarith
  exact fun hb => hb (isInteriorPoint_of_chart hU hO hj hk hm hk' hl hr hkz.1 hre)

end dense

section map

variable {S : Type u} {T : Type u} [TopologicalSpace S] [TopologicalSpace T] [T2Space S] [T2Space
  T] {j : S → T}

omit [T2Space S] in
theorem IsLineWithEnds.map_of_embedding (hj : IsEmbedding j) {L : Set S} {u v : S}
  (hl : IsLineWithEnds L u v) :
    IsLineWithEnds (j '' L) (j u) (j v) := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hl.exists_arc
  have h1 : IsArcMap (j ∘ a) := ⟨hj.continuous.comp ha.1, hj.injective.comp ha.2⟩
  have := h1.isLineWithEnds
  rwa [range_comp] at this

omit [T2Space T] in
theorem IsLineWithEnds.pull (hj : IsEmbedding j) {L : Set T} {u v : T} (hl : IsLineWithEnds L u v)
    (hs : L ⊆ range j) : ∃ u' v', j u' = u ∧ j v' = v ∧ IsLineWithEnds (j ⁻¹' L) u' v' := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hl.exists_arc
  have hex : ∀ t, ∃ y, j y = a t := fun t => hs ⟨t, rfl⟩
  choose a' ha' using hex
  have hc : Continuous a' := by
    rw [hj.continuous_iff]
    have : j ∘ a' = a := funext ha'
    rw [this]
    exact ha.1
  have hi : IsArcMap a' := ⟨hc, fun x y he => ha.2 (by rw [← ha', ← ha', he])⟩
  refine ⟨a' 0, a' 1, ha' 0, ha' 1, ?_⟩
  have := hi.isLineWithEnds
  have e : j ⁻¹' range a = range a' := by
    ext y
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, hj.injective ((ha' t).trans ht)⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, (ha' t).symm⟩
  rwa [e]

omit [T2Space S] in
/-- The image of a graph by an embedding. -/
theorem IsGraph.map (hj : IsEmbedding j) {V : Set S} {E : Set (Set S)} (h : IsGraph V E) :
    IsGraph (j '' V) ((fun e => j '' e) '' E) := by
  refine ⟨h.fin.image _, h.fine.image _, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨u, v, hne, hl, hi⟩ := h.edge e he
    refine ⟨j u, j v, hj.injective.ne hne, hl.map_of_embedding hj, ?_⟩
    rw [← image_inter hj.injective, hi, image_pair]
  · rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ hne
    have hne' : e ≠ f := fun h' => hne (by rw [h'])
    rw [← image_inter hj.injective]
    exact image_mono (h.disj e he f hf hne')

omit [T2Space T] in
/-- The part of a graph on the image of an embedding, made of whole edges. -/
theorem IsGraph.pull (hj : IsEmbedding j) {V : Set T} {E : Set (Set T)} (h : IsGraph V E) :
    IsGraph (j ⁻¹' V) ((fun e => j ⁻¹' e) '' {e ∈ E | e ⊆ range j}) := by
  refine ⟨h.fin.preimage hj.injective.injOn, (h.fine.subset (sep_subset _ _)).image _, ?_, ?_⟩
  · rintro _ ⟨e, ⟨he, hs⟩, rfl⟩
    obtain ⟨u, v, hne, hl, hi⟩ := h.edge e he
    obtain ⟨u', v', rfl, rfl, hl'⟩ := hl.pull hj hs
    refine ⟨u', v', fun h' => hne (by rw [h']), hl', ?_⟩
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h1
      have h2 : j y ∈ e ∩ V := h1
      rw [hi] at h2
      rcases h2 with h2 | h2
      · exact .inl (hj.injective h2)
      · exact .inr (hj.injective h2)
    · rintro (h1 | h1)
      · have : j y ∈ e ∩ V := by rw [hi, h1]; exact .inl rfl
        exact this
      · have : j y ∈ e ∩ V := by rw [hi, h1]; exact .inr rfl
        exact this
  · rintro _ ⟨e, ⟨he, hs⟩, rfl⟩ _ ⟨f, ⟨hf, hs'⟩, rfl⟩ hne
    have hne' : e ≠ f := fun h' => hne (by rw [h'])
    exact fun y hy => h.disj e he f hf hne' hy

end map

/-- An `O`-arc in a graph is the union of the edges inside it. -/
theorem IsGraph.subset_edges {X : Type u} [TopologicalSpace X] [T2Space X] [Nonempty X] {V : Set X}
  {E : Set (Set X)}
    (hg : IsGraph V E) {P : Set X} (hP : IsOArc P) (hPG : P ⊆ ⋃₀ E) : P ⊆ ⋃₀ {e ∈ E | e ⊆ P} := by
  classical
  have harcs : ∀ e, ∃ a : 𝕀 → X, e ∈ E → IsArcMap a ∧ range a = e ∧ e ∩ V = {a 0, a 1} := by
    intro e
    by_cases he : e ∈ E
    · obtain ⟨u, v, -, hl, hi⟩ := hg.edge e he
      obtain ⟨a, ha, h1, rfl, rfl⟩ := hl.exists_arc
      exact ⟨a, fun _ => ⟨ha, h1, hi⟩⟩
    · exact ⟨fun _ => Classical.arbitrary X, fun h => absurd h he⟩
  choose A hA using harcs
  obtain ⟨m, s, ε, -, hs, hcov, -⟩ := exists_edge_walk hg hP hPG A hA
  intro y hy
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hcov hy)
  exact ⟨s p, hs p hp, hyp⟩

section pull

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T] [T2Space S] [T2Space T] {j : S
  → T}

omit [T2Space S] in
theorem isClosedDisc_preimage [CompactSpace S] [Nonempty S] (hj : IsClosedEmbedding j) {Φ : Set T}
    (hΦ : IsClosedDisc Φ) (hs : Φ ⊆ range j) :
    IsClosedDisc (j ⁻¹' Φ) ∧ discBd (j ⁻¹' Φ) = j ⁻¹' discBd Φ := by
  obtain ⟨ρ, hρ, hl⟩ := exists_inv_of_compactOn (isCompact_univ (X := S)) hj.continuous.continuousOn
    hj.injective.injOn
  have hl' : ∀ x, ρ (j x) = x := fun x => hl (mem_univ x)
  have hsr : ∀ y ∈ Φ, j (ρ y) = y := fun y hy => by
    obtain ⟨x, rfl⟩ := hs hy
    rw [hl']
  have hrΦ : Φ ⊆ j '' univ := by
    rw [image_univ]
    exact hs
  have e : ∀ F : Set T, F ⊆ Φ → ρ '' F = j ⁻¹' F := fun F hF => by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change j (ρ y) ∈ F
      rwa [hsr y (hF hy)]
    · intro hx
      exact ⟨j x, hx, hl' x⟩
  obtain ⟨h1, h2⟩ := hΦ.image (f := ρ) (f' := j) (hρ.mono hrΦ) hj.continuous.continuousOn
    (fun y hy => hsr y hy)
  rw [e Φ subset_rfl] at h1 h2
  rw [e _ (discBd_subset Φ)] at h2
  exact ⟨h1, h2⟩

/-- Cells and edges of a dissection of a closed surface, restricted to a surface inside it. -/
theorem pull_dissection [CompactSpace S] [Nonempty S] (hman : ∀ x : S, IsManifoldPoint x)
  (hj : IsClosedEmbedding j) {K : Set T} (hK : IsClosed K)
    (hu : range j ∪ K = univ) (hi : range j ∩ K = j '' bd S) {V : Set T} {E 𝓕 : Set (Set T)}
      (hd : IsDissection V E 𝓕)
    (hb : j '' bd S ⊆ ⋃₀ E) :
    IsDissection (j ⁻¹' V) ((fun e => j ⁻¹' e) '' {e ∈ E | e ⊆ range j}) ((fun Φ
      => j ⁻¹' Φ) '' {Φ ∈ 𝓕 | Φ ⊆ range j}) := by
  classical
  have hR : IsClosed (range j) := hj.isClosed_range
  have hside : ∀ Φ ∈ 𝓕, Φ ⊆ range j ∨ Φ ⊆ K := by
    intro Φ hΦ
    have hD := hd.disc Φ hΦ
    have hcov : discInt Φ ⊆ range j ∪ K := fun y _ => hu ▸ mem_univ y
    by_cases h1 : (discInt Φ ∩ range j).Nonempty
    · by_cases h2 : (discInt Φ ∩ K).Nonempty
      · obtain ⟨y, hy, hy1, hy2⟩ :=
          isPreconnected_closed_iff.mp hD.isPreconnected_discInt _ _ hR hK hcov h1 h2
        exact absurd (hb (hi ▸ (⟨hy1, hy2⟩ : y ∈ range j ∩ K))) (Set.disjoint_left.mp
          (hd.int Φ hΦ) hy)
      · left
        have h3 : discInt Φ ⊆ range j := fun y hy =>
          (hcov hy).resolve_right fun h => h2 ⟨y, hy, h⟩
        exact hD.subset_closure_discInt.trans (closure_minimal h3 hR)
    · right
      have h3 : discInt Φ ⊆ K := fun y hy => (hcov hy).resolve_left fun h => h1 ⟨y, hy, h⟩
      exact hD.subset_closure_discInt.trans (closure_minimal h3 hK)
  have hpb : ∀ Φ ∈ {Φ ∈ 𝓕 | Φ ⊆ range j}, IsClosedDisc (j ⁻¹' Φ) ∧ discBd (j ⁻¹' Φ)
    = j ⁻¹' discBd Φ :=
    fun Φ hΦ => isClosedDisc_preimage hj (hd.disc Φ hΦ.1) hΦ.2
  have hint : ∀ Φ ∈ {Φ ∈ 𝓕 | Φ ⊆ range j}, ∀ y ∈ discInt (j ⁻¹' Φ), j y ∈ discInt Φ := by
    intro Φ hΦ y hy
    refine ⟨hy.1, fun h => hy.2 ?_⟩
    rw [(hpb Φ hΦ).2]
    exact h
  refine ⟨hd.graph.pull hj.isEmbedding, (hd.fin.subset (sep_subset _ _)).image _, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rintro _ ⟨Φ, hΦ, rfl⟩
    exact (hpb Φ hΦ).1
  · refine eq_univ_of_forall fun x => ?_
    have hfin : {Φ ∈ 𝓕 | Φ ⊆ range j}.Finite := hd.fin.subset (sep_subset _ _)
    have hQ : IsClosed (⋃₀ {Φ ∈ 𝓕 | Φ ⊆ range j}) :=
      hfin.isClosed_sUnion fun Φ hΦ => (hd.disc Φ hΦ.1).isClosed
    have hsub : (bd S)ᶜ ⊆ j ⁻¹' (⋃₀ {Φ ∈ 𝓕 | Φ ⊆ range j}) := by
      intro y hy
      have h1 : j y ∈ ⋃₀ 𝓕 := hd.cover ▸ mem_univ _
      obtain ⟨Φ, hΦ, hyΦ⟩ := h1
      rcases hside Φ hΦ with h2 | h2
      · exact ⟨Φ, ⟨hΦ, h2⟩, hyΦ⟩
      · have h3 : j y ∈ j '' bd S := hi ▸ (⟨⟨y, rfl⟩, h2 hyΦ⟩ : j y ∈ range j ∩ K)
        obtain ⟨z, hz, he⟩ := h3
        exact absurd (hj.injective he ▸ hz) hy
    have h4 := closure_minimal hsub (hQ.preimage hj.continuous) (mem_closure_compl_bd (hman x))
    obtain ⟨Φ, hΦ, hx⟩ := h4
    exact ⟨_, ⟨Φ, hΦ, rfl⟩, hx⟩
  · rintro _ ⟨Φ, hΦ, rfl⟩
    rw [(hpb Φ hΦ).2]
    intro y hy
    have hne : Nonempty T := ⟨j y⟩
    have hdO := (hd.disc Φ hΦ.1).isOArc_discBd
    obtain ⟨e, he, hye⟩ := hd.graph.subset_edges hdO (hd.bd Φ hΦ.1) hy
    exact ⟨_, ⟨e, ⟨he.1, he.2.trans ((discBd_subset Φ).trans hΦ.2)⟩, rfl⟩, hye⟩
  · rintro _ ⟨Φ, hΦ, rfl⟩
    rw [Set.disjoint_left]
    rintro y hy ⟨_, ⟨e, he, rfl⟩, hye⟩
    exact Set.disjoint_left.mp (hd.int Φ hΦ.1) (hint Φ hΦ y hy) ⟨e, he.1, hye⟩
  · rintro _ ⟨Φ, hΦ, rfl⟩ _ ⟨Φ', hΦ', rfl⟩ hne
    have hne' : Φ ≠ Φ' := fun h => hne (by rw [h])
    rw [Set.disjoint_left]
    intro y hy hy'
    exact Set.disjoint_left.mp (hd.disj Φ hΦ.1 Φ' hΦ'.1 hne') (hint Φ hΦ y hy) hy'
  · intro x hx
    have hx' : j x ∉ V := hx
    refine (encard_le_encard ?_).trans ((encard_image_le (fun Φ => j ⁻¹' Φ) _).trans (hd.count
      (j x) hx'))
    rintro _ ⟨⟨Φ, hΦ, rfl⟩, hxΦ⟩
    exact ⟨Φ, ⟨hΦ.1, hxΦ⟩, rfl⟩

end pull

end GraphMinor.Surface

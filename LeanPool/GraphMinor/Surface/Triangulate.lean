/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Fan
public import Mathlib.Topology.Separation.Connected
import LeanPool.GraphMinor.Surface.Circle

/-!
# Triangulating a closed surface

A dissection can be refined to one in which each face has three vertices and no two edges have the
same ends (`exists_triang`), without changing the number `|V| - |E| + |F|`. We cut each edge in two,
and then put a cone on each face by `exists_cone`. These refinements are the triangulations named in
the proof of Graph Minors XIX, (6.5) (page 341).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

variable {X : Type} [TopologicalSpace X]

/-- A dissection whose faces have three vertices each, and with no parallel edges. -/
structure IsTriang (V : Set X) (E 𝓕 : Set (Set X)) : Prop where
  dis : IsDissection V E 𝓕
  cov : V ⊆ ⋃₀ E
  three : ∀ Φ ∈ 𝓕, (Φ ∩ V).ncard = 3
  simple : ∀ e ∈ E, ∀ f ∈ E, e ∩ V = f ∩ V → e = f

theorem ncard_biUnion_eq {ι α : Type*} (s : Finset ι) (f : ι → Set α) (hf : ∀ i ∈ s, (f i).Finite)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : (⋃ i ∈ s, f i).Finite := s.finite_toSet.biUnion fun i hi => hf i
      (Finset.mem_insert_of_mem hi)
    have h2 : Disjoint (f a) (⋃ i ∈ s, f i) := by
      refine disjoint_iUnion₂_right.mpr fun i hi => hd a (Finset.mem_insert_self _ _) i
        (Finset.mem_insert_of_mem hi) ?_
      rintro rfl
      exact ha hi
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, ncard_union_eq h2 (hf a
      (Finset.mem_insert_self _ _)) h1,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]

variable [T2Space X]

omit [T2Space X] in
/-- Vertices on no edge can be dropped from a dissection. -/
theorem IsDissection.trim {V : Set X} {E 𝓕 : Set (Set X)} (h : IsDissection V E 𝓕) :
    IsDissection (V ∩ ⋃₀ E) E 𝓕 := by
  refine ⟨⟨h.graph.fin.subset inter_subset_left, h.graph.fine, fun e he => ?_,
    fun e he f hf hne x hx => ?_⟩, h.fin, h.disc, h.cover, h.bd, h.int, h.disj, fun x hx => ?_⟩
  · obtain ⟨u, v, huv, hl, hi⟩ := h.graph.edge e he
    refine ⟨u, v, huv, hl, ?_⟩
    ext y
    constructor
    · rintro ⟨h1, h2, -⟩
      exact hi ▸ ⟨h1, h2⟩
    · intro hy
      have : y ∈ e ∩ V := hi ▸ hy
      exact ⟨this.1, this.2, e, he, this.1⟩
  · exact ⟨h.graph.disj e he f hf hne hx, e, he, hx.1⟩
  · by_cases hV : x ∈ V
    · have hxE : x ∉ ⋃₀ E := fun h' => hx ⟨hV, h'⟩
      have hle : {Φ ∈ 𝓕 | x ∈ Φ}.encard ≤ 1 := by
        refine encard_le_one_iff.mpr ?_
        rintro Φ Φ' ⟨hΦ, h1⟩ ⟨hΦ', h2⟩
        by_contra hne
        have h3 : x ∈ discInt Φ := ⟨h1, fun h' => hxE (h.bd Φ hΦ h')⟩
        exact Set.disjoint_left.mp (h.disj Φ hΦ Φ' hΦ' hne) h3 h2
      exact hle.trans (by norm_num)
    · exact h.count x hV

omit [TopologicalSpace X] [T2Space X] in
private theorem half_edge_vertex_intersection
    {V : Set X} {E : Set (Set X)} {mid : Set X → X} {H e : Set X} {a b : X}
    (he : e ∈ E) (hsub : H ⊆ e) (hends : e ∩ V = {a, b})
    (ha : a ∈ H) (hm : mid e ∈ H) (hb : b ∉ H)
    (hmidE : ∀ f ∈ E, mid f ∈ e → e = f) :
    H ∩ (V ∪ mid '' E) = {a, mid e} := by
  ext y
  constructor
  · rintro ⟨hy, hyV | ⟨f, hf, rfl⟩⟩
    · rcases hends.subset ⟨hsub hy, hyV⟩ with hya | hyb
      · exact Or.inl hya
      · exact (hb (hyb ▸ hy)).elim
    · exact Or.inr (congrArg mid (hmidE f hf (hsub hy)).symm)
  · rintro (rfl | rfl)
    · exact ⟨ha, Or.inl (hends.symm.subset (Or.inl rfl)).2⟩
    · exact ⟨hm, Or.inr ⟨e, he, rfl⟩⟩

/-- Cutting every edge of a dissection in two. -/
theorem IsDissection.exists_halves {V : Set X} {E 𝓕 : Set (Set X)} (h : IsDissection V E 𝓕)
  (hV : V ⊆ ⋃₀ E) :
    ∃ (V₁ : Set X) (E₁ : Set (Set X)), IsDissection V₁ E₁ 𝓕 ∧ V ⊆ V₁ ∧ V₁ ⊆ ⋃₀ E₁ ∧ ⋃₀ E₁ = ⋃₀ E ∧
      (∀ e ∈ E₁, ∀ f ∈ E₁, e ∩ V₁ = f ∩ V₁ → e = f) ∧ V₁.ncard = V.ncard + E.ncard ∧ E₁.ncard
        = 2 * E.ncard ∧
      ∀ e ∈ E, ∃ m ∈ V₁, m ∉ V ∧ m ∈ e := by
  classical
  have hg := h.graph
  rcases E.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · have hV0 : V = ∅ := by simpa using hV
    subst hV0
    exact ⟨∅, ∅, h, Subset.rfl, by simp, rfl, by simp, by simp, by simp, by simp⟩
  obtain ⟨u₀, -, -, hl₀, -⟩ := hg.edge e₀ he₀
  have hne : Nonempty X := ⟨u₀⟩
  have hch : ∀ e ∈ E, ∃ a : 𝕀 → X, IsArcMap a ∧ range a = e ∧ e ∩ V = {a 0, a 1} := fun e he => by
    obtain ⟨u, v, huv, hl, hi⟩ := hg.edge e he
    obtain ⟨a, ha, hr, h0, h1⟩ := hl.exists_arc
    exact ⟨a, ha, hr, by rw [hi, h0, h1]⟩
  choose! a harc hrange hends using hch
  let m : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hm0 : (0 : 𝕀) < m := by
    change (0 : ℝ) < 1 / 2
    norm_num
  have hm1 : m < 1 := by
    change (1 / 2 : ℝ) < 1
    norm_num
  let mid : Set X → X := fun e => a e m
  let H₀ : Set X → Set X := fun e => a e '' Icc 0 m
  let H₁ : Set X → Set X := fun e => a e '' Icc m 1
  let V₁ : Set X := V ∪ mid '' E
  let E₁ : Set (Set X) := H₀ '' E ∪ H₁ '' E
  have hat : ∀ e ∈ E, ∀ t, a e t ∈ e := fun e he t => by
    have h1 : a e t ∈ range (a e) := mem_range_self t
    rwa [hrange e he] at h1
  have hmid : ∀ e ∈ E, mid e ∈ e := fun e he => hat e he m
  have hmidV : ∀ e ∈ E, mid e ∉ V := fun e he hV' => by
    have h1 : mid e ∈ e ∩ V := ⟨hmid e he, hV'⟩
    rw [hends e he] at h1
    rcases h1 with h1 | h1
    · exact hm0.ne' ((harc e he).2 h1)
    · exact hm1.ne ((harc e he).2 h1)
  have hmidE : ∀ e ∈ E, ∀ f ∈ E, mid e ∈ f → f = e := fun e he f hf h1 => by
    by_contra hc
    exact hmidV e he (hg.disj f hf e he hc ⟨h1, hmid e he⟩)
  have hH₀s : ∀ e ∈ E, H₀ e ⊆ e := fun e he => by
    rintro _ ⟨t, -, rfl⟩
    exact hat e he t
  have hH₁s : ∀ e ∈ E, H₁ e ⊆ e := fun e he => by
    rintro _ ⟨t, -, rfl⟩
    exact hat e he t
  have hmH₀ : ∀ e, mid e ∈ H₀ e := fun e => ⟨m, ⟨hm0.le, le_rfl⟩, rfl⟩
  have hmH₁ : ∀ e, mid e ∈ H₁ e := fun e => ⟨m, ⟨le_rfl, hm1.le⟩, rfl⟩
  have h0H₀ : ∀ e, a e 0 ∈ H₀ e := fun e => ⟨0, ⟨le_rfl, hm0.le⟩, rfl⟩
  have h1H₁ : ∀ e, a e 1 ∈ H₁ e := fun e => ⟨1, ⟨hm1.le, le_rfl⟩, rfl⟩
  have h1notH₀ : ∀ e ∈ E, a e 1 ∉ H₀ e := fun e he => by
    rintro ⟨t, ht, h1⟩
    have h2 : t = 1 := (harc e he).2 h1
    exact absurd (ht.2.trans_lt hm1) (by rw [h2]; exact lt_irrefl _)
  have h0notH₁ : ∀ e ∈ E, a e 0 ∉ H₁ e := fun e he => by
    rintro ⟨t, ht, h1⟩
    have h2 : t = 0 := (harc e he).2 h1
    exact absurd (hm0.trans_le ht.1) (by rw [h2]; exact lt_irrefl _)
  have hH₀V : ∀ e ∈ E, H₀ e ∩ V₁ = {a e 0, mid e} := fun e he =>
    half_edge_vertex_intersection he (hH₀s e he) (hends e he)
      (h0H₀ e) (hmH₀ e) (h1notH₀ e he) (fun f hf => hmidE f hf e he)
  have hH₁V : ∀ e ∈ E, H₁ e ∩ V₁ = {mid e, a e 1} := by
    intro e he
    rw [pair_comm]
    exact half_edge_vertex_intersection he (hH₁s e he) ((hends e he).trans (pair_comm _ _))
      (h1H₁ e) (hmH₁ e) (h0notH₁ e he) (fun f hf => hmidE f hf e he)
  have hH₀H₁ : ∀ e ∈ E, H₀ e ∩ H₁ e ⊆ {mid e} := by
    rintro e he _ ⟨⟨s, hs, rfl⟩, ⟨t, ht, he'⟩⟩
    have h1 : t = s := (harc e he).2 he'
    subst h1
    have : t = m := le_antisymm hs.2 ht.1
    rw [this]
    rfl
  have hunion : ∀ e ∈ E, H₀ e ∪ H₁ e = e := fun e he => by
    change a e '' Icc 0 m ∪ a e '' Icc m 1 = e
    rw [← image_union, Icc_union_Icc_eq_Icc hm0.le hm1.le]
    conv_rhs => rw [← hrange e he]
    ext x
    simp only [mem_range, mem_image, mem_Icc]
    exact ⟨fun ⟨t, _, ht⟩ => ⟨t, ht⟩, fun ⟨t, ht⟩ => ⟨t, ⟨t.2.1, t.2.2⟩, ht⟩⟩
  have hsU : ⋃₀ E₁ = ⋃₀ E := by
    ext x
    constructor
    · rintro ⟨_, ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩, h1⟩
      · exact ⟨e, he, hH₀s e he h1⟩
      · exact ⟨e, he, hH₁s e he h1⟩
    · rintro ⟨e, he, h1⟩
      rcases (hunion e he).symm ▸ h1 with h2 | h2
      · exact ⟨_, .inl ⟨e, he, rfl⟩, h2⟩
      · exact ⟨_, .inr ⟨e, he, rfl⟩, h2⟩
  have hV₁f : V₁.Finite := hg.fin.union (hg.fine.image _)
  have hline₀ : ∀ e ∈ E, a e 0 ≠ mid e ∧ IsLineWithEnds (H₀ e) (a e 0) (mid e) := fun e he => by
    have h2 := ((harc e he).sub (s := 0) (t := m) hm0.ne).isLineWithEnds
    rw [range_subArc _ hm0.le, subArc_zero, subArc_one] at h2
    exact ⟨fun h1 => hm0.ne ((harc e he).2 h1), h2⟩
  have hline₁ : ∀ e ∈ E, mid e ≠ a e 1 ∧ IsLineWithEnds (H₁ e) (mid e) (a e 1) := fun e he => by
    have h2 := ((harc e he).sub (s := m) (t := 1) hm1.ne).isLineWithEnds
    rw [range_subArc _ hm1.le, subArc_zero, subArc_one] at h2
    exact ⟨fun h1 => hm1.ne ((harc e he).2 h1), h2⟩
  have hdis : IsDissection V₁ E₁ 𝓕 := by
    refine ⟨⟨hV₁f, (hg.fine.image _).union (hg.fine.image _), ?_, ?_⟩, h.fin, h.disc, h.cover,
      ?_, ?_, h.disj, ?_⟩
    · rintro _ (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
      · exact ⟨_, _, (hline₀ e he).1, (hline₀ e he).2, hH₀V e he⟩
      · exact ⟨_, _, (hline₁ e he).1, (hline₁ e he).2, hH₁V e he⟩
    · have hin : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ x ∈ e, x ∈ f → x ∈ V₁ := fun e he f hf hne' x h1 h2 =>
        .inl (hg.disj e he f hf hne' ⟨h1, h2⟩)
      rintro _ (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) _ (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩) hne' x ⟨h1, h2⟩
      · by_cases hef : e = f
        · subst hef
          exact absurd rfl hne'
        · exact hin e he f hf hef x (hH₀s e he h1) (hH₀s f hf h2)
      · by_cases hef : e = f
        · subst hef
          rw [hH₀H₁ e he ⟨h1, h2⟩]
          exact .inr ⟨e, he, rfl⟩
        · exact hin e he f hf hef x (hH₀s e he h1) (hH₁s f hf h2)
      · by_cases hef : e = f
        · subst hef
          rw [hH₀H₁ e he ⟨h2, h1⟩]
          exact .inr ⟨e, he, rfl⟩
        · exact hin e he f hf hef x (hH₁s e he h1) (hH₀s f hf h2)
      · by_cases hef : e = f
        · subst hef
          exact absurd rfl hne'
        · exact hin e he f hf hef x (hH₁s e he h1) (hH₁s f hf h2)
    · rw [hsU]
      exact h.bd
    · rw [hsU]
      exact h.int
    · exact fun x hx => h.count x fun h' => hx (.inl h')
  have hne01 : ∀ e ∈ E, H₀ e ≠ H₁ e := fun e he h1 => h0notH₁ e he (h1 ▸ h0H₀ e)
  have hinj₀ : InjOn H₀ E := fun e he f hf h1 => by
    have h2 : mid e ∈ H₀ f := by
      rw [← (show H₀ e = H₀ f from h1)]
      exact hmH₀ e
    exact (hmidE e he f hf (hH₀s f hf h2)).symm
  have hinj₁ : InjOn H₁ E := fun e he f hf h1 => by
    have h2 : mid e ∈ H₁ f := by
      rw [← (show H₁ e = H₁ f from h1)]
      exact hmH₁ e
    exact (hmidE e he f hf (hH₁s f hf h2)).symm
  have hinjm : InjOn mid E := fun e he f hf h1 => (hmidE e he f hf (h1 ▸ hmid f hf)).symm
  have hdV : Disjoint V (mid '' E) := Set.disjoint_right.mpr fun _ ⟨e, he, h1⟩ h2 => hmidV e he
    (h1 ▸ h2)
  have hdE : Disjoint (H₀ '' E) (H₁ '' E) := Set.disjoint_left.mpr fun _ ⟨e, he, h1⟩ ⟨f, hf, h2⟩
    => by
    have h3 : mid f ∈ H₀ e := by
      rw [h1, ← h2]
      exact hmH₁ f
    have h4 := hmidE f hf e he (hH₀s e he h3)
    subst h4
    exact hne01 e he (h1.trans h2.symm)
  refine ⟨V₁, E₁, hdis, subset_union_left, ?_, hsU, ?_, ?_, ?_, fun e he => ⟨mid e, .inr ⟨e, he,
    rfl⟩, hmidV e he, hmid e he⟩⟩
  · rw [hsU]
    rintro x (h1 | ⟨e, he, rfl⟩)
    · exact hV h1
    · exact ⟨e, he, hmid e he⟩
  · have key : ∀ (e f : Set X), e ∈ E → f ∈ E → ∀ g g' : Set X, mid e ∈ g → (g = H₀ e ∨ g = H₁ e) →
    (g' ⊆ f) →
        g ∩ V₁ = g' ∩ V₁ → f = e := by
      intro e f he hf g g' h1 _ h3 h4
      have h5 : mid e ∈ g ∩ V₁ := ⟨h1, .inr ⟨e, he, rfl⟩⟩
      rw [h4] at h5
      exact hmidE e he f hf (h3 h5.1)
    have h01 : ∀ e ∈ E, H₀ e ∩ V₁ ≠ H₁ e ∩ V₁ := fun e he h1 => by
      have h2 : a e 0 ∈ H₀ e ∩ V₁ := by
        rw [hH₀V e he]
        exact .inl rfl
      rw [h1] at h2
      exact h0notH₁ e he h2.1
    rintro _ (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) _ (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩) h1
    · have := key e f he hf _ _ (hmH₀ e) (.inl rfl) (hH₀s f hf) h1
      subst this
      rfl
    · have := key e f he hf _ _ (hmH₀ e) (.inl rfl) (hH₁s f hf) h1
      subst this
      exact absurd h1 (h01 f hf)
    · have := key e f he hf _ _ (hmH₁ e) (.inr rfl) (hH₀s f hf) h1
      subst this
      exact absurd h1.symm (h01 f hf)
    · have := key e f he hf _ _ (hmH₁ e) (.inr rfl) (hH₁s f hf) h1
      subst this
      rfl
  · rw [ncard_union_eq hdV hg.fin (hg.fine.image _), hinjm.ncard_image]
  · rw [ncard_union_eq hdE (hg.fine.image _) (hg.fine.image _), hinj₀.ncard_image,
      hinj₁.ncard_image]
    omega

omit [T2Space X] in
/-- The boundary of a disc, or any other `O`-arc, has infinitely many points. -/
theorem isOArc_infinite {F : Set X} (hF : IsOArc F) : F.Infinite :=
  hF.infinite

/-- Each face of a dissection has an edge on its boundary, so two vertices. -/
theorem IsDissection.two_vertices {V : Set X} {E 𝓕 : Set (Set X)} (h : IsDissection V E 𝓕) {Φ : Set
  X} (hΦ : Φ ∈ 𝓕) :
    ∃ a b, a ∈ Φ ∩ V ∧ b ∈ Φ ∩ V ∧ a ≠ b := by
  have hO : IsOArc (discBd Φ) := (h.disc Φ hΦ).isOArc_discBd
  obtain ⟨y, hy, hyV⟩ := ((isOArc_infinite hO).sdiff h.graph.fin).nonempty
  obtain ⟨e, he, hye⟩ := h.bd Φ hΦ hy
  have hsub : discBd Φ ⊆ gr V E := (h.bd Φ hΦ).trans subset_union_right
  obtain ⟨u, v, huv, hl, hi⟩ := h.graph.edge e he
  rcases h.graph.edge_or hO hsub he with h1 | h1
  · have hu : u ∈ e ∩ V := hi ▸ .inl rfl
    have hv : v ∈ e ∩ V := hi ▸ .inr rfl
    exact ⟨u, v, ⟨discBd_subset Φ (h1 hu.1), hu.2⟩, ⟨discBd_subset Φ (h1 hv.1), hv.2⟩, huv⟩
  · exact absurd hy (Set.disjoint_left.mp h1 ⟨hye, hyV⟩)

omit [T2Space X] in
theorem IsClosedDisc.discInt_nonempty {Φ : Set X} (hΦ : IsClosedDisc Φ) : (discInt Φ).Nonempty := by
  obtain ⟨h', g', c'⟩ := hΦ.exists_isChart
  have hg0 : g' 0 ∈ Φ := c'.gm (by simp)
  have h3 := hΦ.subset_closure_discInt hg0
  by_contra hc'
  rw [not_nonempty_iff_eq_empty] at hc'
  rw [hc', closure_empty] at h3
  exact h3

omit [T2Space X] in
private theorem dissection_from_chord_fans
    {V : Set X} {E 𝓕 : Set (Set X)} (h : IsDissection V E 𝓕)
    (c : Set X → X) (𝓛 𝓒 : Set X → Set (Set X))
    (hfan : ∀ Φ ∈ 𝓕, IsChordFan Φ (insert (c Φ) (Φ ∩ V)) (𝓛 Φ) (𝓒 Φ)) :
    let V₂ : Set X := V ∪ c '' 𝓕
    let S₂ : Set (Set X) := ⋃ Φ ∈ 𝓕, 𝓛 Φ
    let E₂ : Set (Set X) := E ∪ S₂
    let 𝓕₂ : Set (Set X) := ⋃ Φ ∈ 𝓕, 𝓒 Φ
    IsGraph V₂ E₂ → IsDissection V₂ E₂ 𝓕₂ := by
  classical
  intro V₂ S₂ E₂ 𝓕₂ hgraph
  have hfin𝓕₂ : 𝓕₂.Finite := h.fin.biUnion fun Φ hΦ => (hfan Φ hΦ).finS
  have hmS : ∀ {L}, L ∈ S₂ → ∃ Φ ∈ 𝓕, L ∈ 𝓛 Φ := fun {L} hL => by simpa [S₂] using hL
  have hm𝓕 : ∀ {Ψ}, Ψ ∈ 𝓕₂ → ∃ Φ ∈ 𝓕, Ψ ∈ 𝓒 Φ := fun {Ψ} hΨ => by simpa [𝓕₂] using hΨ
  have hfS : ∀ Φ ∈ 𝓕, ∀ Ψ ∈ 𝓒 Φ, Ψ ⊆ Φ := fun Φ hΦ Ψ hΨ => (hfan Φ hΦ).sub Ψ hΨ
  have hfL : ∀ Φ ∈ 𝓕, ∀ L ∈ 𝓛 Φ, L ⊆ Φ := fun Φ hΦ L hL => (hfan Φ hΦ).subL L hL
  have hintΨ : ∀ Φ ∈ 𝓕, ∀ Ψ ∈ 𝓒 Φ, discInt Ψ ⊆ discInt Φ := fun Φ hΦ Ψ hΨ y hy =>
    ⟨hfS Φ hΦ Ψ hΨ hy.1, fun h' => Set.disjoint_left.mp ((hfan Φ hΦ).int Ψ hΨ) hy (.inl h')⟩
  refine ⟨hgraph, hfin𝓕₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ψ hΨ
    obtain ⟨Φ, hΦ, hΨ⟩ := hm𝓕 hΨ
    exact (hfan Φ hΦ).disc Ψ hΨ
  · rw [eq_univ_iff_forall]
    intro y
    obtain ⟨Φ, hΦ, hy⟩ := (eq_univ_iff_forall.mp h.cover) y
    rw [← (hfan Φ hΦ).cover] at hy
    obtain ⟨Ψ, hΨ, hy⟩ := hy
    exact ⟨Ψ, by simpa [𝓕₂] using ⟨Φ, hΦ, hΨ⟩, hy⟩
  · intro Ψ hΨ y hy
    obtain ⟨Φ, hΦ, hΨ⟩ := hm𝓕 hΨ
    rcases (hfan Φ hΦ).bd Ψ hΨ hy with h1 | ⟨L, hL, h1⟩
    · obtain ⟨e, he, h2⟩ := h.bd Φ hΦ h1
      exact ⟨e, .inl he, h2⟩
    · exact ⟨L, .inr (by simpa [S₂] using ⟨Φ, hΦ, hL⟩), h1⟩
  · intro Ψ hΨ
    obtain ⟨Φ, hΦ, hΨ⟩ := hm𝓕 hΨ
    refine Set.disjoint_left.mpr ?_
    rintro y hy ⟨e, he | he, h1⟩
    · exact Set.disjoint_left.mp (h.int Φ hΦ) (hintΨ Φ hΦ Ψ hΨ hy) ⟨e, he, h1⟩
    · obtain ⟨Φ', hΦ', hL⟩ := hmS he
      by_cases hq : Φ = Φ'
      · subst hq
        exact Set.disjoint_left.mp ((hfan Φ hΦ).int Ψ hΨ) hy (.inr ⟨e, hL, h1⟩)
      · exact Set.disjoint_left.mp (h.disj Φ hΦ Φ' hΦ' hq) (hintΨ Φ hΦ Ψ hΨ hy) (hfL Φ' hΦ' e hL h1)
  · intro Ψ hΨ Ψ' hΨ' hne
    obtain ⟨Φ, hΦ, hΨ⟩ := hm𝓕 hΨ
    obtain ⟨Φ', hΦ', hΨ'⟩ := hm𝓕 hΨ'
    by_cases hq : Φ = Φ'
    · subst hq
      exact (hfan Φ hΦ).disj Ψ hΨ Ψ' hΨ' hne
    · exact Set.disjoint_left.mpr fun y hy hy' =>
        Set.disjoint_left.mp (h.disj Φ hΦ Φ' hΦ' hq) (hintΨ Φ hΦ Ψ hΨ hy) (hfS Φ' hΦ' Ψ' hΨ' hy')
  · intro y hy
    have hyV : y ∉ V := fun h1 => hy (.inl h1)
    have hyQ : ∀ Φ ∈ 𝓕, y ∉ insert (c Φ) (Φ ∩ V) := fun Φ hΦ h1 => by
      rcases h1 with h1 | h1
      · exact hy (.inr ⟨Φ, hΦ, h1.symm⟩)
      · exact hyV h1.2
    by_cases hint : ∃ Φ ∈ 𝓕, y ∈ discInt Φ
    · obtain ⟨Φ, hΦ, hyi⟩ := hint
      have hsub : {Ψ ∈ 𝓕₂ | y ∈ Ψ} ⊆ {Ψ ∈ 𝓒 Φ | y ∈ Ψ} := by
        rintro Ψ ⟨hΨ, h1⟩
        obtain ⟨Φ', hΦ', hΨ⟩ := hm𝓕 hΨ
        by_cases hq : Φ = Φ'
        · subst hq
          exact ⟨hΨ, h1⟩
        · exact absurd (hfS Φ' hΦ' Ψ hΨ h1) (Set.disjoint_left.mp (h.disj Φ hΦ Φ' hΦ' hq) hyi)
      exact (encard_le_encard hsub).trans ((hfan Φ hΦ).count₂ y (hyQ Φ hΦ))
    · push Not at hint
      have hle : ∀ Φ ∈ {Φ ∈ 𝓕 | y ∈ Φ}, ({Ψ ∈ 𝓒 Φ | y ∈ Ψ}).encard ≤ 1 := by
        rintro Φ ⟨hΦ, h1⟩
        have hb : y ∈ discBd Φ := by
          by_contra hn
          exact hint Φ hΦ ⟨h1, hn⟩
        exact (hfan Φ hΦ).count₁ y hb (hyQ Φ hΦ)
      have hown : ∀ Ψ, Ψ ∈ 𝓕₂ → ∃ Φ ∈ 𝓕, Ψ ∈ 𝓒 Φ := fun Ψ hΨ => hm𝓕 hΨ
      choose! own hown₁ hown₂ using hown
      have hle2 : ({Ψ ∈ 𝓕₂ | y ∈ Ψ}).encard ≤ ({Φ ∈ 𝓕 | y ∈ Φ}).encard := by
        refine encard_le_encard_of_injOn (f := own) ?_ ?_
        · rintro Ψ ⟨hΨ, h1⟩
          exact ⟨hown₁ Ψ hΨ, hfS _ (hown₁ Ψ hΨ) Ψ (hown₂ Ψ hΨ) h1⟩
        · rintro Ψ ⟨hΨ, h1⟩ Ψ' ⟨hΨ', h2⟩ h3
          have hm : own Ψ ∈ {Φ ∈ 𝓕 | y ∈ Φ} := ⟨hown₁ Ψ hΨ, hfS _ (hown₁ Ψ hΨ) Ψ (hown₂ Ψ hΨ) h1⟩
          refine encard_le_one_iff.mp (hle _ hm) Ψ Ψ' ⟨hown₂ Ψ hΨ, h1⟩ ⟨?_, h2⟩
          rw [h3]
          exact hown₂ Ψ' hΨ'
      exact hle2.trans (h.count y hyV)

/-- Putting a cone on each face of a simple dissection gives a triangulation with the same value of
`|V| - |E| + |F|`. -/
theorem IsDissection.exists_coned [Nonempty X] {V : Set X} {E 𝓕 : Set (Set X)}
  (h : IsDissection V E 𝓕) (hV : V ⊆ ⋃₀ E)
    (hs : ∀ e ∈ E, ∀ f ∈ E, e ∩ V = f ∩ V → e = f) :
    ∃ (V₂ : Set X) (E₂ 𝓕₂ : Set (Set X)), IsTriang V₂ E₂ 𝓕₂ ∧ V ⊆ V₂ ∧ E ⊆ E₂ ∧
      (V₂.ncard : ℤ) - E₂.ncard + 𝓕₂.ncard = (V.ncard : ℤ) - E.ncard + 𝓕.ncard := by
  classical
  have hg := h.graph
  have hVb : ∀ Φ ∈ 𝓕, Φ ∩ V ⊆ discBd Φ := fun Φ hΦ y hy => by
    by_contra hn
    exact Set.disjoint_left.mp (h.int Φ hΦ) ⟨hy.1, hn⟩ (hV hy.2)
  have hch : ∀ Φ ∈ 𝓕, ∃ (c : X) (𝓛 𝓒 : Set (Set X)), c ∈ discInt Φ ∧ IsChordFan Φ (insert c
    (Φ ∩ V)) 𝓛 𝓒 ∧
      𝓛.ncard = (Φ ∩ V).ncard ∧ 𝓒.ncard = (Φ ∩ V).ncard ∧
      (∀ L ∈ 𝓛, ∃ p ∈ Φ ∩ V, IsLineWithEnds L c p ∧ L ∩ discBd Φ = {p}) ∧
      ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → L ∩ L' = {c} := fun Φ hΦ => by
    obtain ⟨a, b, ha, hb, hab⟩ := h.two_vertices hΦ
    exact exists_cone (h.disc Φ hΦ) (hg.fin.subset inter_subset_right) (hVb Φ hΦ) ha hb hab
  choose! c 𝓛 𝓒 hc hfan hnL hnS hsp hpr using hch
  have hIntOff : ∀ Φ ∈ 𝓕, ∀ Φ' ∈ 𝓕, Φ ≠ Φ' → ∀ y ∈ Φ, y ∈ Φ' → y ∈ discBd Φ
    := fun Φ hΦ Φ' hΦ' hne y h1 h2 => by
    by_contra hn
    exact Set.disjoint_left.mp (h.disj Φ hΦ Φ' hΦ' hne) ⟨h1, hn⟩ h2
  have hcIn : ∀ Φ ∈ 𝓕, ∀ Φ' ∈ 𝓕, c Φ ∈ Φ' → Φ' = Φ := fun Φ hΦ Φ' hΦ' h1 => by
    by_contra hne
    exact Set.disjoint_left.mp (h.disj Φ hΦ Φ' hΦ' (Ne.symm hne)) (hc Φ hΦ) h1
  have hcE : ∀ Φ ∈ 𝓕, c Φ ∉ ⋃₀ E := fun Φ hΦ h1 => Set.disjoint_left.mp (h.int Φ hΦ) (hc Φ hΦ) h1
  have hcΦ : ∀ Φ ∈ 𝓕, c Φ ∈ Φ := fun Φ hΦ => (hc Φ hΦ).1
  have hbdn : ∀ Φ ∈ 𝓕, c Φ ∉ discBd Φ := fun Φ hΦ => (hc Φ hΦ).2
  have hcV : ∀ Φ ∈ 𝓕, c Φ ∉ V := fun Φ hΦ h1 => hcE Φ hΦ (hV h1)
  have hfS : ∀ Φ ∈ 𝓕, ∀ Ψ ∈ 𝓒 Φ, Ψ ⊆ Φ := fun Φ hΦ Ψ hΨ => (hfan Φ hΦ).sub Ψ hΨ
  have hfL : ∀ Φ ∈ 𝓕, ∀ L ∈ 𝓛 Φ, L ⊆ Φ := fun Φ hΦ L hL => (hfan Φ hΦ).subL L hL
  have hintΨ : ∀ Φ ∈ 𝓕, ∀ Ψ ∈ 𝓒 Φ, discInt Ψ ⊆ discInt Φ := fun Φ hΦ Ψ hΨ y hy =>
    ⟨hfS Φ hΦ Ψ hΨ hy.1, fun h' => Set.disjoint_left.mp ((hfan Φ hΦ).int Ψ hΨ) hy (.inl h')⟩
  have hLV : ∀ Φ ∈ 𝓕, ∀ L ∈ 𝓛 Φ, ∀ y ∈ L, y ∈ discBd Φ → y ∈ V := fun Φ hΦ L hL y h1 h2 => by
    obtain ⟨p, hp, -, h3⟩ := hsp Φ hΦ L hL
    have h4 : y ∈ L ∩ discBd Φ := ⟨h1, h2⟩
    rw [h3] at h4
    exact h4 ▸ hp.2
  have hEbd : ∀ Φ ∈ 𝓕, ∀ y ∈ Φ, y ∈ ⋃₀ E → y ∈ discBd Φ := fun Φ hΦ y h1 h2 => by
    by_contra hn
    exact Set.disjoint_left.mp (h.int Φ hΦ) ⟨h1, hn⟩ h2
  have hEnd : ∀ Φ ∈ 𝓕, ∀ L ∈ 𝓛 Φ, ∃ p ∈ Φ ∩ V, p ≠ c Φ ∧ L ∩ (V ∪ c '' 𝓕) = {c Φ, p}
    ∧ IsLineWithEnds L (c Φ) p := by
    intro Φ hΦ L hL
    obtain ⟨p, hp, hl, h3⟩ := hsp Φ hΦ L hL
    refine ⟨p, hp, fun h4 => hcV Φ hΦ (h4 ▸ hp.2), ?_, hl⟩
    ext y
    constructor
    · rintro ⟨h4, h5 | ⟨Φ', hΦ', rfl⟩⟩
      · have h6 : c Φ ∈ L ∧ y ∈ discBd Φ := ⟨hl.left_mem, hVb Φ hΦ ⟨hfL Φ hΦ L hL h4, h5⟩⟩
        have h7 : y ∈ L ∩ discBd Φ := ⟨h4, h6.2⟩
        rw [h3] at h7
        exact .inr h7
      · have := hcIn Φ' hΦ' Φ hΦ (hfL Φ hΦ L hL h4)
        subst this
        exact .inl rfl
    · rintro (rfl | rfl)
      · exact ⟨hl.left_mem, .inr ⟨Φ, hΦ, rfl⟩⟩
      · exact ⟨hl.right_mem, .inl hp.2⟩
  let V₂ : Set X := V ∪ c '' 𝓕
  let S₂ : Set (Set X) := ⋃ Φ ∈ 𝓕, 𝓛 Φ
  let E₂ : Set (Set X) := E ∪ S₂
  let 𝓕₂ : Set (Set X) := ⋃ Φ ∈ 𝓕, 𝓒 Φ
  have hdS₂ : ∀ Φ ∈ 𝓕, ∀ Φ' ∈ 𝓕, Φ ≠ Φ' → Disjoint (𝓛 Φ) (𝓛 Φ') := fun Φ hΦ Φ' hΦ' hne =>
    Set.disjoint_left.mpr fun L h1 h2 => by
      obtain ⟨p, -, hl, -⟩ := hsp Φ hΦ L h1
      exact hne (hcIn Φ hΦ Φ' hΦ' (hfL Φ' hΦ' L h2 hl.left_mem)).symm
  have hd𝓒 : ∀ Φ ∈ 𝓕, ∀ Φ' ∈ 𝓕, Φ ≠ Φ' → Disjoint (𝓒 Φ) (𝓒 Φ') := fun Φ hΦ Φ' hΦ' hne =>
    Set.disjoint_left.mpr fun Ψ h1 h2 => by
      obtain ⟨y, hy⟩ := ((hfan Φ hΦ).disc Ψ h1).discInt_nonempty
      exact Set.disjoint_left.mp (h.disj Φ hΦ Φ' hΦ' hne) (hintΨ Φ hΦ Ψ h1 hy)
        (hfS Φ' hΦ' Ψ h2 hy.1)
  have hdES : Disjoint E S₂ := Set.disjoint_left.mpr fun e he hS => by
    obtain ⟨Φ, hΦ, hL⟩ : ∃ Φ ∈ 𝓕, e ∈ 𝓛 Φ := by simpa [S₂] using hS
    obtain ⟨p, -, hl, -⟩ := hsp Φ hΦ e hL
    exact hcE Φ hΦ ⟨e, he, hl.left_mem⟩
  have hfinS : S₂.Finite := h.fin.biUnion fun Φ hΦ => (hfan Φ hΦ).finL
  have hcinj : InjOn c 𝓕 := fun Φ hΦ Φ' hΦ' h1 => (hcIn Φ hΦ Φ' hΦ' (h1 ▸ hcΦ Φ' hΦ')).symm
  have hdVc : Disjoint V (c '' 𝓕) := Set.disjoint_right.mpr fun _ ⟨Φ, hΦ, h1⟩ h2 => hcV Φ hΦ
    (h1 ▸ h2)
  have hmS : ∀ {L}, L ∈ S₂ → ∃ Φ ∈ 𝓕, L ∈ 𝓛 Φ := fun {L} hL => by simpa [S₂] using hL
  have hm𝓕 : ∀ {Ψ}, Ψ ∈ 𝓕₂ → ∃ Φ ∈ 𝓕, Ψ ∈ 𝓒 Φ := fun {Ψ} hΨ => by simpa [𝓕₂] using hΨ
  have hEV₂ : ∀ e ∈ E, e ∩ V₂ = e ∩ V := fun e he => by
    ext y
    constructor
    · rintro ⟨h1, h2 | ⟨Φ, hΦ, rfl⟩⟩
      · exact ⟨h1, h2⟩
      · exact absurd ⟨e, he, h1⟩ (hcE Φ hΦ)
    · exact fun h1 => ⟨h1.1, .inl h1.2⟩
  have hgraph : IsGraph V₂ E₂ := by
    refine ⟨hg.fin.union (h.fin.image _), hg.fine.union hfinS, ?_, ?_⟩
    · rintro e (he | he)
      · obtain ⟨u, v, huv, hl, hi⟩ := hg.edge e he
        exact ⟨u, v, huv, hl, (hEV₂ e he).trans hi⟩
      · obtain ⟨Φ, hΦ, hL⟩ := hmS he
        obtain ⟨p, -, hne, hi, hl⟩ := hEnd Φ hΦ e hL
        exact ⟨c Φ, p, hne.symm, hl, hi⟩
    · have hmix : ∀ e ∈ E, ∀ L ∈ S₂, ∀ y ∈ e, y ∈ L → y ∈ V₂ := fun e he L hL y h1 h2 => by
        obtain ⟨Φ, hΦ, hL⟩ := hmS hL
        exact .inl (hLV Φ hΦ L hL y h2 (hEbd Φ hΦ y (hfL Φ hΦ L hL h2) ⟨e, he, h1⟩))
      rintro e (he | he) f (hf | hf) hne y ⟨h1, h2⟩
      · exact .inl (hg.disj e he f hf hne ⟨h1, h2⟩)
      · exact hmix e he f hf y h1 h2
      · exact hmix f hf e he y h2 h1
      · obtain ⟨Φ, hΦ, hL⟩ := hmS he
        obtain ⟨Φ', hΦ', hL'⟩ := hmS hf
        by_cases hq : Φ = Φ'
        · subst hq
          have h3 : y ∈ e ∩ f := ⟨h1, h2⟩
          rw [hpr Φ hΦ e hL f hL' hne] at h3
          exact .inr ⟨Φ, hΦ, h3.symm⟩
        · exact .inl (hLV Φ hΦ e hL y h1 (hIntOff Φ hΦ Φ' hΦ' hq y (hfL Φ hΦ e hL h1)
          (hfL Φ' hΦ' f hL' h2)))
  have hsimple : ∀ e ∈ E₂, ∀ f ∈ E₂, e ∩ V₂ = f ∩ V₂ → e = f := by
    have hcross : ∀ e ∈ E, ∀ L ∈ S₂, e ∩ V₂ ≠ L ∩ V₂ := fun e he L hL h1 => by
      obtain ⟨Φ, hΦ, hL⟩ := hmS hL
      obtain ⟨p, -, hl, -⟩ := hsp Φ hΦ L hL
      have h2 : c Φ ∈ L ∩ V₂ := ⟨hl.left_mem, .inr ⟨Φ, hΦ, rfl⟩⟩
      rw [← h1] at h2
      exact hcE Φ hΦ ⟨e, he, h2.1⟩
    rintro e (he | he) f (hf | hf) h1
    · rw [hEV₂ e he, hEV₂ f hf] at h1
      exact hs e he f hf h1
    · exact absurd h1 (hcross e he f hf)
    · exact absurd h1.symm (hcross f hf e he)
    · obtain ⟨Φ, hΦ, hL⟩ := hmS he
      obtain ⟨Φ', hΦ', hL'⟩ := hmS hf
      obtain ⟨p, hp, -, -, hl⟩ := hEnd Φ hΦ e hL
      obtain ⟨p', hp', -, -, hl'⟩ := hEnd Φ' hΦ' f hL'
      have h2 : c Φ ∈ f ∩ V₂ := h1 ▸ ⟨hl.left_mem, .inr ⟨Φ, hΦ, rfl⟩⟩
      have := (hcIn Φ hΦ Φ' hΦ' (hfL Φ' hΦ' f hL' h2.1)).symm
      subst this
      by_contra hne
      have h3 : p ∈ f ∩ V₂ := h1 ▸ ⟨hl.right_mem, .inl hp.2⟩
      have h4 : p ∈ e ∩ f := ⟨hl.right_mem, h3.1⟩
      rw [hpr Φ hΦ e hL f hL' hne] at h4
      exact hbdn Φ hΦ (h4 ▸ hVb Φ hΦ hp)
  have hdis : IsDissection V₂ E₂ 𝓕₂ := dissection_from_chord_fans h c 𝓛 𝓒 hfan hgraph
  have htri : IsTriang V₂ E₂ 𝓕₂ := by
    refine ⟨hdis, ?_, ?_, hsimple⟩
    · rintro y (hy | ⟨Φ, hΦ, rfl⟩)
      · obtain ⟨e, he, h1⟩ := hV hy
        exact ⟨e, .inl he, h1⟩
      · obtain ⟨a, b, ha, -, -⟩ := h.two_vertices hΦ
        have hn : (Φ ∩ V).Nonempty := ⟨a, ha⟩
        have hL : (𝓛 Φ).Nonempty := by
          rw [← ncard_pos ((hfan Φ hΦ).finL), hnL Φ hΦ]
          exact (ncard_pos (hg.fin.subset inter_subset_right)).mpr hn
        obtain ⟨L, hL⟩ := hL
        obtain ⟨p, -, hl, -⟩ := hsp Φ hΦ L hL
        exact ⟨L, .inr (by simpa [S₂] using ⟨Φ, hΦ, hL⟩), hl.left_mem⟩
    intro Ψ hΨ
    obtain ⟨Φ, hΦ, hΨ⟩ := hm𝓕 hΨ
    have h1 : Ψ ∩ V₂ = Ψ ∩ insert (c Φ) (Φ ∩ V) := by
      ext y
      constructor
      · rintro ⟨h2, h3 | ⟨Φ', hΦ', rfl⟩⟩
        · exact ⟨h2, .inr ⟨hfS Φ hΦ Ψ hΨ h2, h3⟩⟩
        · have := hcIn Φ' hΦ' Φ hΦ (hfS Φ hΦ Ψ hΨ h2)
          subst this
          exact ⟨h2, .inl rfl⟩
      · rintro ⟨h2, h3 | h3⟩
        · exact ⟨h2, .inr ⟨Φ, hΦ, h3.symm⟩⟩
        · exact ⟨h2, .inl h3.2⟩
    rw [h1]
    exact (hfan Φ hΦ).three Ψ hΨ
  refine ⟨V₂, E₂, 𝓕₂, htri, subset_union_left, subset_union_left, ?_⟩
  have hS : S₂ = ⋃ Φ ∈ h.fin.toFinset, 𝓛 Φ := by simp [S₂]
  have hF : 𝓕₂ = ⋃ Φ ∈ h.fin.toFinset, 𝓒 Φ := by simp [𝓕₂]
  have c1 : S₂.ncard = ∑ Φ ∈ h.fin.toFinset, (Φ ∩ V).ncard := by
    rw [hS, ncard_biUnion_eq _ _ (fun Φ hΦ => (hfan Φ (by simpa using hΦ)).finL)
      (fun Φ hΦ Φ' hΦ' => hdS₂ Φ (by simpa using hΦ) Φ' (by simpa using hΦ'))]
    exact Finset.sum_congr rfl fun Φ hΦ => hnL Φ (by simpa using hΦ)
  have c2 : 𝓕₂.ncard = ∑ Φ ∈ h.fin.toFinset, (Φ ∩ V).ncard := by
    rw [hF, ncard_biUnion_eq _ _ (fun Φ hΦ => (hfan Φ (by simpa using hΦ)).finS)
      (fun Φ hΦ Φ' hΦ' => hd𝓒 Φ (by simpa using hΦ) Φ' (by simpa using hΦ'))]
    exact Finset.sum_congr rfl fun Φ hΦ => hnS Φ (by simpa using hΦ)
  have c3 : V₂.ncard = V.ncard + 𝓕.ncard := by
    rw [ncard_union_eq hdVc hg.fin (h.fin.image _), hcinj.ncard_image]
  have c4 : E₂.ncard = E.ncard + S₂.ncard := ncard_union_eq hdES hg.fine hfinS
  rw [c3, c4, c1, c2]
  push_cast
  ring

/-- **Triangulations.** Every dissection of a nonempty space can be refined to a triangulation, with
the same value of `|V| - |E| + |F|` and with each edge a union of edges of the triangulation. -/
theorem IsDissection.exists_triang [Nonempty X] {V : Set X} {E 𝓕 : Set (Set X)}
  (h : IsDissection V E 𝓕) :
    ∃ (V₂ : Set X) (E₂ 𝓕₂ : Set (Set X)), IsTriang V₂ E₂ 𝓕₂ ∧ V ∩ ⋃₀ E ⊆ V₂ ∧ ⋃₀ E ⊆ ⋃₀ E₂ ∧
      (V₂.ncard : ℤ) - E₂.ncard + 𝓕₂.ncard = ((V ∩ ⋃₀ E).ncard : ℤ) - E.ncard + 𝓕.ncard := by
  have ht := h.trim
  obtain ⟨V₁, E₁, hd, hV, hV₁, hU, hs, hcV, hcE, -⟩ := ht.exists_halves inter_subset_right
  obtain ⟨V₂, E₂, 𝓕₂, htri, h1, h2, h3⟩ := hd.exists_coned hV₁ hs
  refine ⟨V₂, E₂, 𝓕₂, htri, hV.trans h1, ?_, ?_⟩
  · rw [← hU]
    exact sUnion_mono h2
  · rw [h3, hcV, hcE]
    push_cast
    ring

end GraphMinor.Surface

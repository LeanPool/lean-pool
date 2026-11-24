/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section7a

/-!
# Graph Minors XX, Section 7, (7.2) and (7.3)

A rooted location `ℒ` in `G/W` lifts to a rooted location `ℒ'` in `G`, by putting `W` into each
member
as roots. For free `P`, (7.1) shows that a heart of `(P, ℒ')`, slashed by `W`, is a heart of
`(P/W, ℒ)`, and so (4.9) applies. Together with (6.3) this gives (7.3).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

section Lift

variable (G : RootedHypergraph α β) {l : List α} (hl : l.Nodup)

/-- `A` with the terms of `l` added as roots, with the incidences of `G`. -/
noncomputable def liftRooted (A : RootedHypergraph α β) : RootedHypergraph α β where
  vertexSet := A.vertexSet ∪ {v | v ∈ l}
  edgeSet := A.edgeSet
  Inc e v := e ∈ A.edgeSet ∧ G.Inc e v ∧ v ∈ A.vertexSet ∪ {v | v ∈ l}
  vertex_mem_of_inc _ _ h := h.2.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := A.vertexSet_finite.union (List.finite_toSet _)
  edgeSet_finite := A.edgeSet_finite
  roots := A.roots ++ marchSlash l A.vertexSet
  roots_nodup := by
    refine List.Nodup.append A.roots_nodup (nodup_marchSlash hl _) fun x hx hx' ↦ ?_
    exact (mem_marchSlash.mp hx').2 (A.roots_subset x hx)
  roots_subset x hx := by
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl (A.roots_subset x h)
    · exact Or.inr (mem_marchSlash.mp h).1

variable {G hl} {A : RootedHypergraph α β}

theorem mem_liftRooted_rootSet {v : α} (hA : Disjoint A.vertexSet {v | v ∈ l}) :
    v ∈ (liftRooted G hl A).rootSet ↔ v ∈ A.rootSet ∨ v ∈ l := by
  change v ∈ A.roots ++ marchSlash l A.vertexSet ↔ _
  rw [List.mem_append, mem_marchSlash]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.1
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h, Set.disjoint_right.mp hA h⟩

variable {W : Set α}

theorem disjoint_of_le_slash (hA : A.toHypergraph ≤ quotientVertices G.toHypergraph W)
    (hset : ∀ v, v ∈ l ↔ v ∈ W) : Disjoint A.vertexSet {v | v ∈ l} :=
  Set.disjoint_left.mpr fun _ hv hl ↦ (hA.vertexSet_subset hv).2 ((hset _).mp hl)

theorem marchSlash_lift_eq (hA : A.toHypergraph ≤ quotientVertices G.toHypergraph W)
    (hset : ∀ v, v ∈ l ↔ v ∈ W) : marchSlash l A.vertexSet = l :=
  marchSlash_of_disjoint fun _ hx hv ↦ (hA.vertexSet_subset hv).2 ((hset _).mp hx)

theorem liftRooted_vertexSet : (liftRooted G hl A).vertexSet = A.vertexSet ∪ {v | v ∈ l} := rfl

theorem liftRooted_edgeSet : (liftRooted G hl A).edgeSet = A.edgeSet := rfl

theorem inc_mem_of_le (hA : A.toHypergraph ≤ quotientVertices G.toHypergraph W) {e : β} {v : α}
  (he : e ∈ A.edgeSet) (hinc : G.Inc e v) :
    A.Inc e v ∨ v ∈ W := by
  by_cases hv : v ∈ W
  · exact Or.inr hv
  · have h₁ : v ∈ (quotientVertices G.toHypergraph W).ends e := ⟨hinc, hv⟩
    rw [hA.ends_eq e he] at h₁
    exact Or.inl h₁

theorem liftRooted_le (hA : A.toHypergraph ≤ quotientVertices G.toHypergraph W)
    (hset : ∀ v, v ∈ l ↔ v ∈ W) (hWV : W ⊆ G.vertexSet) :
    (liftRooted G hl A).toHypergraph ≤ G.toHypergraph := by
  refine ⟨?_, hA.edgeSet_subset, fun e he ↦ ?_⟩
  · rintro v (hv | hv)
    · exact (hA.vertexSet_subset hv).1
    · exact hWV ((hset v).mp hv)
  · ext v
    refine ⟨fun h ↦ ⟨he, h, ?_⟩, fun h ↦ h.2.1⟩
    rcases inc_mem_of_le hA he h with h₁ | h₁
    · exact Or.inl (A.vertex_mem_of_inc h₁)
    · exact Or.inr ((hset v).mpr h₁)

theorem slash_liftRooted (hA : A.toHypergraph ≤ quotientVertices G.toHypergraph W)
    (hset : ∀ v, v ∈ l ↔ v ∈ W) : (liftRooted G hl A).slash W = A := by
  refine RootedHypergraph.ext_of ?_ rfl ?_ ?_
  · ext v
    refine ⟨?_, fun h ↦ ⟨Or.inl h, (hA.vertexSet_subset h).2⟩⟩
    rintro ⟨h₁ | h₁, h₂⟩
    · exact h₁
    · exact absurd ((hset v).mp h₁) h₂
  · ext e v
    constructor
    · rintro ⟨⟨he, hinc, -⟩, hv⟩
      exact (inc_mem_of_le hA he hinc).resolve_right hv
    · intro h
      have hv := A.vertex_mem_of_inc h
      have he := A.edge_mem_of_inc h
      have h₁ : v ∈ (quotientVertices G.toHypergraph W).ends e := by
        rw [hA.ends_eq e he]
        exact h
      exact ⟨⟨he, h₁.1, Or.inl hv⟩, h₁.2⟩
  · change marchSlash (A.roots ++ marchSlash l A.vertexSet) W = A.roots
    rw [marchSlash_lift_eq hA hset]
    have hn : ∀ x ∈ A.roots, x ∉ W := fun x hx ↦ (hA.vertexSet_subset (A.roots_subset x hx)).2
    classical
    simp only [marchSlash, List.filter_append]
    rw [List.filter_eq_self.mpr (by simpa using hn), List.filter_eq_nil_iff.mpr (by
      intro x hx
      simpa using (hset x).mp hx), List.append_nil]

theorem mem_liftRooted_rootSet' (hA : A.toHypergraph ≤ quotientVertices G.toHypergraph W)
    (hset : ∀ v, v ∈ l ↔ v ∈ W) {v : α} :
    v ∈ (liftRooted G hl A).rootSet ↔ v ∈ A.rootSet ∨ v ∈ W := by
  rw [mem_liftRooted_rootSet (disjoint_of_le_slash hA hset), hset]

theorem isComplemented_liftRooted (hA : IsComplemented (G.slash W) A)
    (hset : ∀ v, v ∈ l ↔ v ∈ W) (hWV : W ⊆ G.vertexSet) :
    IsComplemented G (liftRooted G hl A) := by
  have hle := hA.le
  refine ⟨liftRooted_le hle hset hWV, fun v hv hr ↦ ?_, fun v e hv he hinc ↦ ?_⟩
  all_goals
    rw [mem_liftRooted_rootSet' hle hset]
    by_cases hvW : v ∈ W
    · exact Or.inr hvW
    refine Or.inl ?_
    have hvA : v ∈ A.vertexSet := hv.resolve_right fun h ↦ hvW ((hset v).mp h)
  · exact hA.roots_mem hvA (mem_slash_rootSet.mpr ⟨hr, hvW⟩)
  · exact hA.inc_diff_mem hvA he ⟨hinc, hvW⟩

theorem isRootedLocation_lift {ℒ : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation (G.slash W) ℒ) (hset : ∀ v, v ∈ l ↔ v ∈ W) (hWV : W ⊆ G.vertexSet) :
    IsRootedLocation G (liftRooted G hl '' ℒ) := by
  have hc : ∀ ⦃B⦄, B ∈ liftRooted G hl '' ℒ → IsComplemented G B := by
    rintro _ ⟨A, hA, rfl⟩
    exact isComplemented_liftRooted (hℒ.isComplemented hA) hset hWV
  refine ⟨hc, ?_⟩
  rintro _ ⟨A₁, hA₁, rfl⟩ _ h₂ hne
  obtain ⟨A₂, hA₂, rfl⟩ := id h₂
  have hne' : A₁ ≠ A₂ := fun h ↦ hne (by rw [h])
  have hle := hℒ.le_complement hA₁ hA₂ hne'
  have hle₁ := (hℒ.isComplemented hA₁).le
  have hle₂ := (hℒ.isComplemented hA₂).le
  have hV : (liftRooted G hl A₁).vertexSet ⊆
      (complement G _ (hc h₂)).vertexSet := by
    rintro v (hv | hv)
    · have hvG := (hle₁.vertexSet_subset hv).1
      rcases hle.vertexSet_subset hv with h | h
      · refine Or.inl ⟨hvG, ?_⟩
        rintro (h₃ | h₃)
        · exact h.2 h₃
        · exact (hle₁.vertexSet_subset hv).2 ((hset v).mp h₃)
      · exact Or.inr ((mem_liftRooted_rootSet' hle₂ hset).mpr (Or.inl h))
    · exact Or.inr ((mem_liftRooted_rootSet' hle₂ hset).mpr (Or.inr ((hset v).mp hv)))
  have hE : (liftRooted G hl A₁).edgeSet ⊆ (complement G _ (hc h₂)).edgeSet := fun e he ↦ by
    have h₃ := hle.edgeSet_subset he
    exact ⟨h₃.1, h₃.2⟩
  exact (le_iff_of_le (hc ⟨A₁, hA₁, rfl⟩).le (by
    rw [complement_toHypergraph]
    exact complementHypergraph_le (hc h₂))).mpr ⟨hV, hE⟩

end Lift

variable {W : Set α} {P : UnlabeledPatchwork α β} {l : List α} {hl : l.Nodup}
  {A : RootedHypergraph α β}

/-- `(P|A')/W` has the same base as `(P/W)|A`, where `A'` is `A` lifted. -/
theorem sameBase_slash_restrict (hA : A.toHypergraph ≤ quotientVertices P.G.toHypergraph W)
    (hset : ∀ v, v ∈ l ↔ v ∈ W) (hWV : W ⊆ P.G.vertexSet) :
    SameBase ((P.restrict (liftRooted P.G hl A)).slash W) ((P.slash W).restrict A) := by
  have hle := liftRooted_le (hl := hl) hA hset hWV
  have hends : ∀ e ∈ A.edgeSet, (liftRooted P.G hl A).ends e = P.G.ends e := fun e he ↦
    (hle.ends_eq e he).symm
  have hends' : ∀ e ∈ A.edgeSet, A.ends e = (quotientVertices P.G.toHypergraph W).ends e :=
    fun e he ↦ (hA.ends_eq e he).symm
  have hslash := slash_liftRooted (hl := hl) hA hset
  refine ⟨?_, ?_, fun _ _ ↦ rfl, fun e he ↦ ?_⟩
  · exact (congrArg RootedHypergraph.toHypergraph hslash).symm
  · ext e
    constructor
    · rintro ⟨⟨h₁, h₂⟩, -⟩
      exact ⟨⟨h₁, h₂⟩, hends e h₂⟩
    · rintro ⟨⟨h₁, h₂⟩, -⟩
      exact ⟨⟨h₁, h₂⟩, hends' e h₂⟩
  · classical
    have he' : e ∈ A.edgeSet := he
    have h₁ : e ∈ P.G.edgeSet := hle.edgeSet_subset he'
    change (if e ∈ (P.slash W).G.edgeSet ∧ A.ends e = (P.slash W).G.ends e then _ else _) =
      patchSlash (if e ∈ P.G.edgeSet ∧ (liftRooted P.G hl A).ends e = P.G.ends e then _ else _) W
    rw [ite_eq_left ⟨h₁, hends' e he'⟩, ite_eq_left ⟨h₁, hends e he'⟩]
    rfl

theorem isFree_restrict {Ω : Type*} {P : Patchwork Ω α β} (hfree : IsFree P)
    {B : RootedHypergraph α β} (hB : B.toHypergraph ≤ P.G.toHypergraph) :
    IsFree (P.restrict B) := fun e he ↦ by
  classical
  have h₁ : e ∈ P.G.edgeSet := hB.edgeSet_subset he
  change (if e ∈ P.G.edgeSet ∧ B.ends e = P.G.ends e then P.Δ e else _).IsFree
  rw [ite_eq_left ⟨h₁, (hB.ends_eq e he).symm⟩]
  exact hfree e h₁

/-- The key step of (7.2): the patch of a lifted member, slashed by `W`, is the patch of the member
in `P/W`. This comes from (7.1). -/
theorem patchSlash_feasibleGroupings (hfree : IsFree P)
    (hA : A.toHypergraph ≤ quotientVertices P.G.toHypergraph W)
    (hset : ∀ v, v ∈ l ↔ v ∈ W) (hWV : W ⊆ P.G.vertexSet) :
    patchSlash (feasibleGroupings (P.restrict (liftRooted P.G hl A))) W =
      feasibleGroupings ((P.slash W).restrict A) := by
  have hle := liftRooted_le (hl := hl) hA hset hWV
  set R := P.restrict (liftRooted P.G hl A) with hR
  have hfreeR : IsFree R := isFree_restrict hfree hle
  have hWR : W ⊆ R.G.rootSet := fun v hv ↦
    (mem_liftRooted_rootSet' (hl := hl) hA hset).mpr (Or.inr hv)
  have hb := sameBase_slash_restrict (hl := hl) hA hset hWV
  have hroots : (R.slash W).G.roots = ((P.slash W).restrict A).G.roots := by
    change (((liftRooted P.G hl A).slash W).roots) = A.roots
    rw [slash_liftRooted hA hset]
  have hrs : (R.slash W).G.rootSet = R.G.rootSet \ W := by
    ext x
    exact mem_slash_rootSet
  have hrs' : R.G.rootSet \ W = A.rootSet := by
    ext x
    refine ⟨fun h ↦ ((mem_liftRooted_rootSet' (hl := hl) hA hset).mp h.1).resolve_right h.2,
      fun h ↦ ?_⟩
    exact ⟨(mem_liftRooted_rootSet' (hl := hl) hA hset).mpr (Or.inl h),
      (hA.vertexSet_subset (A.roots_subset x h)).2⟩
  refine Patch.ext_of hrs' ?_
  ext K
  constructor
  · rintro ⟨hg, hv, hK⟩
    exact feasible_of_sameBase hb hroots
      ((theorem_7_1_proof hfreeR hWR hg hv).mpr (by
        have : W ∩ R.G.rootSet = W := inter_eq_left.mpr hWR
        rw [show (feasibleGroupings R).verts = R.G.rootSet from rfl, this] at hK
        exact hK))
  · intro hK
    have hK' := feasible_of_sameBase hb.symm hroots.symm hK
    have hg : IsGrouping (R.G.rootSet \ W) K := by
      have := hK'.1
      rwa [hrs] at this
    have hv : K.verts = R.G.rootSet \ W := by
      have := hK'.2.1
      rwa [hrs] at this
    refine ⟨hg, hv, ?_⟩
    have : W ∩ R.G.rootSet = W := inter_eq_left.mpr hWR
    rw [show (feasibleGroupings R).verts = R.G.rootSet from rfl, this]
    exact (theorem_7_1_proof hfreeR hWR hg hv).mp hK'

/-- A tangle of order `> |W|` needs vertices or edges outside `W`. -/
theorem not_tangle_of_vertexSet_subset {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (hW : W.ncard < θ)
    (hWfin : W.Finite) (hV : G.vertexSet ⊆ W) (hE : G.edgeSet = ∅) : False := by
  have hsep : IsSeparation G G G :=
    ⟨le_rfl, le_rfl, union_self G, by
      apply Set.eq_empty_of_forall_notMem
      intro e he
      have : e ∈ G.edgeSet := he.1
      rw [hE] at this
      exact this⟩
  have hord : separationOrder G G < θ := lt_of_le_of_lt (Set.ncard_le_ncard
    (fun x hx ↦ hV hx.1) hWfin) hW
  have hmem : (G, G) ∈ 𝒯 := by
    rcases h𝒯.axiom1 hsep hord with h | h <;> exact h
  exact h𝒯.axiom3 hmem rfl

/-- Graph Minors XX, (7.2) (page 346): "Let $\mathcal{F}$ be a well-behaved set of patchworks and
let $\theta \ge 1$. Then there is
a well-behaved set of patchworks $\mathcal{F}'$ with the following property. Let $P = (G,
\mu, \Delta)$ be a free patchwork, let $\mathcal{T}$ be a tangle in $G$ of order $\ge
\theta$, let $W \subseteq V(G)$ with $|W| < \theta$, and let $\mathcal{L}$ be a fine rooted
location in $G/W$ such that $\mathcal{L}$ is linked to $\mathcal{T}/W$, and $\mathcal{F}$
contains a heart of $(P/W, \mathcal{L})$. Then there is a fine rooted location
$\mathcal{L}'$ in $G$ such that* - *$W \subseteq \bar{\pi}(A)$ for all $A \in
\mathcal{L}'$,* - *$\mathcal{L}'/W = \mathcal{L}$ and hence is linked to $\mathcal{T}/W$,
and* - *$\mathcal{F}'$ contains a heart of $(P, \mathcal{L}')$." -/
theorem theorem_7_2_proof {𝓕 : Set (UnlabeledPatchwork α β)} (h𝓕 : WellBehaved 𝓕) (θ : ℕ) :
    ∃ 𝓕' : Set (UnlabeledPatchwork α β), WellBehaved 𝓕' ∧
      ∀ (P : UnlabeledPatchwork α β), IsFree P →
      ∀ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle P.G.toHypergraph θ' 𝒯 →
        θ ≤ θ' → ∀ W : Set α, W ⊆ P.G.vertexSet → W.ncard < θ →
        ∀ ℒ : Set (RootedHypergraph α β), IsFine (P.G.slash W) ℒ →
          (∃ Q ∈ 𝓕, HasPatchworkHeart (P.slash W) ℒ Q) →
          ∃ ℒ' : Set (RootedHypergraph α β), IsFine P.G ℒ' ∧ IsRootedLocation P.G ℒ' ∧
            (∀ A ∈ ℒ', W ⊆ A.rootSet) ∧ locationSlash ℒ' W = ℒ ∧
            ∃ Q ∈ 𝓕', HasPatchworkHeart P ℒ' Q := by
  refine ⟨_, theorem_4_9_proof h𝓕 θ, fun P hfree θ' 𝒯 h𝒯 hθ' W hWV hWθ ℒ hfine ⟨Q, hQ, e,
    hheart⟩ ↦ ?_⟩
  have hWfin : W.Finite := P.G.vertexSet_finite.subset hWV
  have hℒ : IsRootedLocation (P.G.slash W) ℒ := hheart.isRootedLocation
  have hfin : ℒ.Finite := hheart.finite hfine
  have hle : ∀ {A}, A ∈ ℒ → A.toHypergraph ≤ quotientVertices P.G.toHypergraph W := fun hA ↦
    (hℒ.isComplemented hA).le
  obtain ⟨l, hl, hset⟩ : ∃ l : List α, l.Nodup ∧ ∀ v, v ∈ l ↔ v ∈ W :=
    ⟨hWfin.toFinset.toList, Finset.nodup_toList _, fun v ↦ by simp⟩
  have hs : ∀ {A}, A ∈ ℒ → (liftRooted P.G hl A).slash W = A := fun hA ↦
    slash_liftRooted (hle hA) hset
  have hne : ℒ.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    subst hn
    refine not_tangle_of_vertexSet_subset h𝒯 (hWθ.trans_le hθ') hWfin (fun v hv ↦ ?_) ?_
    · by_contra hvW
      obtain ⟨A, hA, -⟩ := hfine.1 v ⟨hv, hvW⟩
      exact hA
    · apply Set.eq_empty_of_forall_notMem
      intro f hf
      obtain ⟨A, hA, -⟩ := hfine.2 f hf
      exact hA
  obtain ⟨A₀, hA₀⟩ := hne
  have hroot : ∀ {A}, A ∈ ℒ → W ⊆ (liftRooted P.G hl A).rootSet := fun hA v hv ↦
    (mem_liftRooted_rootSet' (hle hA) hset).mpr (Or.inr hv)
  have hloc := isRootedLocation_lift (hl := hl) hℒ hset hWV
  have hfine' : IsFine P.G (liftRooted P.G hl '' ℒ) := by
    constructor
    · intro v hv
      by_cases hvW : v ∈ W
      · exact ⟨_, ⟨A₀, hA₀, rfl⟩, Or.inr ((hset v).mpr hvW)⟩
      · obtain ⟨A, hA, hvA⟩ := hfine.1 v ⟨hv, hvW⟩
        exact ⟨_, ⟨A, hA, rfl⟩, Or.inl hvA⟩
    · intro f hf
      obtain ⟨A, hA, hfA⟩ := hfine.2 f hf
      exact ⟨_, ⟨A, hA, rfl⟩, hfA⟩
  let e' : RootedHypergraph α β → β := fun B ↦ e (B.slash W)
  have he' : ∀ {A}, A ∈ ℒ → e' (liftRooted P.G hl A) = e A := fun hA ↦ congrArg e (hs hA)
  have hinj : InjOn e' (liftRooted P.G hl '' ℒ) := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ h
    rw [he' hA, he' hB] at h
    rw [hheart.injOn_newEdge hA hB h]
  obtain ⟨Q', hQ'⟩ := exists_heart hloc hfine' (hfin.image _) hinj
  have himg : e' '' (liftRooted P.G hl '' ℒ) = e '' ℒ := by
    ext g
    constructor
    · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
      exact ⟨A, hA, (he' hA).symm⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨_, ⟨A, hA, rfl⟩, he' hA⟩
  have hE' := hQ'.edgeSet_eq_image hfine'
  have hD' := hQ'.dom_eq_image hfine'
  have hE := hheart.edgeSet_eq_image hfine
  have hD := hheart.dom_eq_image hfine
  refine ⟨_, ⟨hfine', hloc, ?_, ?_, Q', ⟨hD'.trans hE'.symm, W, hWfin, hWθ.le, ?_, Q, hQ, ?_⟩,
    e', hQ'⟩⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact hroot hA
  · ext B
    constructor
    · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
      change (liftRooted P.G hl A).slash W ∈ ℒ
      rw [hs hA]
      exact hA
    · intro hB
      exact ⟨_, ⟨B, hB, rfl⟩, hs hB⟩
  · intro v hv
    rw [hQ'.vertexSet_eq]
    exact root_mem_core hloc ⟨A₀, hA₀, rfl⟩ (hroot hA₀ hv)
  · refine ⟨RootedHypergraph.ext_of ?_ (hE'.trans (himg.trans hE.symm)) ?_ ?_,
      hD'.trans (himg.trans hD.symm), ?_, ?_⟩
    · ext v
      change v ∈ Q'.G.vertexSet \ W ↔ _
      rw [mem_sdiff, hQ'.vertexSet_eq, hheart.vertexSet_eq, mem_core_iff, mem_core_iff]
      constructor
      · rintro ⟨⟨hv, h⟩, hvW⟩
        refine ⟨⟨hv, hvW⟩, fun A hA hvA ↦ ?_⟩
        exact ((mem_liftRooted_rootSet' (hl := hl) (hle hA) hset).mp
          (h _ ⟨A, hA, rfl⟩ (Or.inl hvA))).resolve_right hvW
      · rintro ⟨⟨hv, hvW⟩, h⟩
        refine ⟨⟨hv, ?_⟩, hvW⟩
        rintro _ ⟨A, hA, rfl⟩ (hvA | hvA)
        · exact (mem_liftRooted_rootSet' (hle hA) hset).mpr (Or.inl (h A hA hvA))
        · exact absurd ((hset v).mp hvA) hvW
    · ext g v
      change Q'.G.Inc g v ∧ v ∉ W ↔ _
      rw [hQ'.inc_iff hfine', hheart.inc_iff hfine]
      constructor
      · rintro ⟨⟨_, ⟨A, hA, rfl⟩, rfl, hv⟩, hvW⟩
        exact ⟨A, hA, (he' hA).symm, ((mem_liftRooted_rootSet' (hl := hl) (hle hA) hset).mp
          hv).resolve_right hvW⟩
      · rintro ⟨A, hA, rfl, hv⟩
        exact ⟨⟨_, ⟨A, hA, rfl⟩, he' hA, (mem_liftRooted_rootSet' (hle hA) hset).mpr (Or.inl hv)⟩,
          (hle hA |>.vertexSet_subset (A.roots_subset v hv)).2⟩
    · change marchSlash Q'.G.roots W = Q.G.roots
      rw [hQ'.roots_eq, hheart.roots_eq]
      rfl
    · intro g hg
      rw [hD] at hg
      obtain ⟨A, hA, rfl⟩ := hg
      change marchSlash (Q'.μ (e A)) W = Q.μ (e A)
      have h₁ := hQ'.μ_newEdge (A := liftRooted P.G hl A) ⟨A, hA, rfl⟩
      rw [he' hA] at h₁
      rw [h₁, hheart.μ_newEdge hA]
      exact congrArg RootedHypergraph.roots (hs hA)
    · intro g hg
      rw [hE] at hg
      obtain ⟨A, hA, rfl⟩ := hg
      change patchSlash (Q'.Δ (e A)) W = Q.Δ (e A)
      have h₁ := hQ'.Δ_newEdge (A := liftRooted P.G hl A) ⟨A, hA, rfl⟩
      rw [he' hA] at h₁
      rw [h₁, hheart.Δ_newEdge hA]
      exact patchSlash_feasibleGroupings hfree (hle hA) hset hWV

/-- Graph Minors XX, (7.3) (page 347): "Let $\Omega$ be a well-quasi-order, let $\mathcal{F}$ be a
well-behaved set of patchworks,
and let $\theta \ge 1$. Let $P_i = (G_i, \mu_i, \Delta_i, \phi_i)$ ($i = 1, 2, \ldots$) be a
countable sequence of free rootless $\Omega$-patchworks. Suppose that for each tangle
$\mathcal{T}$ in $G_i$ of order $\ge \theta$, there exist $W \subseteq V(G_i)$ with $|W| <
\theta$ and a fine rooted location $\mathcal{L}$ in $G/W$, such that $\mathcal{L}$ is linked
to $\mathcal{T}/W$, and $\mathcal{F}$ contains a heart of $((G_i, \mu_i, \Delta_i)/W,
\mathcal{L})$. Then there exist $j > i \ge 1$ such that $P_i$ is simulated in $P_j$." -/
theorem theorem_7_3_proof [Infinite β] {Ω : Type (max u v)} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    {𝓕 : Set (UnlabeledPatchwork α β)} (h𝓕 : WellBehaved 𝓕) {θ : ℕ} (hθ : 1 ≤ θ)
    (P : ℕ → GM04.Patchwork Ω α β) (hfree : ∀ i, IsFree (P i)) (hroot : ∀ i, IsRootless (P i))
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' → ∃ (W : Set α)
        (ℒ : Set (RootedHypergraph α β)), W ⊆ (P i).G.vertexSet ∧ W.ncard < θ ∧
        IsFine ((P i).G.slash W) ℒ ∧
        IsLinkedTo ((P i).G.slash W) (quotientTangle (P i).G.toHypergraph 𝒯 W) ℒ ∧
        ∃ Q ∈ 𝓕, HasPatchworkHeart (((P i).relabel fun _ ↦ ()).slash W) ℒ Q) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  obtain ⟨𝓕', h𝓕', hprop⟩ := theorem_7_2_proof h𝓕 θ
  refine theorem_6_3_proof hΩ h𝓕' hθ P (fun i ↦ ⟨hroot i, fun e he ↦ ?_⟩) fun i θ' 𝒯 h𝒯 hθ' ↦ ?_
  · refine Patch.IsFree.isRobust ?_ (hfree i e he)
    rw [(P i).Δ_verts e he]
    exact (P i).G.vertexSet_finite.subset fun v hv ↦ (P i).G.vertex_mem_of_inc hv
  · obtain ⟨W, ℒ, hWV, hWθ, hfine, hlink, hheart⟩ := h i θ' 𝒯 h𝒯 hθ'
    obtain ⟨ℒ', hfine', hloc, hWA, hslash, hh⟩ := hprop ((P i).relabel fun _ ↦ ())
      (fun e he ↦ hfree i e he) θ' 𝒯 h𝒯 hθ' W hWV hWθ ℒ hfine hheart
    refine ⟨W, ℒ', hWV, hWθ, hfine', hloc, hWA, ?_, hh⟩
    rw [hslash]
    exact hlink

end GraphMinor.GM20

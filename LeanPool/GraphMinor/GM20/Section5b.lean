/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5a

/-!
# Hearts of fine rooted locations

The results of Section 5 of Graph Minors XX replace a fine rooted location `ℒ` by another one `ℒ'`,
and
compare the hearts. This file gives the tools.
- `exists_heart`: a fine rooted location has a heart, for any injective choice of new edges.
- `mem_chain`: the patchwork `Q'` is reached from `Q₀` by a chain of 1-vertex extensions, if `Q'`
  has
  the same edges and each extra vertex is on one edge. The patchworks in the chain need not be
  hearts, since a 1-vertex extension allows any march and patch on the changed edge.
- `addRoots`: the rooted hypergraph `f(C)` of the proof of (5.3), with the vertices of `X` made
  roots,
  and `isRootedLocation_addRoots`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

/-- The patchworks of `s` in (4.8), up to agreement with the start and the end. -/
def chainSet (𝓕 : Set (UnlabeledPatchwork α β)) (k : ℕ) : Set (UnlabeledPatchwork α β) :=
  completions Unit {P₂ | ∃ s : ℕ → UnlabeledPatchwork α β, ∃ k' ≤ k, s 0 ∈ completions Unit 𝓕 ∧
    s k' = P₂ ∧ ∀ i < k', ∃ f v, IsOneVertexExtension (s i) (s (i + 1)) f v}

theorem wellBehaved_chainSet {𝓕 : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕) (k : ℕ) :
    WellBehaved (chainSet 𝓕 k) :=
  (theorem_4_8_proof h.completions k).completions

/-- Two patchworks which `mem_chain` connects. -/
structure ChainData (Q₀ Q' : UnlabeledPatchwork α β) (X : Set α) : Prop where
  roots_eq : Q'.G.roots = Q₀.G.roots
  edgeSet_eq : Q'.G.edgeSet = Q₀.G.edgeSet
  dom_eq : Q'.dom = Q₀.dom
  vertexSet_eq : Q'.G.vertexSet = Q₀.G.vertexSet ∪ X
  disjoint : Disjoint X Q₀.G.vertexSet
  inc_iff : ∀ e v, v ∈ Q₀.G.vertexSet → (Q₀.G.Inc e v ↔ Q'.G.Inc e v)
  exists_edge : ∀ x ∈ X, ∃ f ∈ Q₀.dom, Q'.G.Inc f x ∧ ∀ e, Q'.G.Inc e x → e = f
  same_of_ends : ∀ e ∈ Q₀.G.edgeSet, Q'.G.ends e = Q₀.G.ends e → e ∈ Q₀.dom →
    Q'.μ e = Q₀.μ e
  sameΔ_of_ends : ∀ e ∈ Q₀.G.edgeSet, Q'.G.ends e = Q₀.G.ends e → Q'.Δ e = Q₀.Δ e

open Classical in
/-- The stage `T ⊆ X` between `Q₀` and `Q'`. -/
noncomputable def chainStage {Q₀ Q' : UnlabeledPatchwork α β} {X : Set α} (h : ChainData Q₀ Q' X)
    (T : Set α) (hT : T ⊆ X) : UnlabeledPatchwork α β :=
  let V := Q₀.G.vertexSet ∪ T
  let hV : V ⊆ Q'.G.vertexSet := fun v hv ↦ by
    rw [h.vertexSet_eq]
    exact hv.imp id fun h' ↦ hT h'
  let ends : β → Set α := fun e ↦ Q'.G.ends e ∩ V
  { G :=
    { vertexSet := V
      edgeSet := Q'.G.edgeSet
      Inc := fun e v ↦ Q'.G.Inc e v ∧ v ∈ V
      vertex_mem_of_inc := fun _ _ h' ↦ h'.2
      edge_mem_of_inc := fun _ _ h' ↦ Q'.G.edge_mem_of_inc h'.1
      vertexSet_finite := Q'.G.vertexSet_finite.subset hV
      edgeSet_finite := Q'.G.edgeSet_finite
      roots := Q'.G.roots
      roots_nodup := Q'.G.roots_nodup
      roots_subset := fun v hv ↦ Or.inl (Q₀.G.roots_subset v (h.roots_eq ▸ hv)) }
    dom := Q'.dom
    μ := fun e ↦ if ends e = Q₀.G.ends e then Q₀.μ e else marchSlash (Q'.μ e) (Vᶜ)
    Δ := fun e ↦ if ends e = Q₀.G.ends e then Q₀.Δ e else if ends e = Q'.G.ends e then Q'.Δ e else
      freePatch (ends e)
    φ := Q'.φ
    dom_subset := Q'.dom_subset
    μ_nodup := fun e he ↦ by
      split_ifs
      · exact Q₀.μ_nodup e (h.dom_eq ▸ he)
      · exact nodup_marchSlash (Q'.μ_nodup e he) _
    μ_set := fun e he ↦ by
      change _ = ends e
      split_ifs with h₁
      · rw [Q₀.μ_set e (h.dom_eq ▸ he), h₁]
      · ext v
        have h₂ := Set.ext_iff.mp (Q'.μ_set e he) v
        simp only [mem_ofPred_eq, mem_marchSlash, mem_compl_iff, not_not] at h₂ ⊢
        exact ⟨fun h' ↦ ⟨h₂.mp h'.1, h'.2⟩, fun h' ↦ ⟨h₂.mpr h'.1, h'.2⟩⟩
    Δ_verts := fun e he ↦ by
      change _ = ends e
      split_ifs with h₁ h₂
      · rw [Q₀.Δ_verts e (h.edgeSet_eq ▸ he), h₁]
      · rw [Q'.Δ_verts e he, h₂]
      · rfl
    Δ_free := fun e he hd ↦ by
      split_ifs with h₁ h₂
      · exact Q₀.Δ_free e (h.edgeSet_eq ▸ he) (fun h' ↦ hd (h.dom_eq ▸ h'))
      · exact Q'.Δ_free e he hd
      · exact freePatch_isFree _ }

section Chain

variable {Q₀ Q' : UnlabeledPatchwork α β} {X : Set α} (h : ChainData Q₀ Q' X)

include h in
theorem chainStage_extension {T : Set α} (hT : T ⊆ X) {x : α} (hx : x ∈ X) (hxT : x ∉ T)
    (hT' : insert x T ⊆ X) :
    ∃ f, IsOneVertexExtension (chainStage h T hT) (chainStage h (insert x T) hT') f x := by
  classical
  obtain ⟨f, hf, hinc, hone⟩ := h.exists_edge x hx
  have hx₀ : x ∉ Q₀.G.vertexSet := Set.disjoint_left.mp h.disjoint hx
  have hends : ∀ e, e ≠ f → Q'.G.ends e ∩ (Q₀.G.vertexSet ∪ insert x T) =
      Q'.G.ends e ∩ (Q₀.G.vertexSet ∪ T) := by
    intro e he
    ext y
    constructor
    · rintro ⟨h₁, h₂ | rfl | h₂⟩
      · exact ⟨h₁, Or.inl h₂⟩
      · exact absurd (hone e h₁) he
      · exact ⟨h₁, Or.inr h₂⟩
    · rintro ⟨h₁, h₂ | h₂⟩
      · exact ⟨h₁, Or.inl h₂⟩
      · exact ⟨h₁, Or.inr (Or.inr h₂)⟩
  refine ⟨f, ?_⟩
  refine
  { f_mem := h.dom_eq ▸ hf
    v_notMem := fun h₁ ↦ h₁.elim hx₀ hxT
    roots_eq := rfl
    edgeSet_eq := rfl
    vertexSet_eq := ?_
    ends_f := ?_
    ends_ne := fun e _ he ↦ hends e he
    dom_eq := rfl
    μ_ne := fun e he hne ↦ ?_
    Δ_ne := fun e he hne ↦ ?_ }
  · change Q₀.G.vertexSet ∪ insert x T = (Q₀.G.vertexSet ∪ T) ∪ {x}
    ext y
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    tauto
  · change Q'.G.ends f ∩ (Q₀.G.vertexSet ∪ insert x T) =
      (Q'.G.ends f ∩ (Q₀.G.vertexSet ∪ T)) ∪ {x}
    ext y
    constructor
    · rintro ⟨h₁, h₂ | rfl | h₂⟩
      · exact Or.inl ⟨h₁, Or.inl h₂⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨h₁, Or.inr h₂⟩
    · rintro (⟨h₁, h₂ | h₂⟩ | rfl)
      · exact ⟨h₁, Or.inl h₂⟩
      · exact ⟨h₁, Or.inr (Or.inr h₂)⟩
      · exact ⟨hinc, Or.inr (Or.inl rfl)⟩
  · simp only [chainStage, hends e hne]
    split_ifs
    · rfl
    · classical
      apply List.filter_congr
      intro y hy
      have hend : y ∈ {y | y ∈ Q'.μ e} := hy
      rw [Q'.μ_set e he] at hend
      have hyx : y ≠ x := fun heq ↦ hne (hone e (heq ▸ hend))
      simp [hyx]
  · simp only [chainStage, hends e hne]

include h in
theorem chainStage_empty : IsCompletionOf Q₀ (chainStage h ∅ (empty_subset _)) := by
  classical
  have hends : ∀ e, Q'.G.ends e ∩ (Q₀.G.vertexSet ∪ ∅) = Q₀.G.ends e := by
    intro e
    ext v
    constructor
    · rintro ⟨h₁, h₂⟩
      exact (h.inc_iff e v (by simpa using h₂)).mpr h₁
    · intro h₁
      have hv : v ∈ Q₀.G.vertexSet := Q₀.G.vertex_mem_of_inc h₁
      exact ⟨(h.inc_iff e v hv).mp h₁, Or.inl hv⟩
  refine ⟨?_, h.dom_eq, fun e _ ↦ ?_, fun e _ ↦ ?_⟩
  · refine RootedHypergraph.ext_of (Set.union_empty _) h.edgeSet_eq ?_ h.roots_eq
    funext e v
    exact propext (Set.ext_iff.mp (hends e) v)
  · simp only [chainStage, hends, ↓reduceIte]
  · simp only [chainStage, hends, ↓reduceIte]

include h in
theorem chainStage_top : IsCompletionOf Q' (chainStage h X subset_rfl) := by
  classical
  have hends : ∀ e, Q'.G.ends e ∩ (Q₀.G.vertexSet ∪ X) = Q'.G.ends e := by
    intro e
    rw [← h.vertexSet_eq]
    exact inter_eq_left.mpr fun v hv ↦ Q'.G.vertex_mem_of_inc hv
  refine ⟨?_, rfl, fun e he ↦ ?_, fun e he ↦ ?_⟩
  · refine RootedHypergraph.ext_of h.vertexSet_eq.symm rfl ?_ rfl
    funext e v
    exact propext (Set.ext_iff.mp (hends e) v)
  · simp only [chainStage, hends]
    split_ifs with h₁
    · exact (h.same_of_ends e (Q'.dom_subset he |> fun h₂ ↦ h.edgeSet_eq ▸ h₂) h₁
        (h.dom_eq ▸ he)).symm
    · refine marchSlash_of_disjoint fun x hx hxc ↦ hxc ?_
      have h₂ : x ∈ {y | y ∈ Q'.μ e} := hx
      rw [Q'.μ_set e he] at h₂
      rw [← h.vertexSet_eq]
      exact Q'.G.vertex_mem_of_inc h₂
  · simp only [chainStage, hends, ↓reduceIte]
    split_ifs with h₁
    · exact (h.sameΔ_of_ends e (h.edgeSet_eq ▸ he) h₁).symm
    · rfl

end Chain

theorem chain_snoc {s : ℕ → UnlabeledPatchwork α β} {n : ℕ}
    {A : UnlabeledPatchwork α β} (hs : s n = A) (hc : ∀ i < n, ∃ f v,
      IsOneVertexExtension (s i) (s (i + 1)) f v) {B : UnlabeledPatchwork α β}
    (hAB : ∃ f v, IsOneVertexExtension A B f v) :
    ∃ s' : ℕ → UnlabeledPatchwork α β, s' 0 = s 0 ∧ s' (n + 1) = B ∧ ∀ i < n + 1, ∃ f v,
      IsOneVertexExtension (s' i) (s' (i + 1)) f v := by
  classical
  refine ⟨fun i ↦ if i ≤ n then s i else B, by simp, by simp, fun i hi ↦ ?_⟩
  by_cases hin : i < n
  · have h₁ : i ≤ n := hin.le
    have h₂ : i + 1 ≤ n := hin
    simp only [h₁, h₂, ↓reduceIte]
    exact hc i hin
  · have hie : i = n := by omega
    subst hie
    simp only [le_refl, ↓reduceIte, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero]
    rw [hs]
    exact hAB

/-- `Q'` is reached from `Q₀` by at most `k` extensions. -/
theorem mem_chain {𝓕 : Set (UnlabeledPatchwork α β)} {Q₀ Q' : UnlabeledPatchwork α β} {X : Set α}
    (hQ₀ : Q₀ ∈ completions Unit 𝓕) (h : ChainData Q₀ Q' X) (hX : X.Finite) {k : ℕ}
    (hk : X.ncard ≤ k) : Q' ∈ chainSet 𝓕 k := by
  have key : ∀ T : Set α, T.Finite → ∀ hT : T ⊆ X, ∃ s : ℕ → UnlabeledPatchwork α β,
      s 0 = chainStage h ∅ (empty_subset _) ∧ s T.ncard = chainStage h T hT ∧
      ∀ i < T.ncard, ∃ f v, IsOneVertexExtension (s i) (s (i + 1)) f v := by
    intro T hfin
    induction T, hfin using Set.Finite.induction_on with
    | empty =>
      intro hT
      exact ⟨fun _ ↦ chainStage h ∅ (empty_subset _), rfl, by simp, by simp⟩
    | @insert x T hxT hfin ih =>
      intro hT
      have hT₀ : T ⊆ X := (subset_insert x T).trans hT
      obtain ⟨s, h₀, h₁, h₂⟩ := ih hT₀
      obtain ⟨f, hf⟩ := chainStage_extension h hT₀ (hT (mem_insert x T)) hxT hT
      obtain ⟨s', h₀', h₁', h₂'⟩ := chain_snoc h₁ h₂ ⟨f, x, hf⟩
      rw [Set.ncard_insert_of_notMem hxT hfin]
      exact ⟨s', h₀'.trans h₀, h₁', h₂'⟩
  obtain ⟨s, h₀, h₁, h₂⟩ := key X hX subset_rfl
  obtain ⟨P₀, hP₀, hc₀⟩ := hQ₀
  refine ⟨chainStage h X subset_rfl, ⟨s, X.ncard, hk, ⟨P₀, hP₀, ?_⟩, h₁, h₂⟩,
    (chainStage_top h).symm⟩
  rw [h₀]
  exact hc₀.trans (chainStage_empty h)

/-! ### Hearts of fine locations -/

section Heart

variable {P : UnlabeledPatchwork α β} {ℒ : Set (RootedHypergraph α β)}

theorem core_edgeSet_eq_empty (hfine : IsFine P.G ℒ) :
    (rootedLocationCore P.G ℒ).edgeSet = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro e he
  obtain ⟨he₁, he₂⟩ := mem_core_edgeSet.mp he
  obtain ⟨A, hA, heA⟩ := hfine.2 e he₁
  exact he₂ A hA heA

/-- A vertex is in `V(M(G, ℒ))` if and only if it is a root of each member of `ℒ` that contains it.
-/
theorem mem_core_iff {G : RootedHypergraph α β} {v : α} :
    v ∈ (rootedLocationCore G ℒ).vertexSet ↔ v ∈ G.vertexSet ∧
      ∀ A ∈ ℒ, v ∈ A.vertexSet → v ∈ A.rootSet := by
  rw [mem_core_vertexSet]
  refine and_congr_right fun hv ↦ forall₂_congr fun A hA ↦ ?_
  constructor
  · rintro (h | h) hvA
    · exact absurd hvA h.2
    · exact h.2
  · intro h
    by_cases hvA : v ∈ A.vertexSet
    · exact Or.inr ⟨hv, h hvA⟩
    · exact Or.inl ⟨hv, hvA⟩

/-- Roots of a member of a rooted location are in `V(M(G, ℒ))`. -/
theorem root_mem_core {G : RootedHypergraph α β} (hℒ : IsRootedLocation G ℒ) {A} (hA : A ∈ ℒ)
    {v : α} (hv : v ∈ A.rootSet) : v ∈ (rootedLocationCore G ℒ).vertexSet := by
  have hvV : v ∈ A.vertexSet := A.roots_subset v hv
  refine mem_core_iff.mpr ⟨(hℒ.isComplemented hA).le.vertexSet_subset hvV, fun B hB hvB ↦ ?_⟩
  by_cases hAB : A = B
  · exact hAB ▸ hv
  · have hle := hℒ.le_complement hA hB hAB
    rcases hle.vertexSet_subset hvV with h | h
    · exact absurd hvB h.2
    · exact h

/-- A fine rooted location has a heart, for any injective choice of new edges. -/
theorem exists_heart (hℒ : IsRootedLocation P.G ℒ) (hfine : IsFine P.G ℒ) (hfin : ℒ.Finite)
    {e : RootedHypergraph α β → β} (he : InjOn e ℒ) :
    ∃ Q, IsPatchworkHeart P ℒ e Q := by
  classical
  have : Nonempty (RootedHypergraph α β) := ⟨P.G⟩
  have hinv : ∀ {A}, A ∈ ℒ → Function.invFunOn e ℒ (e A) = A := fun hA ↦
    he (Function.invFunOn_mem ⟨_, hA, rfl⟩) hA (Function.invFunOn_eq ⟨_, hA, rfl⟩)
  have hemp := core_edgeSet_eq_empty hfine
  let G : RootedHypergraph α β :=
    { vertexSet := (rootedLocationCore P.G ℒ).vertexSet
      edgeSet := e '' ℒ
      Inc := fun f v ↦ ∃ A ∈ ℒ, e A = f ∧ v ∈ A.rootSet
      vertex_mem_of_inc := fun _ _ ⟨_, hA, _, hv⟩ ↦ root_mem_core hℒ hA hv
      edge_mem_of_inc := fun _ _ ⟨A, hA, h₁, _⟩ ↦ ⟨A, hA, h₁⟩
      vertexSet_finite := (rootedLocationCore P.G ℒ).vertexSet_finite
      edgeSet_finite := hfin.image e
      roots := P.G.roots
      roots_nodup := P.G.roots_nodup
      roots_subset := fun v hv ↦ mem_core_iff.mpr ⟨P.G.roots_subset v hv,
        fun A hA hvA ↦ (hℒ.isComplemented hA).roots_mem hvA hv⟩ }
  have hends : ∀ {A}, A ∈ ℒ → G.ends (e A) = A.rootSet := fun {A} hA ↦ by
    ext v
    constructor
    · rintro ⟨B, hB, h₁, h₂⟩
      exact (he hB hA h₁) ▸ h₂
    · exact fun h ↦ ⟨A, hA, rfl, h⟩
  let Q : UnlabeledPatchwork α β :=
    { G := G
      dom := e '' ℒ
      μ := fun f ↦ (Function.invFunOn e ℒ f).roots
      Δ := fun f ↦ feasibleGroupings (P.restrict (Function.invFunOn e ℒ f))
      φ := fun _ ↦ ()
      dom_subset := subset_rfl
      μ_nodup := fun _ _ ↦ RootedHypergraph.roots_nodup _
      μ_set := by
        rintro _ ⟨A, hA, rfl⟩
        rw [hinv hA, hends hA]
        rfl
      Δ_verts := by
        rintro _ ⟨A, hA, rfl⟩
        rw [hinv hA, hends hA]
        rfl
      Δ_free := fun f hf hf' ↦ absurd hf hf' }
  refine ⟨Q, ?_⟩
  refine
  { isRootedLocation := hℒ
    injOn_newEdge := he
    newEdge_notMem_core := fun A _ h ↦ by rw [hemp] at h; exact h
    vertexSet_eq := rfl
    edgeSet_eq := by rw [hemp, Set.empty_union]
    roots_eq := rfl
    ends_core := fun f hf ↦ by rw [hemp] at hf; exact hf.elim
    ends_newEdge := fun A hA ↦ hends hA
    dom_eq := by rw [hemp, Set.empty_inter, Set.empty_union]
    μ_core := fun f hf ↦ by rw [hemp] at hf; exact hf.1.elim
    μ_newEdge := fun A hA ↦ by
      change (Function.invFunOn e ℒ (e A)).roots = _
      rw [hinv hA]
    Δ_core := fun f hf ↦ by rw [hemp] at hf; exact hf.elim
    Δ_newEdge := fun A hA ↦ by
      change feasibleGroupings (P.restrict (Function.invFunOn e ℒ (e A))) = _
      rw [hinv hA] }

end Heart

/-! ### Making vertices roots -/

/-- The rooted hypergraph `C` with the terms of `l` in `V(C)` made roots. -/
noncomputable def addRoots {l : List α} (hl : l.Nodup) (C : RootedHypergraph α β) :
    RootedHypergraph α β :=
  C.reroot (C.roots ++ marchSlash l (C.vertexSetᶜ ∪ C.rootSet))
    (List.Nodup.append C.roots_nodup (nodup_marchSlash hl _)
      fun _ hx hx' ↦ (mem_marchSlash.mp hx').2 (Or.inr hx))
    fun x hx ↦ (List.mem_append.mp hx).elim (C.roots_subset x) fun h ↦ by
      have h₂ := (mem_marchSlash.mp h).2
      by_contra hn
      exact h₂ (Or.inl hn)

section AddRoots

variable {l : List α} (hl : l.Nodup) (C : RootedHypergraph α β)

theorem addRoots_toHypergraph : (addRoots hl C).toHypergraph = C.toHypergraph := rfl

theorem mem_addRoots_rootSet {x : α} :
    x ∈ (addRoots hl C).rootSet ↔ x ∈ C.rootSet ∨ (x ∈ l ∧ x ∈ C.vertexSet) := by
  change x ∈ C.roots ++ marchSlash l (C.vertexSetᶜ ∪ C.rootSet) ↔ _
  rw [List.mem_append, mem_marchSlash]
  constructor
  · rintro (h | ⟨h₁, h₂⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h₁, ?_⟩
      by_contra hn
      exact h₂ (Or.inl hn)
  · rintro (h | ⟨h₁, h₂⟩)
    · exact Or.inl h
    · by_cases hr : x ∈ C.rootSet
      · exact Or.inl hr
      · exact Or.inr ⟨h₁, fun h ↦ h.elim (fun h₃ ↦ h₃ h₂) hr⟩

theorem addRoots_eq (h : ∀ x ∈ l, x ∈ C.vertexSet → x ∈ C.rootSet) : addRoots hl C = C := by
  refine RootedHypergraph.ext_of rfl rfl rfl ?_
  change C.roots ++ marchSlash l (C.vertexSetᶜ ∪ C.rootSet) = C.roots
  have : marchSlash l (C.vertexSetᶜ ∪ C.rootSet) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨h₁, h₂⟩ := mem_marchSlash.mp hx
    by_cases hv : x ∈ C.vertexSet
    · exact h₂ (Or.inr (h x h₁ hv))
    · exact h₂ (Or.inl hv)
  rw [this, List.append_nil]

variable {G : RootedHypergraph α β}

theorem isComplemented_addRoots (h : IsComplemented G C) : IsComplemented G (addRoots hl C) where
  le := h.le
  roots_mem _ hv hr := (mem_addRoots_rootSet hl C).mpr (Or.inl (h.roots_mem hv hr))
  inc_diff_mem _ _ hv he hinc := (mem_addRoots_rootSet hl C).mpr (Or.inl
    (h.inc_diff_mem hv he hinc))

theorem complementHypergraph_mono {A B : RootedHypergraph α β} (hB : IsComplemented G B)
  (h : A.toHypergraph ≤ (complement G B hB).toHypergraph) :
    A.toHypergraph ≤ (complement G (addRoots hl B) (isComplemented_addRoots hl B hB)).toHypergraph
      := by
  refine ⟨fun v hv ↦ ?_, h.edgeSet_subset, fun e he ↦ h.ends_eq e he⟩
  rcases h.vertexSet_subset hv with h₁ | h₁
  · exact Or.inl h₁
  · exact Or.inr ((mem_addRoots_rootSet hl B).mpr (Or.inl h₁))

end AddRoots

variable {ℒ : Set (RootedHypergraph α β)} {G : RootedHypergraph α β}

/-- `f` is injective on a rooted location: two members with the same hypergraph have all vertices as
roots, and so `addRoots` does nothing to them. -/
theorem injOn_addRoots {l : List α} (hl : l.Nodup) (hℒ : IsRootedLocation G ℒ) :
    InjOn (addRoots hl) ℒ := by
  intro A hA B hB heq
  by_contra hne
  have hH : A.toHypergraph = B.toHypergraph := congrArg (·.toHypergraph) heq
  have hroot : ∀ {A B : RootedHypergraph α β}, A ∈ ℒ → B ∈ ℒ → A ≠ B →
      A.toHypergraph = B.toHypergraph → ∀ x ∈ B.vertexSet, x ∈ B.rootSet := by
    intro A B hA hB hne hH x hx
    have hxA : x ∈ A.vertexSet := by rw [hH]; exact hx
    rcases (hℒ.le_complement hA hB hne).vertexSet_subset hxA with h | h
    · exact absurd hx h.2
    · exact h
  have h₁ := addRoots_eq hl A fun x _ hx ↦ hroot hB hA (Ne.symm hne) hH.symm x hx
  have h₂ := addRoots_eq hl B fun x _ hx ↦ hroot hA hB hne hH x hx
  exact hne (by rw [← h₁, ← h₂]; exact heq)

/-- Making vertices roots keeps a rooted location. -/
theorem isRootedLocation_addRoots {l : List α} (hl : l.Nodup) (hℒ : IsRootedLocation G ℒ) :
    IsRootedLocation G (addRoots hl '' ℒ) where
  isComplemented := by
    rintro _ ⟨C, hC, rfl⟩
    exact isComplemented_addRoots hl C (hℒ.isComplemented hC)
  le_complement := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
    have hne' : A ≠ B := fun h ↦ hne (by rw [h])
    exact complementHypergraph_mono hl (hℒ.isComplemented hB) (hℒ.le_complement hA hB hne')

end GraphMinor.GM20

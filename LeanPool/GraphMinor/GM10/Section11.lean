/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM10.Section9
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Set.Card

/-!
# Graph Minors X, Section 11: Structure Relative to a Tangle

This file formalizes Section 11 (pages 184–188) of N. Robertson and P. D. Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190:

- **Star-of-trees gluing construction:** gluing tree-decompositions `(Tᵢ, τᵢ)` of subhypergraphs
  `Aᵢ ≤ G` around a central bag `τ₀ ≤ G` to form a tree-decomposition of `G`.
- **(11.2) (`theorem_11_2`, pages 185–186):** for `θ ≥ 1`, `𝒮` `θ`-pervasive in `G`, and
  `Z ⊆ V(G)` with `|Z| = 3θ - 2`, either there is a low-order separation splitting `Z` into smaller
  pieces or there is a location in `G` with design in `𝒮` where every member has small intersection
  with `Z`.
- **(11.3) (`theorem_11_3`, pages 186–188):** the inductive strengthened form of `(11.1)` with a
  prescribed set `Z ⊆ V(G)` of size `≤ 3θ - 2`.
- **(11.1) (`theorem_11_1`, page 185):** every hypergraph `G` in which a class of designs `𝒮` is
  `θ`-pervasive has a tree-decomposition over `𝒮^{3θ - 2} ∪ ℛ_{4θ - 3}`.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Hypergraph

variable {α β : Type*}

/-! ## Helper subhypergraphs and design lemmas -/

/-- If `K.edgeSet = ∅` and `K.vertexSet ⊆ H.vertexSet`, then `K ≤ H`. -/
theorem le_of_edgeSet_eq_empty {K H : Hypergraph α β}
    (hE : K.edgeSet = ∅) (hV : K.vertexSet ⊆ H.vertexSet) : K ≤ H :=
  ⟨hV, hE.symm ▸ Set.empty_subset _, fun _ he ↦ (Set.notMem_empty _ (hE ▸ he)).elim⟩

/-- The edgeless subhypergraph of `G` with vertex set `X ∩ V(G)`. -/
private def edgelessSubhypergraph (G : Hypergraph α β) (X : Set α) : Hypergraph α β where
  vertexSet := X ∩ G.vertexSet
  edgeSet := ∅
  Inc _ _ := False
  vertex_mem_of_inc _ _ h := h.elim
  edge_mem_of_inc _ _ h := h.elim
  vertexSet_finite := G.vertexSet_finite.subset Set.inter_subset_right
  edgeSet_finite := Set.finite_empty

@[simp]
private theorem edgelessSubhypergraph_vertexSet (G : Hypergraph α β) {X : Set α}
    (hX : X ⊆ G.vertexSet) :
    (edgelessSubhypergraph G X).vertexSet = X :=
  Set.inter_eq_self_of_subset_left hX

@[simp]
private theorem edgelessSubhypergraph_edgeSet (G : Hypergraph α β) (X : Set α) :
    (edgelessSubhypergraph G X).edgeSet = ∅ := rfl

private theorem edgelessSubhypergraph_le (G : Hypergraph α β) (X : Set α) :
    edgelessSubhypergraph G X ≤ G :=
  le_of_edgeSet_eq_empty rfl Set.inter_subset_right

/-- Adding a set of vertices `Z ⊆ V(G)` to a subhypergraph `H ≤ G` without adding edges. -/
private def addVertices (G H : Hypergraph α β) (Z : Set α) : Hypergraph α β where
  vertexSet := H.vertexSet ∪ (Z ∩ G.vertexSet)
  edgeSet := H.edgeSet
  Inc := H.Inc
  vertex_mem_of_inc _ _ h := Or.inl (H.vertex_mem_of_inc h)
  edge_mem_of_inc _ _ h := H.edge_mem_of_inc h
  vertexSet_finite := H.vertexSet_finite.union (G.vertexSet_finite.subset Set.inter_subset_right)
  edgeSet_finite := H.edgeSet_finite

@[simp]
private theorem addVertices_vertexSet {G H : Hypergraph α β} {Z : Set α} (hZ : Z ⊆ G.vertexSet) :
    (addVertices G H Z).vertexSet = H.vertexSet ∪ Z := by
  simp [addVertices, Set.inter_eq_self_of_subset_left hZ]

@[simp]
private theorem addVertices_edgeSet (G H : Hypergraph α β) (Z : Set α) :
    (addVertices G H Z).edgeSet = H.edgeSet := rfl

private theorem le_addVertices (G H : Hypergraph α β) (Z : Set α) :
    H ≤ addVertices G H Z :=
  ⟨Set.subset_union_left, subset_rfl, fun _ _ ↦ rfl⟩

private theorem addVertices_le {G H : Hypergraph α β} (hH : H ≤ G) (Z : Set α) :
    addVertices G H Z ≤ G :=
  ⟨Set.union_subset hH.vertexSet_subset Set.inter_subset_right,
   hH.edgeSet_subset, hH.ends_eq⟩

/-- Remark at the start of the proof of (11.3) (page 186):
"from the definition of $\theta$-pervasive, if $\mathscr{S}$ is $\theta$-pervasive in $G$
then it is $\theta$-pervasive in every subhypergraph of $G$." -/
theorem IsPervasive.mono {G G' : Hypergraph α β} {θ : ℕ} {𝒮 : Set (Design α β)}
    (hperv : IsPervasive G θ 𝒮) (hle : G' ≤ G) :
    IsPervasive G' θ 𝒮 :=
  fun _ hle' _ _ hθ' h𝒯 ↦ hperv (hle'.trans hle) hθ' h𝒯

/-- For any set `ℒ` of separations of `G`, `locationCore G ℒ ≤ G`. -/
theorem locationCore_le {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ ⦃p⦄, p ∈ ℒ → G.IsSeparation p.1 p.2) :
    locationCore G ℒ ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, locationCore, Set.mem_ofPred_eq]
    refine ⟨fun hinc ↦ ⟨hinc, fun p hp ↦ ?_, he.2⟩, fun h ↦ h.1⟩
    have hp_le := (hsep hp).right_le
    have hv_ends : v ∈ p.2.ends e := hp_le.ends_eq e (he.2 p hp) ▸ hinc
    exact p.2.vertex_mem_of_inc hv_ends

/-- For any location `ℒ` in `G`, `locationDesign G ℒ` is a design (page 185). -/
theorem IsLocation.isDesign_locationDesign {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hloc : IsLocation G ℒ) :
    IsDesign (locationDesign G ℒ) := by
  rintro X ⟨p, hp, rfl⟩ x ⟨hxA, hxB⟩
  refine ⟨(hloc.isSeparation hp).left_le.vertexSet_subset hxA, fun q hq ↦ ?_⟩
  by_cases hpq : p = q
  · exact hpq ▸ hxB
  · exact (hloc.left_le_right hp hq hpq).vertexSet_subset hxA

/-- Any location in a hypergraph `G` is a finite set of separations. -/
theorem IsLocation.finite {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hloc : IsLocation G ℒ) : ℒ.Finite :=
  finite_of_forall_isSeparation fun _ hp ↦ hloc.isSeparation hp

/-- Relabelling a tree-decomposition along `e : ι ≃ ι'` preserves `vertexDesign`. -/
theorem vertexDesign_map {ι ι' : Type*} (T : SimpleGraph ι) (τ : ι → Hypergraph α β)
    (e : ι ≃ ι') (t₀ : ι) :
    vertexDesign (T.map e.toEmbedding) (τ ∘ e.symm) (e t₀) = vertexDesign T τ t₀ := by
  ext : 1
  · simp [vertexDesign]
  · ext X
    simp only [vertexDesign, Set.mem_ofPred_eq, Function.comp_apply, Equiv.symm_apply_apply]
    constructor
    · rintro ⟨t', hadj', rfl⟩
      obtain ⟨t, rfl⟩ := e.surjective t'
      have hadj : T.Adj t₀ t := (SimpleGraph.Iso.map e T).map_rel_iff.1 hadj'
      exact ⟨t, hadj, by simp⟩
    · rintro ⟨t, hadj, rfl⟩
      have hadj' : (T.map e.toEmbedding).Adj (e t₀) (e t) :=
        (SimpleGraph.Iso.map e T).map_rel_iff.2 hadj
      exact ⟨e t, hadj', by simp⟩

/-- Relabelling a tree-decomposition over `𝒮` along `e : ι ≃ ι'` gives a tree-decomposition over
`𝒮`. -/
theorem IsTreeDecompositionOver.relabel {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {G : Hypergraph α β} {𝒮 : Set (Design α β)} {T : SimpleGraph ι} {τ : ι → Hypergraph α β}
    (h : IsTreeDecompositionOver G 𝒮 T τ) (e : ι ≃ ι') :
    IsTreeDecompositionOver G 𝒮 (T.map e.toEmbedding) (τ ∘ e.symm) := by
  refine ⟨h.1.relabel e, fun t' ↦ ?_⟩
  obtain ⟨t, rfl⟩ := e.surjective t'
  rw [vertexDesign_map]
  exact h.2 t

/-! ## Proof of Graph Minors X, (11.2) -/

/-- **Graph Minors X, (11.2)** (pages 185–186):
"Let $\theta \ge 1$, let $\mathscr{S}$ be $\theta$-pervasive in $G$, and let $Z \subseteq
V(G)$ with $|Z| = 3\theta - 2$. Then either* (i) *there is a separation $(A, B)$ of $G$ of
order $< \theta$ with* $$ |(Z \cup V(A)) \cap V(B)|, |(Z \cup V(B)) \cap V(A)| \le 3\theta -
3 $$ ... *or* (ii) *there is a location $\{(A_1, B_1), \dots, (A_k, B_k)\}$ in $G$, with design
in $\mathscr{S}$, such that for $1 \le i \le k$,* $$ |Z \cap V(A_i)| \le |V(A_i \cap B_i)| <
\theta." -/
theorem theorem_11_2_proof {G : Hypergraph α β} {θ : ℕ} {𝒮 : Set (Design α β)} {Z : Set α}
    (hθ : 1 ≤ θ) (hperv : IsPervasive G θ 𝒮)
    (hZ_sub : Z ⊆ G.vertexSet) (hZ_card : Z.ncard = 3 * θ - 2) :
    (∃ A B : Hypergraph α β, G.IsSeparation A B ∧ separationOrder A B < θ ∧
      ((Z ∪ A.vertexSet) ∩ B.vertexSet).ncard ≤ 3 * θ - 3 ∧
      ((Z ∪ B.vertexSet) ∩ A.vertexSet).ncard ≤ 3 * θ - 3) ∨
    (∃ ℒ : Set (Hypergraph α β × Hypergraph α β),
      IsLocation G ℒ ∧ locationDesign G ℒ ∈ 𝒮 ∧
      ∀ p ∈ ℒ, (Z ∩ p.1.vertexSet).ncard ≤ separationOrder p.1 p.2 ∧
        separationOrder p.1 p.2 < θ) := by
  let 𝒯 : Set (Hypergraph α β × Hypergraph α β) :=
    {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
      (Z ∩ p.1.vertexSet).ncard ≤ separationOrder p.1 p.2}
  have hZ_fin : Z.Finite := G.vertexSet_finite.subset hZ_sub
  have hax2 : TangleAxiom2 G 𝒯 := by
    intro A₁ B₁ A₂ B₂ A₃ B₃ h1 h2 h3 hunion
    have hZ_union : Z = (Z ∩ A₁.vertexSet) ∪ (Z ∩ A₂.vertexSet) ∪ (Z ∩ A₃.vertexSet) := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff]
      refine ⟨fun hx ↦ ?_, fun h ↦ h.elim (fun h' ↦ h'.elim And.left And.left) And.left⟩
      have hxG : x ∈ (A₁ ∪ A₂ ∪ A₃).vertexSet := hunion.symm ▸ hZ_sub hx
      rcases hxG with (hx1 | hx2) | hx3
      · exact Or.inl (Or.inl ⟨hx, hx1⟩)
      · exact Or.inl (Or.inr ⟨hx, hx2⟩)
      · exact Or.inr ⟨hx, hx3⟩
    have h1_le : (Z ∩ A₁.vertexSet).ncard ≤ θ - 1 :=
      Nat.le_sub_one_of_lt (h1.2.2.trans_lt h1.2.1)
    have h2_le : (Z ∩ A₂.vertexSet).ncard ≤ θ - 1 :=
      Nat.le_sub_one_of_lt (h2.2.2.trans_lt h2.2.1)
    have h3_le : (Z ∩ A₃.vertexSet).ncard ≤ θ - 1 :=
      Nat.le_sub_one_of_lt (h3.2.2.trans_lt h3.2.1)
    have hcard_le : Z.ncard ≤ (Z ∩ A₁.vertexSet).ncard + (Z ∩ A₂.vertexSet).ncard +
        (Z ∩ A₃.vertexSet).ncard :=
      calc Z.ncard
        _ = ((Z ∩ A₁.vertexSet) ∪ (Z ∩ A₂.vertexSet) ∪ (Z ∩ A₃.vertexSet)).ncard :=
          congrArg Set.ncard hZ_union
        _ ≤ ((Z ∩ A₁.vertexSet) ∪ (Z ∩ A₂.vertexSet)).ncard + (Z ∩ A₃.vertexSet).ncard :=
          Set.ncard_union_le _ _
        _ ≤ (Z ∩ A₁.vertexSet).ncard + (Z ∩ A₂.vertexSet).ncard + (Z ∩ A₃.vertexSet).ncard :=
          Nat.add_le_add_right (Set.ncard_union_le _ _) _
    have : 3 * θ - 2 ≤ (θ - 1) + (θ - 1) + (θ - 1) := by
      rw [← hZ_card]
      exact hcard_le.trans (Nat.add_le_add (Nat.add_le_add h1_le h2_le) h3_le)
    omega
  have hax3 : TangleAxiom3 G 𝒯 := by
    intro A B hAB hV
    have hZ_eq : Z ∩ A.vertexSet = Z := by
      rw [hV, Set.inter_eq_self_of_subset_left hZ_sub]
    have hlt : Z.ncard < θ := by
      rw [← hZ_eq]
      exact hAB.2.2.trans_lt hAB.2.1
    omega
  by_cases hax1 : TangleAxiom1 G θ 𝒯
  · right
    have hTangle : IsTangle G θ 𝒯 :=
      ⟨hθ, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2.1, hax1, hax2, hax3⟩
    obtain ⟨ℒ, hloc, hℒ_sub, hdes⟩ := hperv le_rfl le_rfl hTangle
    exact ⟨ℒ, hloc, hdes, fun p hp ↦ ⟨(hℒ_sub hp).2.2, (hℒ_sub hp).2.1⟩⟩
  · left
    unfold TangleAxiom1 at hax1
    push Not at hax1
    obtain ⟨A, B, hsep, hord, hnotA, hnotB⟩ := hax1
    have hZA : separationOrder A B < (Z ∩ A.vertexSet).ncard := by
      by_contra! hle
      exact hnotA ⟨hsep, hord, hle⟩
    have hZB : separationOrder A B < (Z ∩ B.vertexSet).ncard := by
      rw [separationOrder_comm]
      by_contra! hle
      exact hnotB ⟨hsep.symm, by rwa [separationOrder_comm], hle⟩
    have hbound : ∀ X Y : Hypergraph α β, G.IsSeparation X Y →
        separationOrder X Y < (Z ∩ X.vertexSet).ncard →
        ((Z ∪ X.vertexSet) ∩ Y.vertexSet).ncard ≤ 3 * θ - 3 := by
      intro X Y hXY hlt
      have hset : (Z ∪ X.vertexSet) ∩ Y.vertexSet =
          (X ∩ Y).vertexSet ∪ (Z \ X.vertexSet) := by
        ext v
        simp only [inter_vertexSet, Set.mem_inter_iff, Set.mem_union,
          Set.mem_sdiff]
        constructor
        · rintro ⟨hvZ | hvX, hvY⟩
          · by_cases hvX : v ∈ X.vertexSet
            · exact Or.inl ⟨hvX, hvY⟩
            · exact Or.inr ⟨hvZ, hvX⟩
          · exact Or.inl ⟨hvX, hvY⟩
        · rintro (⟨hvX, hvY⟩ | ⟨hvZ, _⟩)
          · exact ⟨Or.inr hvX, hvY⟩
          · have hvG : v ∈ G.vertexSet := hZ_sub hvZ
            rw [← hXY.vertexSet_union] at hvG
            rcases hvG with hvX | hvY
            · exact ⟨Or.inr hvX, by contradiction⟩
            · exact ⟨Or.inl hvZ, hvY⟩
      have hle1 : ((Z ∪ X.vertexSet) ∩ Y.vertexSet).ncard ≤
          separationOrder X Y + (Z \ X.vertexSet).ncard := by
        rw [hset]
        exact Set.ncard_union_le _ _
      have hdisj_ZX : Disjoint (Z ∩ X.vertexSet) (Z \ X.vertexSet) :=
        Set.disjoint_iff_inter_eq_empty.2 (by ext; simp)
      have hZ_split : (Z ∩ X.vertexSet).ncard + (Z \ X.vertexSet).ncard = Z.ncard := by
        rw [← Set.ncard_union_eq hdisj_ZX
          (hZ_fin.subset Set.inter_subset_left) (hZ_fin.subset Set.sdiff_subset),
          Set.inter_union_sdiff]
      have hltZ : ((Z ∪ X.vertexSet) ∩ Y.vertexSet).ncard < 3 * θ - 2 := by
        calc ((Z ∪ X.vertexSet) ∩ Y.vertexSet).ncard
          _ ≤ separationOrder X Y + (Z \ X.vertexSet).ncard := hle1
          _ < (Z ∩ X.vertexSet).ncard + (Z \ X.vertexSet).ncard :=
            Nat.add_lt_add_right hlt _
          _ = 3 * θ - 2 := hZ_split.trans hZ_card
      omega
    exact ⟨A, B, hsep, hord, hbound A B hsep hZA,
      hbound B A hsep.symm (by rwa [separationOrder_comm])⟩

/-! ## Star-of-trees gluing construction for (11.3) -/

/-- Adjacency relation for the star-of-trees graph on `Option (Σ i : Fin k, ι i)`, gluing
disjoint trees `T i` by connecting the center `none` to `some ⟨i, r i⟩` for each `i`. -/
private def StarAdj {k : ℕ} {ι : Fin k → Type*} (T : ∀ i, SimpleGraph (ι i)) (r : ∀ i, ι i) :
    Option (Σ i, ι i) → Option (Σ i, ι i) → Prop
  | none, none => False
  | none, some ⟨i, u⟩ => u = r i
  | some ⟨i, u⟩, none => u = r i
  | some ⟨i, u⟩, some ⟨j, v⟩ => ∃ h : i = j, (T j).Adj (h ▸ u) v

/-- The star-of-trees simple graph on `Option (Σ i : Fin k, ι i)`. -/
private def StarTree {k : ℕ} {ι : Fin k → Type*} (T : ∀ i, SimpleGraph (ι i)) (r : ∀ i, ι i) :
    SimpleGraph (Option (Σ i, ι i)) where
  Adj := StarAdj T r
  symm := ⟨by
    rintro (_ | ⟨i, u⟩) (_ | ⟨j, v⟩) h
    · exact h
    · exact h
    · exact h
    · rcases h with ⟨rfl, hadj⟩
      exact ⟨rfl, hadj.symm⟩⟩
  loopless := ⟨by
    rintro (_ | ⟨i, u⟩) h
    · exact h
    · rcases h with ⟨h_eq, hadj⟩
      have : h_eq = rfl := Subsingleton.elim _ _
      subst this
      exact (T i).loopless.irrefl u hadj⟩

/-- The bag map on `Option (Σ i : Fin k, ι i)` assigning `τ₀` to `none` and `τ i u` to
`some ⟨i, u⟩`. -/
private def starBag {k : ℕ} {ι : Fin k → Type*} (τ₀ : Hypergraph α β)
    (τ : ∀ i, ι i → Hypergraph α β) : Option (Σ i, ι i) → Hypergraph α β
  | none => τ₀
  | some ⟨i, u⟩ => τ i u

/-- Embedding of `T i` into `StarTree T r` sending `u` to `some ⟨i, u⟩`. -/
private abbrev starInl {k : ℕ} {ι : Fin k → Type*} (T : ∀ i, SimpleGraph (ι i)) (r : ∀ i, ι i)
    (i : Fin k) : T i →g StarTree T r where
  toFun u := some ⟨i, u⟩
  map_rel' hadj := ⟨rfl, hadj⟩

private theorem starInl_injective {k : ℕ} {ι : Fin k → Type*} (T : ∀ i, SimpleGraph (ι i))
    (r : ∀ i, ι i) (i : Fin k) :
    Function.Injective (starInl T r i) := by
  intro u v h
  exact (Sigma.mk.inj_iff.1 (Option.some.inj h)).2 |> eq_of_heq

private theorem starTree_adj_none_r {k : ℕ} {ι : Fin k → Type*} (T : ∀ i, SimpleGraph (ι i))
    (r : ∀ i, ι i) (i : Fin k) :
    (StarTree T r).Adj none (some ⟨i, r i⟩) := by
  rfl

/-- Projection from `Option (Σ j, ι j)` onto `ι i` sending `some ⟨i, u⟩` to `u` and all other
vertices to `r i`. -/
private def starProj {k : ℕ} {ι : Fin k → Type*} (r : ∀ i, ι i) (i : Fin k) :
    Option (Σ j, ι j) → ι i
  | none => r i
  | some ⟨j, u⟩ => if h : j = i then h ▸ u else r i

@[simp]
private theorem starProj_none {k : ℕ} {ι : Fin k → Type*} (r : ∀ i, ι i) (i : Fin k) :
    starProj r i none = r i := rfl

@[simp]
private theorem starProj_some_self {k : ℕ} {ι : Fin k → Type*} (r : ∀ i, ι i) (i : Fin k)
  (u : ι i) :
    starProj r i (some ⟨i, u⟩) = u := by
  simp [starProj]

private theorem starProj_some_of_ne {k : ℕ} {ι : Fin k → Type*} (r : ∀ i, ι i) {i j : Fin k}
    (h : j ≠ i) (u : ι j) :
    starProj r i (some ⟨j, u⟩) = r i := by
  simp [starProj, h]

/-- If each `T i` is a tree, then `StarTree T r` is a tree. -/
private theorem starTree_isTree {k : ℕ} {ι : Fin k → Type*} {T : ∀ i, SimpleGraph (ι i)}
    {r : ∀ i, ι i} (hT : ∀ i, (T i).IsTree) :
    (StarTree T r).IsTree := by
  have hconn : (StarTree T r).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨none, ?_⟩
    rintro (_ | ⟨i, u⟩)
    · exact Reachable.refl _
    · have h1 : (StarTree T r).Reachable none (some ⟨i, r i⟩) :=
        (starTree_adj_none_r T r i).reachable
      obtain ⟨p⟩ := (hT i).connected (r i) u
      exact h1.trans ⟨p.map (starInl T r i)⟩
  refine ⟨hconn, isAcyclic_iff_forall_adj_isBridge.2 ?_⟩
  intro a b hadj
  rw [isBridge_iff]
  -- Helper: if `P` is invariant under `H.Adj`, `P a` and `¬ P b`, then `¬ H.Reachable a b`.
  have not_reach_of_inv : ∀ {H : SimpleGraph (Option (Σ i, ι i))}
      (P : Option (Σ i, ι i) → Prop) {x y : Option (Σ i, ι i)},
      (∀ u v, H.Adj u v → P u → P v) → P x → ¬ P y → ¬ H.Reachable x y := by
    intro H P x y hinv hx hy ⟨w⟩
    apply hy
    clear hy
    induction w with
    | nil => exact hx
    | cons hstep _ ih => exact ih (hinv _ _ hstep hx)
  rcases a with _ | ⟨i, u⟩ <;> rcases b with _ | ⟨j, v⟩
  · exact hadj.elim
  · change v = r j at hadj
    subst hadj
    let P : Option (Σ l, ι l) → Prop
      | none => False
      | some ⟨l, _⟩ => l = j
    intro hr
    refine not_reach_of_inv (x := some ⟨j, r j⟩) (y := none) P ?_ rfl not_false hr.symm
    rintro (_ | ⟨l₁, w₁⟩) (_ | ⟨l₂, w₂⟩) hstep hl₁
    · exact hl₁.elim
    · exact hl₁.elim
    · change l₁ = j at hl₁
      subst hl₁
      rcases deleteEdges_adj.1 hstep with ⟨hw₁, hne⟩
      change w₁ = r l₁ at hw₁
      subst hw₁
      exact (hne Sym2.eq_swap).elim
    · rcases (deleteEdges_adj.1 hstep).1 with ⟨rfl, _⟩
      exact hl₁
  · change u = r i at hadj
    subst hadj
    let P : Option (Σ l, ι l) → Prop
      | none => False
      | some ⟨l, _⟩ => l = i
    refine not_reach_of_inv P ?_ (rfl : P (some ⟨i, r i⟩)) (not_false : ¬ P none)
    rintro (_ | ⟨l₁, w₁⟩) (_ | ⟨l₂, w₂⟩) hstep hl₁
    · exact hl₁.elim
    · exact hl₁.elim
    · change l₁ = i at hl₁
      subst hl₁
      rcases deleteEdges_adj.1 hstep with ⟨hw₁, hne⟩
      change w₁ = r l₁ at hw₁
      subst hw₁
      exact (hne rfl).elim
    · rcases (deleteEdges_adj.1 hstep).1 with ⟨rfl, _⟩
      exact hl₁
  · rcases hadj with ⟨rfl, hadj_uv⟩
    rintro ⟨w⟩
    have hreach_proj : ∀ {x y : Option (Σ l, ι l)},
        ((StarTree T r).deleteEdges {s(some ⟨i, u⟩, some ⟨i, v⟩)}).Walk x y →
        ((T i).deleteEdges {s(u, v)}).Reachable (starProj r i x) (starProj r i y) := by
      intro x y q
      induction q with
      | nil => exact Reachable.refl _
      | @cons a b c hstep _ ih =>
        refine Reachable.trans ?_ ih
        rcases deleteEdges_adj.1 hstep with ⟨hab, hne⟩
        rcases a with _ | ⟨l₁, w₁⟩ <;> rcases b with _ | ⟨l₂, w₂⟩
        · exact hab.elim
        · change w₂ = r l₂ at hab
          subst hab
          by_cases hl : l₂ = i
          · subst hl; simp
          · simp [starProj_some_of_ne r hl]
        · change w₁ = r l₁ at hab
          subst hab
          by_cases hl : l₁ = i
          · subst hl; simp
          · simp [starProj_some_of_ne r hl]
        · rcases hab with ⟨rfl, hadj_w⟩
          by_cases hl : l₁ = i
          · subst hl
            simp only [starProj_some_self]
            refine (deleteEdges_adj.2 ⟨hadj_w, ?_⟩).reachable
            intro heq
            apply hne
            rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · exact Sym2.eq_swap
          · simp [starProj_some_of_ne r hl]
    have huv := hreach_proj w
    simp only [starProj_some_self] at huv
    exact not_reachable_deleteEdges (hT i) hadj_uv huv

private theorem onTreePath_of_mem_support {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {x y z : V} {p : G.Walk x y} (hp : p.IsPath) (hz : z ∈ p.support) :
    OnTreePath G x y z := by
  intro q hq
  obtain ⟨_, _, huniq⟩ := hG.existsUnique_path x y
  rwa [(huniq q hq).trans (huniq p hp).symm]

private theorem onTreePath_star_some_some {k : ℕ} {ι : Fin k → Type*}
    {T : ∀ i, SimpleGraph (ι i)} {r : ∀ i, ι i} (hT : ∀ i, (T i).IsTree)
    {i : Fin k} {u₁ u₂ : ι i} {t : Option (Σ j, ι j)}
    (hon : OnTreePath (StarTree T r) (some ⟨i, u₁⟩) (some ⟨i, u₂⟩) t) :
    ∃ w : ι i, t = some ⟨i, w⟩ ∧ OnTreePath (T i) u₁ u₂ w := by
  obtain ⟨q₀, hq₀, _⟩ := (hT i).existsUnique_path u₁ u₂
  have hmem₀ := hon (q₀.map (starInl T r i)) (hq₀.map (starInl_injective T r i))
  rw [Walk.support_map, List.mem_map] at hmem₀
  obtain ⟨w, _, rfl⟩ := hmem₀
  refine ⟨w, rfl, fun q hq ↦ ?_⟩
  have hmem := hon (q.map (starInl T r i)) (hq.map (starInl_injective T r i))
  rw [Walk.support_map, List.mem_map] at hmem
  obtain ⟨w', hw', heq⟩ := hmem
  exact starInl_injective T r i heq ▸ hw'

private theorem onTreePath_star_none_some {k : ℕ} {ι : Fin k → Type*}
    {T : ∀ i, SimpleGraph (ι i)} {r : ∀ i, ι i} (hT : ∀ i, (T i).IsTree)
    {i : Fin k} {u : ι i} {t : Option (Σ j, ι j)}
    (hon : OnTreePath (StarTree T r) none (some ⟨i, u⟩) t) :
    t = none ∨ ∃ w : ι i, t = some ⟨i, w⟩ ∧ OnTreePath (T i) (r i) u w := by
  have hpath : ∀ (q : (T i).Walk (r i) u), q.IsPath →
      (Walk.cons (starTree_adj_none_r T r i) (q.map (starInl T r i))).IsPath := by
    intro q hq
    rw [Walk.cons_isPath_iff]
    refine ⟨hq.map (starInl_injective T r i), ?_⟩
    rw [Walk.support_map, List.mem_map]
    rintro ⟨w, _, h⟩
    nomatch h
  obtain ⟨q₀, hq₀, _⟩ := (hT i).existsUnique_path (r i) u
  have hmem₀ := hon _ (hpath q₀ hq₀)
  simp only [Walk.support_cons, Walk.support_map, List.mem_cons, List.mem_map] at hmem₀
  rcases hmem₀ with rfl | ⟨w, _, rfl⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨w, rfl, fun q hq ↦ ?_⟩
    have hmem := hon _ (hpath q hq)
    simp only [Walk.support_cons, Walk.support_map, List.mem_cons, List.mem_map,
       reduceCtorEq, false_or] at hmem
    obtain ⟨w', hw', heq⟩ := hmem
    exact starInl_injective T r i heq ▸ hw'

private theorem none_mem_support_of_walk_ne {k : ℕ} {ι : Fin k → Type*}
    {T : ∀ i, SimpleGraph (ι i)} {r : ∀ i, ι i}
    {i j : Fin k} (hij : i ≠ j) {u₁ : ι i} {u₂ : ι j}
    (w : (StarTree T r).Walk (some ⟨i, u₁⟩) (some ⟨j, u₂⟩)) :
    none ∈ w.support := by
  have haux : ∀ {a b : Option (Σ l, ι l)} (q : (StarTree T r).Walk a b),
      none ∉ q.support → ∀ {l : Fin k} (x : ι l), a = some ⟨l, x⟩ →
      ∃ y : ι l, b = some ⟨l, y⟩ := by
    intro a b q hnot
    induction q with
    | nil =>
      intro l x ha
      exact ⟨x, ha⟩
    | @cons a a' b hstep q' ih =>
      intro l x ha
      simp only [Walk.support_cons, List.mem_cons, not_or] at hnot
      subst ha
      rcases a' with _ | ⟨l', x'⟩
      · exact (hnot.2 (Walk.start_mem_support q')).elim
      · rcases hstep with ⟨rfl, _⟩
        exact ih hnot.2 x' rfl
  by_contra hnot
  obtain ⟨y, hy⟩ := haux w hnot u₁ rfl
  exact hij (Sigma.mk.inj_iff.1 (Option.some.inj hy)).1.symm

/-- Star-of-trees gluing lemma for **Graph Minors X, (11.3)**:
gluing tree-decompositions `(T i, τ i)` of `A i ≤ G` around a central bag `τ₀ ≤ G` produces a
tree-decomposition `(StarTree T r, starBag τ₀ τ)` of `G` with the expected vertex designs. -/
private theorem isTreeDecomposition_starTree {k : ℕ} {ι : Fin k → Type*} [∀ i, Fintype (ι i)]
    {G : Hypergraph α β} {A : Fin k → Hypergraph α β} {Z_sub : Fin k → Set α}
    {T : ∀ i, SimpleGraph (ι i)} {τ : ∀ i, ι i → Hypergraph α β} {r : ∀ i, ι i}
    {τ₀ : Hypergraph α β}
    (hA_le : ∀ i, A i ≤ G) (hτ₀_le : τ₀ ≤ G)
    (hTD : ∀ i, IsTreeDecomposition (A i) (T i) (τ i))
    (hr_sub : ∀ i, Z_sub i ⊆ (τ i (r i)).vertexSet)
    (hZ_sub_eq : ∀ i, τ₀.vertexSet ∩ (A i).vertexSet = Z_sub i)
    (hunion_V : τ₀.vertexSet ∪ (⋃ i, (A i).vertexSet) = G.vertexSet)
    (hunion_E : τ₀.edgeSet ∪ (⋃ i, (A i).edgeSet) = G.edgeSet)
    (hdisj_E0 : ∀ i, Disjoint τ₀.edgeSet (A i).edgeSet)
    (hdisj_E : ∀ i j, i ≠ j → Disjoint (A i).edgeSet (A j).edgeSet)
    (hinter_V : ∀ i j, i ≠ j → (A i).vertexSet ∩ (A j).vertexSet ⊆ τ₀.vertexSet) :
    IsTreeDecomposition G (StarTree T r) (starBag τ₀ τ) ∧
      vertexDesign (StarTree T r) (starBag τ₀ τ) none = (τ₀, Set.range Z_sub) ∧
      (∀ i (u : ι i), u ≠ r i →
        vertexDesign (StarTree T r) (starBag τ₀ τ) (some ⟨i, u⟩) =
          vertexDesign (T i) (τ i) u) ∧
      (∀ i,
        vertexDesign (StarTree T r) (starBag τ₀ τ) (some ⟨i, r i⟩) =
          designExtension (vertexDesign (T i) (τ i) (r i)) (Z_sub i)) := by
  have hTree : (StarTree T r).IsTree := starTree_isTree fun i ↦ (hTD i).isTree
  have hbag_le : ∀ t, starBag τ₀ τ t ≤ G := by
    rintro (_ | ⟨i, u⟩)
    · exact hτ₀_le
    · exact ((hTD i).le u).trans (hA_le i)
  have hbag_disj : ∀ ⦃t t'⦄, t ≠ t' → (starBag τ₀ τ t ∩ starBag τ₀ τ t').edgeSet = ∅ := by
    rintro (_ | ⟨i, u⟩) (_ | ⟨j, v⟩) hne
    · exact (hne rfl).elim
    · rw [inter_edgeSet, ← Set.disjoint_iff_inter_eq_empty]
      exact (hdisj_E0 j).mono_right ((hTD j).le v).edgeSet_subset
    · rw [inter_edgeSet, ← Set.disjoint_iff_inter_eq_empty]
      exact (hdisj_E0 i).symm.mono_left ((hTD i).le u).edgeSet_subset
    · by_cases hij : i = j
      · subst hij
        have huv : u ≠ v := fun h ↦ hne (h ▸ rfl)
        exact (hTD i).edgeSet_inter_eq huv
      · rw [inter_edgeSet, ← Set.disjoint_iff_inter_eq_empty]
        exact (hdisj_E i j hij).mono ((hTD i).le u).edgeSet_subset ((hTD j).le v).edgeSet_subset
  have hTD_star : IsTreeDecomposition G (StarTree T r) (starBag τ₀ τ) := by
    refine ⟨hTree, hbag_le, ?_, hbag_disj, ?_⟩
    · refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (biUnion_le_of_le fun t _ ↦ hbag_le t) le_rfl ?_ ?_
      · rw [← hunion_V]
        ext x
        simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_prop, Set.mem_union,
          Option.exists, Sigma.exists, starBag]
        refine ⟨?_, ?_⟩
        · rintro (hx | ⟨i, u, hx⟩)
          · exact Or.inl hx
          · exact Or.inr ⟨i, ((hTD i).le u).vertexSet_subset hx⟩
        · rintro (hx | ⟨i, hx⟩)
          · exact Or.inl hx
          · rw [← (hTD i).biUnion_eq] at hx
            simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_prop] at hx
            obtain ⟨u, hu⟩ := hx
            exact Or.inr ⟨i, u, hu⟩
      · rw [← hunion_E]
        ext e
        simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_prop, Set.mem_union,
          Option.exists, Sigma.exists, starBag]
        refine ⟨?_, ?_⟩
        · rintro (he | ⟨i, u, he⟩)
          · exact Or.inl he
          · exact Or.inr ⟨i, ((hTD i).le u).edgeSet_subset he⟩
        · rintro (he | ⟨i, he⟩)
          · exact Or.inl he
          · rw [← (hTD i).biUnion_eq] at he
            simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, exists_prop] at he
            obtain ⟨u, hu⟩ := he
            exact Or.inr ⟨i, u, hu⟩
    · -- Helper for path between `none` and `some ⟨i, u⟩`:
      have hnone_some : ∀ (i : Fin k) (u : ι i) (t' : Option (Σ l, ι l)),
          OnTreePath (StarTree T r) none (some ⟨i, u⟩) t' →
          (τ₀ ∩ τ i u).vertexSet ⊆ (starBag τ₀ τ t').vertexSet := by
        intro i u t' hon x ⟨hx0, hxu⟩
        rcases onTreePath_star_none_some (fun l ↦ (hTD l).isTree) hon with rfl | ⟨w, rfl, hon_w⟩
        · exact hx0
        · have hxr : x ∈ (τ i (r i)).vertexSet := by
            apply hr_sub i
            rw [← hZ_sub_eq i]
            exact ⟨hx0, ((hTD i).le u).vertexSet_subset hxu⟩
          exact ((hTD i).inter_le hon_w).vertexSet_subset ⟨hxr, hxu⟩
      intro t t' t'' hon
      by_cases htt'' : t = t''
      · subst htt''
        have ht' : t' = t := by
          have := hon Walk.nil Walk.IsPath.nil
          simpa using this
        subst ht'
        exact ⟨Set.inter_subset_left, Set.inter_subset_left, fun e ⟨he, _⟩ ↦ by
          ext v; simp [Hypergraph.ends, inter_inc]⟩
      · refine le_of_edgeSet_eq_empty (hbag_disj htt'') ?_
        rcases t with _ | ⟨i, u₁⟩ <;> rcases t'' with _ | ⟨j, u₂⟩
        · exact (htt'' rfl).elim
        · exact hnone_some j u₂ t' hon
        · rw [inter_vertexSet, Set.inter_comm]
          exact hnone_some i u₁ t' (GraphMinor.TreePath.symm hon)
        · by_cases hij : i = j
          · subst hij
            obtain ⟨w, rfl, hon_w⟩ :=
              onTreePath_star_some_some (fun l ↦ (hTD l).isTree) hon
            exact ((hTD i).inter_le hon_w).vertexSet_subset
          · intro x ⟨hx1, hx2⟩
            have hx0 : x ∈ τ₀.vertexSet :=
              hinter_V i j hij ⟨((hTD i).le u₁).vertexSet_subset hx1,
                ((hTD j).le u₂).vertexSet_subset hx2⟩
            classical
            obtain ⟨p, hp, _⟩ := hTree.existsUnique_path (some ⟨i, u₁⟩) (some ⟨j, u₂⟩)
            have hnone : none ∈ p.support := none_mem_support_of_walk_ne hij p
            have ht'_mem : t' ∈ p.support := hon p hp
            rw [← Walk.take_spec p hnone, Walk.support_append] at ht'_mem
            rcases List.mem_append.1 ht'_mem with ht'1 | ht'2
            · have hon1 : OnTreePath (StarTree T r) (some ⟨i, u₁⟩) none t' :=
                onTreePath_of_mem_support hTree (hp.takeUntil hnone) ht'1
              exact hnone_some i u₁ t' (GraphMinor.TreePath.symm hon1) ⟨hx0, hx1⟩
            · have hon2 : OnTreePath (StarTree T r) none (some ⟨j, u₂⟩) t' :=
                onTreePath_of_mem_support hTree (hp.dropUntil hnone)
                  (List.tail_subset _ ht'2)
              exact hnone_some j u₂ t' hon2 ⟨hx0, hx2⟩
  have hroot_inter : ∀ i, (τ₀ ∩ τ i (r i)).vertexSet = Z_sub i := by
    intro i
    apply Set.Subset.antisymm
    · rw [← hZ_sub_eq i]
      exact Set.inter_subset_inter_right _ ((hTD i).le (r i)).vertexSet_subset
    · refine Set.subset_inter ?_ (hr_sub i)
      rw [← hZ_sub_eq i]
      exact Set.inter_subset_left
  refine ⟨hTD_star, ?_, ?_, ?_⟩
  · -- vertexDesign at `none`
    ext : 1
    · rfl
    · ext X
      simp only [vertexDesign, starBag, Set.mem_ofPred_eq, Set.mem_range, Option.exists,
        Sigma.exists]
      constructor
      · rintro (⟨h, _⟩ | ⟨i, u, rfl : u = r i, rfl⟩)
        · exact h.elim
        · exact ⟨i, (hroot_inter i).symm⟩
      · rintro ⟨i, rfl⟩
        exact Or.inr ⟨i, r i, rfl, (hroot_inter i).symm⟩
  · -- vertexDesign at `some ⟨i, u⟩` for `u ≠ r i`
    intro i u hu
    ext : 1
    · rfl
    · ext X
      simp only [vertexDesign, starBag, Set.mem_ofPred_eq, Option.exists, Sigma.exists]
      constructor
      · rintro (⟨h : u = r i, _⟩ | ⟨j, v, ⟨rfl, hadj⟩, rfl⟩)
        · exact (hu h).elim
        · exact ⟨v, hadj, rfl⟩
      · rintro ⟨v, hadj, rfl⟩
        exact Or.inr ⟨i, v, ⟨rfl, hadj⟩, rfl⟩
  · -- vertexDesign at `some ⟨i, r i⟩`
    intro i
    ext : 1
    · rfl
    · ext X
      simp only [vertexDesign, designExtension, starBag, Set.mem_ofPred_eq, Set.mem_insert_iff,
        Option.exists, Sigma.exists]
      constructor
      · rintro (⟨_, rfl⟩ | ⟨j, v, ⟨rfl, hadj⟩, rfl⟩)
        · left
          rw [inter_vertexSet, Set.inter_comm, ← inter_vertexSet, hroot_inter i]
        · exact Or.inr ⟨v, hadj, rfl⟩
      · rintro (rfl | ⟨v, hadj, rfl⟩)
        · refine Or.inl ⟨rfl, ?_⟩
          rw [inter_vertexSet, Set.inter_comm, ← inter_vertexSet, hroot_inter i]
        · exact Or.inr ⟨i, v, ⟨rfl, hadj⟩, rfl⟩

/-! ## Proof of Graph Minors X, (11.3) and (11.1) -/

private abbrev HasRootedDecomposition (G : Hypergraph α β)
    (𝒮 : Set (Design α β)) (Z : Set α) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (r : ι),
    IsTreeDecompositionOver G 𝒮 T τ ∧
    Z ⊆ (τ r).vertexSet ∧ designExtension (vertexDesign T τ r) Z ∈ 𝒮

private abbrev RootedDecompositionStep (𝒮 : Set (Design α β)) (θ n : ℕ) : Prop :=
  ∀ (m : ℕ), m < n → ∀ (G : Hypergraph α β) (Z : Set α),
    G.vertexSet.ncard = m → IsPervasive G θ 𝒮 → Z ⊆ G.vertexSet → Z.ncard ≤ 3 * θ - 2 →
    HasRootedDecomposition G (enlargementClass 𝒮 (3 * θ - 2) ∪
      smallDesignClass (4 * θ - 3)) Z

private theorem glueRootedDecompositions {𝒮' : Set (Design α β)}
    {G' : Hypergraph α β} {Z' : Set α} {k : ℕ}
    {A : Fin k → Hypergraph α β} {Z_sub : Fin k → Set α} {τ₀ : Hypergraph α β} :
    (∀ i, A i ≤ G') → τ₀ ≤ G' →
    (∀ i, ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (r : ι),
      IsTreeDecompositionOver (A i) 𝒮' T τ ∧
      Z_sub i ⊆ (τ r).vertexSet ∧
      designExtension (vertexDesign T τ r) (Z_sub i) ∈ 𝒮') →
    (∀ i, τ₀.vertexSet ∩ (A i).vertexSet = Z_sub i) →
    τ₀.vertexSet ∪ (⋃ i, (A i).vertexSet) = G'.vertexSet →
    τ₀.edgeSet ∪ (⋃ i, (A i).edgeSet) = G'.edgeSet →
    (∀ i, Disjoint τ₀.edgeSet (A i).edgeSet) →
    (∀ i j, i ≠ j → Disjoint (A i).edgeSet (A j).edgeSet) →
    (∀ i j, i ≠ j → (A i).vertexSet ∩ (A j).vertexSet ⊆ τ₀.vertexSet) →
    Z' ⊆ τ₀.vertexSet →
    (τ₀, Set.range Z_sub) ∈ 𝒮' →
    designExtension (τ₀, Set.range Z_sub) Z' ∈ 𝒮' →
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (t₀ : ι),
      IsTreeDecompositionOver G' 𝒮' T τ ∧
      Z' ⊆ (τ t₀).vertexSet ∧
      designExtension (vertexDesign T τ t₀) Z' ∈ 𝒮' := by
  classical
  intro hA_le hτ₀_le hex hZ_sub_eq hunion_V hunion_E
    hdisj_E0 hdisj_E hinter_V hZ'_sub hdes0 hdes0_ext
  choose ι hfin T τ r hTD hr_sub hr_ext using hex
  obtain ⟨hTD_star, hdes_none, hdes_ne, hdes_r⟩ :=
    isTreeDecomposition_starTree hA_le hτ₀_le (fun i ↦ (hTD i).1) hr_sub hZ_sub_eq
      hunion_V hunion_E hdisj_E0 hdisj_E hinter_V
  have hover_star : IsTreeDecompositionOver G' 𝒮' (StarTree T r) (starBag τ₀ τ) := by
    refine ⟨hTD_star, ?_⟩
    rintro (_ | ⟨i, u⟩)
    · rw [hdes_none]; exact hdes0
    · by_cases hu : u = r i
      · subst hu; rw [hdes_r]; exact hr_ext i
      · rw [hdes_ne i u hu]; exact (hTD i).2 u
  let e := Fintype.equivFin (Option (Σ i : Fin k, ι i))
  refine ⟨Fin (Fintype.card (Option (Σ i : Fin k, ι i))), inferInstance,
    (StarTree T r).map e.toEmbedding, starBag τ₀ τ ∘ e.symm, e none,
    hover_star.relabel e, ?_, ?_⟩
  · simpa [starBag] using hZ'_sub
  · rw [vertexDesign_map, hdes_none]
    exact hdes0_ext

private theorem rootedDecomposition_of_lowOrderSeparation {G' : Hypergraph α β} {θ n : ℕ}
    {𝒮 : Set (Design α β)} {Z'' : Set α}
    (hθ : 1 ≤ θ) (hn : G'.vertexSet.ncard = n) (hperv' : IsPervasive G' θ 𝒮)
    (hZ''_sub : Z'' ⊆ G'.vertexSet) (hZ''_card : Z''.ncard = 3 * θ - 2)
    (ih : RootedDecompositionStep 𝒮 θ n)
    {A₁ A₂ : Hypergraph α β} (hsep : G'.IsSeparation A₁ A₂)
    (hord : separationOrder A₁ A₂ < θ)
    (hcard2 : ((Z'' ∪ A₁.vertexSet) ∩ A₂.vertexSet).ncard ≤ 3 * θ - 3)
    (hcard1 : ((Z'' ∪ A₂.vertexSet) ∩ A₁.vertexSet).ncard ≤ 3 * θ - 3) :
    HasRootedDecomposition G'
      (enlargementClass 𝒮 (3 * θ - 2) ∪ smallDesignClass (4 * θ - 3)) Z'' := by
  classical
  let 𝒮' : Set (Design α β) := enlargementClass 𝒮 (3 * θ - 2) ∪ smallDesignClass (4 * θ - 3)
  let A : Fin 2 → Hypergraph α β := fun i ↦ if i = 0 then A₁ else A₂
  let Z_sub : Fin 2 → Set α := fun i ↦
    if i = 0 then (Z'' ∪ A₂.vertexSet) ∩ A₁.vertexSet
    else (Z'' ∪ A₁.vertexSet) ∩ A₂.vertexSet
  let τ₀ : Hypergraph α β :=
    edgelessSubhypergraph G' (Z'' ∪ (A₁ ∩ A₂).vertexSet)
  have hτ₀_V : τ₀.vertexSet = Z'' ∪ (A₁ ∩ A₂).vertexSet :=
    edgelessSubhypergraph_vertexSet G'
      (Set.union_subset hZ''_sub
        (Set.inter_subset_left.trans hsep.left_le.vertexSet_subset))
  have hA_le : ∀ i, A i ≤ G' := by
    intro i; fin_cases i
    · exact hsep.left_le
    · exact hsep.right_le
  have hZ_sub_eq : ∀ i, τ₀.vertexSet ∩ (A i).vertexSet = Z_sub i := by
    intro i; fin_cases i
    · ext x
      simp only [hτ₀_V, A, Z_sub, inter_vertexSet, Fin.zero_eta, ↓reduceIte,
        Set.mem_inter_iff, Set.mem_union]
      tauto
    · ext x
      simp only [hτ₀_V, A, Z_sub, inter_vertexSet, Fin.mk_one, one_ne_zero, ↓reduceIte,
        Set.mem_inter_iff, Set.mem_union]
      tauto
  have hex_ind : ∀ i : Fin 2,
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (r : ι),
        IsTreeDecompositionOver (A i) 𝒮' T τ ∧
        Z_sub i ⊆ (τ r).vertexSet ∧
        designExtension (vertexDesign T τ r) (Z_sub i) ∈ 𝒮' := by
    intro i
    have hZi_sub : Z_sub i ⊆ (A i).vertexSet := by
      fin_cases i <;> simp [Z_sub, A]
    have hZi_card : (Z_sub i).ncard ≤ 3 * θ - 3 := by
      fin_cases i
      · exact hcard1
      · exact hcard2
    have hAi_lt : (A i).vertexSet.ncard < n := by
      rw [← hn]
      refine Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.2
        ⟨(hA_le i).vertexSet_subset, fun hV_eq ↦ ?_⟩) G'.vertexSet_finite
      have hZ''_in_Zi : Z'' ⊆ Z_sub i := by
        rw [← hZ_sub_eq i, hV_eq, hτ₀_V]
        exact Set.subset_inter Set.subset_union_left hZ''_sub
      have hZ''_le : Z''.ncard ≤ (Z_sub i).ncard :=
        Set.ncard_le_ncard hZ''_in_Zi ((A i).vertexSet_finite.subset hZi_sub)
      omega
    exact ih (A i).vertexSet.ncard hAi_lt (A i) (Z_sub i) rfl
      (hperv'.mono (hA_le i)) hZi_sub (by omega)
  have hτ₀_card : τ₀.vertexSet.ncard ≤ 4 * θ - 3 := by
    rw [hτ₀_V]
    have h1 : (Z'' ∪ (A₁ ∩ A₂).vertexSet).ncard ≤
        Z''.ncard + separationOrder A₁ A₂ := Set.ncard_union_le _ _
    omega
  have hdes0_isDesign : IsDesign (τ₀, Set.range Z_sub) := by
    rintro X ⟨i, rfl⟩
    rw [← hZ_sub_eq i]
    exact Set.inter_subset_left
  have hdes0_ext_isDesign : IsDesign (designExtension (τ₀, Set.range Z_sub) Z'') := by
    rintro X (rfl | ⟨i, rfl⟩)
    · change X ⊆ τ₀.vertexSet
      rw [hτ₀_V]; exact Set.subset_union_left
    · change Z_sub i ⊆ τ₀.vertexSet
      rw [← hZ_sub_eq i]; exact Set.inter_subset_left
  refine glueRootedDecompositions (𝒮' := 𝒮') hA_le (edgelessSubhypergraph_le G' _) hex_ind
    hZ_sub_eq ?_ ?_ ?_ ?_ ?_
    (by rw [hτ₀_V]; exact Set.subset_union_left)
    (Or.inr ⟨hdes0_isDesign, hτ₀_card⟩)
    (Or.inr ⟨hdes0_ext_isDesign, hτ₀_card⟩)
  · have hunion_A : (⋃ i, (A i).vertexSet) = G'.vertexSet := by
      rw [← hsep.vertexSet_union]
      ext x
      simp only [Set.mem_iUnion, Fin.exists_fin_two, A, ↓reduceIte, one_ne_zero,
        Set.mem_union]
    rw [hunion_A, Set.union_eq_right.2 (edgelessSubhypergraph_le G' _).vertexSet_subset]
  · rw [edgelessSubhypergraph_edgeSet, Set.empty_union, ← hsep.edgeSet_union]
    ext e
    simp only [Set.mem_iUnion, Fin.exists_fin_two, A, ↓reduceIte, one_ne_zero,
      Set.mem_union]
  · intro i
    rw [edgelessSubhypergraph_edgeSet]
    exact disjoint_bot_left
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint A₁.edgeSet A₂.edgeSet
      exact Set.disjoint_iff_inter_eq_empty.2 hsep.edgeSet_inter_eq
    · change Disjoint A₂.edgeSet A₁.edgeSet
      exact (Set.disjoint_iff_inter_eq_empty.2 hsep.edgeSet_inter_eq).symm
    · exact (hij rfl).elim
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change (A₁ ∩ A₂).vertexSet ⊆ τ₀.vertexSet
      rw [hτ₀_V]; exact Set.subset_union_right
    · change A₂.vertexSet ∩ A₁.vertexSet ⊆ τ₀.vertexSet
      rw [hτ₀_V, Set.inter_comm]; exact Set.subset_union_right
    · exact (hij rfl).elim

private theorem rootedDecomposition_of_location {G' : Hypergraph α β} {θ n : ℕ}
    {𝒮 : Set (Design α β)} {Z'' : Set α}
    (hθ : 1 ≤ θ) (hn : G'.vertexSet.ncard = n) (hperv' : IsPervasive G' θ 𝒮)
    (hZ''_sub : Z'' ⊆ G'.vertexSet) (hZ''_card : Z''.ncard = 3 * θ - 2)
    (ih : RootedDecompositionStep 𝒮 θ n)
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hloc : IsLocation G' ℒ)
    (hdes_ℒ : locationDesign G' ℒ ∈ 𝒮)
    (hℒ_bound : ∀ p ∈ ℒ, (Z'' ∩ p.1.vertexSet).ncard ≤ separationOrder p.1 p.2 ∧
      separationOrder p.1 p.2 < θ) :
    HasRootedDecomposition G'
      (enlargementClass 𝒮 (3 * θ - 2) ∪ smallDesignClass (4 * θ - 3)) Z'' := by
  classical
  let 𝒮' : Set (Design α β) := enlargementClass 𝒮 (3 * θ - 2) ∪ smallDesignClass (4 * θ - 3)
  have hℒ_fin : ℒ.Finite := hloc.finite
  let k := hℒ_fin.toFinset.card
  let eℒ : Fin k ≃ ℒ :=
    (Finset.equivFin hℒ_fin.toFinset).symm.trans
      (Equiv.subtypeEquivRight fun _ ↦ hℒ_fin.mem_toFinset)
  let A : Fin k → Hypergraph α β := fun i ↦ (eℒ i).1.1
  let B : Fin k → Hypergraph α β := fun i ↦ (eℒ i).1.2
  let Z_sub : Fin k → Set α := fun i ↦ (Z'' ∪ (B i).vertexSet) ∩ (A i).vertexSet
  let H₀ : Hypergraph α β := locationCore G' ℒ
  let τ₀ : Hypergraph α β := addVertices G' H₀ Z''
  have hH₀_le : H₀ ≤ G' := locationCore_le fun _ hp ↦ hloc.isSeparation hp
  have hτ₀_le : τ₀ ≤ G' := addVertices_le hH₀_le Z''
  have hτ₀_V : τ₀.vertexSet = H₀.vertexSet ∪ Z'' := addVertices_vertexSet hZ''_sub
  have hsep_i : ∀ i : Fin k, G'.IsSeparation (A i) (B i) :=
    fun i ↦ hloc.isSeparation (eℒ i).2
  have hA_le : ∀ i, A i ≤ G' := fun i ↦ (hsep_i i).left_le
  have hleft_le_right : ∀ i j : Fin k, i ≠ j → A i ≤ B j :=
    fun i j hij ↦ hloc.left_le_right (eℒ i).2 (eℒ j).2
      (fun h ↦ hij (eℒ.injective (Subtype.ext h)))
  have hH₀_inter_A : ∀ i : Fin k, H₀.vertexSet ∩ (A i).vertexSet =
      (A i ∩ B i).vertexSet := by
    intro i
    ext x
    simp only [H₀, locationCore, inter_vertexSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨_, hall⟩, hxA⟩
      exact ⟨hxA, hall (eℒ i).1 (eℒ i).2⟩
    · rintro ⟨hxA, hxB⟩
      refine ⟨⟨(hA_le i).vertexSet_subset hxA, fun p hp ↦ ?_⟩, hxA⟩
      obtain ⟨j, hj⟩ := eℒ.surjective ⟨p, hp⟩
      have hp_eq : p = (eℒ j).1 := congrArg Subtype.val hj.symm
      rw [hp_eq]
      by_cases hij : i = j
      · subst hij; exact hxB
      · exact (hleft_le_right i j hij).vertexSet_subset hxA
  have hZ_sub_eq : ∀ i, τ₀.vertexSet ∩ (A i).vertexSet = Z_sub i := by
    intro i
    rw [hτ₀_V, Set.union_inter_distrib_right, hH₀_inter_A i]
    ext x
    simp only [Z_sub, inter_vertexSet, Set.mem_union, Set.mem_inter_iff]
    tauto
  have hex_ind : ∀ i : Fin k,
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (r : ι),
        IsTreeDecompositionOver (A i) 𝒮' T τ ∧
        Z_sub i ⊆ (τ r).vertexSet ∧
        designExtension (vertexDesign T τ r) (Z_sub i) ∈ 𝒮' := by
    intro i
    have hZi_sub : Z_sub i ⊆ (A i).vertexSet := Set.inter_subset_right
    obtain ⟨hZA_le, hord_lt⟩ :
        (Z'' ∩ (A i).vertexSet).ncard ≤ separationOrder (A i) (B i) ∧
        separationOrder (A i) (B i) < θ := hℒ_bound (eℒ i).1 (eℒ i).2
    have hZi_eq : Z_sub i = (Z'' ∩ (A i).vertexSet) ∪ (A i ∩ B i).vertexSet := by
      ext x
      simp only [Z_sub, inter_vertexSet, Set.mem_inter_iff, Set.mem_union]
      tauto
    have hZi_card : (Z_sub i).ncard ≤ 3 * θ - 2 := by
      have h1 : (Z_sub i).ncard ≤
          (Z'' ∩ (A i).vertexSet).ncard + separationOrder (A i) (B i) := by
        rw [hZi_eq]
        exact Set.ncard_union_le _ _
      omega
    have hAi_lt : (A i).vertexSet.ncard < n := by
      rw [← hn]
      refine Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.2
        ⟨(hA_le i).vertexSet_subset, fun hV_eq ↦ ?_⟩) G'.vertexSet_finite
      have hZ''_eq : Z'' ∩ (A i).vertexSet = Z'' := by
        rw [hV_eq, Set.inter_eq_self_of_subset_left hZ''_sub]
      have : Z''.ncard < θ := by
        rw [hZ''_eq] at hZA_le
        exact hZA_le.trans_lt hord_lt
      omega
    exact ih (A i).vertexSet.ncard hAi_lt (A i) (Z_sub i) rfl
      (hperv'.mono (hA_le i)) hZi_sub hZi_card
  have hZi_inter_H₀ : ∀ i : Fin k, Z_sub i ∩ H₀.vertexSet = (A i ∩ B i).vertexSet := by
    intro i
    have h1 : τ₀.vertexSet ∩ H₀.vertexSet = H₀.vertexSet := by
      rw [hτ₀_V]
      exact Set.inter_eq_right.2 Set.subset_union_left
    calc Z_sub i ∩ H₀.vertexSet
      _ = (τ₀.vertexSet ∩ (A i).vertexSet) ∩ H₀.vertexSet := by rw [hZ_sub_eq i]
      _ = (τ₀.vertexSet ∩ H₀.vertexSet) ∩ (A i).vertexSet := Set.inter_right_comm _ _ _
      _ = H₀.vertexSet ∩ (A i).vertexSet := by rw [h1]
      _ = (A i ∩ B i).vertexSet := hH₀_inter_A i
  have hdes_H₀ : IsDesign (locationDesign G' ℒ) := hloc.isDesign_locationDesign
  have hdes0_isDesign : IsDesign (τ₀, Set.range Z_sub) := by
    rintro X ⟨i, rfl⟩
    rw [← hZ_sub_eq i]
    exact Set.inter_subset_left
  have hdes0_ext_isDesign : IsDesign (designExtension (τ₀, Set.range Z_sub) Z'') := by
    rintro X (rfl | ⟨i, rfl⟩)
    · change X ⊆ τ₀.vertexSet
      rw [hτ₀_V]; exact Set.subset_union_right
    · change Z_sub i ⊆ τ₀.vertexSet
      rw [← hZ_sub_eq i]; exact Set.inter_subset_left
  have henlarge0 : IsEnlargementVia (locationDesign G' ℒ) (τ₀, Set.range Z_sub) Z'' :=
    { isDesign := hdes_H₀
      isDesign' := hdes0_isDesign
      subset_vertexSet := by change Z'' ⊆ τ₀.vertexSet; rw [hτ₀_V]; exact Set.subset_union_right
      le := le_addVertices G' H₀ Z''
      sdiff_subset := by
        change τ₀.vertexSet \ H₀.vertexSet ⊆ Z''
        rw [hτ₀_V]
        intro x ⟨hx, hnot⟩
        exact hx.resolve_left hnot
      edgeSet_subset := subset_rfl
      inter_mem := by
        rintro X ⟨i, rfl⟩ _
        change Z_sub i ∩ H₀.vertexSet ∈ (locationDesign G' ℒ).2
        rw [hZi_inter_H₀ i]
        exact ⟨(eℒ i).1, (eℒ i).2, rfl⟩ }
  have henlarge0_ext : IsEnlargementVia (locationDesign G' ℒ)
      (designExtension (τ₀, Set.range Z_sub) Z'') Z'' :=
    { isDesign := hdes_H₀
      isDesign' := hdes0_ext_isDesign
      subset_vertexSet := by change Z'' ⊆ τ₀.vertexSet; rw [hτ₀_V]; exact Set.subset_union_right
      le := le_addVertices G' H₀ Z''
      sdiff_subset := by
        change τ₀.vertexSet \ H₀.vertexSet ⊆ Z''
        rw [hτ₀_V]
        intro x ⟨hx, hnot⟩
        exact hx.resolve_left hnot
      edgeSet_subset := subset_rfl
      inter_mem := by
        rintro X (rfl | ⟨i, rfl⟩) hne
        · exact (hne rfl).elim
        · change Z_sub i ∩ H₀.vertexSet ∈ (locationDesign G' ℒ).2
          rw [hZi_inter_H₀ i]
          exact ⟨(eℒ i).1, (eℒ i).2, rfl⟩ }
  refine glueRootedDecompositions (𝒮' := 𝒮') hA_le hτ₀_le hex_ind hZ_sub_eq ?_ ?_ ?_ ?_ ?_
    (by rw [hτ₀_V]; exact Set.subset_union_right)
    (Or.inl ⟨locationDesign G' ℒ, hdes_ℒ, Z'', hZ''_card.le, henlarge0⟩)
    (Or.inl ⟨locationDesign G' ℒ, hdes_ℒ, Z'', hZ''_card.le, henlarge0_ext⟩)
  · apply Set.Subset.antisymm
    · exact Set.union_subset hτ₀_le.vertexSet_subset
        (Set.iUnion_subset fun i ↦ (hA_le i).vertexSet_subset)
    · intro x hxG
      by_cases hxA : ∃ i : Fin k, x ∈ (A i).vertexSet
      · exact Or.inr (Set.mem_iUnion.2 hxA)
      · push Not at hxA
        left
        rw [hτ₀_V]
        refine Or.inl ⟨hxG, fun p hp ↦ ?_⟩
        obtain ⟨i, hi⟩ := eℒ.surjective ⟨p, hp⟩
        have hp_eq : p = (eℒ i).1 := congrArg Subtype.val hi.symm
        rw [hp_eq]
        have hxAB : x ∈ (A i).vertexSet ∪ (B i).vertexSet :=
          (hsep_i i).vertexSet_union.symm ▸ hxG
        exact hxAB.resolve_left (hxA i)
  · apply Set.Subset.antisymm
    · exact Set.union_subset hτ₀_le.edgeSet_subset
        (Set.iUnion_subset fun i ↦ (hA_le i).edgeSet_subset)
    · intro e heG
      by_cases heA : ∃ i : Fin k, e ∈ (A i).edgeSet
      · exact Or.inr (Set.mem_iUnion.2 heA)
      · push Not at heA
        left
        refine ⟨heG, fun p hp ↦ ?_⟩
        obtain ⟨i, hi⟩ := eℒ.surjective ⟨p, hp⟩
        have hp_eq : p = (eℒ i).1 := congrArg Subtype.val hi.symm
        rw [hp_eq]
        have heAB : e ∈ (A i).edgeSet ∪ (B i).edgeSet :=
          (hsep_i i).edgeSet_union.symm ▸ heG
        exact heAB.resolve_left (heA i)
  · intro i
    rw [Set.disjoint_iff_inter_eq_empty]
    ext e
    simp only [τ₀, addVertices_edgeSet, H₀, locationCore, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨_, hall⟩ heA
    exact (hsep_i i).notMem_edgeSet_right heA (hall (eℒ i).1 (eℒ i).2)
  · intro i j hij
    rw [Set.disjoint_iff_inter_eq_empty]
    ext e
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro heAi heAj
    exact (hsep_i j).notMem_edgeSet_right heAj
      ((hleft_le_right i j hij).edgeSet_subset heAi)
  · intro i j hij x ⟨hxAi, hxAj⟩
    rw [hτ₀_V]
    refine Or.inl ⟨(hA_le i).vertexSet_subset hxAi, fun p hp ↦ ?_⟩
    obtain ⟨l, hl⟩ := eℒ.surjective ⟨p, hp⟩
    have hp_eq : p = (eℒ l).1 := congrArg Subtype.val hl.symm
    rw [hp_eq]
    by_cases hil : i = l
    · subst hil
      exact (hleft_le_right j i hij.symm).vertexSet_subset hxAj
    · exact (hleft_le_right i l hil).vertexSet_subset hxAi

/-- **Graph Minors X, (11.3)** (page 186):
"Let $\mathscr{S}$ be a class of designs, and let $\theta \ge 1$. Let $G$ be a hypergraph
such that $\mathscr{S}$ is $\theta$-pervasive in $G$, and let $Z \subseteq V(G)$ with $|Z|
\le 3\theta - 2$. Then there is a tree-decomposition $(T, \tau)$ of $G$ over
$\mathscr{S}^{3\theta - 2} \cup \mathscr{R}_{4\theta - 3}$, such that for some $t_0 \in
V(T)$, $Z \subseteq V(\tau(t_0))$ and $\mathscr{S}^{3\theta - 2} \cup \mathscr{R}_{4\theta -
3}$ contains the $Z$-extension of the design of $t_0$ in $(T, \tau)$." -/
theorem theorem_11_3_proof {G : Hypergraph α β} {θ : ℕ} {𝒮 : Set (Design α β)} {Z : Set α}
    (hθ : 1 ≤ θ) (hperv : IsPervasive G θ 𝒮)
    (hZ_sub : Z ⊆ G.vertexSet) (hZ_card : Z.ncard ≤ 3 * θ - 2) :
    let 𝒮' := enlargementClass 𝒮 (3 * θ - 2) ∪ smallDesignClass (4 * θ - 3)
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (t₀ : ι),
      IsTreeDecompositionOver G 𝒮' T τ ∧
      Z ⊆ (τ t₀).vertexSet ∧
      designExtension (vertexDesign T τ t₀) Z ∈ 𝒮' := by
  classical
  let 𝒮' : Set (Design α β) := enlargementClass 𝒮 (3 * θ - 2) ∪ smallDesignClass (4 * θ - 3)
  -- Strong induction on `G.vertexSet.ncard`:
  suffices hmain : ∀ (n : ℕ) (G' : Hypergraph α β) (Z' : Set α),
      G'.vertexSet.ncard = n →
      IsPervasive G' θ 𝒮 → Z' ⊆ G'.vertexSet → Z'.ncard ≤ 3 * θ - 2 →
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (t₀ : ι),
        IsTreeDecompositionOver G' 𝒮' T τ ∧
        Z' ⊆ (τ t₀).vertexSet ∧
        designExtension (vertexDesign T τ t₀) Z' ∈ 𝒮' from
    hmain G.vertexSet.ncard G Z rfl hperv hZ_sub hZ_card
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro G' Z' hn hperv' hZ'_sub hZ'_card
    -- First prove the exact case `|Z''| = 3 * θ - 2` for `G'`:
    have hexact : ∀ (Z'' : Set α), Z'' ⊆ G'.vertexSet → Z''.ncard = 3 * θ - 2 →
        ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (t₀ : ι),
          IsTreeDecompositionOver G' 𝒮' T τ ∧
          Z'' ⊆ (τ t₀).vertexSet ∧
          designExtension (vertexDesign T τ t₀) Z'' ∈ 𝒮' := by
      intro Z'' hZ''_sub hZ''_card
      rcases theorem_11_2_proof hθ hperv' hZ''_sub hZ''_card with
        ⟨A₁, A₂, hsep, hord, hcard2, hcard1⟩ | ⟨ℒ, hloc, hdes_ℒ, hℒ_bound⟩
      · exact rootedDecomposition_of_lowOrderSeparation hθ hn hperv' hZ''_sub hZ''_card
          ih hsep hord hcard2 hcard1
      · exact rootedDecomposition_of_location hθ hn hperv' hZ''_sub hZ''_card
          ih hloc hdes_ℒ hℒ_bound
    -- Now handle general `|Z'| ≤ 3 * θ - 2`:
    by_cases hG'_small : G'.vertexSet.ncard < 3 * θ - 2
    · -- Base case: `|V(G')| < 3 * θ - 2`, 1-vertex tree (`k = 0`)
      let A : Fin 0 → Hypergraph α β := Fin.elim0
      let Z_sub : Fin 0 → Set α := Fin.elim0
      have hcard_le : G'.vertexSet.ncard ≤ 4 * θ - 3 := by omega
      have hdes0 : IsDesign (G', Set.range Z_sub) := by
        rintro X ⟨i, _⟩; exact Fin.elim0 i
      have hdes0_ext : IsDesign (designExtension (G', Set.range Z_sub) Z') := by
        rintro X (rfl | ⟨i, _⟩)
        · exact hZ'_sub
        · exact Fin.elim0 i
      refine glueRootedDecompositions (𝒮' := 𝒮') (A := A) (Z_sub := Z_sub) (τ₀ := G')
        (fun i ↦ Fin.elim0 i)
        le_rfl (fun i ↦ Fin.elim0 i)
        (fun i ↦ Fin.elim0 i) ?_ ?_ (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
        (fun i ↦ Fin.elim0 i) hZ'_sub
        (Or.inr ⟨hdes0, hcard_le⟩) (Or.inr ⟨hdes0_ext, hcard_le⟩)
      · simp
      · simp
    · -- `|V(G')| ≥ 3 * θ - 2`: extend `Z'` to `Z'' ⊆ V(G')` with `|Z''| = 3 * θ - 2`
      push Not at hG'_small
      obtain ⟨Z'', hZ'_Z'', hZ''_sub, hZ''_card⟩ :=
        Set.exists_subsuperset_card_eq hZ'_sub hZ'_card hG'_small
      obtain ⟨ι₁, hfin₁, T₁, τ₁, r₁, hover₁, hr₁_sub, hr₁_ext⟩ :=
        hexact Z'' hZ''_sub hZ''_card
      let A : Fin 1 → Hypergraph α β := fun _ ↦ G'
      let Z_sub : Fin 1 → Set α := fun _ ↦ Z''
      let τ₀ : Hypergraph α β := edgelessSubhypergraph G' Z''
      have hτ₀_V : τ₀.vertexSet = Z'' := edgelessSubhypergraph_vertexSet G' hZ''_sub
      have hτ₀_card : τ₀.vertexSet.ncard ≤ 4 * θ - 3 := by
        rw [hτ₀_V]; omega
      have hdes0 : IsDesign (τ₀, Set.range Z_sub) := by
        rintro X ⟨_, rfl⟩
        change Z'' ⊆ τ₀.vertexSet
        rw [hτ₀_V]
      have hdes0_ext : IsDesign (designExtension (τ₀, Set.range Z_sub) Z') := by
        rintro X (rfl | ⟨_, rfl⟩)
        · change X ⊆ τ₀.vertexSet
          rw [hτ₀_V]; exact hZ'_Z''
        · change Z'' ⊆ τ₀.vertexSet
          rw [hτ₀_V]
      refine glueRootedDecompositions (𝒮' := 𝒮') (A := A) (Z_sub := Z_sub) (τ₀ := τ₀)
        (fun _ ↦ le_rfl) (edgelessSubhypergraph_le G' Z'')
        (fun _ ↦ ⟨ι₁, hfin₁, T₁, τ₁, r₁, hover₁, hr₁_sub, hr₁_ext⟩)
        (fun _ ↦ by rw [hτ₀_V]; exact Set.inter_eq_self_of_subset_left hZ''_sub)
        ?_ ?_
        (fun _ ↦ by rw [edgelessSubhypergraph_edgeSet]; exact disjoint_bot_left)
        (fun i j hij ↦ (hij (Subsingleton.elim i j)).elim)
        (fun i j hij ↦ (hij (Subsingleton.elim i j)).elim)
        (by rwa [hτ₀_V])
        (Or.inr ⟨hdes0, hτ₀_card⟩)
        (Or.inr ⟨hdes0_ext, hτ₀_card⟩)
      · dsimp only [A]
        rw [hτ₀_V, Set.iUnion_const, Set.union_eq_self_of_subset_left hZ''_sub]
      · dsimp only [A]
        rw [edgelessSubhypergraph_edgeSet, Set.iUnion_const, Set.empty_union]

/-- **Graph Minors X, (11.1)** (page 185):
"For any $\theta \ge 1$, let $\mathscr{S}$ be a class of designs which is $\theta$-pervasive
in a hypergraph $G$; then $G$ has a tree-decomposition over $\mathscr{S}^{3\theta - 2} \cup
\mathscr{R}_{4\theta - 3}$." -/
theorem theorem_11_1_proof {G : Hypergraph α β} {θ : ℕ} {𝒮 : Set (Design α β)}
    (hθ : 1 ≤ θ) (hperv : IsPervasive G θ 𝒮) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β),
      IsTreeDecompositionOver G
        (enlargementClass 𝒮 (3 * θ - 2) ∪ smallDesignClass (4 * θ - 3)) T τ := by
  obtain ⟨ι, hfin, T, τ, _, hover, _, _⟩ :=
    theorem_11_3_proof hθ hperv (Set.empty_subset G.vertexSet) (by simp)
  exact ⟨ι, hfin, T, τ, hover⟩

end GraphMinor.GM10

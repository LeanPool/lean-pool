/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.Hall.Basic

/-!
# Kőnig's theorem

In a finite bipartite graph, the maximum number of edges in a matching equals the minimum number
of vertices in a vertex cover.

## Main statements

* `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_le`: weak duality. In any graph, a matching has
  at most as many edges as a finite vertex cover has vertices.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_isVertexCover`: **Kőnig's theorem**. A finite
  bipartite graph has a matching and a vertex cover of the same size.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_edgeSet_eq_vertexCoverNum`: the same, with
  the vertex cover number.
* `SimpleGraph.indepNum_add_vertexCoverNum`: **Gallai's identity** `α(G) + τ(G) = n`, for every
  finite graph.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_edgeSet_add_indepNum`: in a finite bipartite
  graph, `α(G) = n - ν(G)`; `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_add_indepNum_le` is the
  inequality `ν(G) + α(G) ≤ n` for every finite graph.

## Implementation notes

The proof is Ore's deficiency argument, reduced to Mathlib's Hall theorem
(`Fintype.all_card_le_filter_rel_iff_exists_injective`). Let `L` and `R` be the two sides, and pick
`S ⊆ L` maximising the deficiency `|S| - |N(S)|`. Maximality gives two Hall conditions, one
matching `N(S)` into `S` and one matching `L \ S` into `R \ N(S)`. The two matchings are
vertex-disjoint, and together they have `|L \ S| + |N(S)|` edges, the size of the vertex cover
`(L \ S) ∪ N(S)`.

## References

* [D. Kőnig, *Graphok és matrixok*][Konig1931]
* [J. Egerváry, *Matrixok kombinatorius tulajdonságairól*][Egervary1931]
* [O. Ore, *Graphs and matching theorems*][Ore1955]
* [T. Gallai, *Über extreme Punkt- und Kantenmengen*][Gallai1959]
-/

@[expose] public section

open Finset Function

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Weak duality -/

/-- **Weak duality.** In any graph, a matching has at most as many edges as a finite vertex cover
has vertices: each matching edge has an endpoint in the cover, and distinct matching edges have
disjoint endpoints. -/
theorem Subgraph.IsMatching.ncard_edgeSet_le {M : G.Subgraph} (hM : M.IsMatching) {C : Set V}
    (hC : G.IsVertexCover C) (hCf : C.Finite) : M.edgeSet.ncard ≤ C.ncard := by
  have hex : ∀ e ∈ M.edgeSet, ∃ v ∈ C, v ∈ e := fun e he ↦ by
    induction e using Sym2.ind with
    | _ a b => exact (hC (M.adj_sub he)).elim (⟨a, ·, Sym2.mem_mk_left a b⟩)
                (⟨b, ·, Sym2.mem_mk_right a b⟩)
  rcases M.edgeSet.eq_empty_or_nonempty with h0 | ⟨e₀, he₀⟩
  · simp [h0]
  have : Nonempty V := ⟨(hex e₀ he₀).choose⟩
  choose! f hfC hfe using hex
  refine Set.ncard_le_ncard_of_injOn f hfC (fun e he e' he' hee' ↦ ?_) hCf
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 (hfe e he)
  obtain ⟨w', hw'⟩ := Sym2.mem_iff_exists.1 (hee' ▸ hfe e' he')
  rw [hw, Subgraph.mem_edgeSet] at he
  rw [hw', Subgraph.mem_edgeSet] at he'
  rw [hw, hw', hM.eq_of_adj_left he he']

/-! ### Matchings from a family of disjoint edges -/

/-- The subgraph whose edges are `s(a i, b i)`, for injective `a`, `b` with disjoint ranges. -/
private def pairSubgraph {ι : Type*} (a b : ι → V) (hab : ∀ i, G.Adj (a i) (b i)) : G.Subgraph where
  verts := Set.range a ∪ Set.range b
  Adj v w := ∃ i, a i = v ∧ b i = w ∨ a i = w ∧ b i = v
  adj_sub := by
    rintro v w ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hab i
    · exact (hab i).symm
  edge_vert := by
    rintro v w ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩

private theorem pairSubgraph_isMatching {ι : Type*} {a b : ι → V} (hab : ∀ i, G.Adj (a i) (b i))
    (ha : Injective a) (hb : Injective b) (hd : ∀ i j, a i ≠ b j) :
    (pairSubgraph a b hab).IsMatching := by
  rintro v (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · refine ⟨b i, ⟨i, Or.inl ⟨rfl, rfl⟩⟩, fun w ⟨j, h⟩ ↦ ?_⟩
    rcases h with ⟨hj, rfl⟩ | ⟨rfl, hj⟩
    · rw [ha hj]
    · exact absurd hj.symm (hd i j)
  · refine ⟨a i, ⟨i, Or.inr ⟨rfl, rfl⟩⟩, fun w ⟨j, h⟩ ↦ ?_⟩
    rcases h with ⟨hj, rfl⟩ | ⟨rfl, hj⟩
    · exact absurd hj (hd j i)
    · rw [hb hj]

private theorem pairSubgraph_edgeSet {ι : Type*} {a b : ι → V} (hab : ∀ i, G.Adj (a i) (b i)) :
    (pairSubgraph a b hab).edgeSet = Set.range fun i ↦ s(a i, b i) := by
  ext ⟨v, w⟩
  simp [pairSubgraph, or_comm, eq_comm, and_comm]

private theorem ncard_pairSubgraph_edgeSet {ι : Type*} {a b : ι → V}
    (hab : ∀ i, G.Adj (a i) (b i)) (ha : Injective a) (hd : ∀ i j, a i ≠ b j) :
    (pairSubgraph a b hab).edgeSet.ncard = Nat.card ι := by
  rw [pairSubgraph_edgeSet, Set.ncard_range_of_injective]
  intro i j hij
  rcases Sym2.eq_iff.1 hij with ⟨h, -⟩ | ⟨h, -⟩
  · exact ha h
  · exact absurd h (hd i j)

/-! ### Ore's deficiency argument -/

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable (Adj : L → R → Prop) [DecidableRel Adj]

/-- The neighbourhood in `R` of a finset of left vertices. -/
private def nbr (S : Finset L) : Finset R := Finset.univ.filter (fun y => ∃ x ∈ S, Adj x y)

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
private theorem mem_nbr {S : Finset L} {y : R} : y ∈ nbr Adj S ↔ ∃ x ∈ S, Adj x y := by
  simp [nbr]

omit [Fintype L] in
private theorem nbr_union (S T : Finset L) : nbr Adj (S ∪ T) = nbr Adj S ∪ nbr Adj T := by
  ext y
  simp only [mem_nbr, mem_union, or_and_right, exists_or]

/-- The deficiency of a set of left vertices: how much bigger it is than its neighbourhood. -/
private def deficiency (S : Finset L) : ℤ := (S.card : ℤ) - (nbr Adj S).card

/-! ## The two Hall conditions forced by deficiency-maximality -/

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
/-- **Reverse Hall condition on `nbr Adj S`.** If `S` maximises `deficiency Adj`, every subset of
`nbr Adj S` has at least as many back-neighbours in `S`. Otherwise, deleting exactly those
back-neighbours from `S` would strictly increase the deficiency, contradicting maximality. -/
private theorem hall_nbr {S : Finset L}
    (hSmax : ∀ T : Finset L, deficiency Adj T ≤ deficiency Adj S)
    (A : Finset {y : R // y ∈ nbr Adj S}) :
    A.card ≤ (Finset.univ.filter (fun l : {x : L // x ∈ S} => ∃ y ∈ A, Adj l.1 y.1)).card := by
  classical
  rw [univ_eq_attach, filter_attach (fun l ↦ ∃ y ∈ A, Adj l y.1), card_map, card_attach]
  set P := S.filter fun l ↦ ∃ y ∈ A, Adj l y.1
  set A' := A.map (Embedding.subtype _)
  have hPS : P ⊆ S := filter_subset _ _
  have hA : A' ⊆ nbr Adj S := fun y hy ↦ by
    obtain ⟨y, -, rfl⟩ := mem_map.1 hy
    exact y.2
  -- the neighbourhood of `S \ P` misses `A'`
  have hN : nbr Adj (S \ P) ⊆ nbr Adj S \ A' := fun y hy ↦ by
    obtain ⟨x, hx, hxy⟩ := (mem_nbr Adj).1 hy
    obtain ⟨hxS, hxP⟩ := mem_sdiff.1 hx
    refine mem_sdiff.2 ⟨(mem_nbr Adj).2 ⟨x, hxS, hxy⟩, fun hyA ↦ hxP (mem_filter.2 ⟨hxS, ?_⟩)⟩
    obtain ⟨y', hy', rfl⟩ := mem_map.1 hyA
    exact ⟨y', hy', hxy⟩
  have h₁ := card_le_card hN
  have h₂ := hSmax (S \ P)
  have h₃ := card_le_card hA
  rw [card_sdiff_of_subset hA] at h₁
  simp only [deficiency, card_sdiff_of_subset hPS] at h₂
  simp only [A', card_map] at h₁ h₃
  have := card_le_card hPS
  omega

omit [Fintype L] [DecidableEq L] in
/-- **Forward Hall condition on `L \ S`.** If `S` maximises `deficiency Adj`, every subset of
`L \ S` has an image in `R \ nbr Adj S` at least as large. Otherwise, adjoining it to `S` would
strictly increase the deficiency, contradicting maximality. -/
private theorem hall_compl {S : Finset L}
    (hSmax : ∀ T : Finset L, deficiency Adj T ≤ deficiency Adj S)
    (A : Finset {x : L // x ∉ S}) :
    A.card ≤ (Finset.univ.filter
      (fun y : {y : R // y ∉ nbr Adj S} => ∃ a ∈ A, Adj a.1 y.1)).card := by
  classical
  set A' := A.map (Embedding.subtype _)
  have hval : (Finset.univ.filter
      (fun y : {y : R // y ∉ nbr Adj S} => ∃ a ∈ A, Adj a.1 y.1)).card =
        #(nbr Adj A' \ nbr Adj S) := by
    rw [← card_map (Embedding.subtype _)]
    congr 1
    ext y
    simp [A', mem_nbr, and_comm]
  have hdisj : Disjoint S A' := Finset.disjoint_left.2 fun x hxS hxA ↦ by
    obtain ⟨a, -, rfl⟩ := mem_map.1 hxA
    exact a.2 hxS
  have h := hSmax (S ∪ A')
  unfold deficiency at h
  rw [card_union_of_disjoint hdisj, nbr_union, union_comm, ← card_sdiff_add_card,
    show #A' = #A from card_map _] at h
  rw [hval]
  omega

/-! ### Kőnig's theorem -/

variable [Finite V] {s t : Set V}

/-- **Kőnig's theorem.** A finite bipartite graph has a matching and a vertex cover with as many
vertices as the matching has edges. -/
theorem IsBipartiteWith.exists_isMatching_isVertexCover (h : G.IsBipartiteWith s t) :
    ∃ M : G.Subgraph, M.IsMatching ∧ ∃ C : Set V, G.IsVertexCover C ∧
      M.edgeSet.ncard = C.ncard := by
  classical
  have := Fintype.ofFinite V
  let r : s → t → Prop := fun x y ↦ G.Adj x y
  obtain ⟨S, -, hS⟩ := exists_max_image (univ : Finset (Finset s)) (deficiency r) ⟨∅, mem_univ _⟩
  have hSmax : ∀ T, deficiency r T ≤ deficiency r S := fun T ↦ hS T (mem_univ T)
  -- Hall's theorem twice: `N(S)` into `S`, and `L \ S` into `R \ N(S)`
  obtain ⟨g, hginj, hgadj⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (y : {y : t // y ∈ nbr r S}) (x : {x : s // x ∈ S}) ↦ r x.1 y.1)).1 (hall_nbr r hSmax)
  obtain ⟨f, hfinj, hfadj⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (x : {x : s // x ∉ S}) (y : {y : t // y ∉ nbr r S}) ↦ r x.1 y.1)).1 (hall_compl r hSmax)
  -- the two matchings, as one family of edges `s(a i, b i)` with `a i ∈ s` and `b i ∈ t`
  let a : {y : t // y ∈ nbr r S} ⊕ {x : s // x ∉ S} → V :=
    Sum.elim (fun y ↦ ((g y).1 : V)) (fun x ↦ (x.1 : V))
  let b : {y : t // y ∈ nbr r S} ⊕ {x : s // x ∉ S} → V :=
    Sum.elim (fun y ↦ (y.1 : V)) (fun x ↦ ((f x).1 : V))
  have hab : ∀ i, G.Adj (a i) (b i) := by rintro (y | x); exacts [hgadj y, hfadj x]
  have has : ∀ i, a i ∈ s := by rintro (y | x); exacts [(g y).1.2, x.1.2]
  have hbt : ∀ i, b i ∈ t := by rintro (y | x); exacts [y.1.2, (f x).1.2]
  have hd : ∀ i j, a i ≠ b j := fun i j ↦ h.disjoint.ne_of_mem (has i) (hbt j)
  have ha : Injective a := by
    rintro (y | x) (y' | x') hyy'
    · exact congrArg Sum.inl (hginj (Subtype.ext (Subtype.ext hyy')))
    · exact absurd ((Subtype.ext hyy' : (g y).1 = x'.1) ▸ (g y).2) x'.2
    · exact absurd ((Subtype.ext hyy' : x.1 = (g y').1) ▸ (g y').2) x.2
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext hyy'))
  have hb : Injective b := by
    rintro (y | x) (y' | x') hyy'
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext hyy'))
    · exact absurd ((Subtype.ext hyy' : y.1 = (f x').1) ▸ y.2) (f x').2
    · exact absurd ((Subtype.ext hyy' : (f x).1 = y'.1) ▸ y'.2) (f x).2
    · exact congrArg Sum.inr (hfinj (Subtype.ext (Subtype.ext hyy')))
  -- the vertex cover `(L \ S) ∪ N(S)`
  let C : Set V := (fun x : s ↦ (x : V)) '' {x | x ∉ S} ∪ (fun y : t ↦ (y : V)) '' {y | y ∈ nbr r S}
  have hC : G.IsVertexCover C := by
    intro v w hvw
    rcases h.mem_of_adj hvw with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · by_cases hx : (⟨v, hv⟩ : s) ∈ S
      · exact Or.inr (Or.inr ⟨⟨w, hw⟩, (mem_nbr r).2 ⟨_, hx, hvw⟩, rfl⟩)
      · exact Or.inl (Or.inl ⟨⟨v, hv⟩, hx, rfl⟩)
    · by_cases hx : (⟨w, hw⟩ : s) ∈ S
      · exact Or.inl (Or.inr ⟨⟨v, hv⟩, (mem_nbr r).2 ⟨_, hx, hvw.symm⟩, rfl⟩)
      · exact Or.inr (Or.inl ⟨⟨w, hw⟩, hx, rfl⟩)
  refine ⟨pairSubgraph a b hab, pairSubgraph_isMatching hab ha hb hd, C, hC, ?_⟩
  have hdisj : Disjoint ((fun x : s ↦ (x : V)) '' {x | x ∉ S})
      ((fun y : t ↦ (y : V)) '' {y | y ∈ nbr r S}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩ ⟨y, -, hxy⟩
    exact h.disjoint.ne_of_mem x.2 y.2 hxy.symm
  rw [ncard_pairSubgraph_edgeSet hab ha hd, Set.ncard_union_eq hdisj,
    Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_image_of_injective _ Subtype.val_injective, Nat.card_sum, add_comm]
  rfl

/-- **Kőnig's theorem**, with the vertex cover number. A finite bipartite graph has a matching
whose number of edges is the vertex cover number. -/
theorem IsBipartiteWith.exists_isMatching_ncard_edgeSet_eq_vertexCoverNum
    (h : G.IsBipartiteWith s t) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (M.edgeSet.ncard : ℕ∞) = G.vertexCoverNum := by
  obtain ⟨M, hM, C, hC, hMC⟩ := h.exists_isMatching_isVertexCover
  refine ⟨M, hM, le_antisymm (le_iInf₂ fun C' hC' ↦ ?_) ?_⟩
  · rw [← (Set.toFinite C').cast_ncard_eq]
    exact_mod_cast hM.ncard_edgeSet_le hC' (Set.toFinite _)
  · rw [hMC, (Set.toFinite C).cast_ncard_eq]
    exact hC.vertexCoverNum_le

/-! ### Gallai's identity -/

private theorem encard_univ_eq_natCard : (Set.univ : Set V).encard = Nat.card V := by
  rw [← (Set.toFinite _).cast_ncard_eq, Set.ncard_univ]

/-- **Gallai's identity.** In a finite graph, the independence number and the vertex cover number
add up to the number of vertices: complements of independent sets are exactly vertex covers. -/
theorem indepNum_add_vertexCoverNum :
    (G.indepNum : ℕ∞) + G.vertexCoverNum = Nat.card V := by
  rw [← encard_univ_eq_natCard]
  refine le_antisymm ?_ ?_
  · -- the complement of a maximum independent set is a vertex cover
    obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    have hcov : G.IsVertexCover (I : Set V)ᶜ := isVertexCover_compl.2 hI.isIndepSet
    rw [Set.encard_univ, ← Set.encard_add_encard_compl (I : Set V),
      Set.encard_coe_eq_coe_finsetCard, hI.card_eq]
    exact add_le_add le_rfl hcov.vertexCoverNum_le
  · -- the complement of a minimum vertex cover is an independent set
    obtain ⟨C, hC, hCcov⟩ := G.vertexCoverNum_exists
    have hI : G.IsIndepSet ((Set.toFinite Cᶜ).toFinset : Set V) := by
      rw [Set.Finite.coe_toFinset]
      exact isIndepSet_compl_iff_isVertexCover.2 hCcov
    rw [Set.encard_univ, ← Set.encard_add_encard_compl C, hC, add_comm,
      (Set.toFinite Cᶜ).encard_eq_coe_toFinset_card]
    exact add_le_add (by exact_mod_cast hI.card_le_indepNum) le_rfl

/-- A matching and an independent set of a finite graph together have at most `Nat.card V`
elements: `ν(G) + α(G) ≤ n`. -/
theorem Subgraph.IsMatching.ncard_edgeSet_add_indepNum_le {M : G.Subgraph}
    (hM : M.IsMatching) : M.edgeSet.ncard + G.indepNum ≤ Nat.card V := by
  obtain ⟨C, hC, hCcov⟩ := G.vertexCoverNum_exists
  have h := G.indepNum_add_vertexCoverNum
  rw [← hC, ← (Set.toFinite C).cast_ncard_eq] at h
  have h' : G.indepNum + C.ncard = Nat.card V := by exact_mod_cast h
  have := hM.ncard_edgeSet_le hCcov (Set.toFinite C)
  omega

/-- **Kőnig–Egerváry, independence form.** In a finite bipartite graph, a maximum matching and a
maximum independent set together have exactly `Nat.card V` elements: `α(G) = n - ν(G)`. -/
theorem IsBipartiteWith.exists_isMatching_ncard_edgeSet_add_indepNum
    (h : G.IsBipartiteWith s t) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard + G.indepNum = Nat.card V := by
  obtain ⟨M, hM, hMC⟩ := h.exists_isMatching_ncard_edgeSet_eq_vertexCoverNum
  refine ⟨M, hM, ?_⟩
  have := G.indepNum_add_vertexCoverNum
  rw [← hMC, add_comm] at this
  exact_mod_cast this

end SimpleGraph

/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Tactic.Ring.RingNF

/-!
# Lexicographic product of simple graphs

The lexicographic product `G.lexProd H` of `G : SimpleGraph α` and `H : SimpleGraph β` replaces
every vertex of `G` by a copy of `H`: `(a, b)` and `(a', b')` are adjacent if `G.Adj a a'`, or if
`a = a'` and `H.Adj b b'`. Clique numbers, independence numbers and colourings multiply.

## Main definitions

* `SimpleGraph.lexProd G H`: the lexicographic product.
* `SimpleGraph.lexProdLeft`, `SimpleGraph.lexProdRight`: the embeddings of `G` and of `H`.
* `SimpleGraph.Coloring.lexProd`: the product colouring.

## Main statements

* `SimpleGraph.compl_lexProd`: `(G.lexProd H)ᶜ = Gᶜ.lexProd Hᶜ`.
* `SimpleGraph.CliqueFree.lexProd`: if `G` has no `(m + 1)`-clique and `H` no `(n + 1)`-clique,
  then `G.lexProd H` has no `(m * n + 1)`-clique. `SimpleGraph.IndepSetFree.lexProd` is the same
  for independent sets.
* `SimpleGraph.cliqueNum_lexProd`, `SimpleGraph.indepNum_lexProd`: for finite graphs, the clique
  and independence numbers of `G.lexProd H` are the products of those of `G` and `H`.
* `SimpleGraph.chromaticNumber_lexProd_le`: `χ(G.lexProd H) ≤ χ(G) * χ(H)`.
* `SimpleGraph.degree_lexProd`, `SimpleGraph.card_edgeFinset_lexProd`: the degree of `(a, b)` is
  `G.degree a * card β + H.degree b`, and there are `|E(G)| * |β| ^ 2 + |α| * |E(H)|` edges.
* `SimpleGraph.lexProdAssoc`: the product is associative up to isomorphism.
* `SimpleGraph.card_cliqueFinset_lexProd_bot`, `SimpleGraph.card_cliqueFinset_turanGraph`: blowing
  up each vertex into `m` independent vertices multiplies the `s`-clique count by `m ^ s`; the
  Turán graph `T(m * r, r)` is the blow-up of `K_r` (`SimpleGraph.topLexProdBotIsoTuranGraph`) and
  has exactly `r.choose s * m ^ s` cliques of size `s`, so Zykov's bound is sharp.

## Implementation notes

Harary calls `G.lexProd H` the composition `G[H]`. Read the edges of a graph as red and its
non-edges as blue. The clique and independent-set bounds together say that if `G` has no red `K_r`
and no blue `K_s`, and `H` has no red `K_r'` and no blue `K_s'`, then `G.lexProd H` has no red
`K_((r-1)(r'-1)+1)` and no blue `K_((s-1)(s'-1)+1)`. This gives the product inequality
`R(pq + 1) - 1 ≥ (R(p + 1) - 1) * (R(q + 1) - 1)`, which Xu, Xie, Exoo and Radziszowski attribute
to Abbott's 1965 thesis.

## References

* [F. Harary, *Graph theory*][Harary1969]
* [X. Xu, Z. Xie, G. Exoo, S. P. Radziszowski,
  *Constructive lower bounds on classical multicolor Ramsey numbers*][XuXieExooRadziszowski2004]
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {α β γ δ : Type*} {G : SimpleGraph α} {H : SimpleGraph β}

/-- The lexicographic product of simple graphs. Every vertex of `G` is replaced by a copy of `H`,
and two copies are joined completely if the corresponding vertices of `G` are adjacent. -/
def lexProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∨ x.1 = y.1 ∧ H.Adj x.2 y.2
  symm.symm x y := by simp [eq_comm, adj_comm]
  loopless.irrefl x := by simp

@[simp]
theorem lexProd_adj {x y : α × β} :
    (G.lexProd H).Adj x y ↔ G.Adj x.1 y.1 ∨ x.1 = y.1 ∧ H.Adj x.2 y.2 :=
  Iff.rfl

instance [DecidableEq α] [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G.lexProd H).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem lexProd_adj_of_ne {a a' : α} {b b' : β} (h : a ≠ a') :
    (G.lexProd H).Adj (a, b) (a', b') ↔ G.Adj a a' := by
  simp [h]

theorem lexProd_adj_left {a a' : α} {b : β} : (G.lexProd H).Adj (a, b) (a', b) ↔ G.Adj a a' := by
  simp

theorem lexProd_adj_right {a : α} {b b' : β} :
    (G.lexProd H).Adj (a, b) (a, b') ↔ H.Adj b b' := by
  simp

theorem boxProd_le_lexProd : G □ H ≤ G.lexProd H := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ (⟨h, -⟩ | ⟨h, rfl⟩)
  exacts [Or.inl h, Or.inr ⟨rfl, h⟩]

@[simp]
theorem bot_lexProd_bot : (⊥ : SimpleGraph α).lexProd (⊥ : SimpleGraph β) = ⊥ := by
  ext; simp

@[simp]
theorem top_lexProd_top : (⊤ : SimpleGraph α).lexProd (⊤ : SimpleGraph β) = ⊤ := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  by_cases h : a = a' <;> simp [h]

theorem compl_lexProd : (G.lexProd H)ᶜ = Gᶜ.lexProd Hᶜ := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  by_cases h : a = a' <;> simp [h]

variable (G H)

/-- The embedding of `G` into `G.lexProd H` given by `b`. -/
@[simps]
def lexProdLeft (b : β) : G ↪g G.lexProd H where
  toFun a := (a, b)
  inj' _ _ := congr_arg Prod.fst
  map_rel_iff' {_ _} := lexProd_adj_left

/-- The embedding of `H` into `G.lexProd H` as the copy over `a`. -/
@[simps]
def lexProdRight (a : α) : H ↪g G.lexProd H where
  toFun := Prod.mk a
  inj' _ _ := congr_arg Prod.snd
  map_rel_iff' {_ _} := lexProd_adj_right

variable {G H}

/-! ### Cliques and independent sets -/

theorem IsClique.lexProd {s : Set α} {t : Set β} (hs : G.IsClique s) (ht : H.IsClique t) :
    (G.lexProd H).IsClique (s ×ˢ t) := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨a', b'⟩ ⟨ha', hb'⟩ hne
  by_cases h : a = a'
  · subst h
    exact Or.inr ⟨rfl, ht hb hb' fun e ↦ hne (Prod.ext rfl e)⟩
  · exact Or.inl (hs ha ha' h)

theorem IsNClique.lexProd {m n : ℕ} {s : Finset α} {t : Finset β} (hs : G.IsNClique m s)
    (ht : H.IsNClique n t) : (G.lexProd H).IsNClique (m * n) (s ×ˢ t) :=
  ⟨by simpa using hs.isClique.lexProd ht.isClique, by rw [card_product, hs.card_eq, ht.card_eq]⟩

/-- A clique of `G.lexProd H` projects to a clique of `G`. -/
theorem IsClique.image_fst_of_lexProd {s : Set (α × β)} (h : (G.lexProd H).IsClique s) :
    G.IsClique (Prod.fst '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  exact (h hx hy fun e ↦ hne (e ▸ rfl)).resolve_right fun h' ↦ hne h'.1

/-- The part of a clique of `G.lexProd H` over a vertex `a` of `G` is a clique of `H`. -/
theorem IsClique.fiber_of_lexProd {s : Set (α × β)} (h : (G.lexProd H).IsClique s) (a : α) :
    H.IsClique {b | (a, b) ∈ s} := by
  intro b hb b' hb' hne
  exact ((h hb hb' fun e ↦ hne (Prod.ext_iff.1 e).2).resolve_left (G.irrefl)).2

/-- If the cliques of `G` have at most `m` vertices and those of `H` at most `n`, the cliques of
`G.lexProd H` have at most `m * n`. -/
theorem IsClique.card_le_mul_of_lexProd {m n : ℕ}
    (hG : ∀ s : Finset α, G.IsClique (s : Set α) → #s ≤ m)
    (hH : ∀ t : Finset β, H.IsClique (t : Set β) → #t ≤ n) {T : Finset (α × β)}
    (hT : (G.lexProd H).IsClique (T : Set (α × β))) : #T ≤ m * n := by
  classical
  have hfib : ∀ a, #{x ∈ T | x.1 = a} ≤ n := fun a ↦ by
    rw [← card_image_of_injOn (f := Prod.snd) fun x hx y hy hxy ↦
      Prod.ext ((mem_filter.1 hx).2.trans (mem_filter.1 hy).2.symm) hxy]
    refine hH _ ((hT.fiber_of_lexProd a).subset ?_)
    intro b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_coe.1 hb)
    obtain ⟨hxT, rfl⟩ := mem_filter.1 hx
    exact hxT
  have hproj : #(T.image Prod.fst) ≤ m := hG _ (by simpa using hT.image_fst_of_lexProd)
  calc #T ≤ n * #(T.image Prod.fst) := card_le_mul_card_image _ _ fun a _ ↦ hfib a
    _ ≤ m * n := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hproj

/-- A clique in a graph with no `(m + 1)`-clique has at most `m` vertices. -/
theorem CliqueFree.card_le_of_isClique {m : ℕ} (hG : G.CliqueFree (m + 1)) {s : Finset α}
    (hs : G.IsClique (s : Set α)) : #s ≤ m := by
  by_contra! h
  obtain ⟨u, hus, hu⟩ := exists_subset_card_eq (show m + 1 ≤ #s by omega)
  exact hG u ⟨hs.subset (by exact_mod_cast hus), hu⟩

theorem CliqueFree.lexProd {m n : ℕ} (hG : G.CliqueFree (m + 1)) (hH : H.CliqueFree (n + 1)) :
    (G.lexProd H).CliqueFree (m * n + 1) := fun T hT ↦ by
  have := hT.isClique.card_le_mul_of_lexProd (fun _ ↦ hG.card_le_of_isClique)
    fun _ ↦ hH.card_le_of_isClique
  rw [hT.card_eq] at this
  omega

theorem IndepSetFree.lexProd {m n : ℕ} (hG : G.IndepSetFree (m + 1))
    (hH : H.IndepSetFree (n + 1)) : (G.lexProd H).IndepSetFree (m * n + 1) := by
  rw [← cliqueFree_compl] at hG hH ⊢
  rw [compl_lexProd]
  exact hG.lexProd hH

theorem cliqueNum_lexProd [Finite α] [Finite β] :
    (G.lexProd H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  refine le_antisymm ?_ ?_
  · obtain ⟨T, hT⟩ := (G.lexProd H).exists_isNClique_cliqueNum
    rw [← hT.card_eq]
    exact hT.isClique.card_le_mul_of_lexProd
      (fun s hs ↦ IsClique.card_le_cliqueNum (G := G) (t := s) (tc := hs))
      fun t ht ↦ IsClique.card_le_cliqueNum (G := H) (t := t) (tc := ht)
  · obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
    obtain ⟨t, ht⟩ := H.exists_isNClique_cliqueNum
    have h := hs.lexProd ht
    rw [← h.card_eq]
    exact IsClique.card_le_cliqueNum (G := G.lexProd H) (t := s ×ˢ t) (tc := h.isClique)

theorem indepNum_lexProd [Finite α] [Finite β] :
    (G.lexProd H).indepNum = G.indepNum * H.indepNum := by
  rw [← cliqueNum_compl, compl_lexProd, cliqueNum_lexProd, cliqueNum_compl, cliqueNum_compl]

/-! ### Colourings -/

/-- The product of colourings of `G` and `H` colours `G.lexProd H`. -/
def Coloring.lexProd (C : G.Coloring γ) (D : H.Coloring δ) : (G.lexProd H).Coloring (γ × δ) :=
  Coloring.mk (fun x ↦ (C x.1, D x.2)) fun {_ _} h ↦ by
    rcases h with h | ⟨-, h⟩
    · exact fun e ↦ C.valid h (congr_arg Prod.fst e)
    · exact fun e ↦ D.valid h (congr_arg Prod.snd e)

theorem Colorable.lexProd {m n : ℕ} (hG : G.Colorable m) (hH : H.Colorable n) :
    (G.lexProd H).Colorable (m * n) :=
  ⟨(Embedding.completeGraph finProdFinEquiv.toEmbedding).toHom.comp
    (hG.some.lexProd hH.some)⟩

theorem chromaticNumber_lexProd_le :
    (G.lexProd H).chromaticNumber ≤ G.chromaticNumber * H.chromaticNumber := by
  rcases isEmpty_or_nonempty (α × β) with h | ⟨a, b⟩
  · simp [chromaticNumber_eq_zero_of_isEmpty]
  have hG0 : G.chromaticNumber ≠ 0 := fun h ↦ (chromaticNumber_eq_zero_iff.1 h).elim a
  have hH0 : H.chromaticNumber ≠ 0 := fun h ↦ (chromaticNumber_eq_zero_iff.1 h).elim b
  rcases eq_or_ne G.chromaticNumber ⊤ with hG | hG
  · simp [hG, hH0]
  rcases eq_or_ne H.chromaticNumber ⊤ with hH | hH
  · simp [hH, hG0]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hG
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hH
  rw [← hm, ← hn, ← Nat.cast_mul]
  exact ((chromaticNumber_le_iff_colorable.1 hm.ge).lexProd
    (chromaticNumber_le_iff_colorable.1 hn.ge)).chromaticNumber_le

/-! ### Associativity, degrees and edges -/

variable (G H) in
/-- The lexicographic product is associative up to isomorphism. `Equiv.prodAssoc` as a graph
isomorphism. -/
@[simps!]
def lexProdAssoc (I : SimpleGraph γ) : (G.lexProd H).lexProd I ≃g G.lexProd (H.lexProd I) where
  toEquiv := Equiv.prodAssoc α β γ
  map_rel_iff' {x y} := by
    obtain ⟨⟨a, b⟩, c⟩ := x
    obtain ⟨⟨a', b'⟩, c'⟩ := y
    simp only [Equiv.prodAssoc_apply, lexProd_adj, Prod.mk.injEq]
    tauto

section Degree

variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableRel G.Adj]
  [DecidableRel H.Adj]

theorem neighborFinset_lexProd (a : α) (b : β) :
    (G.lexProd H).neighborFinset (a, b) =
      G.neighborFinset a ×ˢ univ ∪ {a} ×ˢ H.neighborFinset b := by
  ext ⟨a', b'⟩
  simp [eq_comm, and_comm]

omit [DecidableEq β] in
/-- The degree of `(a, b)` in `G.lexProd H` is `G.degree a * card β + H.degree b`. -/
theorem degree_lexProd (a : α) (b : β) :
    (G.lexProd H).degree (a, b) = G.degree a * Fintype.card β + H.degree b := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_lexProd, card_union_of_disjoint
    (Finset.disjoint_left.2 fun _ h₁ h₂ ↦ G.irrefl ((mem_singleton.1 (mem_product.1 h₂).1) ▸
      (mem_neighborFinset _ _ _).1 (mem_product.1 h₁).1)), card_product, card_product, card_univ,
    card_singleton, one_mul, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree]

omit [DecidableEq β] in
/-- `G.lexProd H` has `|E(G)| * |β| ^ 2 + |α| * |E(H)|` edges. -/
theorem card_edgeFinset_lexProd :
    #(G.lexProd H).edgeFinset =
      #G.edgeFinset * Fintype.card β ^ 2 + Fintype.card α * #H.edgeFinset := by
  have h := (G.lexProd H).sum_degrees_eq_twice_card_edges
  have hG := G.sum_degrees_eq_twice_card_edges
  have hH := H.sum_degrees_eq_twice_card_edges
  have hrow : ∀ a : α, ∑ b : β, (G.lexProd H).degree (a, b) =
      G.degree a * Fintype.card β * Fintype.card β + 2 * #H.edgeFinset := fun a ↦ by
    rw [sum_congr rfl fun b _ ↦ degree_lexProd a b, sum_add_distrib, sum_const, card_univ,
      smul_eq_mul, hH, mul_comm (Fintype.card β)]
  rw [Fintype.sum_prod_type, sum_congr rfl fun a _ ↦ hrow a, sum_add_distrib, ← sum_mul,
    ← sum_mul, hG, sum_const, card_univ, smul_eq_mul] at h
  have h' : 2 * #(G.lexProd H).edgeFinset =
      2 * (#G.edgeFinset * Fintype.card β ^ 2 + Fintype.card α * #H.edgeFinset) := by
    rw [← h]
    ring
  omega

end Degree

/-! ### Blow-ups and Turán graphs -/

section Finite

variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [Fintype α] [Fintype β] in
private theorem map_mem_cliqueFinset {G' : SimpleGraph β} [Fintype α] [Fintype β]
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ↪g G') {n : ℕ} {S : Finset α}
    (hS : S ∈ G.cliqueFinset n) : S.map e.toEmbedding ∈ G'.cliqueFinset n := by
  rw [mem_cliqueFinset_iff] at hS ⊢
  refine ⟨?_, by rw [card_map, hS.card_eq]⟩
  rw [coe_map]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  exact e.map_adj_iff.2 (hS.isClique hx hy fun h ↦ hne (h ▸ rfl))

/-- Isomorphic graphs have the same number of `n`-cliques. -/
theorem Iso.card_cliqueFinset_eq {G' : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (f : G ≃g G') (n : ℕ) : #(G.cliqueFinset n) = #(G'.cliqueFinset n) := by
  refine card_nbij' (·.map f.toEmbedding.toEmbedding) (·.map f.symm.toEmbedding.toEmbedding)
    (fun S hS ↦ map_mem_cliqueFinset f.toEmbedding hS)
    (fun S hS ↦ map_mem_cliqueFinset f.symm.toEmbedding hS) (fun S _ ↦ ?_) (fun S _ ↦ ?_) <;>
    dsimp only <;> rw [Finset.map_map] <;> convert Finset.map_refl <;> ext x
  · exact RelIso.symm_apply_apply f x
  · exact RelIso.apply_symm_apply f x

variable [DecidableRel G.Adj]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableRel G.Adj] in
/-- In `G.lexProd ⊥`, distinct vertices of a clique have distinct first coordinates. -/
theorem IsClique.injOn_fst_of_lexProd_bot {S : Set (α × β)}
    (h : (G.lexProd (⊥ : SimpleGraph β)).IsClique S) : S.InjOn Prod.fst :=
  fun x hx y hy hxy ↦ by_contra fun hne ↦ (h hx hy hne).elim (by simp [hxy]) (·.2)

/-- Replacing every vertex of `G` by `card β` independent vertices multiplies the number of
`s`-cliques by `card β ^ s`. -/
theorem card_cliqueFinset_lexProd_bot (s : ℕ) :
    #((G.lexProd (⊥ : SimpleGraph β)).cliqueFinset s) =
      #(G.cliqueFinset s) * Fintype.card β ^ s := by
  set L := G.lexProd (⊥ : SimpleGraph β)
  have himage : ∀ S ∈ L.cliqueFinset s, S.image Prod.fst ∈ G.cliqueFinset s := fun S hS ↦ by
    rw [mem_cliqueFinset_iff] at hS ⊢
    refine ⟨by simpa using hS.isClique.image_fst_of_lexProd, ?_⟩
    rw [card_image_of_injOn (by simpa using hS.isClique.injOn_fst_of_lexProd_bot), hS.card_eq]
  rw [card_eq_sum_card_fiberwise himage]
  refine sum_const_nat fun A hA ↦ ?_
  have hAc := mem_cliqueFinset_iff.1 hA
  rw [← hAc.card_eq, ← card_univ (α := β), ← prod_const, ← card_pi]
  symm
  refine card_nbij (fun g ↦ A.attach.image fun a ↦ (a.1, g a.1 a.2)) (fun g _ ↦ ?_)
    (fun g _ g' _ hgg' ↦ ?_) (fun S hS ↦ ?_)
  · -- the transversal of `g` is a clique with first coordinates `A`
    have hinj : Function.Injective fun a : A ↦ ((a : α), g a.1 a.2) := fun a a' h ↦
      Subtype.ext (congr_arg Prod.fst h)
    rw [mem_coe, mem_filter, mem_cliqueFinset_iff]
    refine ⟨⟨?_, by rw [card_image_of_injective _ hinj, card_attach]⟩, ?_⟩
    · rw [coe_image]
      rintro _ ⟨a, -, rfl⟩ _ ⟨a', -, rfl⟩ hne
      have haa' : (a : α) ≠ a' := fun h ↦ hne (by rw [Subtype.ext h])
      exact Or.inl (hAc.isClique a.2 a'.2 haa')
    · rw [image_image]
      exact attach_image_val
  · -- transversals determine their choice functions
    funext a ha
    have hmem : (a, g a ha) ∈ (fun g ↦ A.attach.image fun x : A ↦ (x.1, g x.1 x.2)) g :=
      mem_image.2 ⟨⟨a, ha⟩, mem_attach _ _, rfl⟩
    rw [hgg'] at hmem
    obtain ⟨⟨a', ha'⟩, -, he⟩ := mem_image.1 hmem
    obtain ⟨rfl, he⟩ := Prod.mk.inj he
    exact he.symm
  · -- every clique over `A` is a transversal
    rw [mem_coe, mem_filter, mem_cliqueFinset_iff] at hS
    obtain ⟨hSc, hSA⟩ := hS
    have hex : ∀ a ∈ A, ∃ b, (a, b) ∈ S := fun a ha ↦ by
      rw [← hSA] at ha
      obtain ⟨x, hx, rfl⟩ := mem_image.1 ha
      exact ⟨x.2, hx⟩
    refine ⟨fun a ha ↦ (hex a ha).choose, by simp, ?_⟩
    ext ⟨a, b⟩
    simp only [mem_image, mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨a', ha', he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact (hex a' ha').choose_spec
    · intro hab
      have ha : a ∈ A := hSA ▸ mem_image_of_mem Prod.fst hab
      exact ⟨a, ha, hSc.isClique.injOn_fst_of_lexProd_bot (hex a ha).choose_spec hab rfl⟩

end Finite

/-- The complete graph on `r` vertices with every vertex replaced by `m` independent vertices is
the Turán graph `T(m * r, r)`. -/
def topLexProdBotIsoTuranGraph (m r : ℕ) :
    (⊤ : SimpleGraph (Fin r)).lexProd (⊥ : SimpleGraph (Fin m)) ≃g turanGraph (m * r) r where
  toEquiv := (Equiv.prodComm (Fin r) (Fin m)).trans finProdFinEquiv
  map_rel_iff' {x y} := by
    obtain ⟨a, b⟩ := x
    obtain ⟨a', b'⟩ := y
    simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, turanGraph_adj,
      finProdFinEquiv_apply_val, lexProd_adj, top_adj, bot_adj, and_false, or_false]
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.2,
      Nat.mod_eq_of_lt a'.2, Ne, Fin.val_inj]

/-- The Turán graph `T(m * r, r)` has exactly `r.choose s * m ^ s` cliques of size `s`, so
Zykov's bound `r.choose s * (n / r) ^ s` is attained when `r ∣ n`. -/
theorem card_cliqueFinset_turanGraph (m r s : ℕ) :
    #((turanGraph (m * r) r).cliqueFinset s) = r.choose s * m ^ s := by
  rw [← (topLexProdBotIsoTuranGraph m r).card_cliqueFinset_eq, card_cliqueFinset_lexProd_bot,
    Fintype.card_fin]
  congr 1
  have : (⊤ : SimpleGraph (Fin r)).cliqueFinset s = univ.powersetCard s := by
    ext S
    simp [mem_cliqueFinset_iff, isNClique_iff, IsClique.top]
  rw [this, card_powersetCard, card_univ, Fintype.card_fin]

end SimpleGraph

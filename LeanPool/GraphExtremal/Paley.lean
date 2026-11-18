/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Paley graphs

The Paley graph of a finite field `F` with `q ≡ 1 [MOD 4]` elements has vertex set `F`, with
`x` and `y` adjacent if `x - y` is a nonzero square. It is isomorphic to its complement, it is
strongly regular with parameters `(q, (q - 1) / 2, (q - 5) / 4, (q - 1) / 4)`, and its cliques
and independent sets have at most `√q` vertices.

## Main definitions

* `SimpleGraph.paleyGraph F`: distinct `x, y` are adjacent if `x - y` or `y - x` is a square.
  When `-1` is a square in `F`, this is the Paley graph (`SimpleGraph.paleyGraph_adj`).
* `SimpleGraph.paleyGraphComplIso`: multiplication by a non-square, an isomorphism from the
  Paley graph to its complement.

## Main statements

* `SimpleGraph.paleyGraph_isSRGWith`: the Paley graph is strongly regular with parameters
  `(q, (q - 1) / 2, (q - 5) / 4, (q - 1) / 4)`.
* `SimpleGraph.paleyGraph_ediam_eq_two`, `SimpleGraph.paleyGraph_connected`: it has diameter `2`.
* `SimpleGraph.paleyGraphAffineIso`: `x ↦ a * x + b` with `a` a nonzero square is an automorphism;
  these act transitively on vertices (`SimpleGraph.paleyGraph_exists_iso_apply_eq`) and on ordered
  edges (`SimpleGraph.paleyGraph_exists_iso_apply_eq_apply_eq`).
* `SimpleGraph.indepNum_paleyGraph`: its independence number equals its clique number.
* `SimpleGraph.paleyGraph_isClique_card_sq_le`, `SimpleGraph.cliqueNum_paleyGraph_sq_le`: its
  cliques have at most `√q` vertices.

## Implementation notes

The definition uses `SimpleGraph.fromRel`, so it needs no hypothesis on `F`. If `-1` is not a
square in `F`, then for each `x ≠ y` exactly one of `x - y`, `y - x` is a square and
`paleyGraph F` is complete.

The codegree count reduces to the sum `∑ x, χ x * χ (x + a) = -1` for the quadratic character
`χ` and `a ≠ 0` (`quadraticChar_sum_mul_add`), which follows from Mathlib's
`jacobiSum_nontrivial_inv`. The clique bound uses that `(x, y) ↦ x + c * y`, with `c` a non-square,
is injective on pairs of elements of a clique.

## References

* [R. E. A. C. Paley, *On orthogonal matrices*][Paley1933]
* [C. Godsil, G. Royle, *Algebraic graph theory*][GodsilRoyle2001]
-/

@[expose] public section

open Finset

/-! ### The shift sum of the quadratic character -/

section QuadraticChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- For `a ≠ 0`, the quadratic character satisfies `∑ x, χ x * χ (x + a) = -1`. -/
theorem quadraticChar_sum_mul_add (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    ∑ x : F, quadraticChar F x * quadraticChar F (x + a) = -1 := by
  set χ := quadraticChar F
  have hχ : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have ha2 : χ a * χ a = 1 := by rw [← sq, quadraticChar_sq_one ha]
  -- `jacobiSum χ χ = ∑ x, χ x * χ (1 - x) = -χ (-1)`
  have hJ : ∑ x : F, χ x * χ (1 - x) = -χ (-1) := by
    have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rwa [(quadraticChar_isQuadratic F).inv] at h
  -- substitute `x ↦ -x` to get the shift by `1`, then `x ↦ a * x` to get the shift by `a`
  have h1 : ∑ x : F, χ x * χ (x + 1) = -1 := by
    have e := Equiv.sum_comp (Equiv.neg F) fun x ↦ χ x * χ (1 - x)
    simp only [Equiv.neg_apply, sub_neg_eq_add] at e
    have hneg : ∀ x : F, χ (-x) * χ (1 + x) = χ (-1) * (χ x * χ (x + 1)) := fun x ↦ by
      rw [neg_eq_neg_one_mul, map_mul, add_comm]; ring
    simp only [hneg, ← mul_sum] at e
    rw [hJ] at e
    linear_combination χ (-1) * e - (∑ x : F, χ x * χ (x + 1) + 1) * hχ
  have e := Equiv.sum_comp (Equiv.mulLeft₀ a ha) fun x ↦ χ x * χ (x + a)
  have hmul : ∀ x : F, χ (a * x) * χ (a * x + a) = χ x * χ (x + 1) := fun x ↦ by
    rw [show a * x + a = a * (x + 1) by ring, map_mul, map_mul]
    linear_combination χ x * χ (x + 1) * ha2
  simp only [Equiv.mulLeft₀_apply, hmul, h1] at e
  exact e.symm

end QuadraticChar

namespace SimpleGraph

variable (F : Type*) [Field F]

/-- The Paley graph of a field: distinct `x` and `y` are adjacent if `x - y` or `y - x` is a
square. When `-1` is a square, adjacency is `x ≠ y ∧ IsSquare (x - y)` (`paleyGraph_adj`). -/
def paleyGraph : SimpleGraph F :=
  fromRel fun x y ↦ IsSquare (x - y)

variable {F}

theorem paleyGraph_adj' {x y : F} :
    (paleyGraph F).Adj x y ↔ x ≠ y ∧ (IsSquare (x - y) ∨ IsSquare (y - x)) :=
  fromRel_adj ..

theorem paleyGraph_adj (h : IsSquare (-1 : F)) {x y : F} :
    (paleyGraph F).Adj x y ↔ x ≠ y ∧ IsSquare (x - y) := by
  refine paleyGraph_adj'.trans <| and_congr_right fun _ ↦ or_iff_left_of_imp fun hs ↦ ?_
  simpa using h.mul hs

@[simp]
theorem paleyGraph_adj_add_right (b : F) {x y : F} :
    (paleyGraph F).Adj (x + b) (y + b) ↔ (paleyGraph F).Adj x y := by
  simp [paleyGraph_adj']

instance [DecidableEq F] [DecidablePred (IsSquare : F → Prop)] :
    DecidableRel (paleyGraph F).Adj :=
  fun _ _ ↦ decidable_of_iff' _ paleyGraph_adj'

/-! ### Symmetries -/

/-- Multiplying by a nonzero square preserves being a square. -/
private theorem isSquare_mul_iff_of_isSquare {a d : F} (ha : a ≠ 0) (hsq : IsSquare a) :
    IsSquare (a * d) ↔ IsSquare d := by
  obtain ⟨c, rfl⟩ := hsq
  have hc : c ≠ 0 := by rintro rfl; simp at ha
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r / c, ?_⟩, fun hd ↦ (IsSquare.mul ⟨c, rfl⟩ hd)⟩
  field_simp
  linear_combination hr

/-- For a nonzero square `a`, the affine map `x ↦ a * x + b` is an automorphism of the Paley
graph. -/
def paleyGraphAffineIso {a : F} (ha : a ≠ 0) (hsq : IsSquare a) (b : F) :
    paleyGraph F ≃g paleyGraph F where
  toEquiv := (Equiv.mulLeft₀ a ha).trans (Equiv.addRight b)
  map_rel_iff' {x y} := by
    change (paleyGraph F).Adj (a * x + b) (a * y + b) ↔ (paleyGraph F).Adj x y
    rw [paleyGraph_adj_add_right, paleyGraph_adj', paleyGraph_adj', ← mul_sub, ← mul_sub, Ne,
      mul_right_inj' ha, isSquare_mul_iff_of_isSquare ha hsq, isSquare_mul_iff_of_isSquare ha hsq]

@[simp]
theorem paleyGraphAffineIso_apply {a : F} (ha : a ≠ 0) (hsq : IsSquare a) (b x : F) :
    paleyGraphAffineIso ha hsq b x = a * x + b := rfl

@[simp]
theorem paleyGraphAffineIso_symm_apply {a : F} (ha : a ≠ 0) (hsq : IsSquare a) (b x : F) :
    (paleyGraphAffineIso ha hsq b).symm x = a⁻¹ * (x + -b) := rfl

/-- The Paley graph is vertex-transitive: the translations act transitively. -/
theorem paleyGraph_exists_iso_apply_eq (x y : F) :
    ∃ φ : paleyGraph F ≃g paleyGraph F, φ x = y :=
  ⟨paleyGraphAffineIso one_ne_zero IsSquare.one (y - x), by simp⟩

/-- When `-1` is a square, the Paley graph is arc-transitive: the affine maps `x ↦ a * x + b`
with `a` a nonzero square act transitively on ordered pairs of adjacent vertices. -/
theorem paleyGraph_exists_iso_apply_eq_apply_eq (h : IsSquare (-1 : F)) {x y x' y' : F}
    (hxy : (paleyGraph F).Adj x y) (hxy' : (paleyGraph F).Adj x' y') :
    ∃ φ : paleyGraph F ≃g paleyGraph F, φ x = x' ∧ φ y = y' := by
  obtain ⟨hne, hsq⟩ := (paleyGraph_adj h).1 hxy.symm
  obtain ⟨hne', hsq'⟩ := (paleyGraph_adj h).1 hxy'.symm
  have hd : y - x ≠ 0 := sub_ne_zero.2 hne
  have hd' : y' - x' ≠ 0 := sub_ne_zero.2 hne'
  have ha : (y' - x') / (y - x) ≠ 0 := div_ne_zero hd' hd
  refine ⟨paleyGraphAffineIso ha (hsq'.div hsq) (x' - (y' - x') / (y - x) * x), ?_, ?_⟩
  · simp
  · simp only [paleyGraphAffineIso_apply]
    field_simp
    ring

/-! ### Cliques, independent sets and the complement -/

/-- An embedding of graphs does not decrease the clique number. -/
theorem Embedding.cliqueNum_le {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β} [Finite β]
    (f : G ↪g G') : G.cliqueNum ≤ G'.cliqueNum := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  rw [← hs.card_eq, ← card_map f.toEmbedding]
  refine IsClique.card_le_cliqueNum (G := G') (t := s.map f.toEmbedding) (tc := ?_)
  rw [coe_map]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  exact f.map_adj_iff.2 (hs.isClique hx hy fun e ↦ hne (e ▸ rfl))

/-- Isomorphic graphs have the same clique number. -/
theorem Iso.cliqueNum_eq {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β} [Finite α]
    [Finite β] (f : G ≃g G') : G.cliqueNum = G'.cliqueNum :=
  le_antisymm (Iso.toEmbedding f).cliqueNum_le (Iso.toEmbedding f.symm).cliqueNum_le

private theorem ne_zero_of_not_isSquare {c : F} (hc : ¬IsSquare c) : c ≠ 0 := by
  rintro rfl
  exact hc IsSquare.zero

/-- The product of a non-square and a nonzero `d` is a square if and only if `d` is not. -/
private theorem isSquare_mul_iff [Finite F] {c d : F} (hc : ¬IsSquare c) (hd : d ≠ 0) :
    IsSquare (c * d) ↔ ¬IsSquare d := by
  cases nonempty_fintype F
  classical
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero (ne_zero_of_not_isSquare hc) hd), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.2 hc, ← quadraticChar_neg_one_iff_not_isSquare]
  omega

/-- Multiplication by a non-square `c` is an isomorphism from the Paley graph to its
complement. -/
def paleyGraphComplIso [Finite F] (h : IsSquare (-1 : F)) {c : F} (hc : ¬IsSquare c) :
    paleyGraph F ≃g (paleyGraph F)ᶜ where
  toEquiv := Equiv.mulLeft₀ c fun hc0 ↦ hc (hc0 ▸ IsSquare.zero)
  map_rel_iff' {x y} := by
    have hc0 := ne_zero_of_not_isSquare hc
    change (paleyGraph F)ᶜ.Adj (c * x) (c * y) ↔ (paleyGraph F).Adj x y
    rw [compl_adj, paleyGraph_adj h, paleyGraph_adj h, ← mul_sub, Ne, mul_right_inj' hc0]
    by_cases hxy : x = y
    · simp [hxy]
    · rw [isSquare_mul_iff hc (sub_ne_zero.2 hxy)]
      tauto

@[simp]
theorem paleyGraphComplIso_apply [Finite F] (h : IsSquare (-1 : F)) {c : F}
    (hc : ¬IsSquare c) (x : F) : paleyGraphComplIso h hc x = c * x := rfl

@[simp]
theorem paleyGraphComplIso_symm_apply [Finite F] (h : IsSquare (-1 : F)) {c : F}
    (hc : ¬IsSquare c) (x : F) : (paleyGraphComplIso h hc).symm x = c⁻¹ * x := rfl

theorem indepNum_paleyGraph [Finite F] (hF : ringChar F ≠ 2) (h : IsSquare (-1 : F)) :
    (paleyGraph F).indepNum = (paleyGraph F).cliqueNum := by
  cases nonempty_fintype F
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hF
  rw [← cliqueNum_compl, (paleyGraphComplIso h hc).cliqueNum_eq]

variable [Fintype F]

/-- A clique of the Paley graph has at most `√q` vertices. -/
theorem paleyGraph_isClique_card_sq_le (hF : ringChar F ≠ 2) (h : IsSquare (-1 : F))
    {s : Finset F} (hs : (paleyGraph F).IsClique (s : Set F)) : #s ^ 2 ≤ Fintype.card F := by
  classical
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hF
  rw [sq, ← card_product]
  refine card_le_card_of_injOn (fun p ↦ p.1 + c * p.2) (fun _ _ ↦ mem_univ _) ?_
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' hxy
  simp only [coe_product, Set.mem_prod, mem_coe] at hp hp' hxy
  by_cases hy : y' = y
  · subst hy
    simp only [add_left_inj] at hxy
    rw [hxy]
  · have hsq : IsSquare (y' - y) := ((paleyGraph_adj h).1 (hs hp'.2 hp.2 hy)).2
    have hns : ¬IsSquare (c * (y' - y)) := by
      rw [isSquare_mul_iff hc (sub_ne_zero.2 hy)]; exact not_not.2 hsq
    have hx : x - x' = c * (y' - y) := by linear_combination hxy
    refine (hns (hx ▸ ?_)).elim
    rcases eq_or_ne x x' with rfl | hxx
    exacts [by simp, ((paleyGraph_adj h).1 (hs hp.1 hp'.1 hxx)).2]

theorem cliqueNum_paleyGraph_sq_le (hF : ringChar F ≠ 2) (h : IsSquare (-1 : F)) :
    (paleyGraph F).cliqueNum ^ 2 ≤ Fintype.card F := by
  obtain ⟨s, hs⟩ := (paleyGraph F).exists_isNClique_cliqueNum
  rw [← hs.card_eq]
  exact paleyGraph_isClique_card_sq_le hF h hs.isClique

/-! ### Strong regularity -/

variable [DecidableEq F]

/-- `2` times the indicator of the nonzero squares, in terms of the quadratic character. -/
private theorem two_mul_ite_isSquare (x : F) :
    2 * (if x ≠ 0 ∧ IsSquare x then 1 else 0 : ℤ) =
      1 + quadraticChar F x - if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hsq : IsSquare x
  · simp [hx, hsq, (quadraticChar_one_iff_isSquare hx).2 hsq]
  · simp [hx, hsq, quadraticChar_neg_one_iff_not_isSquare.2 hsq]

/-- Twice the number of nonzero squares is `q - 1`. -/
private theorem two_mul_card_isSquare (hF : ringChar F ≠ 2) :
    2 * (#{x : F | x ≠ 0 ∧ IsSquare x} : ℤ) = Fintype.card F - 1 := by
  rw [card_filter, Nat.cast_sum, mul_sum]
  push_cast
  simp only [two_mul_ite_isSquare, sum_sub_distrib, sum_add_distrib,
    quadraticChar_sum_zero hF, sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_univ,
    nsmul_eq_mul, mul_one]
  ring

/-- `4` times the number of `x` with `x` and `x + a` both nonzero squares is
`q - 3 - χ a - χ (-a)`. -/
private theorem four_mul_card_isSquare_add (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    4 * (#{x : F | (x ≠ 0 ∧ IsSquare x) ∧ (x + a ≠ 0 ∧ IsSquare (x + a))} : ℤ) =
      Fintype.card F - 3 - quadraticChar F a - quadraticChar F (-a) := by
  set χ := quadraticChar F
  have hpt : ∀ x : F, 4 * (if (x ≠ 0 ∧ IsSquare x) ∧ (x + a ≠ 0 ∧ IsSquare (x + a))
      then 1 else 0 : ℤ) = (1 + χ x - if x = 0 then 1 else 0) *
        (1 + χ (x + a) - if x + a = 0 then 1 else 0) := fun x ↦ by
    rw [← two_mul_ite_isSquare, ← two_mul_ite_isSquare]
    split_ifs <;> simp_all
  have hshift : ∑ x : F, χ (x + a) = 0 := by
    have e := Equiv.sum_comp (Equiv.addRight a) (χ ·)
    simp only [Equiv.coe_addRight] at e
    rw [e, quadraticChar_sum_zero hF]
  have hsum : ∑ x : F, χ x = 0 := quadraticChar_sum_zero hF
  have hprod : ∑ x : F, χ x * χ (x + a) = -1 := quadraticChar_sum_mul_add hF ha
  have hz : ∀ x : F, x + a = 0 ↔ x = -a := fun x ↦ eq_neg_iff_add_eq_zero.symm
  have hexp : ∀ x : F, (1 + χ x - if x = 0 then 1 else 0) *
      (1 + χ (x + a) - if x + a = 0 then 1 else 0) =
        1 + χ (x + a) + χ x + χ x * χ (x + a) - (if x + a = 0 then 1 else 0) -
          (if x = 0 then 1 else 0) - χ x * (if x + a = 0 then 1 else 0) -
          (if x = 0 then 1 else 0) * χ (x + a) +
          (if x = 0 then 1 else 0) * (if x + a = 0 then 1 else 0) := fun x ↦ by ring
  rw [card_filter, Nat.cast_sum, mul_sum]
  push_cast
  simp only [hpt, hexp, sum_add_distrib, sum_sub_distrib, hshift, hsum, hprod]
  simp [hz, ha]
  ring

omit [Fintype F] [DecidableEq F] in
private theorem paleyGraph_adj_comm_iff (h : IsSquare (-1 : F)) {v z : F} :
    (paleyGraph F).Adj v z ↔ z - v ≠ 0 ∧ IsSquare (z - v) := by
  rw [adj_comm, paleyGraph_adj h, sub_ne_zero]

private theorem degree_paleyGraph (h : IsSquare (-1 : F)) (v : F) :
    (paleyGraph F).degree v = #{x : F | x ≠ 0 ∧ IsSquare x} := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  refine card_nbij' (· - v) (· + v) (fun z hz ↦ ?_) (fun x hx ↦ ?_) (fun z _ ↦ by simp)
    (fun x _ ↦ by simp)
  · simpa [paleyGraph_adj_comm_iff h] using hz
  · simpa [paleyGraph_adj_comm_iff h] using hx

private theorem card_commonNeighbors_paleyGraph (h : IsSquare (-1 : F)) (v w : F) :
    Fintype.card ((paleyGraph F).commonNeighbors v w) =
      #{x : F | (x ≠ 0 ∧ IsSquare x) ∧ (x + (w - v) ≠ 0 ∧ IsSquare (x + (w - v)))} := by
  rw [Fintype.card_of_subtype {z | (paleyGraph F).Adj v z ∧ (paleyGraph F).Adj w z}
    fun z ↦ by simp [mem_commonNeighbors]]
  refine card_nbij' (· - w) (· + w) (fun z hz ↦ ?_) (fun x hx ↦ ?_) (fun z _ ↦ by simp)
    (fun x _ ↦ by simp)
  · simp only [mem_coe, mem_filter, mem_univ, true_and, paleyGraph_adj_comm_iff h] at hz ⊢
    rw [show z - w + (w - v) = z - v by ring]
    exact ⟨hz.2, hz.1⟩
  · simp only [mem_coe, mem_filter, mem_univ, true_and, paleyGraph_adj_comm_iff h] at hx ⊢
    rw [show x + w - v = x + (w - v) by ring, add_sub_cancel_right]
    exact ⟨hx.2, hx.1⟩

/-- The Paley graph of a finite field with `q` elements, `q ≡ 1 [MOD 4]`, is strongly regular
with parameters `(q, (q - 1) / 2, (q - 5) / 4, (q - 1) / 4)`. -/
theorem paleyGraph_isSRGWith (hF : ringChar F ≠ 2) (h : IsSquare (-1 : F)) :
    (paleyGraph F).IsSRGWith (Fintype.card F) ((Fintype.card F - 1) / 2)
      ((Fintype.card F - 5) / 4) ((Fintype.card F - 1) / 4) := by
  have hq2 := FiniteField.odd_card_of_char_ne_two hF
  have hq4 := FiniteField.isSquare_neg_one_iff.1 h
  have hχ : ∀ a : F, quadraticChar F (-a) = quadraticChar F a := fun a ↦ by
    rw [neg_eq_neg_one_mul, map_mul,
      (quadraticChar_one_iff_isSquare (neg_ne_zero.2 one_ne_zero)).2 h, one_mul]
  have hN : ∀ v w : F, v ≠ w → 4 * (Fintype.card ((paleyGraph F).commonNeighbors v w) : ℤ) =
      Fintype.card F - 3 - 2 * quadraticChar F (v - w) := fun v w hvw ↦ by
    rw [card_commonNeighbors_paleyGraph h, four_mul_card_isSquare_add hF
      (sub_ne_zero.2 hvw.symm), hχ, show w - v = -(v - w) by ring, hχ]
    ring
  refine ⟨rfl, fun v ↦ ?_, fun v w hvw ↦ ?_, fun v w hvw hnadj ↦ ?_⟩
  · have := two_mul_card_isSquare hF
    rw [degree_paleyGraph h]
    omega
  · have hvw' := (paleyGraph_adj h).1 hvw
    have := hN v w hvw'.1
    rw [(quadraticChar_one_iff_isSquare (sub_ne_zero.2 hvw'.1)).2 hvw'.2] at this
    omega
  · have hns : ¬IsSquare (v - w) := fun hs ↦ hnadj ((paleyGraph_adj h).2 ⟨hvw, hs⟩)
    have := hN v w hvw
    rw [quadraticChar_neg_one_iff_not_isSquare.2 hns] at this
    omega

omit [Fintype F] [DecidableEq F] in
/-- The Paley graph of a finite field with `q ≡ 1 [MOD 4]` elements has diameter `2`. -/
theorem paleyGraph_ediam_eq_two [Finite F] (hF : ringChar F ≠ 2) (h : IsSquare (-1 : F)) :
    (paleyGraph F).ediam = 2 := by
  cases nonempty_fintype F
  classical
  have hq2 := FiniteField.odd_card_of_char_ne_two hF
  have hq4 := FiniteField.isSquare_neg_one_iff.1 h
  have hq1 := Fintype.one_lt_card (α := F)
  refine (paleyGraph_isSRGWith hF h).ediam_eq_two (fun htop ↦ ?_) (by omega)
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hF
  have hadj : (paleyGraph F).Adj c 0 := by
    rw [htop]
    exact (ne_zero_of_not_isSquare hc)
  exact hc (by simpa using ((paleyGraph_adj h).1 hadj).2)

omit [Fintype F] [DecidableEq F] in
/-- The Paley graph of a finite field with `q ≡ 1 [MOD 4]` elements is connected. -/
theorem paleyGraph_connected [Finite F] (hF : ringChar F ≠ 2) (h : IsSquare (-1 : F)) :
    (paleyGraph F).Connected :=
  connected_of_ediam_ne_top (by rw [paleyGraph_ediam_eq_two hF h]; simp)

end SimpleGraph

/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Construction.LowerBound
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.MaximalFamily
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.TensorPower
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Product
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.TensorPower
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Tightness.Exponent

/-!
# The arithmetic triangle removal lemma in `Fin n → ZMod p`

This file states the main results of Fox and Lovász, "A tight bound for Green's arithmetic
triangle removal lemma in vector spaces", in `Fin n → ZMod p`, where `N = p ^ n`. The three
theorems write out the triangles and multicolored sum-freeness in terms of Mathlib definitions.

## Main statements

* `card_le_rpow_one_sub_c_mul`: the Kleinberg–Sawin–Speyer bound `m ≤ p ^ ((1 - c p) * n)` for
  multicolored sum-free families (Theorem 2 of Fox and Lovász).
* `div_pow_rpow_C_mul_sq_le_card_triangles`: `m` vertex-disjoint triangles span at least
  `(m / N) ^ C p * N ^ 2` triangles (Theorem 3).
* `exists_subset_card_sdiff_add_le_forall_add_ne_zero`: the arithmetic triangle removal lemma
  with `δ = (ε / 3) ^ C p` (Theorem 1).
* `IsMulticoloredSumFree.card_triangles_prod_pi` and
  `IsMulticoloredSumFree.triangles_prod_pi_nonempty`: the construction of Section 3, which shows
  that the exponent `C p` cannot be lowered.
* `IsMulticoloredSumFree.mul_sq_le_card_of_forall_exists_subset`: if the removal lemma holds with
  `ε` and `δ`, then every multicolored sum-free family of more than `ε * N` triples has at least
  `δ * N ^ 2` members.
* `le_rpow_C_sub_of_forall_exists_subset`: `δ ≤ ε ^ (C p - η)` whenever `ε` and `δ` work in the
  removal lemma and `0 < ε < ε₀ p η` (the "Furthermore" part of Theorem 1). It uses the
  multicolored sum-free families of size `p ^ ((1 - c p - η') * n)` for `n ≥ n₀ p η'` of
  `exists_isMulticoloredSumFree_rpow_le` (the second part of Theorem 2).
-/

public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {p n : ℕ} [Fact p.Prime]

/-- **The Kleinberg–Sawin–Speyer bound** (Theorem 2 of Fox and Lovász). If the triples
`(x i, y i, z i)` in `Fin n → ZMod p` satisfy `x i + y j + z k = 0` exactly when `i = j = k`, then
there are at most `p ^ ((1 - c p) * n)` of them. -/
theorem card_le_rpow_one_sub_c_mul {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}
    (h : ∀ i j k, x i + y j + z k = 0 ↔ i = j ∧ j = k) :
    Fintype.card ι ≤ (p : ℝ) ^ ((1 - c p) * n) := by
  have := IsMulticoloredSumFree.card_le_card_rpow (p := p) h
  rwa [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm] at this

/-- **Theorem 3 of Fox and Lovász.** If `X × Y × Z` contains `m` vertex-disjoint triangles
`(x i, y i, z i)` in `Fin n → ZMod p`, then it contains at least `(m / N) ^ C p * N ^ 2` triangles,
where `N = p ^ n`. -/
theorem div_pow_rpow_C_mul_sq_le_card_triangles {ι : Type*} [Fintype ι]
    {x y z : ι → Fin n → ZMod p} {X Y Z : Finset (Fin n → ZMod p)} (hx : Injective x)
    (hy : Injective y) (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y)
    (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) :
    (Fintype.card ι / (p : ℝ) ^ n) ^ C p * (p ^ n) ^ 2 ≤
      #((X ×ˢ Y ×ˢ Z).filter fun (u, v, w) ↦ u + v + w = 0) := by
  have := div_rpow_C_mul_sq_le_card_triangles (p := p) hx hy hz hxX hyY hzZ hsum
  rwa [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow] at this

/-- **Theorem 1 of Fox and Lovász: the arithmetic triangle removal lemma.** If `X × Y × Z` has
fewer than `(ε / 3) ^ C p * N ^ 2` triangles `x + y + z = 0` in `Fin n → ZMod p`, where `N = p ^ n`,
then removing at most `ε * N` elements from `X`, `Y` and `Z` leaves no triangle. -/
theorem exists_subset_card_sdiff_add_le_forall_add_ne_zero {ε : ℝ} (hε : 0 ≤ ε)
    {X Y Z : Finset (Fin n → ZMod p)}
    (h : #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < (ε / 3) ^ C p * (p ^ n) ^ 2) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
      ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0 := by
  have hN : (Fintype.card (Fin n → ZMod p) : ℝ) = p ^ n := by simp
  obtain ⟨X', hX', Y', hY', Z', hZ', hcard, hempty⟩ :=
    exists_subset_card_sdiff_add_le_of_card_triangles_lt (X := X) (Y := Y) (Z := Z) hε
      (by rwa [hN])
  exact ⟨X', hX', Y', hY', Z', hZ', by rwa [← hN], triangles_eq_empty_iff.1 hempty⟩

variable {l : ℕ} {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}

/-- **The construction of Section 3 of Fox and Lovász, part one.** For a multicolored sum-free
family of `m` triples in `Fin n → ZMod p` with vertex sets `X`, `Y` and `Z`, the sets `X × W`,
`Y × W` and `Z × W` with `W = Fin l → ZMod p` contain `m * p ^ (2 * l)` triangles. -/
private lemma IsMulticoloredSumFree.card_triangles_prod_pi (h : IsMulticoloredSumFree x y z) :
    #(triangles (univ.image x ×ˢ (univ : Finset (Fin l → ZMod p))) (univ.image y ×ˢ univ)
      (univ.image z ×ˢ univ)) = Fintype.card ι * p ^ (2 * l) := by
  rw [h.card_triangles_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_mul,
    mul_comm l]

/-- **The construction of Section 3 of Fox and Lovász, part two.** Removing fewer than
`m * p ^ l` elements from the sets `X × W`, `Y × W` and `Z × W` of
`card_triangles_prod_pi` leaves a triangle. -/
private lemma IsMulticoloredSumFree.triangles_prod_pi_nonempty (h : IsMulticoloredSumFree x y z)
    {X' Y' Z' : Finset ((Fin n → ZMod p) × (Fin l → ZMod p))}
    (hcard : #((univ.image x ×ˢ univ) \ X') + #((univ.image y ×ˢ univ) \ Y') +
      #((univ.image z ×ˢ univ) \ Z') < Fintype.card ι * p ^ l) :
    (triangles X' Y' Z').Nonempty := by
  refine h.triangles_nonempty ?_
  rwa [Fintype.card_fun, ZMod.card, Fintype.card_fin]

omit [Fact p.Prime] in
/-- **Tightness of the arithmetic triangle removal lemma** (Section 3 of Fox and Lovász). Suppose
that in `Fin n → ZMod p` every `X × Y × Z` with fewer than `δ * N ^ 2` triangles can be made
triangle-free by removing at most `ε * N` elements, where `N = p ^ n`. Then every multicolored
sum-free family of more than `ε * N` triples has at least `δ * N ^ 2` members. With the
Kleinberg–Sawin–Speyer families of size `p ^ ((1 - c p) * n - o(n))` of Norin and Pebody, this gives
`δ ≤ ε ^ (C p - o(1))`. -/
private lemma IsMulticoloredSumFree.mul_sq_le_card_of_forall_exists_subset {ε δ : ℝ}
    (h : IsMulticoloredSumFree x y z) (hε : ε * p ^ n < Fintype.card ι)
    (hδ : ∀ X Y Z : Finset (Fin n → ZMod p),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ * (p ^ n) ^ 2 ≤ Fintype.card ι := by
  by_contra! hlt
  obtain ⟨X', -, Y', -, Z', -, hcard, hempty⟩ := hδ _ _ _ (by rwa [← triangles,
    h.card_triangles_image])
  simpa [triangles_eq_empty_iff.2 hempty] using triangles_nonempty_of_card_sdiff_add_lt
    (X := X') (Y := Y') (Z := Z') h.injective_left h.injective_middle h.injective_right
    (fun i ↦ (h i i i).2 ⟨rfl, rfl⟩) (by exact_mod_cast hcard.trans_lt hε)

omit [Fact p.Prime] in
/-- If the removal lemma holds in `Fin n → ZMod p` with `ε` and `δ`, and some multicolored
sum-free family has more than `ε * N` members, where `N = p ^ n`, then `δ * N ^ 2 ≤ ε * N + 1`. -/
private lemma IsMulticoloredSumFree.mul_sq_le_mul_add_one {ε δ : ℝ}
    (h : IsMulticoloredSumFree x y z) (hε0 : 0 ≤ ε) (hε : ε * p ^ n < Fintype.card ι)
    (hδ : ∀ X Y Z : Finset (Fin n → ZMod p),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ * (p ^ n) ^ 2 ≤ ε * p ^ n + 1 := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (⌊ε * p ^ n⌋₊ + 1)) (β := ι)
    (by rw [Fintype.card_fin]; exact (Nat.floor_lt (by positivity)).2 hε)
  grw [(h.comp f.injective).mul_sq_le_card_of_forall_exists_subset ?_ hδ]
  · rw [Fintype.card_fin]
    push_cast
    linarith [Nat.floor_le (by positivity : 0 ≤ ε * p ^ n)]
  · rw [Fintype.card_fin]
    exact_mod_cast Nat.lt_floor_add_one (ε * p ^ n)

/-- The asymptotic tightness bound for fixed `κ` and `η'` with `1 ≤ κ`, `1 / c p - η / 2 ≤ κ`
and `0 < η' < 1 / κ - c p`, for `0 < ε < p ^ (-(n₀ p η' + 1))` and
`ε ≤ (p + p ^ 2) ^ (-2 / η)`. -/
private lemma le_rpow_C_sub_of_lt {η κ η' ε δ : ℝ} (hη : 0 < η) (hκ₁ : 1 ≤ κ)
    (hκη : (c p)⁻¹ - η / 2 ≤ κ) (hη'₀ : 0 < η') (hη' : η' < κ⁻¹ - c p) (hε0 : 0 < ε)
    (hε : ε < ((p : ℝ) ^ (n₀ p η' + 1))⁻¹) (hε' : ε ≤ (p + p ^ 2 : ℝ)⁻¹ ^ (2 / η))
    (hδ : ∀ n (X Y Z : Finset (Fin n → ZMod p)),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ ≤ ε ^ (C p - η) := by
  have hp₀ := (Fact.out : p.Prime).pos
  have hp : 1 < (p : ℝ) := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  have hεκ : ε < (((p : ℝ) ^ κ⁻¹) ^ (n₀ p η' + 1))⁻¹ := by
    grw [Real.rpow_le_self_of_one_le hp.le (inv_le_one_of_one_le₀ hκ₁)]
    exact hε
  obtain ⟨n, hn, hpow, hpow'⟩ :=
    exists_lt_pow_le_inv_lt (Real.one_lt_rpow hp (by positivity)) hε0 hεκ
  have hε₁ : ε ≤ 1 := hε.le.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hp.le))
  obtain ⟨m, x, y, z, hxyz, hm⟩ :=
    exists_isMulticoloredSumFree_rpow_le (Fact.out : p.Prime).two_le hη'₀ hn.le
  have := hxyz.mul_sq_le_mul_add_one hε0.le (by
    rw [Fintype.card_fin]
    exact mul_pow_lt_of_rpow_mul_le hp hε0 (by grind) (by linarith) hpow hm) (hδ n)
  grw [le_mul_rpow_one_add_of_mul_sq_le (by positivity) (by positivity) hε0 hε₁ hκ₁
    (inv_pow_le_mul_rpow (by positivity) hε0 (by positivity) hpow') this]
  exact mul_rpow_le_rpow_sub (by positivity) hε0 hε₁ hη (by rw [C, one_div]; linarith) hε'

private lemma ε₀_pos (η : ℝ) : 0 < ε₀ p η := by
  have := (Fact.out : p.Prime).pos
  rw [ε₀]
  positivity

/-- **Asymptotic tightness of the arithmetic triangle removal lemma** (the "Furthermore" part of
Theorem 1 of Fox and Lovász). For every `η > 0` and every `0 < ε < ε₀ p η`, any `δ` that works
with `ε` in the removal lemma in `Fin n → ZMod p` for every `n` satisfies `δ ≤ ε ^ (C p - η)`.
Here `ε₀ p η = p ^ (-(n₀ p η' + 1))` with `η' = c p * min (1 - c p) (c p * η / 2) / 2` and
`n₀ p η' = ⌈(2 ^ (p + 3) * p ^ 10 / η') ^ 2⌉ + p ^ 4 + 1`. The proof combines the construction of
Section 3 with the multicolored sum-free families of size `p ^ ((1 - c p - η') * n)` of Kleinberg,
Sawin and Speyer. -/
theorem le_rpow_C_sub_of_forall_exists_subset {η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hε₀ : ε < ε₀ p η)
    (hδ : ∀ n (X Y Z : Finset (Fin n → ZMod p)),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ ≤ ε ^ (C p - η) := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hc := c_pos (Fact.out : p.Prime).two_le
  have hc₁ := c_lt_one (Fact.out : p.Prime).two_le
  rw [ε₀] at hε₀
  refine le_rpow_C_sub_of_lt hη (le_max_left _ _) (le_max_right _ _)
    (mul_min_div_two_pos hc hc₁ hη) (mul_min_div_two_lt_inv_max_sub hc hc₁ hη) hε hε₀
    (hε₀.le.trans (inv_pow_le_inv_add_sq_rpow hp hη ?_)) hδ
  push_cast
  linarith [div_le_sq_div_mul_min_div_two (X := 2 ^ (p + 3) * (p : ℝ) ^ 10) hc hc₁ hη
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith))),
    sq_add_one_le_n₀ p (c p * min (1 - c p) (c p * η / 2) / 2)]

end ArithmeticTriangleRemovalInVectorSpaces

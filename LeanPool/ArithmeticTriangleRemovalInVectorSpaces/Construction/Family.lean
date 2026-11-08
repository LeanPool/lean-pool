/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Construction.TypeClass
public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Basic
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Construction.Behrend
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Construction.Hash
import Mathlib.NumberTheory.Bertrand

/-!
# The sum-free family of a base point

Let `a₀`, `b₀` and `c₀` be vectors in `Fin n → ℕ` with `a₀ r + b₀ r + c₀ r = p - 1` for every `r`.
The triples `(a, b, c)` with `a`, `b` and `c` in the type classes of `a₀`, `b₀` and `c₀` and
`a r + b r + c r = p - 1` for every `r` are permuted transitively in each coordinate, so each
vector lies in equally many of them. Hashing them with a prime `P` chosen by Bertrand's postulate
into a set chosen by Behrend's construction gives a multicolored sum-free family nearly as large as
the smallest of the three type classes.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.permTriple σ v`: the triple `v` with the entries of its
  three vectors permuted by `σ`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.card_filter_mul_card_typeClass_eq`: the fibers of a
  projection compatible with the permutations all have the same size.
* `ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_mul_exp_le`: hashing with
  a prime from Bertrand's postulate into a set from Behrend's construction.
* `ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_of_typeClass`: a
  multicolored sum-free family in `Fin n → ZMod p` with at least
  `w * exp (-4 * √(log ((12 + 2 * p) * p ^ (3 * n)))) / (4 * (12 + 2 * p))` members, where `w` is
  at most the size of each type class.
-/

public section

open Finset Real

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {n p : ℕ}

/-- Permuting the entries of the three vectors of a triple simultaneously. -/
private def permTriple (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)
  | (a, b, c) => (a ∘ σ, b ∘ σ, c ∘ σ)

private lemma permTriple_permTriple (σ τ : Equiv.Perm (Fin n))
    (v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) :
    permTriple σ (permTriple τ v) = permTriple (τ * σ) v :=
  rfl

private lemma permTriple_one (v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)) : permTriple 1 v = v :=
  rfl

/-- **Equal fibers.** If permutations act on `V` compatibly with a map `g` into the type class of
`w₀`, then every fiber of `g` over the type class has `#V / #(typeClass w₀)` elements. -/
private lemma card_filter_mul_card_typeClass_eq
    {V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))}
    {w₀ : Fin n → ℕ} (g : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → Fin n → ℕ)
    (hg : ∀ σ v, g (permTriple σ v) = g v ∘ σ) (hgV : ∀ v ∈ V, g v ∈ typeClass w₀)
    (hV : ∀ σ, ∀ v ∈ V, permTriple σ v ∈ V) {w : Fin n → ℕ} (hw : w ∈ typeClass w₀) :
    #{v ∈ V | g v = w} * #(typeClass w₀) = #V := by
  rw [card_eq_sum_card_fiberwise hgV, sum_const_nat, mul_comm]
  intro w' hw'
  obtain ⟨σ, rfl⟩ := exists_eq_comp_of_mem_typeClass hw hw'
  refine card_nbij' (permTriple σ⁻¹) (permTriple σ) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, Set.mem_ofPred_eq] at hv ⊢
    obtain ⟨hvV, hvg⟩ := hv
    refine ⟨hV σ⁻¹ v hvV, ?_⟩
    rw [hg, hvg]
    ext r
    simp
  · intro v hv
    simp only [coe_filter, Set.mem_ofPred_eq] at hv ⊢
    obtain ⟨hvV, hvg⟩ := hv
    exact ⟨hV σ v hvV, by rw [hg, hvg]⟩
  · intro v _
    rw [permTriple_permTriple, inv_mul_cancel, permTriple_one]
  · intro v _
    rw [permTriple_permTriple, mul_inv_cancel, permTriple_one]

variable {a₀ b₀ c₀ : Fin n → ℕ}

private lemma permTriple_mem_vecSumTriples (σ : Equiv.Perm (Fin n))
    {v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)}
    (hv : v ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) :
    permTriple σ v ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀) := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨ha, hb, hc, hsum⟩ := mk_mem_vecSumTriples.1 hv
  exact mk_mem_vecSumTriples.2 ⟨comp_mem_typeClass ha σ, comp_mem_typeClass hb σ,
    comp_mem_typeClass hc σ, fun r ↦ hsum (σ r)⟩

private lemma sum_add_add_eq (h₀ : ∀ r, a₀ r + b₀ r + c₀ r = p - 1) {a b c : Fin n → ℕ}
    (ha : a ∈ typeClass a₀) (hb : b ∈ typeClass b₀) (hc : c ∈ typeClass c₀) :
    ∑ r, (a r + b r + c r) = n * (p - 1) := by
  rw [sum_add_distrib, sum_add_distrib, sum_eq_of_mem_typeClass ha, sum_eq_of_mem_typeClass hb,
    sum_eq_of_mem_typeClass hc, ← sum_add_distrib, ← sum_add_distrib]
  simp [h₀]

private lemma card_typeClass_le_card_vecSumTriples (h₀ : ∀ r, a₀ r + b₀ r + c₀ r = p - 1) :
    #(typeClass a₀) ≤ #(vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) := by
  rw [← card_filter_mul_card_typeClass_eq (fun (a, _, _) ↦ a) (fun _ _ ↦ rfl)
    (by simp +contextual) (fun σ _ ↦ permTriple_mem_vecSumTriples σ) (self_mem_typeClass a₀)]
  refine Nat.le_mul_of_pos_left _ (card_pos.2 ⟨(a₀, b₀, c₀), ?_⟩)
  simpa using ⟨self_mem_typeClass a₀, self_mem_typeClass b₀, self_mem_typeClass c₀, h₀⟩

/-- If `0 < w` is at most the size of each type class, then at most
`3 * (#V / w)` triples of `V = vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)` share
a vector with a given one. -/
private lemma card_filter_shares_le {w : ℝ} (hw : 0 < w) (hwa : w ≤ #(typeClass a₀))
    (hwb : w ≤ #(typeClass b₀)) (hwc : w ≤ #(typeClass c₀))
    {v : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)}
    (hv : v ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) :
    #{v' ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀) | Shares v v'} ≤
      3 * (#(vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) / w) := by
  have hfib {w₀ : Fin n → ℕ} (g : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ) → Fin n → ℕ)
      (hg : ∀ σ v, g (permTriple σ v) = g v ∘ σ)
      (hgV : ∀ v ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀),
        g v ∈ typeClass w₀)
      (hw₀ : w ≤ #(typeClass w₀)) {x : Fin n → ℕ} (hx : x ∈ typeClass w₀) :
      #{v ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀) | g v = x} ≤
        #(vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) / w := by
    rw [le_div_iff₀ hw, ← card_filter_mul_card_typeClass_eq g hg hgV
      (fun σ _ ↦ permTriple_mem_vecSumTriples σ) hx]
    push_cast
    gcongr
  obtain ⟨a, b, c⟩ := v
  obtain ⟨ha, hb, hc, -⟩ := mk_mem_vecSumTriples.1 hv
  have hsub : {v' ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀) |
      Shares (a, b, c) v'} ⊆
      {v' ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀) |
        (fun (a', _, _) ↦ a') v' = a} ∪
      {v' ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀) |
        (fun (_, b', _) ↦ b') v' = b} ∪
      {v' ∈ vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀) |
        (fun (_, _, c') ↦ c') v' = c} := by
    rintro ⟨a', b', c'⟩
    simp only [mem_filter, mem_union, shares_mk]
    grind
  grw [card_le_card hsub, card_union_le, card_union_le]
  push_cast
  linarith [hfib (fun (a, _, _) ↦ a) (fun _ _ ↦ rfl) (by simp +contextual) hwa ha,
    hfib (fun (_, b, _) ↦ b) (fun _ _ ↦ rfl) (by simp +contextual) hwb hb,
    hfib (fun (_, _, c) ↦ c) (fun _ _ ↦ rfl) (by simp +contextual) hwc hc]

/-- Hashing `vecSumTriples p A B C` with a prime `P ≤ 2 * (2 * F + p)` from Bertrand's postulate
into a set from Behrend's construction gives a multicolored sum-free family with at least
`#V * exp (-4 * √(log P)) / (4 * P)` members, if at most `F` triples share a vector with a given
one. -/
private lemma exists_isMulticoloredSumFree_mul_exp_le {A B C : Finset (Fin n → ℕ)} (hp : 2 ≤ p)
    (hsum : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ∑ r, (a r + b r + c r) = n * (p - 1)) {F : ℝ}
    (hF₀ : 0 ≤ F)
    (hF : ∀ v ∈ vecSumTriples p A B C, #{v' ∈ vecSumTriples p A B C | Shares v v'} ≤ F) :
    ∃ (P m : ℕ) (x y z : Fin m → Fin n → ZMod p), IsMulticoloredSumFree x y z ∧ 0 < P ∧
      P ≤ 2 * (2 * F + p) ∧ #(vecSumTriples p A B C) * exp (-4 * √(log P)) ≤ 4 * m * P := by
  obtain ⟨P, hP, hPlt, hPle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * ⌊F⌋₊ + p) (by grind)
  have := Fact.mk hP
  obtain ⟨S, hS, hScard⟩ := exists_threeAPFree_le_card_zmod hP.pos
  obtain ⟨m, x, y, z, hsf, hm⟩ := exists_isMulticoloredSumFree_of_hash hp (by grind) hsum
    (fun v hv ↦ Nat.le_floor (hF v hv)) hS
  refine ⟨P, m, x, y, z, hsf, hP.pos, ?_, ?_⟩
  · grw [hPle]
    push_cast
    grw [Nat.floor_le hF₀]
  · have hPF : (P : ℝ) / 2 ≤ P - ⌊F⌋₊ := by
      rw [le_sub_comm, sub_half, le_div_iff₀ two_pos]
      exact_mod_cast (by grind : ⌊F⌋₊ * 2 ≤ P)
    have h : #(vecSumTriples p A B C) * (P / 2 * exp (-4 * √(log P))) * (P / 2) ≤ m * P ^ 3 := by
      grw [hScard, hPF]
      exact hm
    refine le_of_mul_le_mul_right ?_ (pow_pos (by exact_mod_cast hP.pos : (0 : ℝ) < P) 2)
    linarith

/-- **The sum-free family of a base point.** If `a₀ r + b₀ r + c₀ r = p - 1` for every `r` and
`1 ≤ w` is at most the size of the type classes of `a₀`, `b₀` and `c₀`, then there is a
multicolored sum-free family in `Fin n → ZMod p` with at least
`w * exp (-4 * √(log ((12 + 2 * p) * p ^ (3 * n)))) / (4 * (12 + 2 * p))` members. -/
lemma exists_isMulticoloredSumFree_of_typeClass (hp : 2 ≤ p)
    (h₀ : ∀ r, a₀ r + b₀ r + c₀ r = p - 1) {w : ℝ} (hw : 1 ≤ w) (hwa : w ≤ #(typeClass a₀))
    (hwb : w ≤ #(typeClass b₀)) (hwc : w ≤ #(typeClass c₀)) :
    ∃ (m : ℕ) (x y z : Fin m → Fin n → ZMod p), IsMulticoloredSumFree x y z ∧
      w * exp (-4 * √(log ((12 + 2 * p) * p ^ (3 * n)))) / (4 * (12 + 2 * p)) ≤ m := by
  obtain ⟨P, m, x, y, z, hsf, hP, hPle, hm⟩ := exists_isMulticoloredSumFree_mul_exp_le hp
    (fun a ha b hb c hc ↦ sum_add_add_eq h₀ ha hb hc) (by positivity)
    (fun v hv ↦ card_filter_shares_le (by positivity) hwa hwb hwc hv)
  refine ⟨m, x, y, z, hsf, ?_⟩
  have hwV : w ≤ #(vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) :=
    hwa.trans (by exact_mod_cast card_typeClass_le_card_vecSumTriples h₀)
  have hPV : (P : ℝ) ≤
      (12 + 2 * p) * (#(vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) / w) := by
    nlinarith [(one_le_div (by positivity)).2 hwV]
  have hE : exp (-4 * √(log ((12 + 2 * p) * p ^ (3 * n)))) ≤ exp (-4 * √(log P)) := by
    rw [exp_le_exp, neg_mul, neg_mul, neg_le_neg_iff]
    gcongr
    grw [hPV, div_le_self (by positivity) hw, card_vecSumTriples_le,
      card_typeClass_le (p := p) (fun r ↦ by grind [h₀ r]),
      card_typeClass_le (p := p) (fun r ↦ by grind [h₀ r]),
      card_typeClass_le (p := p) (fun r ↦ by grind [h₀ r])]
    push_cast
    exact le_of_eq (by ring)
  rw [div_le_iff₀ (by positivity)]
  calc w * exp (-4 * √(log ((12 + 2 * p) * p ^ (3 * n))))
      ≤ w * exp (-4 * √(log P)) := by grw [hE]
    _ = w * (#(vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) *
        exp (-4 * √(log P))) / #(vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) := by
      field_simp [(by linarith : (0 : ℝ) < #(vecSumTriples p (typeClass a₀) (typeClass b₀)
        (typeClass c₀))).ne']
    _ ≤ w * (4 * m * ((12 + 2 * p) *
        (#(vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) / w))) /
        #(vecSumTriples p (typeClass a₀) (typeClass b₀) (typeClass c₀)) := by grw [hm, hPV]
    _ = m * (4 * (12 + 2 * p)) := by
      field_simp [(by linarith : (0 : ℝ) < #(vecSumTriples p (typeClass a₀) (typeClass b₀)
        (typeClass c₀))).ne']

end ArithmeticTriangleRemovalInVectorSpaces

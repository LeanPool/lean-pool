/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.Sampling
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Pruning vertices of large degree

Let `X × Y × Z` contain `D` triangles and `m` vertex-disjoint triangles `(x i, y i, z i)`. Fox and
Lovász remove vertices of large degree one at a time (Lemma 6). We choose instead, among all
`X' ⊆ X`, `Y' ⊆ Y` and `Z' ⊆ Z`, one minimizing the potential `r + A * D' ^ η`. Here `r` counts the
triangles `(x i, y i, z i)` outside `X' × Y' × Z'`, `D'` counts the triangles of `X' × Y' × Z'`,
`η = c p / (1 + c p)` and `A = m / (2 * D ^ η)`. Removing a vertex of degree `d` from a minimizer
raises `r` by at most one and lowers `D'` by `d`, so `d ≤ D' ^ (1 - η) / (A * η)`. Lemma 5 of Fox
and Lovász then gives `(η * m / 2) ^ (1 + c p) ≤ 125 * p ^ 2 * #V ^ (1 - c p) * D ^ c p`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.potential`: the potential `r + A * D' ^ η`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.card_filter_fst_le_of_potential_le`: the degree bound
  at a vertex whose removal does not lower the potential.
* `ArithmeticTriangleRemovalInVectorSpaces.card_triangles_pos_of_potential_le`: a configuration
  whose potential is at most that of `(X, Y, Z)` contains a triangle.
* `ArithmeticTriangleRemovalInVectorSpaces.rpow_le_mul_rpow_mul_card_triangles_rpow`: the bound
  `(η * m / 2) ^ (1 + c p) ≤ 125 * p ^ 2 * #V ^ (1 - c p) * D ^ c p`.
-/

public section

open Finset Function Submodule

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- A vertex of degree `d` whose removal from a configuration with `D` triangles does not lower the
potential satisfies `d ≤ D ^ (1 - η) / (A * η)`, by Bernoulli's inequality. -/
private lemma le_rpow_one_sub_div_of_mul_rpow_le {A η D d : ℝ} (hA : 0 < A) (hη₀ : 0 < η)
    (hη₁ : η ≤ 1) (hd₀ : 0 ≤ d) (hdD : d ≤ D) (h : A * D ^ η ≤ 1 + A * (D - d) ^ η) :
    d ≤ D ^ (1 - η) / (A * η) := by
  rcases hd₀.eq_or_lt with rfl | hd
  · positivity
  have hD : 0 < D := hd.trans_le hdD
  have hB : (D - d) ^ η ≤ D ^ η * (1 - η * (d / D)) := by
    rw [(by field_simp : D - d = D * (1 - d / D)),
      Real.mul_rpow hD.le (sub_nonneg.2 ((div_le_one hD).2 hdD))]
    gcongr
    simpa [sub_eq_add_neg] using
      rpow_one_add_le_one_add_mul_self (neg_le_neg ((div_le_one hD).2 hdD)) hη₀.le hη₁
  have key : A * D ^ η * η * (d / D) ≤ 1 := by linarith [mul_le_mul_of_nonneg_left hB hA.le]
  rw [mul_div_assoc', div_le_one hD] at key
  rw [Real.rpow_sub hD, Real.rpow_one, div_div, le_div_iff₀ (by positivity)]
  linarith

/-- If `(1 - η) * (1 + c) = 1` and `D' ≤ K * (D' ^ (1 - η) / B / N) ^ (1 + c) * N ^ 2`, then
`B ^ (1 + c) ≤ K * N ^ (1 - c)`. -/
private lemma rpow_le_mul_rpow_of_le_mul_div_rpow {K N D' B c η : ℝ} (hN : 0 < N) (hD' : 0 < D')
    (hB : 0 < B) (hη : (1 - η) * (1 + c) = 1)
    (h : D' ≤ K * (D' ^ (1 - η) / B / N) ^ (1 + c) * N ^ 2) :
    B ^ (1 + c) ≤ K * N ^ (1 - c) := by
  have hN2 : N ^ 2 = N ^ (1 + c) * N ^ (1 - c) := by
    rw [← Real.rpow_add hN]
    norm_num
  rw [Real.div_rpow (by positivity) hN.le, Real.div_rpow (by positivity) hB.le,
    ← Real.rpow_mul hD'.le, hη, Real.rpow_one, hN2] at h
  field_simp at h
  exact h

/-- The arithmetic of the pruning argument: Lemma 5 of Fox and Lovász for the degree bound
`D' ^ (1 - η) / (A * η)` with `A = m / (2 * D ^ η)` gives
`(η * m / 2) ^ (1 + c) ≤ K * N ^ (1 - c) * D ^ c`. -/
private lemma rpow_le_mul_rpow_mul_rpow_of_le {K N D D' m c : ℝ} (hc : 0 < c) (hN : 0 < N)
    (hD : 0 < D) (hD' : 0 < D') (hm : 0 < m)
    (h : D' ≤ K * (D' ^ (1 - c / (1 + c)) / (m / (2 * D ^ (c / (1 + c))) * (c / (1 + c))) / N) ^
      (1 + c) * N ^ 2) :
    (c / (1 + c) * m / 2) ^ (1 + c) ≤ K * N ^ (1 - c) * D ^ c := by
  have h := rpow_le_mul_rpow_of_le_mul_div_rpow hN hD' (by positivity) (by grind) h
  rwa [(by field_simp : m / (2 * D ^ (c / (1 + c))) * (c / (1 + c)) =
    c / (1 + c) * m / 2 / D ^ (c / (1 + c))), Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hD.le, (by grind : c / (1 + c) * (1 + c) = c),
    div_le_iff₀ (by positivity)] at h

variable {V ι : Type*} [AddCommGroup V] [DecidableEq V] [Fintype ι] {x y z : ι → V}

/-- The potential `r + A * D' ^ η` of `(X, Y, Z)`: `r` counts the indices `i` such that
`(x i, y i, z i)` does not lie in `X × Y × Z`, and `D'` counts the triangles of `X × Y × Z`. -/
private noncomputable def potential (x y z : ι → V) (A η : ℝ) : Finset V × Finset V × Finset V → ℝ
  | (X, Y, Z) => #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + A * #(triangles X Y Z) ^ η

omit [AddCommGroup V] in
/-- An injective family takes each value at most once. -/
private lemma card_filter_apply_eq_le_one {f : ι → V} (hf : Injective f) (v : V) :
    #{i | f i = v} ≤ 1 :=
  card_le_one.2 fun _ _ _ _ ↦ hf (by simp_all)

omit [AddCommGroup V] in
/-- Removing a vertex from `X` puts at most one more vertex-disjoint triangle outside. -/
private lemma card_filter_not_mem_erase_left_le (hx : Injective x) (X Y Z : Finset V) (v : V) :
    #{i | ¬(x i ∈ X.erase v ∧ y i ∈ Y ∧ z i ∈ Z)} ≤ #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
  classical
  grw [← card_filter_apply_eq_le_one hx v, ← card_union_le]
  apply card_le_card
  intro i
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_erase]
  tauto

omit [AddCommGroup V] in
/-- Removing a vertex from `Y` puts at most one more vertex-disjoint triangle outside. -/
private lemma card_filter_not_mem_erase_middle_le (hy : Injective y) (X Y Z : Finset V) (v : V) :
    #{i | ¬(x i ∈ X ∧ y i ∈ Y.erase v ∧ z i ∈ Z)} ≤ #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
  classical
  grw [← card_filter_apply_eq_le_one hy v, ← card_union_le]
  apply card_le_card
  intro i
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_erase]
  tauto

omit [AddCommGroup V] in
/-- Removing a vertex from `Z` puts at most one more vertex-disjoint triangle outside. -/
private lemma card_filter_not_mem_erase_right_le (hz : Injective z) (X Y Z : Finset V) (v : V) :
    #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z.erase v)} ≤ #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
  classical
  grw [← card_filter_apply_eq_le_one hz v, ← card_union_le]
  apply card_le_card
  intro i
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_erase]
  tauto

variable {A η : ℝ} {X Y Z X' Y' Z' : Finset V} {v : V}

/-- If removing `v` from `X` does not lower the potential, then `v` lies in at most
`D' ^ (1 - η) / (A * η)` triangles. -/
private lemma card_filter_fst_le_of_potential_le (hx : Injective x) (hA : 0 < A) (hη₀ : 0 < η)
    (hη₁ : η ≤ 1) (h : potential x y z A η (X, Y, Z) ≤ potential x y z A η (X.erase v, Y, Z)) :
    #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤
      #(triangles X Y Z) ^ (1 - η) / (A * η) := by
  refine le_rpow_one_sub_div_of_mul_rpow_le hA hη₀ hη₁ (Nat.cast_nonneg _)
    (by exact_mod_cast card_filter_le _ _) ?_
  have hr : (#{i | ¬(x i ∈ X.erase v ∧ y i ∈ Y ∧ z i ∈ Z)} : ℝ) ≤
      #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
    exact_mod_cast card_filter_not_mem_erase_left_le hx X Y Z v
  simp only [potential, ← card_triangles_erase_left X Y Z v] at h ⊢
  push_cast at h ⊢
  rw [add_sub_cancel_right]
  linarith

/-- If removing `v` from `Y` does not lower the potential, then `v` lies in at most
`D' ^ (1 - η) / (A * η)` triangles. -/
private lemma card_filter_snd_le_of_potential_le (hy : Injective y) (hA : 0 < A) (hη₀ : 0 < η)
    (hη₁ : η ≤ 1) (h : potential x y z A η (X, Y, Z) ≤ potential x y z A η (X, Y.erase v, Z)) :
    #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤
      #(triangles X Y Z) ^ (1 - η) / (A * η) := by
  refine le_rpow_one_sub_div_of_mul_rpow_le hA hη₀ hη₁ (Nat.cast_nonneg _)
    (by exact_mod_cast card_filter_le _ _) ?_
  have hr : (#{i | ¬(x i ∈ X ∧ y i ∈ Y.erase v ∧ z i ∈ Z)} : ℝ) ≤
      #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
    exact_mod_cast card_filter_not_mem_erase_middle_le hy X Y Z v
  simp only [potential, ← card_triangles_erase_middle X Y Z v] at h ⊢
  push_cast at h ⊢
  rw [add_sub_cancel_right]
  linarith

/-- If removing `v` from `Z` does not lower the potential, then `v` lies in at most
`D' ^ (1 - η) / (A * η)` triangles. -/
private lemma card_filter_thd_le_of_potential_le (hz : Injective z) (hA : 0 < A) (hη₀ : 0 < η)
    (hη₁ : η ≤ 1) (h : potential x y z A η (X, Y, Z) ≤ potential x y z A η (X, Y, Z.erase v)) :
    #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤
      #(triangles X Y Z) ^ (1 - η) / (A * η) := by
  refine le_rpow_one_sub_div_of_mul_rpow_le hA hη₀ hη₁ (Nat.cast_nonneg _)
    (by exact_mod_cast card_filter_le _ _) ?_
  have hr : (#{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z.erase v)} : ℝ) ≤
      #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + 1 := by
    exact_mod_cast card_filter_not_mem_erase_right_le hz X Y Z v
  simp only [potential, ← card_triangles_erase_right X Y Z v] at h ⊢
  push_cast at h ⊢
  rw [add_sub_cancel_right]
  linarith

/-- If `(x i, y i, z i)` lies in `X × Y × Z` for every `i`, then the potential of `(X, Y, Z)` is
`A * D ^ η`. -/
private lemma potential_eq_mul_rpow (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z) :
    potential x y z A η (X, Y, Z) = A * #(triangles X Y Z) ^ η := by
  simp [potential, hxX, hyY, hzZ]

/-- If `X × Y × Z` contains no triangle, then its potential is the number of indices. -/
private lemma potential_eq_card_of_triangles_eq_empty (hsum : ∀ i, x i + y i + z i = 0) (hη : η ≠ 0)
    (h : triangles X Y Z = ∅) : potential x y z A η (X, Y, Z) = Fintype.card ι := by
  have hout (i : ι) : ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z) := by
    rintro ⟨hx, hy, hz⟩
    simpa [h] using mem_triangles.2 ⟨hx, hy, hz, hsum i⟩
  simp [potential, hout, h, Real.zero_rpow hη]

omit [Fintype ι] in
/-- If `X × Y × Z` contains the triangles `(x i, y i, z i)` and there is at least one index, then
`X × Y × Z` contains a triangle. -/
lemma card_triangles_pos [Nonempty ι] (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y)
    (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) : 0 < #(triangles X Y Z) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact card_pos.2 ⟨_, mem_triangles.2 ⟨hxX i, hyY i, hzZ i, hsum i⟩⟩

/-- Let `X × Y × Z` contain the triangles `(x i, y i, z i)`, `D` triangles in total, and take
`A = m / (2 * D ^ η)`. If the potential of `(X', Y', Z')` is at most that of `(X, Y, Z)`, then
`X' × Y' × Z'` contains a triangle: otherwise its potential is `m`, whereas that of `(X, Y, Z)` is
`m / 2`. -/
private lemma card_triangles_pos_of_potential_le [Nonempty ι] (hsum : ∀ i, x i + y i + z i = 0)
    (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z) (hη : η ≠ 0)
    (h : potential x y z (Fintype.card ι / (2 * #(triangles X Y Z) ^ η)) η (X', Y', Z') ≤
      potential x y z (Fintype.card ι / (2 * #(triangles X Y Z) ^ η)) η (X, Y, Z)) :
    0 < #(triangles X' Y' Z') := by
  have hD := card_triangles_pos hxX hyY hzZ hsum
  rw [card_pos, nonempty_iff_ne_empty]
  intro hT
  rw [potential_eq_card_of_triangles_eq_empty hsum hη hT, potential_eq_mul_rpow hxX hyY hzZ] at h
  field_simp at h
  linarith [(by positivity : (0 : ℝ) < Fintype.card ι)]

variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Fintype V]

/-- **Pruning.** If the first two vertices of each triangle of `X × Y × Z` are linearly
independent, their span contains the first two vertices of no other triangle, and `X × Y × Z`
contains `m` vertex-disjoint triangles `(x i, y i, z i)`, then
`(η * m / 2) ^ (1 + c p) ≤ 125 * p ^ 2 * #V ^ (1 - c p) * D ^ c p`, where `η = c p / (1 + c p)`
and `D` is the number of triangles. -/
lemma rpow_le_mul_rpow_mul_card_triangles_rpow
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hx : Injective x) (hy : Injective y) (hz : Injective z) (hxX : ∀ i, x i ∈ X)
    (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) :
    (c p / (1 + c p) * Fintype.card ι / 2) ^ (1 + c p) ≤
      125 * p ^ 2 * Fintype.card V ^ (1 - c p) * #(triangles X Y Z) ^ c p := by
  have hc := c_pos (Fact.out : p.Prime).two_le
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Fintype.card_eq_zero, Nat.cast_zero, mul_zero, zero_div,
      Real.zero_rpow (by linarith : 1 + c p ≠ 0)]
    positivity
  have hD := card_triangles_pos hxX hyY hzZ hsum
  have hA : 0 < (Fintype.card ι : ℝ) / (2 * #(triangles X Y Z) ^ (c p / (1 + c p))) := by
    positivity
  obtain ⟨⟨X', Y', Z'⟩, hS, hmin⟩ := exists_min_image (X.powerset ×ˢ Y.powerset ×ˢ Z.powerset)
    (potential x y z ((Fintype.card ι : ℝ) / (2 * #(triangles X Y Z) ^ (c p / (1 + c p))))
      (c p / (1 + c p))) ⟨(X, Y, Z), by simp⟩
  obtain ⟨hX', hY', hZ'⟩ : X' ⊆ X ∧ Y' ⊆ Y ∧ Z' ⊆ Z := by simpa using hS
  have hη₁ : c p / (1 + c p) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  refine rpow_le_mul_rpow_mul_rpow_of_le hc (by positivity) (by positivity)
    (Nat.cast_pos.2 (card_triangles_pos_of_potential_le hsum hxX hyY hzZ (by positivity)
      (hmin _ (by simp)))) (by positivity) ?_
  refine card_triangles_le_of_degree_le
    (fun a b c ht ↦ hli a b c (triangles_mono hX' hY' hZ' ht))
    (fun a b c ht a' b' c' ht' ↦ hspan a b c (triangles_mono hX' hY' hZ' ht) a' b' c'
      (triangles_mono hX' hY' hZ' ht')) ?_ ?_ ?_
  · intro v
    rw [div_mul_cancel₀ _ (by positivity)]
    exact card_filter_fst_le_of_potential_le hx hA (by positivity) hη₁
      (hmin _ (by simp [hY', hZ', (erase_subset v X').trans hX']))
  · intro v
    rw [div_mul_cancel₀ _ (by positivity)]
    exact card_filter_snd_le_of_potential_le hy hA (by positivity) hη₁
      (hmin _ (by simp [hX', hZ', (erase_subset v Y').trans hY']))
  · intro v
    rw [div_mul_cancel₀ _ (by positivity)]
    exact card_filter_thd_le_of_potential_le hz hA (by positivity) hη₁
      (hmin _ (by simp [hX', hY', (erase_subset v Z').trans hZ']))

end ArithmeticTriangleRemovalInVectorSpaces

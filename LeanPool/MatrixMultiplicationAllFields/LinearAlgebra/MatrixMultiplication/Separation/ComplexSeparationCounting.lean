/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation.Separation

abbrev Grid (d Q : ℕ) := Fin d → Fin Q

def gridSquaredNorm {d Q : ℕ} (x : Grid d Q) : ℕ := ∑ i, (x i : ℕ) ^ 2

def gridDot {d Q : ℕ} (t u : Grid d Q) : ℕ := ∑ i, (t i : ℕ) * (u i : ℕ)

theorem gridSquaredNorm_le {d Q : ℕ} (x : Grid d Q) : gridSquaredNorm x ≤ d * Q ^ 2 := by
  calc
    gridSquaredNorm x ≤ ∑ _i : Fin d, Q ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.pow_le_pow_left (Nat.le_of_lt (x i).isLt) 2
    _ = d * Q ^ 2 := by simp

theorem gridDot_le {d Q : ℕ} (t u : Grid d Q) : gridDot t u ≤ d * Q ^ 2 := by
  calc
    gridDot t u ≤ ∑ _i : Fin d, Q ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [pow_two] using
        Nat.mul_le_mul (Nat.le_of_lt (t i).isLt) (Nat.le_of_lt (u i).isLt)
    _ = d * Q ^ 2 := by simp

def normColor {d Q : ℕ} (x : Grid d Q) : Fin (d * Q ^ 2 + 1) :=
  ⟨gridSquaredNorm x, Nat.lt_succ_of_le (gridSquaredNorm_le x)⟩

def dotColor {d Q : ℕ} (t u : Grid d Q) : Fin (d * Q ^ 2 + 1) :=
  ⟨gridDot t u, Nat.lt_succ_of_le (gridDot_le t u)⟩

theorem two_stage_pigeonhole {A : Type*} [Fintype A] [DecidableEq A]
    {M K m : ℕ} (hM : 0 < M) (f : A → Fin M) (g : A → A → Fin M)
    (hK : M * K ≤ Fintype.card A) (hm : M * m ≤ Fintype.card A) :
    ∃ tags : Finset A, tags.card = K ∧
      (∃ radius : Fin M, ∀ t ∈ tags, f t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset A, slice.card = m ∧
        ∃ level : Fin M, ∀ u ∈ slice, g t u = level := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨radius, hr⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f
    (by simpa only [Fintype.card_fin] using hK)
  obtain ⟨tags, htags, hcard⟩ := Finset.exists_subset_card_eq hr
  refine ⟨tags, hcard, ⟨radius, ?_⟩, ?_⟩
  · intro t ht
    exact (Finset.mem_filter.mp (htags ht)).2
  · intro t ht
    obtain ⟨level, hl⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (g t)
      (by simpa only [Fintype.card_fin] using hm)
    obtain ⟨slice, hslice, hsize⟩ := Finset.exists_subset_card_eq hl
    refine ⟨slice, hsize, level, ?_⟩
    intro u hu
    exact (Finset.mem_filter.mp (hslice hu)).2

theorem grid_tags_slices {d Q K m : ℕ}
    (hK : (d * Q ^ 2 + 1) * K ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d) :
    ∃ tags : Finset (Grid d Q), tags.card = K ∧
      (∃ radius : Fin (d * Q ^ 2 + 1), ∀ t ∈ tags, normColor t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset (Grid d Q), slice.card = m ∧
        ∃ level : Fin (d * Q ^ 2 + 1), ∀ u ∈ slice, dotColor t u = level := by
  exact two_stage_pigeonhole (Nat.succ_pos _) normColor dotColor
    (by simpa only [Grid, Fintype.card_fun, Fintype.card_fin] using hK)
    (by simpa only [Grid, Fintype.card_fun, Fintype.card_fin] using hm)

end MatrixMultiplication.Foundation.Separation

end MatrixMultiplicationAllFields

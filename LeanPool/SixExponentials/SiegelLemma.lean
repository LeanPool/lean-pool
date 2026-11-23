/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# Siegel's lemma, entrywise

Siegel's lemma for an integer matrix with an entrywise bound on its coefficients.

From `SixExponentials/Basic/siegel_entrywise.lean` of `carlok/six-exponentials-lean`;
see `LeanPool.SixExponentials` for provenance.
-/

@[expose] public section

namespace SixExponentials.Transcendence

/-!
# Siegel's lemma with an entrywise bound

Let `A` be an integer matrix with `m` rows, `n ≥ 2m` columns and entries of absolute value at most
`B ≥ 1`. With no rows, a unit vector is a non-zero solution of `A t = 0`. Otherwise Siegel's lemma
gives a non-zero integer solution with `|t_b| ≤ (n · max(1, ‖A‖))^(m / (n - m))`, where `‖A‖ ≤ B`
is the largest absolute value of an entry. The exponent `m / (n - m)` lies in `[0, 1]` and
`n B ≥ 1`, so `|t_b| ≤ n B`.
-/

attribute [local instance] Matrix.seminormedAddCommGroup in
theorem siegel_entrywise {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)
    (hβ : 0 < Fintype.card β) (hcard : 2 * Fintype.card α ≤ Fintype.card β) {B : ℝ}
    (hB : 1 ≤ B) (hA : ∀ a b, |(A a b : ℝ)| ≤ B) :
    ∃ t : β → ℤ, t ≠ 0 ∧ (∀ a, ∑ b, A a b * t b = 0) ∧
      ∀ b, |(t b : ℝ)| ≤ Fintype.card β * B := by
  classical
  have hn1 : (1 : ℝ) ≤ Fintype.card β := by exact_mod_cast hβ
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · -- no equations: a unit vector will do
    obtain ⟨b0⟩ : Nonempty β := Fintype.card_pos_iff.1 hβ
    have : IsEmpty α := Fintype.card_eq_zero_iff.1 h0
    refine ⟨Pi.single b0 1, fun h => by simpa using congrFun h b0, fun a => isEmptyElim a,
      fun b => ?_⟩
    by_cases hb : b = b0
    · subst hb; simp; nlinarith
    · simp [hb]; nlinarith
  · obtain ⟨t, ht0, hAt, hnorm⟩ :=
      Int.Matrix.exists_ne_zero_int_vec_norm_le A (by omega) hpos
    refine ⟨t, ht0, fun a => by simpa [Matrix.mulVec, dotProduct] using congrFun hAt a,
      fun b => ?_⟩
    have hmax : max 1 ‖A‖ ≤ B := max_le hB <| (Matrix.norm_le_iff (by linarith)).2
      fun i j => by rw [Int.norm_eq_abs]; exact hA i j
    have h2 : (2 : ℝ) * Fintype.card α ≤ Fintype.card β := by exact_mod_cast hcard
    have hm : (0 : ℝ) < Fintype.card α := by exact_mod_cast hpos
    -- with at least twice as many unknowns as equations the Siegel exponent is at most one
    have he1 : ((Fintype.card α : ℕ) : ℝ) / ((Fintype.card β : ℕ) - (Fintype.card α : ℕ)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have he0 :
        (0 : ℝ) ≤ ((Fintype.card α : ℕ) : ℝ) / ((Fintype.card β : ℕ) - (Fintype.card α : ℕ)) :=
      div_nonneg hm.le (by linarith)
    have hbase : (1 : ℝ) ≤ Fintype.card β * B := by nlinarith
    calc |(t b : ℝ)| = ‖t b‖ := (Int.norm_eq_abs _).symm
      _ ≤ ‖t‖ := norm_le_pi_norm t b
      _ ≤ _ := hnorm
      _ ≤ ((Fintype.card β : ℝ) * B) ^ (((Fintype.card α : ℕ) : ℝ) /
            ((Fintype.card β : ℕ) - (Fintype.card α : ℕ))) :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hmax (by positivity)) he0
      _ ≤ ((Fintype.card β : ℝ) * B) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase he1
      _ = Fintype.card β * B := Real.rpow_one _

end SixExponentials.Transcendence

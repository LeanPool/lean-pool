/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Boolean

/-!
# Mixed slice moments

The second identity in Lemma C.1, for disjoint selected and excluded variable sets.
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- The Boolean indicator that every index in `S` is selected and every index in `T` excluded. -/
noncomputable def mixedMonomial {n : ℕ} (S T : Finset (Fin n)) : BooleanPolynomial n :=
  booleanMonomial S 1 * ∏ i ∈ T, (1 - booleanVar i)

theorem mixedMonomial_insert {n : ℕ} (S T : Finset (Fin n)) {i : Fin n} (hi : i ∉ T) :
    mixedMonomial S (insert i T) = mixedMonomial S T - mixedMonomial (insert i S) T := by
  classical
  have hmono : booleanMonomial (insert i S) 1 = booleanMonomial S 1 * booleanVar i := by
    rw [booleanVar, booleanMonomial_mul]
    simp
  simp only [mixedMonomial, Finset.prod_insert hi, hmono]
  ring

/-- The scalar recurrence for inserting one excluded index. -/
theorem mixed_moment_step (n r q : ℕ) (s : ℝ) (hsize : r + q < n) :
    falling s r * falling ((n : ℝ) - s) q / falling n (r + q) -
      falling s (r + 1) * falling ((n : ℝ) - s) q / falling n (r + 1 + q) =
      falling s r * falling ((n : ℝ) - s) (q + 1) / falling n (r + (q + 1)) := by
  have hf : falling (n : ℝ) (r + q) ≠ 0 := by
    rw [falling_natCast]
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hsize.le))
  have hgap : (n : ℝ) - (r + q) ≠ 0 := by
    have hR : (r : ℝ) + q < n := by exact_mod_cast hsize
    linarith
  rw [show r + 1 + q = (r + q) + 1 by omega,
    show r + (q + 1) = (r + q) + 1 by omega]
  simp only [falling_succ]
  push_cast at hgap ⊢
  field_simp [hf, hgap]
  ring

/-- Lemma C.1's mixed-moment identity for the constructed slice functional. -/
theorem sliceFunctional_mixedMonomial {n : ℕ} (s : ℝ) (S T : Finset (Fin n))
    (hST : Disjoint S T) :
    sliceFunctional n s (mixedMonomial S T) =
      falling s S.card * falling ((n : ℝ) - s) T.card / falling n (S.card + T.card) := by
  classical
  induction T using Finset.induction_on generalizing S with
  | empty =>
    simp [mixedMonomial, sliceFunctional_monomial, sliceMoment]
  | @insert i T hi ih =>
    have hiS : i ∉ S := (Finset.disjoint_insert_right.mp hST).1
    have hST0 : Disjoint S T := (Finset.disjoint_insert_right.mp hST).2
    have hST1 : Disjoint (insert i S) T := Finset.disjoint_insert_left.mpr ⟨hi, hST0⟩
    have hsize : S.card + T.card < n := by
      have hc : (S ∪ insert i T).card ≤ n := by simpa using Finset.card_le_univ (S ∪ insert i T)
      rw [Finset.card_union_of_disjoint hST, Finset.card_insert_of_notMem hi] at hc
      omega
    rw [mixedMonomial_insert S T hi, map_sub, ih S hST0, ih (insert i S) hST1,
      Finset.card_insert_of_notMem hiS, Finset.card_insert_of_notMem hi]
    exact mixed_moment_step n S.card T.card s hsize

end NoncommutativeAMGM

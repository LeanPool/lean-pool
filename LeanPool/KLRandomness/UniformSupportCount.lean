/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Counts for uniformly chosen fixed-size supports

The sample space is the actual finite type of `m`-element subsets of a pool
of `M` positions.  Counts for containing a fixed set specialize to the one-
and two-position inclusion probabilities needed for the support variance bound.
-/

@[expose] public section

namespace Klr.UniformSupport

/-- The finite sample space of supports with exactly `m` positions. -/
abbrev Support (M m : ℕ) := {S : Finset (Fin M) // S.card = m}

theorem card_support (M m : ℕ) : Fintype.card (Support M m) = M.choose m := by
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter (fun S : Finset (Fin M) => S.card = m)) =
      (Finset.univ : Finset (Fin M)).powersetCard m := by
    ext S
    simp
  rw [he, Finset.card_powersetCard]
  simp

theorem card_support_pos {M m : ℕ} (hm : m ≤ M) : 0 < Fintype.card (Support M m) := by
  rw [card_support]
  exact Nat.choose_pos hm

theorem support_nonempty {M m : ℕ} (hm : m ≤ M) : Nonempty (Support M m) :=
  Fintype.card_pos_iff.mp (card_support_pos hm)

private def eventEquiv (M m : ℕ) (P : Finset (Fin M) → Prop) [DecidablePred P] :
    {S : Support M m // P S.val} ≃
      ↥(((Finset.univ : Finset (Fin M)).powersetCard m).filter P) where
  toFun S := ⟨S.val.val, by simpa using And.intro S.val.property S.property⟩
  invFun S := ⟨⟨S.val, by simpa using (Finset.mem_filter.mp S.property).1⟩,
    (Finset.mem_filter.mp S.property).2⟩
  left_inv S := rfl
  right_inv S := rfl

theorem card_event (M m : ℕ) (P : Finset (Fin M) → Prop) [DecidablePred P] :
    Nat.card {S : Support M m | P S.val} =
      (((Finset.univ : Finset (Fin M)).powersetCard m).filter P).card := by
  change Nat.card {S : Support M m // P S.val} = _
  rw [Nat.card_congr (eventEquiv M m P), Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Exact number of supports containing a prescribed finite set. -/
theorem card_contains {M m : ℕ} (T : Finset (Fin M)) (hTm : T.card ≤ m) :
    Nat.card {S : Support M m | T ⊆ S.val} = (M - T.card).choose (m - T.card) := by
  rw [card_event]
  simpa using Finset.card_filter_powersetCard_subset T Finset.univ m
    (Finset.subset_univ _) hTm

theorem card_contains_one {M m : ℕ} (hm : 1 ≤ m) (a : Fin M) :
    Nat.card {S : Support M m | a ∈ S.val} = (M - 1).choose (m - 1) := by
  simpa using card_contains (m := m) ({a} : Finset (Fin M)) (by simpa using hm)

theorem card_contains_pair {M m : ℕ} (hm : 2 ≤ m) (a b : Fin M) (hab : a ≠ b) :
    Nat.card {S : Support M m | a ∈ S.val ∧ b ∈ S.val} =
      (M - 2).choose (m - 2) := by
  simpa [hab, Finset.insert_subset_iff] using
    card_contains (m := m) ({a, b} : Finset (Fin M)) (by simp [hab, hm])

theorem choose_ratio_one {M m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ M) :
    ((M - 1).choose (m - 1) : ℝ) / M.choose m = (m : ℝ) / M := by
  have hM : 0 < M := by omega
  have hC : (M.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmM).ne'
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  apply (div_eq_div_iff hC hM').mpr
  have h := Nat.add_one_mul_choose_eq (M - 1) (m - 1)
  have he : M * (M - 1).choose (m - 1) = M.choose m * m := by
    simpa only [Nat.sub_add_cancel hM, Nat.sub_add_cancel hm1] using h
  exact_mod_cast (by nlinarith [he] : (M - 1).choose (m - 1) * M = m * M.choose m)

theorem choose_ratio_pair {M m : ℕ} (hm2 : 2 ≤ m) (hmM : m ≤ M) :
    ((M - 2).choose (m - 2) : ℝ) / M.choose m =
      ((m : ℝ) * (m - 1)) / ((M : ℝ) * (M - 1)) := by
  have hM2 : 2 ≤ M := by omega
  have hC : (M.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmM).ne'
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hM1 : (M : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ M := by exact_mod_cast hM2
    linarith
  apply (div_eq_div_iff hC (mul_ne_zero hM hM1)).mpr
  have h1 : M * (M - 1).choose (m - 1) = M.choose m * m := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ M), Nat.sub_add_cancel (by omega : 1 ≤ m)]
      using Nat.add_one_mul_choose_eq (M - 1) (m - 1)
  have h2 : (M - 1) * (M - 2).choose (m - 2) =
      (M - 1).choose (m - 1) * (m - 1) := by
    simpa only [show M - 2 + 1 = M - 1 by omega, show m - 2 + 1 = m - 1 by omega]
      using Nat.add_one_mul_choose_eq (M - 2) (m - 2)
  have he : (M - 2).choose (m - 2) * (M * (M - 1)) =
      (m * (m - 1)) * M.choose m := by nlinarith [congrArg (M * ·) h2]
  have he' := congrArg (fun n : ℕ => (n : ℝ)) he
  push_cast at he'
  simpa only [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_sub (by omega : 1 ≤ m),
    Nat.cast_one] using he'

/-- Sampling without replacement makes two distinct inclusion indicators negatively correlated. -/
theorem choose_ratio_pair_le_sq {M m : ℕ} (hm2 : 2 ≤ m) (hmM : m ≤ M) :
    ((M - 2).choose (m - 2) : ℝ) / M.choose m ≤ ((m : ℝ) / M) ^ 2 := by
  rw [choose_ratio_pair hm2 hmM]
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM1 : (0 : ℝ) < M - 1 := by
    have hh : (2 : ℝ) ≤ M := by exact_mod_cast (le_trans hm2 hmM)
    linarith
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmM' : (m : ℝ) ≤ M := by exact_mod_cast hmM
  apply (div_le_iff₀ (mul_pos hM hM1)).mpr
  field_simp
  nlinarith

end Klr.UniformSupport

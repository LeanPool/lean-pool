/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import Mathlib.Tactic.Linarith
public import LeanPool.LatinQuarter.Rows

/-!
# The global clue budget
-/

@[expose] public section

namespace LatinQuarter
open scoped BigOperators

theorem quarter_eq (n : ℕ) : n * n / 4 = (n / 2) * (n - n / 2) := by
  have hn : n = 2 * (n / 2) + n % 2 := by omega
  have hk : n / 2 ≤ n := by omega
  have hsub : n - n / 2 + n / 2 = n := Nat.sub_add_cancel hk
  have he : n * n = 4 * ((n / 2) * (n - n / 2)) + n % 2 := by
    have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hm with hm | hm <;> rw [hm] at hn ⊢ <;> nlinarith
  omega

theorem sum_free_columns {n : ℕ} (P : Finset (Cell n)) :
    (∑ r, Fintype.card (FreeColumn P r)) + P.card = n * n := by
  classical
  let e : ((r : Fin n) × FreeColumn P r) ≃ {p : Cell n // p ∉ P} :=
    { toFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
      invFun := fun x => ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }
  have hc := Fintype.card_congr e
  rw [Fintype.card_sigma, Fintype.card_subtype_compl] at hc
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at hc
  have hp : P.card ≤ n * n := by
    simpa using (Finset.card_le_univ P)
  omega

/-- The global clue budget supplies exactly the strict inequality used
by the residual-position pigeonhole argument. -/
theorem clue_budget {n : ℕ} (P : Finset (Cell n))
    (hP : P.card < n * n / 4) :
    (n - n / 2) * (n - n / 2) <
      ∑ r, (Fintype.card (FreeColumn P r) - n / 2) := by
  have hs := sum_free_columns P
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun r => Fintype.card (FreeColumn P r))
    (g := fun r => Fintype.card (FreeColumn P r) - n / 2 + n / 2)
    (fun r _ => by omega)
  rw [Finset.sum_add_distrib] at hb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  rw [quarter_eq] at hP
  have hk : n / 2 ≤ n := by omega
  have hn : n = n / 2 + (n - n / 2) := by omega
  nlinarith

end LatinQuarter

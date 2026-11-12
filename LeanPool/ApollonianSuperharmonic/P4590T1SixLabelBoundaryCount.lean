/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: P4590T1SixLabelBoundaryCount]

/-!
# P4590T1SixLabelBoundaryCount

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4590T1SixLabelBoundaryCount (p : Fin 3 → Bool → Prop)
    (hAE : ¬ (p 0 true ∧ p 2 true))
    (hBF : ¬ (p 0 false ∧ p 2 false))
    (hCD : ¬ (p 1 true ∧ p 1 false))
    (hCE : ¬ (p 1 true ∧ p 2 true))
    (hDF : ¬ (p 1 false ∧ p 2 false))
    (hEF : ¬ (p 2 true ∧ p 2 false)) :
    let k := Nat.card {is : Fin 3 × Bool // p is.1 is.2}
    k ≤ 3 ∧
    (k = 2 →
      (p 0 true ∧ p 0 false) ∨
      (p 0 true ∧ p 1 true) ∨
      (p 0 false ∧ p 1 false) ∨
      ∃ i j : Fin 3, i ≠ j ∧ p i true ∧ p j false) ∧
    (k = 3 →
      (p 0 true ∧ p 0 false ∧ p 1 true) ∨
      (p 0 true ∧ p 0 false ∧ p 1 false) ∨
      (p 0 true ∧ p 1 true ∧ p 2 false) ∨
      (p 0 false ∧ p 1 false ∧ p 2 true)) ∧
    ((∀ i, p i true ↔ p i false) →
      k ≠ 3 ∧ (k = 2 → p 0 true ∧ p 0 false)) := by
-- BODY
  classical
  have hc : Nat.card {is : Fin 3 × Bool // p is.1 is.2} =
      (if p 0 false then 1 else 0) + (if p 0 true then 1 else 0) +
      (if p 1 false then 1 else 0) + (if p 1 true then 1 else 0) +
      (if p 2 false then 1 else 0) + (if p 2 true then 1 else 0) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have huniv : (Finset.univ : Finset (Fin 3 × Bool)) =
        {(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)} := by
      decide
    rw [huniv]
    by_cases ha : p 0 true <;> by_cases hb : p 0 false <;>
      by_cases hc : p 1 true <;> by_cases hd : p 1 false <;>
      by_cases he : p 2 true <;> by_cases hf : p 2 false <;>
      simp_all [Finset.filter_insert, Finset.filter_singleton]
  dsimp only
  rw [hc]
  simp only [ne_eq, Fin.exists_fin_succ, Fin.exists_fin_zero, Fin.forall_fin_succ,
    Fin.forall_fin_zero]
  by_cases ha : p 0 true <;> by_cases hb : p 0 false <;>
    by_cases hc : p 1 true <;> by_cases hd : p 1 false <;>
    by_cases he : p 2 true <;> by_cases hf : p 2 false <;>
    simp_all

end ApollonianSuperharmonic

end

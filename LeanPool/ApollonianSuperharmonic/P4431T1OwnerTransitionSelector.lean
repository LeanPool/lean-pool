/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FinCases

-- [TABLET NODE: P4431T1OwnerTransitionSelector]

/-!
# P4431T1OwnerTransitionSelector

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4431T1OwnerTransitionSelector {α : Type*}
    (o : Fin 4 → α) (s : Fin 4 → Bool)
    (hleft : ∀ i k, s i ≠ s (i + 1) → o k = o i → s k = s i)
    (hright : ∀ i k, s i ≠ s (i + 1) →
      o k = o (i + 1) → s k = s (i + 1))
    (hrepeat : o 0 = o 1 ∨ o 0 = o 2 ∨ o 0 = o 3 ∨
      o 1 = o 2 ∨ o 1 = o 3 ∨ o 2 = o 3)
    (hchecker : ¬ ((o 0 = o 2 ∧ o 1 ≠ o 0 ∧ o 3 ≠ o 0) ∨
      (o 1 = o 3 ∧ o 0 ≠ o 1 ∧ o 2 ≠ o 1)))
    (hopposite : s 0 ≠ s 2 ∨ s 1 ≠ s 3) :
    ∃ i, s i ≠ s (i + 1) ∧
      (o i = o (i + 3) ∨ o (i + 1) = o (i + 2)) := by
-- BODY
  classical
  have finite_selection :
      ∀ (a b c d : Fin 4) (sa sb sc sd : Bool),
        let p : Fin 4 → Fin 4 := ![a, b, c, d]
        let t : Fin 4 → Bool := ![sa, sb, sc, sd]
        (∀ i k, t i ≠ t (i + 1) →
          (p k = p i → t k = t i) ∧
            (p k = p (i + 1) → t k = t (i + 1))) →
        (a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) →
        ¬ ((a = c ∧ b ≠ a ∧ d ≠ a) ∨
          (b = d ∧ a ≠ b ∧ c ≠ b)) →
        (sa ≠ sc ∨ sb ≠ sd) →
        ∃ i, t i ≠ t (i + 1) ∧
          (p i = p (i + 3) ∨ p (i + 1) = p (i + 2)) := by
    exact ((((by decide +kernel))))
  let encode : α → Fin 4 := fun a =>
    if a = o 0 then 0 else if a = o 1 then 1 else if a = o 2 then 2 else 3
  have encode_eq (i j : Fin 4) : encode (o i) = encode (o j) ↔ o i = o j := by
    clear * - o encode
    fin_cases i <;> fin_cases j <;>
      simp only [ Fin.isValue, Fin.zero_eta, ↓reduceIte, encode, Fin.mk_one, left_eq_ite_iff,
    zero_ne_one, imp_false, Decidable.not_not, Fin.reduceFinMk, ite_eq_left_iff, one_ne_zero ] <;>
      (try split_ifs) <;> simp_all [eq_comm]
  have ho : ![encode (o 0), encode (o 1), encode (o 2), encode (o 3)] =
      fun i => encode (o i) := by
    funext i
    fin_cases i <;> rfl
  have hs : ![s 0, s 1, s 2, s 3] = s := by
    funext i
    fin_cases i <;> rfl
  have hf := finite_selection (encode (o 0)) (encode (o 1))
    (encode (o 2)) (encode (o 3)) (s 0) (s 1) (s 2) (s 3)
  dsimp only at hf
  rw [ho, hs] at hf
  simp only [ne_eq, encode_eq] at hf
  exact hf (fun i k h => ⟨hleft i k h, hright i k h⟩)
    hrepeat hchecker hopposite

end ApollonianSuperharmonic

end

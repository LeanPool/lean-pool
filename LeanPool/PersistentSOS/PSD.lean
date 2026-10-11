/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Exact positive semidefinite certificate calculus

Integer fraction-free Schur certificates are checked by the Lean kernel.
-/

@[expose] public section


namespace PersistentSOS

open scoped BigOperators

/-- The quadratic form of a real matrix. -/
def quadraticForm {n : ℕ} (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

/-- Nonnegativity of the quadratic form; symmetry is verified independently. -/
def IsPSD {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ x, 0 ≤ quadraticForm A x

lemma quadraticForm_zero (A : Fin 0 → Fin 0 → ℝ) : IsPSD A := by
  intro x
  simp [quadraticForm]

/-- One fraction - free Schur step, with an independently checked previous pivot. -/
lemma schur_step {n : ℕ} (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (B : Fin n → Fin n → ℝ) (p : ℝ)
    (hp : 0 < p) (ha : 0 < A 0 0)
    (hsym : ∀ i : Fin n, A i.succ 0 = A 0 i.succ)
    (hstep : ∀ i j, p * B i j = A 0 0 * A i.succ j.succ -
      A i.succ 0 * A 0 j.succ) (hB : IsPSD B) : IsPSD A := by
  intro x
  let y : Fin n → ℝ := fun i => x i.succ
  let v : ℝ := ∑ i : Fin n, A 0 i.succ * y i
  have htail : A 0 0 * quadraticForm (fun i j : Fin n => A i.succ j.succ) y =
      p * quadraticForm B y + v ^ 2 := by
    simp only [quadraticForm, v, pow_two, Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have h := hstep i j
    rw [hsym] at h
    linear_combination -(y i * y j) * h
  have hleft : (∑ i : Fin n, x 0 * A 0 i.succ * x i.succ) = x 0 * v := by
    simp [v, y, Finset.mul_sum, mul_assoc]
  have hright : (∑ i : Fin n, x i.succ * A i.succ 0 * x 0) = x 0 * v := by
    simp only [v, y, Finset.mul_sum, hsym]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hfull : quadraticForm A x = A 0 0 * x 0 ^ 2 + 2 * x 0 * v +
      quadraticForm (fun i j : Fin n => A i.succ j.succ) y := by
    simp only [quadraticForm, Fin.sum_univ_succ, Finset.sum_add_distrib]
    rw [hleft, hright]
    dsimp [y]
    ring
  have hnonneg := hB y
  have hsquare := sq_nonneg (A 0 0 * x 0 + v)
  have hscaled : 0 ≤ A 0 0 * quadraticForm A x := by
    rw [hfull]
    nlinarith [mul_nonneg hp.le hnonneg]
  exact nonneg_of_mul_nonneg_right hscaled ha

/-- Integer identities suffice for a Schur step over the reals. -/
lemma integer_schur_step {n : ℕ} (A : Fin (n + 1) → Fin (n + 1) → ℤ)
    (B : Fin n → Fin n → ℤ) (p : ℤ)
    (hp : 0 < p) (ha : 0 < A 0 0)
    (hsym : ∀ i : Fin n, A i.succ 0 = A 0 i.succ)
    (hstep : ∀ i j, p * B i j = A 0 0 * A i.succ j.succ -
      A i.succ 0 * A 0 j.succ)
    (hB : IsPSD (fun i j => (B i j : ℝ))) :
    IsPSD (fun i j => (A i j : ℝ)) := by
  apply schur_step _ _ (p : ℝ) (by exact_mod_cast hp) (by exact_mod_cast ha)
    (fun i => by exact_mod_cast hsym i) _ hB
  intro i j
  exact_mod_cast hstep i j

end PersistentSOS

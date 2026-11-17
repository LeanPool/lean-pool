/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BernoulliCubeExpectations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

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

public import LeanPool.GinibrePoincare.Analysis.BernoulliTaylorEnergy

/-!
# Bernoulli Cube Expectations
-/


@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Sum of the actual fair signs in the recursive finite cube. -/
def bernoulliCubeSum : (n : ℕ) → BernoulliCube n → ℝ
  | 0, _ => 0
  | n + 1, p => bernoulliCubeSum n p.1 + if p.2 then 1 else -1

/-- Expectation under the uniform law on the finite cube. -/
def bernoulliCubeAverage (n : ℕ) (f : BernoulliCube n → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card (BernoulliCube n)

theorem bernoulliCube_card (n : ℕ) : Fintype.card (BernoulliCube n) = 2 ^ n := by
  induction n with
  | zero => change Fintype.card Unit = 1; simp
  | succ n ih =>
      change Fintype.card (BernoulliCube n × Bool) = _
      simp [ih, pow_succ]

theorem bernoulliCubeAverage_succ (n : ℕ) (f : BernoulliCube (n + 1) → ℝ) :
    bernoulliCubeAverage (n + 1) f =
      (bernoulliCubeAverage n (fun x => f (x, true)) +
        bernoulliCubeAverage n (fun x => f (x, false))) / 2 := by
  unfold bernoulliCubeAverage
  change (∑ p : BernoulliCube n × Bool, f p) / Fintype.card (BernoulliCube n × Bool) = _
  erw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
    Finset.sum_add_distrib]
  ring

/-- The conditional energy of a sum test has exactly one identical contribution per coordinate. -/
theorem bernoulliCubeEnergy_sum_test (n : ℕ) (f : ℝ → ℝ) :
    bernoulliCubeEnergy (n + 1) (fun x => f (bernoulliCubeSum (n + 1) x)) =
      ((n : ℝ) + 1) / 2 * bernoulliCubeAverage n
        (fun x => (f (bernoulliCubeSum n x + 1) - f (bernoulliCubeSum n x - 1)) ^ 2) := by
  induction n generalizing f with
  | zero =>
      unfold bernoulliCubeEnergy
      simp [bernoulliCubeAverage, bernoulliCubeSum, BernoulliCube, bernoulliCubeEnergy]
      ring
  | succ n ih =>
      change ((∑ y : Bool, bernoulliCubeEnergy (n + 1)
          (fun x => f (bernoulliCubeSum (n + 1) x + if y then 1 else -1))) / 2 +
        (∑ x : BernoulliCube (n + 1),
          (f (bernoulliCubeSum (n + 1) x + 1) - f (bernoulliCubeSum (n + 1) x + -1)) ^ 2 / 2) /
            Fintype.card (BernoulliCube (n + 1))) = _
      simp only [Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false]
      rw [ih (fun t => f (t + 1)), ih (fun t => f (t + -1))]
      have he : (∑ x : BernoulliCube (n + 1),
          (f (bernoulliCubeSum (n + 1) x + 1) - f (bernoulliCubeSum (n + 1) x + -1)) ^ 2 / 2) /
            Fintype.card (BernoulliCube (n + 1)) =
          bernoulliCubeAverage (n + 1)
            (fun x => (f (bernoulliCubeSum (n + 1) x + 1) - f (bernoulliCubeSum (n + 1) x - 1)) ^
              2) / 2 := by
        simp only [bernoulliCubeAverage, ← Finset.sum_div, sub_eq_add_neg]
        ring
      rw [he, bernoulliCubeAverage_succ]
      simp only [bernoulliCubeSum, Bool.false_eq_true, ite_true, ite_false, Nat.cast_add,
        Nat.cast_one]
      have h1 : (fun x : BernoulliCube n =>
          (f (bernoulliCubeSum n x + 1 + 1) - f (bernoulliCubeSum n x - 1 + 1)) ^ 2) =
        (fun x => (f (bernoulliCubeSum n x + 1 + 1) - f (bernoulliCubeSum n x + 1 - 1)) ^ 2) := by
        funext x
        congr 2 ; ring
      have h2 : (fun x : BernoulliCube n =>
          (f (bernoulliCubeSum n x + 1 + -1) - f (bernoulliCubeSum n x - 1 + -1)) ^ 2) =
        (fun x => (f (bernoulliCubeSum n x + -1 + 1) - f (bernoulliCubeSum n x + -1 - 1)) ^ 2) := by
        funext x
        congr 2 ; ring
      rw [h1, h2]
      ring

end
end GinibrePoincare

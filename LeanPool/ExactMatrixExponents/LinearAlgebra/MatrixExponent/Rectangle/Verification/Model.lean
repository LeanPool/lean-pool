/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Model
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Public seeds and division-free arithmetic verification

Each seed chooses a straight-line program followed by scalar equality
tests. Its cost counts all binary arithmetic instructions and all tests.
This is a subclass of the equality-test trees in Section 8.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Verification
open Filter Finset

open scoped Classical in
/-- Indexes the index by the coordinates of `Fin 3 × Rectangle.Pos n n`. -/
abbrev Index (n : ℕ) := Fin 3 × Rectangle.Pos n n
open scoped Classical in
/-- Computes the poly by the application `MvPolynomial (Index n) F`. -/
abbrev Poly (F : Type*) [Field F] (n : ℕ) := MvPolynomial (Index n) F

open scoped Classical in
/-- The set of values attained by `MvPolynomial.C ∪ Set.range MvPolynomial.X`. -/
def inputs (F : Type*) [Field F] (n : ℕ) : Set (Poly F n) :=
  Set.range MvPolynomial.C ∪ Set.range MvPolynomial.X

variable {F : Type*} [Field F] {n : ℕ}

open scoped Classical in
/-- The condition `∀ i j : Fin n, ∑ k, x (0, i, k) * x (1, k, j) = x (2, i, j)` on the specified
data. -/
def Correct (x : Index n → F) : Prop :=
  ∀ i j : Fin n, ∑ k, x (0, i, k) * x (1, k, j) = x (2, i, j)

open scoped Classical in
/-- The data for the test construction, including `count`, `left`, `right`. -/
structure Test (F : Type*) [Field F] (n : ℕ) where
  /-- The number of entries. -/
  count : ℕ
  /-- The left-side data carried by `Test`, with type `Fin count → Poly F n`. -/
  left : Fin count → Poly F n
  /-- The right-side data carried by `Test`, with type `Fin count → Poly F n`. -/
  right : Fin count → Poly F n

open scoped Classical in
/-- The condition `∀ i, MvPolynomial.eval x (T.left i) = MvPolynomial.eval x (T.right i)` on the
specified data. -/
def Test.accept (T : Test F n) (x : Index n → F) : Prop :=
  ∀ i, MvPolynomial.eval x (T.left i) = MvPolynomial.eval x (T.right i)

open scoped Classical in
/-- The condition `∃ (m : ℕ) (V : Set (Poly F n)), Integral.Build (inputs F n) m V ∧ (∀ i,
T.left i ∈ V ∧ T.right i ∈ V) ∧ (m : ℝ) + T.count ≤ c` on the specified data. -/
def Test.cost (T : Test F n) (c : ℝ) : Prop :=
  ∃ (m : ℕ) (V : Set (Poly F n)), Integral.Build (inputs F n) m V ∧
    (∀ i, T.left i ∈ V ∧ T.right i ∈ V) ∧ (m : ℝ) + T.count ≤ c

open scoped Classical in
/-- The uniform of type `Prop` for the given inputs. -/
def Uniform (F : Type*) [Field F] (n : ℕ) (s c p : ℝ) : Prop :=
  ∃ (L : ℕ) (A : Fin L → Test F n), 0 < L ∧ (L : ℝ) ≤ s ∧ (∀ i, (A i).cost c) ∧
    (∀ x, Correct x → ∀ i, (A i).accept x) ∧
    ∀ x, ¬ Correct x → (#{i | (A i).accept x} : ℝ) ≤ p * L

open scoped Classical in
/-- The condition `∀ ε > (0 : ℝ), ∀ p > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Uniform F n ((n : ℝ) ^ (ρ +
ε)) ((n : ℝ) ^ (v + ε)) p` on the specified data. -/
def Support (F : Type*) [Field F] (ρ v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Uniform F n ((n : ℝ) ^ (ρ + ε)) ((n : ℝ) ^ (v
    + ε)) p

open scoped Classical in
/-- The entropy of type `Prop` for the given inputs. -/
def Entropy (F : Type*) [Field F] (η v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (L : ℕ) (A : Fin L → Test F n) (w : Fin L → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ -(∑ i, w i * Real.log (w i)) ≤ (η + ε) * Real.log n ∧
      (∀ i, (A i).cost ((n : ℝ) ^ (v + ε))) ∧
      ∀ x, (∑ i, if (A i).accept x ↔ Correct x then w i else 0) ≥ 2 / 3

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Verification

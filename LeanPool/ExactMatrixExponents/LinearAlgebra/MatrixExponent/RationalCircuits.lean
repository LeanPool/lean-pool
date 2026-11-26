/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.MatrixRank
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Formal arithmetic complexity of square matrix multiplication

A straight-line computation records the set of available wire values. All
inputs and field constants are initially available. One step adds the value
of one binary gate, with unrestricted reuse. The division rule tests the
denominator in the rational function field, even in positive characteristic.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent

/-- Indexes the pos by the coordinates of `Fin n × Fin n`. -/
abbrev Pos (n : ℕ) := Fin n × Fin n
/-- Indexes the var by the coordinates of `Pos n ⊕ Pos n`. -/
abbrev Var (n : ℕ) := Pos n ⊕ Pos n
/-- Computes the rat by the application `FractionRing (MvPolynomial (Var n) F)`. -/
abbrev Rat (F : Type*) [Field F] (n : ℕ) := FractionRing (MvPolynomial (Var n) F)

/-- Computes the input by the application `algebraMap (MvPolynomial (Var n) F) (Rat F n)
(MvPolynomial.X i)`. -/
def input (F : Type*) [Field F] {n : ℕ} (i : Var n) : Rat F n :=
  algebraMap (MvPolynomial (Var n) F) (Rat F n) (MvPolynomial.X i)

/-- The set of values attained by `(algebraMap F (Rat F n)) ∪ Set.range (input F)`. -/
def initial (F : Type*) [Field F] (n : ℕ) : Set (Rat F n) :=
  Set.range (algebraMap F (Rat F n)) ∪ Set.range (input F)

/-- The quantity computed by `∑ k : Fin n, input F (.inl (p.1, k)) * input F (.inr (k, p.2))`. -/
def output (F : Type*) [Field F] {n : ℕ} (p : Pos n) : Rat F n :=
  ∑ k : Fin n, input F (.inl (p.1, k)) * input F (.inr (k, p.2))

/-- The build used in the `MatrixExponent` construction. -/
inductive Build {K : Type*} [Field K] (S : Set K) : ℕ → Set K → Prop
  | nil : Build S 0 S
  | add {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x + y) T)
  | sub {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x - y) T)
  | mul {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x * y) T)
  | div {m T x y} : Build S m T → x ∈ T → y ∈ T → y ≠ 0 → Build S (m + 1) (insert (x / y) T)

/-- The condition `∃ T, Build (initial F n) m T ∧ ∀ p : Pos n, output F p ∈ T` on the specified
data. -/
def Computes (F : Type*) [Field F] (n m : ℕ) : Prop :=
  ∃ T, Build (initial F n) m T ∧ ∀ p : Pos n, output F p ∈ T

/-- The condition `∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∃ m : ℕ, Computes F n m ∧
(m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)` on the specified data. -/
def Admissible (F : Type*) [Field F] (s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, Computes F n m ∧ (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)

/-- The infimum of `{s | Admissible F s}`. -/
def omega (F : Type*) [Field F] : ℝ := sInf {s | Admissible F s}

/-- Coefficient rank for square matrix multiplication. -/
abbrev RankLE (F : Type*) [Field F] (n r : ℕ) : Prop :=
  TensorSpectrum.MatrixRank F n n n r

end MatrixMultiplicationAllFields.MatrixExponent

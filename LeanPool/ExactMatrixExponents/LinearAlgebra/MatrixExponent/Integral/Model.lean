/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Model

/-! Division-free circuits computing formal polynomial identities over a ring. -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Integral

/-- Uses `Rectangle.Pos` as the representation. -/
abbrev Pos := Rectangle.Pos
/-- Uses `Rectangle.Var` as the representation. -/
abbrev Var := Rectangle.Var
/-- Computes the poly by the application `MvPolynomial (Var i j k) F`. -/
abbrev Poly (F : Type*) [CommRing F] (i j k : ℕ) := MvPolynomial (Var i j k) F
/-- Uses `Rectangle.side` as the representation. -/
abbrev side := Rectangle.side

/-- Computes the input by the application `MvPolynomial.X x`. -/
abbrev input (F : Type*) [CommRing F] {i j k : ℕ} (x : Var i j k) : Poly F i j k :=
  MvPolynomial.X x

/-- The build used in the `Integral` construction. -/
inductive Build {K : Type*} [CommRing K] (S : Set K) : ℕ → Set K → Prop
  | nil : Build S 0 S
  | add {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x + y) T)
  | sub {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x - y) T)
  | mul {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x * y) T)

/-- The set of values attained by `(algebraMap F (Poly F i j k)) ∪ Set.range (input F)`. -/
def initial (F : Type*) [CommRing F] (i j k : ℕ) : Set (Poly F i j k) :=
  Set.range (algebraMap F (Poly F i j k)) ∪ Set.range (input F)

/-- The quantity computed by `∑ l : Fin k, input F (.inl (p.1, l)) * input F (.inr (l, p.2))`. -/
def output (F : Type*) [CommRing F] {i j k : ℕ} (p : Pos i j) : Poly F i j k :=
  ∑ l : Fin k, input F (.inl (p.1, l)) * input F (.inr (l, p.2))

/-- The condition `∃ T, Build (initial F i j k) m T ∧ ∀ p : Pos i j, output F p ∈ T` on the
specified data. -/
def Computes (F : Type*) [CommRing F] (i j k m : ℕ) : Prop :=
  ∃ T, Build (initial F i j k) m T ∧ ∀ p : Pos i j, output F p ∈ T

/-- The defining condition `∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∃ m : ℕ, Computes
F (side n a) (side n b) (side n c) m ∧ (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)`. -/
def Admissible (F : Type*) [CommRing F] (a b c s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, Computes F (side n a) (side n b) (side n c) m ∧
      (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)

/-- The infimum of `{s | Admissible F a b c s}`. -/
def exponent (F : Type*) [CommRing F] (a b c : ℝ) : ℝ := sInf {s | Admissible F a b c s}

/-- Coefficient rank for rectangular matrix multiplication over a commutative ring. -/
abbrev Rank (F : Type*) [CommRing F] (i j k r : ℕ) : Prop :=
  TensorSpectrum.MatrixRank F i j k r

end MatrixMultiplicationAllFields.MatrixExponent.Integral

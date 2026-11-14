/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.FiniteAPI

/-!
# Real and complex matrix quadratic forms
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace OlevskiiGram

/-- Dot product on a finite real coordinate space. -/
def realDot {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- Quadratic form associated to a real matrix. -/
def realQuadraticForm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, x i * ∑ j, A i j * x j

/-- Real symmetry for a matrix. -/
def RealSymmetric {ι : Type*} (A : Matrix ι ι ℝ) : Prop :=
  ∀ i j, A i j = A j i

/-- Positive semidefiniteness in quadratic-form language. -/
def RealPSD {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, 0 ≤ realQuadraticForm A x

/-- Loewner order for real matrices, expressed by positive semidefinite difference. -/
def RealLoewnerLE {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) : Prop :=
  RealPSD (B - A)

/-- The real matrix inequality `0 ≤ A ≤ I`. -/
def RealLoewnerBetweenZeroAndOne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop :=
  RealPSD A ∧ RealLoewnerLE A 1

/-- Coordinatewise membership in the real cube `[-1,1]^ι`. -/
def InRealUnitCube {ι : Type*} (x : ι → ℝ) : Prop :=
  ∀ i, |x i| ≤ 1

/-- Rank-one real matrix `q qᵀ`. -/
def realRankOne {ι : Type*} (q : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => q i * q j

/-- Complex Hermitian symmetry, in entrywise form. -/
def ComplexHermitian {ι : Type*} (A : Matrix ι ι ℂ) : Prop :=
  ∀ i j, A j i = star (A i j)

/-- Real part of a complex matrix. -/
def complexReMatrix {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℝ :=
  fun i j => (A i j).re

/-- Imaginary part of a complex matrix. -/
def complexImMatrix {ι : Type*} (A : Matrix ι ι ℂ) : Matrix ι ι ℝ :=
  fun i j => (A i j).im

/-- Real part of the complex quadratic form `x* A x`. -/
def complexQuadraticFormRe {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ :=
  Complex.re (∑ i, star (x i) * ∑ j, A i j * x j)

/-- Positive semidefiniteness for complex matrices, stated through quadratic forms. -/
def ComplexPSD {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : Prop :=
  ∀ x : ι → ℂ, 0 ≤ complexQuadraticFormRe A x

/-- The complex matrix inequality `0 ≤ A ≤ I`. -/
def ComplexLoewnerBetweenZeroAndOne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Prop :=
  ComplexPSD A ∧ ComplexPSD (1 - A)

/-- The real block matrix associated to `A + iB`. -/
def realBlockMatrix {ι : Type*} (A B : Matrix ι ι ℝ) :
    Matrix (Sum ι ι) (Sum ι ι) ℝ
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inl i, Sum.inr j => -B i j
  | Sum.inr i, Sum.inl j => B i j
  | Sum.inr i, Sum.inr j => A i j

end OlevskiiGram

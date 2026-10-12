/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Internal finite Gram API

Finite Gram matrices, their Euclidean operators, and bounded-function predicates
used by the finite decomposition and realization theorems.
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section


noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace OlevskiiGram

/-- Lebesgue measure restricted to the open unit interval. -/
abbrev μ01 : Measure ℝ :=
  volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- The finite Gram matrix, using the paper's inner-product convention. -/
def gramMatrix {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (z : Fin N → H) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => inner ℂ (z k) (z j)

/-- The continuous Euclidean operator associated to a finite complex matrix. -/
def matrixL2Operator {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  LinearMap.toContinuousLinearMap
    ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin N) (n := Fin N)) A)

/-- An upper bound on the Euclidean operator norm of a finite complex matrix. -/
def matrixL2OperatorNormLE {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (C : ℝ) : Prop :=
  ‖matrixL2Operator A‖ ≤ C

/-- An essential supremum bound relative to the open-unit-interval measure. -/
def LInfNormLe (C : ℝ) (f : ℝ → ℂ) : Prop :=
  eLpNormEssSup f μ01 ≤ ENNReal.ofReal C

/-- Bounded functions whose unit-interval correlations represent a finite Gram matrix. -/
def RepresentsGramMatrixWithBound {N : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : ℝ) (z : Fin N → H) (f : Fin N → ℝ → ℂ) : Prop :=
  (∀ j, LInfNormLe C (f j)) ∧
    ∀ j k,
      (∫ t in Set.Ioo (0 : ℝ) (1 : ℝ), (f j) t * star ((f k) t)) =
        inner ℂ (z k) (z j)

end OlevskiiGram

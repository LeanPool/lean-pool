/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.AnalyticFredholm
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Finite-dimensional determinant reductions for analytic Fredholm theory

The classical analytic-Fredholm argument reduces the noninvertible locus of an
analytic operator family to the zero set of a scalar analytic function.  Mathlib
does not construct that reduction, and `FastDynamo.Operator.AnalyticFredholm`
therefore takes an `AnalyticFredholm.ScalarReduction` as an explicit input.
This module supplies the finite-dimensional determinant calculation from which
`AnalyticFredholmContinuation` builds one.

## Contents

* **Finite-dimensional determinants** (namespace `FiniteDimensionalSchur`):
  `analyticAt_det`, analyticity of composition of continuous-linear-map
  families (`analyticAt_clm_comp`), the basis-free determinant of a
  finite-dimensional operator family with `isInvertible_iff_det_ne_zero` and
  its analyticity, and the packaging definition
  `scalarReductionOfFiniteDimensionalCriterion`: an exact invertibility
  criterion through a finite-dimensional continuous endomorphism gives a
  scalar reduction.
* **Invertibility under composition** (namespace `FiniteDimensionalDeterminant`):
  `isInvertible_comp_iff_of_right`, composition on the right by an invertible
  map preserves continuous invertibility.
-/

@[expose] public section

/-!
## Finite-dimensional determinants

The finite-dimensional analytic part of the classical analytic-Fredholm
reduction.  The infinite-dimensional step, the reduction of the operator family
to a finite-dimensional one, is supplied by the caller.

The results below prove that:

* the determinant of an analytic complex matrix family, and the basis-free
  determinant of an analytic family of endomorphisms of a finite-dimensional
  space, are analytic;
* composition of analytic continuous-linear-map families is analytic;
* on a finite-dimensional space, invertibility is equivalent to nonvanishing of
  the determinant; and
* any operator family equipped with an exact invertibility criterion through
  such a finite-dimensional family gives an actual
  `AnalyticFredholm.ScalarReduction`.
-/

namespace FastDynamo

noncomputable section

open Set
open scoped Matrix.Norms.Elementwise

namespace FiniteDimensionalSchur

universe u

/-! ## Analytic determinants -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of an analytic square-matrix family is analytic. -/
theorem analyticAt_det {M : E → Matrix n n ℂ} {x : E}
    (hM : AnalyticAt ℂ M x) :
    AnalyticAt ℂ (fun y ↦ (M y).det) x := by
  let p : MvPolynomial (n × n) ℂ :=
    Matrix.det (Matrix.mvPolynomialX n n ℂ)
  have hentry : ∀ q : n × n,
      AnalyticAt ℂ (fun y ↦ M y q.1 q.2) x := by
    intro q
    exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hM q.1) q.2
  have hp := AnalyticAt.aeval_mvPolynomial hentry p
  have heq :
      (fun y ↦ MvPolynomial.aeval (fun q ↦ M y q.1 q.2) p) =
        (fun y ↦ (M y).det) := by
    funext y
    rw [MvPolynomial.aeval_eq_eval]
    dsimp only [p]
    rw [Matrix.eval_det_mvPolynomialX]
    congr 1
  rw [heq] at hp
  exact hp

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## Analytic composition of operator families -/

/-- Analyticity of composition for two compatible continuous-linear-map
families, the operator analogue of analyticity of matrix multiplication. -/
theorem analyticAt_clm_comp
    {V W Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {G : E → (W →L[ℂ] Y)} {H : E → (V →L[ℂ] W)} {x : E}
    (hG : AnalyticAt ℂ G x) (hH : AnalyticAt ℂ H x) :
    AnalyticAt ℂ (fun y ↦ (G y).comp (H y)) x := by
  exact
    ((ContinuousLinearMap.compL ℂ V W Y).analyticAt_bilinear (G x, H x)).comp₂
      hG hH

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]

variable [CompleteSpace Q]

/-! ## Basis-free determinant of finite-dimensional operator families -/

variable [FiniteDimensional ℂ P]

/-- The determinant of an analytic continuous-endomorphism family on a
finite-dimensional complex normed space is analytic.  A basis is chosen only
inside the proof; the resulting scalar is `LinearMap.det`, hence basis-free. -/
theorem analyticAt_continuousLinearMap_det
    {S : E → (P →L[ℂ] P)} {x : E} (hS : AnalyticAt ℂ S x) :
    AnalyticAt ℂ (fun y ↦ (S y).det) x := by
  let b := Module.finBasis ℂ P
  let toMatrixLinear :
      (P →L[ℂ] P) →ₗ[ℂ]
        Matrix (Fin (Module.finrank ℂ P)) (Fin (Module.finrank ℂ P)) ℂ :=
    (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℂ)
  let toMatrix :
      (P →L[ℂ] P) →L[ℂ]
        Matrix (Fin (Module.finrank ℂ P)) (Fin (Module.finrank ℂ P)) ℂ :=
    LinearMap.toContinuousLinearMap toMatrixLinear
  have hMatrix : AnalyticAt ℂ
      (fun y ↦ LinearMap.toMatrix b b (S y : P →ₗ[ℂ] P)) x := by
    exact (toMatrix.analyticAt (S x)).comp hS
  have hdet := analyticAt_det hMatrix
  simpa only [LinearMap.det_toMatrix] using hdet

/-- Setwise form of `analyticAt_continuousLinearMap_det`. -/
theorem analyticOnNhd_continuousLinearMap_det
    {S : E → (P →L[ℂ] P)} {U : Set E} (hS : AnalyticOnNhd ℂ S U) :
    AnalyticOnNhd ℂ (fun y ↦ (S y).det) U := by
  intro x hx
  exact analyticAt_continuousLinearMap_det (hS x hx)

/-- On a finite-dimensional complex normed space, continuous invertibility is
equivalent to nonvanishing of the basis-free determinant. -/
theorem isInvertible_iff_det_ne_zero (S : P →L[ℂ] P) :
    S.IsInvertible ↔ S.det ≠ 0 := by
  rw [← AnalyticFredholm.isUnit_iff_isInvertible]
  have hunit :
      IsUnit S ↔ IsUnit ((Module.End.toContinuousLinearMap P).symm S) :=
    (isUnit_map_iff (Module.End.toContinuousLinearMap P).symm S).symm
  rw [hunit]
  change IsUnit (S : P →ₗ[ℂ] P) ↔ LinearMap.det (S : P →ₗ[ℂ] P) ≠ 0
  rw [LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-! ## Packaging as an analytic-Fredholm scalar reduction -/

variable {X : Type u}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Turn an exact invertibility criterion through a finite-dimensional
continuous endomorphism into an analytic-Fredholm scalar reduction. -/
def scalarReductionOfFiniteDimensionalCriterion
    (F : ℂ → (X →L[ℂ] X)) (S : ℂ → (P →L[ℂ] P)) (U : Set ℂ)
    (hS : AnalyticOnNhd ℂ S U)
    (hcriterion : ∀ z ∈ U, (F z).IsInvertible ↔ (S z).IsInvertible) :
    AnalyticFredholm.ScalarReduction F U where
  determinant := fun z ↦ (S z).det
  analyticOnNhd := analyticOnNhd_continuousLinearMap_det hS
  isInvertible_iff_ne_zero := by
    intro z hz
    exact (hcriterion z hz).trans (isInvertible_iff_det_ne_zero (S z))

end FiniteDimensionalSchur

end

end FastDynamo

/-!
## Invertibility under composition
-/

namespace FastDynamo

noncomputable section

open Set

namespace FiniteDimensionalDeterminant

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- Composition on the right by an invertible continuous-linear map preserves
continuous invertibility. -/
theorem isInvertible_comp_iff_of_right
    {V W Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {U : W →L[ℂ] Y} {T : V →L[ℂ] W} (hT : T.IsInvertible) :
    (U.comp T).IsInvertible ↔ U.IsInvertible := by
  rcases hT with ⟨e, rfl⟩
  exact ContinuousLinearMap.isInvertible_comp_equiv

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable [CompleteSpace Q] [FiniteDimensional ℂ P] [CompleteSpace X]

end FiniteDimensionalDeterminant

end

end FastDynamo

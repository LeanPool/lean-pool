/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeDirichletH2.ReflectionParentH1Graph

/-!
# Coarse-graining support: Support.Sobolev.Foundations.CubeDirichletH2.ReflectionDivergenceRhs

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

open scoped BigOperators ENNReal

noncomputable section

/-!
# Dirichlet odd reflection for a divergence-form right-hand side

On a centered cube, the product-odd reflection of a zero-trace scalar
function has the corresponding odd-reflected vector field as its gradient.
Reflecting the vector datum by the same rule preserves the constant-coefficient
divergence-form weak equation, including its sign.
-/

/-- A scalar constant-coefficient divergence-form equation on a centered cube
extends to compactly supported smooth tests on the centered parent cube under
all-face Dirichlet odd reflection.  No sign or positivity assumption on the
constant coefficient is needed. -/
theorem exists_h1Function_cubeDirichletOddReflectionParent_divergence_rhs_originCube
    {d : ℕ} {m : ℤ} {sigma0 : ℝ}
    {u : H10Function (openCubeSet (originCube d m))}
    {h : Vec d → Vec d}
    (hh : MemVectorL2 (openCubeSet (originCube d m)) h)
    (hweak : ∀ ψ : H10Function (openCubeSet (originCube d m)),
      sigma0 *
          ∫ x in openCubeSet (originCube d m),
            vecDot (u.toH1Function.grad x) (ψ.toH1Function.grad x)
              ∂MeasureTheory.volume =
        -∫ x in openCubeSet (originCube d m),
            vecDot (h x) (ψ.toH1Function.grad x) ∂MeasureTheory.volume) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d m)
            u.toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) ∧
        ∀ (φ : Vec d → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ →
          tsupport φ ⊆ openCubeSet (originCube d (m + 1)) →
          sigma0 *
              ∫ x in openCubeSet (originCube d (m + 1)),
                vecDot (uP.grad x) (euclideanGradient φ x)
                  ∂MeasureTheory.volume =
            -∫ x in openCubeSet (originCube d (m + 1)),
                vecDot
                  (cubeDirichletOddReflectionVectorField (originCube d m) h x)
                  (euclideanGradient φ x) ∂MeasureTheory.volume := by
  obtain ⟨uP, huP_toFun, huP_grad⟩ :=
    exists_h1Function_cubeDirichletOddReflectionParent_originCube u
  refine ⟨uP, huP_toFun, huP_grad, ?_⟩
  intro φ hφ hφ_compact hφ_sub
  have huGrad : MemVectorL2 (openCubeSet (originCube d m))
      (fun y => u.toH1Function.grad y) := by
    simpa [MemVectorL2, volumeMeasureOn] using
      u.toH1Function.grad_memVectorL2
  have hfolded :
      sigma0 *
          ∫ y in openCubeSet (originCube d m),
            vecDot (u.toH1Function.grad y)
              (fun i : Fin d =>
                ∑ choice : Fin d → Fin 3,
                  (cubeDirichletOddReflectionCellSign choice *
                    cubeFaceReflectionCellFoldSign choice i) *
                    euclideanCoordDeriv i φ
                      (cubeFaceReflectionCellFoldMap
                        (originCube d m) choice y))
              ∂MeasureTheory.volume =
        -∫ y in openCubeSet (originCube d m),
            vecDot (h y)
              (fun i : Fin d =>
                ∑ choice : Fin d → Fin 3,
                  (cubeDirichletOddReflectionCellSign choice *
                    cubeFaceReflectionCellFoldSign choice i) *
                    euclideanCoordDeriv i φ
                      (cubeFaceReflectionCellFoldMap
                        (originCube d m) choice y))
              ∂MeasureTheory.volume := by
    let ψ : H10Function (openCubeSet (originCube d m)) :=
      H10Function.cubeDirichletOddReflectionFoldedParentScalarTestToH10
        m hφ hφ_compact hφ_sub
    have htest := hweak ψ
    have hψ_grad :
        ψ.toH1Function.grad =
          fun y i =>
            ∑ choice : Fin d → Fin 3,
              (cubeDirichletOddReflectionCellSign choice *
                cubeFaceReflectionCellFoldSign choice i) *
                euclideanCoordDeriv i φ
                  (cubeFaceReflectionCellFoldMap
                    (originCube d m) choice y) := by
      funext y i
      change
        euclideanCoordDeriv i
            (cubeDirichletOddReflectionFoldedParentScalarTest
              (originCube d m) φ) y = _
      exact
        euclideanCoordDeriv_cubeDirichletOddReflectionFoldedParentScalarTest
          (originCube d m) i hφ y
    simpa [hψ_grad] using htest
  rw [huP_grad,
    setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
      (m := m)
      (f := fun x =>
        vecDot
          (cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) x)
          (euclideanGradient φ x)),
    setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
      (m := m)
      (f := fun x =>
        vecDot
          (cubeDirichletOddReflectionVectorField (originCube d m) h x)
          (euclideanGradient φ x)),
    setIntegral_cubeReflection_vectorDot_oddReflectedField_eq_foldedDerivativeSum
      (Q := originCube d m) (G := fun y => u.toH1Function.grad y)
      huGrad hφ hφ_compact,
    setIntegral_cubeReflection_vectorDot_oddReflectedField_eq_foldedDerivativeSum
      (Q := originCube d m) (G := h) hh hφ hφ_compact]
  exact hfolded

end

end HCPolySupport

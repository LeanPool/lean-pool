/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePermutationGradient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradient

/-! # Covariance of the concrete gradient under particle relabelling -/


@[expose] public section


open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem permute_realCoordinateDirection {n : ℕ} (σ : ParticlePermutation n)
    (i : Fin n) : permute σ (realCoordinateDirection i) =
      realCoordinateDirection (σ.symm i) := by
  ext j
  simp [permute, realCoordinateDirection, coordinateDirection, Equiv.eq_symm_apply]

theorem permute_imaginaryCoordinateDirection {n : ℕ} (σ : ParticlePermutation n)
    (i : Fin n) : permute σ (imaginaryCoordinateDirection i) =
      imaginaryCoordinateDirection (σ.symm i) := by
  ext j
  simp [permute, imaginaryCoordinateDirection, coordinateDirection, Equiv.eq_symm_apply]

/-- The Euclidean gradient of a relabelled smooth function is relabelled by
the inverse permutation on its coordinate indices. -/
theorem ginibreEuclideanGradient_comp_permute {n : ℕ}
    (σ : ParticlePermutation n) (f : Configuration n → ℝ)
    (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    ginibreEuclideanGradient (fun y => f (permute σ y)) z =
      WithLp.toLp 2 (fun k : Fin n × Fin 2 =>
        ginibreEuclideanGradient f (permute σ z) (σ.symm k.1, k.2)) := by
  apply PiLp.ext
  intro k
  rw [ginibreEuclideanGradient_coordinate, ginibreEuclideanGradient_coordinate]
  let P : Configuration n →L[ℝ] Configuration n :=
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℂ) σ.symm).toContinuousLinearMap
  have hP (y : Configuration n) : P y = permute σ y := by
    funext i
    simp [P, ContinuousLinearEquiv.piCongrLeft,
      Equiv.piCongrLeft_apply, permute]
  have hcomp : (fun y => f (permute σ y)) = f ∘ P := by
    funext y
    exact congrArg f (hP y).symm
  rw [hcomp]
  have hder := fderiv_comp (x := z) (f := P) (g := f)
    (hf.differentiable (by simp)).differentiableAt P.differentiableAt
  rw [hder]
  simp only [ContinuousLinearMap.comp_apply]
  have hPder : fderiv ℝ P z = P := (P.hasFDerivAt).fderiv
  rw [hPder, hP z]
  by_cases hk : k.2 = 0
  · simp only [hk, ite_eq_left, ginibreCoordinateDirection]
    rw [show P (realCoordinateDirection k.1) =
      realCoordinateDirection (σ.symm k.1) by rw [hP, permute_realCoordinateDirection]]
  · simp only [hk, ginibreCoordinateDirection]
    simp only [ite_false]
    rw [show P (imaginaryCoordinateDirection k.1) =
      imaginaryCoordinateDirection (σ.symm k.1) by rw [hP, permute_imaginaryCoordinateDirection]]

end
end GinibrePoincare

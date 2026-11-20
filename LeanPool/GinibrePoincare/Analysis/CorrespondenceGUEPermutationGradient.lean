/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEPermutationGradient.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEFullMeasure
/-!
# Correspondence GUE permutation gradient

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueSymmetric_gradient_norm_sq`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

theorem guePermute_basis (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    guePermuteIsometry n σ (EuclideanSpace.basisFun (Fin n) ℝ i)=
      EuclideanSpace.basisFun (Fin n) ℝ (σ.symm i) := by
  ext j
  simp only [guePermuteIsometry_apply, guePermute, EuclideanSpace.basisFun_apply]
  change (Pi.single i (1 : ℝ) : Fin n→ℝ) (σ j)=(Pi.single (σ.symm i) 1 : Fin n→ℝ) j
  by_cases h : j=σ.symm i
  · subst j
    simp
  · have hi : σ j≠i := fun he => h (σ.injective (he.trans (σ.apply_symm_apply i).symm))
    simp [Pi.single, h, hi]

theorem gueSymmetric_gradient_norm_sq (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀ σ x, f (guePermute n σ x) = f x) (σ : Equiv.Perm (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f (guePermute n σ x)‖^2=‖gradient f x‖^2 := by
  have he : f ∘ guePermute n σ=f := funext (hs σ)
  have hd := (hf.differentiable (by norm_num) (guePermute n σ x)).hasFDerivAt.comp x
    (guePermuteIsometry n σ).toContinuousLinearEquiv.hasFDerivAt
  have hder : (fderiv ℝ f (guePermute n σ x)).comp
      (guePermuteIsometry n σ).toContinuousLinearEquiv.toContinuousLinearMap=fderiv ℝ f x := by
    rw [← hd.fderiv, he]
  have hc (i : Fin n) : (gradient f x) i=(gradient f (guePermute n σ x)) (σ.symm i) := by
    rw [gue_gradient_coordinate, gue_gradient_coordinate,← hder, ContinuousLinearMap.comp_apply]
    exact congrArg (fderiv ℝ f (guePermute n σ x)) (guePermute_basis n σ i)
  simp only [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hc]
  exact (Equiv.sum_comp σ.symm (fun i => (gradient f (guePermute n σ x) i)^2)).symm

end
end GinibrePoincare

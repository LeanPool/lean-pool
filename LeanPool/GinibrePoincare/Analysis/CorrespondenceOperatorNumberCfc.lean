/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberCfc.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberResolvent
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorCfcEigenvector
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
/-!
# Correspondence operator number cfc

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_cfc_coefficient`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem correspondenceOperatorNumberResolvent_basis (n : ℕ) (hn : 0 < n)
    (pq : HermiteMultiIndex n) :
    correspondenceOperatorNumberResolvent n hn ((gaussianHermiteHilbertBasis n hn) pq)=
      correspondenceOperatorNumberResolventWeight n pq • (gaussianHermiteHilbertBasis n hn) pq := by
  classical
  apply gaussianHermiteCoefficient_ext hn
  intro ab
  rw [correspondenceOperatorNumberResolvent_coefficient]
  have hc (ij : HermiteMultiIndex n) :
      gaussianHermiteCoefficient hn ((gaussianHermiteHilbertBasis n hn) pq) ij=
        if ij=pq then 1 else 0 := by
    change (gaussianHermiteHilbertBasis n hn).repr ((gaussianHermiteHilbertBasis n hn) pq) ij=_
    rw [HilbertBasis.repr_self, lp.single_apply]
    simp [Pi.single_apply]
  have hsm : gaussianHermiteCoefficient hn
      (correspondenceOperatorNumberResolventWeight n pq • (gaussianHermiteHilbertBasis n hn) pq) ab=
      (correspondenceOperatorNumberResolventWeight n pq : ℂ)*
        gaussianHermiteCoefficient hn ((gaussianHermiteHilbertBasis n hn) pq) ab := by
    rw [gaussianHermiteCoefficient_eq_inner]
    change inner ℂ (multivariateNormalizedL2 n hn ab.1 ab.2)
      ((correspondenceOperatorNumberResolventWeight n pq : ℂ) • (gaussianHermiteHilbertBasis n hn)
          pq) = _
    rw [inner_smul_right,← gaussianHermiteCoefficient_eq_inner]
  rw [hsm, hc]
  by_cases h : ab=pq
  · subst ab
    simp [correspondenceOperatorNumberResolventWeight]
  · simp [h]

/-- The real continuous functional calculus on bounded operators of the complex Gaussian `L²`
space. The `ℝ`-module structure of `Lp` agrees with the restriction of scalars from `ℂ` only
after unfolding, so the generic C⋆-algebra instance is stated here at the concrete type. -/
instance complexGaussianL2_realContinuousFunctionalCalculus (n : ℕ) :
    ContinuousFunctionalCalculus ℝ
      (Lp ℂ 2 (complexGaussianMeasure n) →L[ℂ] Lp ℂ 2 (complexGaussianMeasure n))
      IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

theorem correspondenceOperatorNumber_cfc_coefficient (n : ℕ) (hn : 0 < n)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (correspondenceOperatorNumberResolvent n hn)))
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (cfc f (correspondenceOperatorNumberResolvent n hn) u) pq =
      (f (correspondenceOperatorNumberResolventWeight n pq) : ℂ) *
        gaussianHermiteCoefficient hn u pq := by
  have hR := correspondenceOperatorNumberResolvent_isSelfAdjoint n hn
  have hx := correspondenceOperatorNumberResolvent_basis n hn pq
  have hr := correspondenceOperator_eigenvalue_mem_spectrum _ _ _
    ((gaussianHermiteHilbertBasis n hn).orthonormal.ne_zero pq) hx
  have he := correspondenceOperator_cfc_eigenvector _ hR _ hr _ hx f hf
  have he' : cfc f (correspondenceOperatorNumberResolvent n hn)
      ((gaussianHermiteHilbertBasis n hn) pq) =
      (f (correspondenceOperatorNumberResolventWeight n pq) : ℂ) •
        (gaussianHermiteHilbertBasis n hn) pq := he
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.cfc (f := f) (a := correspondenceOperatorNumberResolvent n hn))
  rw [gaussianHermiteCoefficient_eq_inner, ← gaussianHermiteHilbertBasis_apply]
  have hSym := hS ((gaussianHermiteHilbertBasis n hn) pq) u
  change inner ℂ (cfc f (correspondenceOperatorNumberResolvent n hn)
      ((gaussianHermiteHilbertBasis n hn) pq)) u =
    inner ℂ ((gaussianHermiteHilbertBasis n hn) pq)
      (cfc f (correspondenceOperatorNumberResolvent n hn) u) at hSym
  rw [← hSym, he', inner_smul_left]
  simp only [Complex.conj_ofReal]
  rw [gaussianHermiteCoefficient_eq_inner, gaussianHermiteHilbertBasis_apply]
end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorFriedrichsSquareRootForm.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorFriedrichsSquareRootRange
/-!
# Correspondence operator Friedrichs square root form

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceFriedrichsResolventSqrt_range_form`.
-/

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

theorem correspondenceComplex_real_inner (n : ℕ) (x y : GinibreFullComplexL2 n) :
    inner ℝ x y=(inner ℂ x y).re := by
  have hr : ‖x+y‖^2=‖x‖^2+2*inner ℝ x y+‖y‖^2 := norm_add_sq_real x y
  have hc : ‖x+y‖^2=‖x‖^2+2*(inner ℂ x y).re+‖y‖^2 := norm_add_sq (𝕜:=ℂ) x y
  linarith

/-- The `L²` product of two copies of `correspondenceOperatorFormSpace n hn`, holding real and
imaginary parts. -/
abbrev CorrespondenceComplexFormSpace (n : ℕ) (hn : 0 < n) :=
  WithLp 2 (correspondenceOperatorFormSpace n hn×correspondenceOperatorFormSpace n hn)

/-- The form resolvent `correspondenceOperatorFormResolventCLM n hn` applied separately to the
real and imaginary parts, as a real-linear map into `CorrespondenceComplexFormSpace n hn`. -/
def correspondenceComplexFormResolvent (n : ℕ) (hn : 0 < n) :
    GinibreFullComplexL2 n→L[ℝ]CorrespondenceComplexFormSpace n hn :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((correspondenceOperatorFormResolventCLM n hn).comp (ginibreFullComplexRe n)).prod
      ((correspondenceOperatorFormResolventCLM n hn).comp (ginibreFullComplexIm n)))

/-- Recombination of a pair `(a, b)` of form-space vectors into `value a + I • value b` in
`GinibreFullComplexL2 n`, where `value` is `correspondenceOperatorFormValue n hn`. -/
def correspondenceComplexFormValue (n : ℕ) (hn : 0 < n) :
    CorrespondenceComplexFormSpace n hn→L[ℝ]GinibreFullComplexL2 n :=
  (ginibreFullComplexOfReal n).comp ((correspondenceOperatorFormValue n hn).comp (WithLp.fstL 2 ℝ _
      _))+
    Complex.I • (ginibreFullComplexOfReal n).comp ((correspondenceOperatorFormValue n hn).comp
        (WithLp.sndL 2 ℝ _ _))

@[simp] theorem correspondenceComplexFormValue_re (n : ℕ) (hn : 0 < n)
    (p : CorrespondenceComplexFormSpace n hn) :
    ginibreFullComplexRe n (correspondenceComplexFormValue n hn p)=correspondenceOperatorFormValue n
        hn p.fst := by
  simp [correspondenceComplexFormValue]

@[simp] theorem correspondenceComplexFormValue_im (n : ℕ) (hn : 0 < n)
    (p : CorrespondenceComplexFormSpace n hn) :
    ginibreFullComplexIm n (correspondenceComplexFormValue n hn p)=correspondenceOperatorFormValue n
        hn p.snd := by
  simp [correspondenceComplexFormValue]

theorem correspondenceComplexFormResolvent_adjoint (n : ℕ) (hn : 0 < n) :
    (correspondenceComplexFormResolvent n hn).adjoint=correspondenceComplexFormValue n hn := by
  apply ContinuousLinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, correspondenceComplex_real_inner n,
      ginibreFullComplex_inner_re,
    correspondenceComplexFormValue_re, correspondenceComplexFormValue_im]
  rw [WithLp.prod_inner_apply]
  change inner ℝ (correspondenceOperatorFormResolvent n hn (ginibreFullComplexRe n x)) p.fst+
    inner ℝ (correspondenceOperatorFormResolvent n hn (ginibreFullComplexIm n x)) p.snd=_
  rw [correspondenceOperatorFormResolvent_riesz, correspondenceOperatorFormResolvent_riesz]

theorem correspondenceFriedrichsResolventSqrt_norm_form (n : ℕ) (hn : 0 < n)
    (x : GinibreFullComplexL2 n) :
    ‖correspondenceComplexFormResolvent n hn x‖=‖correspondenceFriedrichsResolventSqrt n hn x‖ := by
  have hA : ‖correspondenceComplexFormResolvent n hn x‖^2=
      inner ℝ (ginibreFullComplexRe n x) (correspondenceOperatorValueResolvent n hn
          (ginibreFullComplexRe n x))+
      inner ℝ (ginibreFullComplexIm n x) (correspondenceOperatorValueResolvent n hn
          (ginibreFullComplexIm n x)) := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖correspondenceOperatorFormResolvent n hn (ginibreFullComplexRe n x)‖^2+
      ‖correspondenceOperatorFormResolvent n hn (ginibreFullComplexIm n x)‖^2=_
    rw [correspondenceOperatorValueResolvent_positive,
        correspondenceOperatorValueResolvent_positive]
  have hB := (correspondenceFriedrichsResolventSqrt n hn).apply_norm_sq_eq_inner_adjoint_left x
  have hself : (correspondenceFriedrichsResolventSqrt n
      hn).adjoint=correspondenceFriedrichsResolventSqrt n hn :=
    correspondenceFriedrichsResolventSqrt_selfAdjoint n hn
  rw [hself] at hB
  change ‖correspondenceFriedrichsResolventSqrt n hn x‖^2=
    (inner ℂ ((correspondenceFriedrichsResolventSqrt n hn*correspondenceFriedrichsResolventSqrt n
        hn) x) x).re at hB
  rw [correspondenceFriedrichsResolventSqrt_square, ginibreFullComplex_inner_re,
    correspondenceOperatorComplexResolvent_re, correspondenceOperatorComplexResolvent_im] at hB
  have hre := real_inner_comm (ginibreFullComplexRe n x) (correspondenceOperatorValueResolvent n hn
      (ginibreFullComplexRe n x))
  have him := real_inner_comm (ginibreFullComplexIm n x) (correspondenceOperatorValueResolvent n hn
      (ginibreFullComplexIm n x))
  rw [hre, him] at hB
  nlinarith [norm_nonneg (correspondenceComplexFormResolvent n hn x), norm_nonneg
      (correspondenceFriedrichsResolventSqrt n hn x)]

/-- The actual resolvent CFC square root has precisely the ordinary weighted
complex H¹ value range. -/
theorem correspondenceFriedrichsResolventSqrt_range_form (n : ℕ) (hn : 0 < n) :
    range (correspondenceFriedrichsResolventSqrt n hn)=range (correspondenceComplexFormValue n hn)
        := by
  have hself : ((correspondenceFriedrichsResolventSqrt n hn).restrictScalars ℝ).adjoint=
      (correspondenceFriedrichsResolventSqrt n hn).restrictScalars ℝ := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    rw [correspondenceComplex_real_inner n, correspondenceComplex_real_inner n]
    exact congrArg Complex.re ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (correspondenceFriedrichsResolventSqrt_selfAdjoint n hn)) x y)
  have h := correspondenceSquareRoot_adjoint_range (correspondenceComplexFormResolvent n hn)
    ((correspondenceFriedrichsResolventSqrt n hn).restrictScalars ℝ) hself
    (correspondenceFriedrichsResolventSqrt_denseRange n hn)
        (correspondenceFriedrichsResolventSqrt_norm_form n hn)
  rw [correspondenceComplexFormResolvent_adjoint] at h
  exact h.symm

end
end GinibrePoincare

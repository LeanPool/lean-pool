/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/ComplexGeneratorCalculus.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CenterOfMassEigenfunctions
public import LeanPool.GinibrePoincare.Analysis.PolynomialChainRule
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-!
# Complex generator calculus

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `complexGinibrePregenerator_eq_direct`.
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Complex second real directional derivative. -/
def complexSecondDirectionalDerivative {n : ℕ} (f : Configuration n → ℂ)
    (v z : Configuration n) : ℂ :=
  fderiv ℝ (fun w => fderiv ℝ f w v) z v

/-- Complex derivative expression corresponding to the real concrete generator. -/
def directComplexGinibrePregenerator (n : ℕ) (f : Configuration n → ℂ)
    (z : Configuration n) : ℂ :=
  ((1 / (n : ℝ) : ℝ) : ℂ) * ∑ j : Fin n,
    (complexSecondDirectionalDerivative f (realCoordinateDirection j) z +
      complexSecondDirectionalDerivative f (imaginaryCoordinateDirection j) z) -
  2 * ∑ j : Fin n, fderiv ℝ f z (coordinateDirection j (z j)) +
  ((2 / (n : ℝ) : ℝ) : ℂ) * ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
    fderiv ℝ f z (coulombPairDirection j k z)

private theorem projection_fderiv {n : ℕ} (T : ℂ →L[ℝ] ℝ)
    (f : Configuration n → ℂ) (hf : Differentiable ℝ f) (z v : Configuration n) :
    fderiv ℝ (fun w => T (f w)) z v = T (fderiv ℝ f z v) := by
  have h := (T.hasFDerivAt.comp z (hf z).hasFDerivAt).fderiv
  change (fderiv ℝ (T ∘ f) z) v = _
  rw [h]
  rfl

private theorem projection_second {n : ℕ} (T : ℂ →L[ℝ] ℝ)
    (f : Configuration n → ℂ) (hf : Differentiable ℝ f)
    (hdf : ∀ v, Differentiable ℝ (fun w => fderiv ℝ f w v)) (z v : Configuration n) :
    secondDirectionalDerivative (fun w => T (f w)) v z =
      T (complexSecondDirectionalDerivative f v z) := by
  unfold secondDirectionalDerivative complexSecondDirectionalDerivative
  have heq : (fun w => fderiv ℝ (fun u => T (f u)) w v) =
      fun w => T (fderiv ℝ f w v) := by
    funext w; exact projection_fderiv T f hf w v
  rw [heq]
  exact projection_fderiv T _ (hdf v) z v

/-- Agreement with the componentwise extension of the actual real pregenerator. -/
theorem complexGinibrePregenerator_eq_direct (n : ℕ) (f : Configuration n → ℂ)
    (hf : Differentiable ℝ f)
    (hdf : ∀ v, Differentiable ℝ (fun w => fderiv ℝ f w v)) (z : Configuration n) :
    complexGinibrePregenerator n f z = directComplexGinibrePregenerator n f z := by
  have hr (w v : Configuration n) : fderiv ℝ (fun u => (f u).re) w v = (fderiv ℝ f w v).re := by
    simpa only [Complex.reCLM_apply] using projection_fderiv Complex.reCLM f hf w v
  have hi (w v : Configuration n) : fderiv ℝ (fun u => (f u).im) w v = (fderiv ℝ f w v).im := by
    simpa only [Complex.imCLM_apply] using projection_fderiv Complex.imCLM f hf w v
  have hrr (w v : Configuration n) : secondDirectionalDerivative (fun u => (f u).re) v w =
      (complexSecondDirectionalDerivative f v w).re := by
    simpa only [Complex.reCLM_apply] using projection_second Complex.reCLM f hf hdf w v
  have hii (w v : Configuration n) : secondDirectionalDerivative (fun u => (f u).im) v w =
      (complexSecondDirectionalDerivative f v w).im := by
    simpa only [Complex.imCLM_apply] using projection_second Complex.imCLM f hf hdf w v
  apply Complex.ext <;>
    simp [complexGinibrePregenerator, ginibrePregenerator, configurationLaplacian,
      directComplexGinibrePregenerator, hr, hi, hrr, hii, Complex.re_sum, Complex.im_sum]

end
end GinibrePoincare

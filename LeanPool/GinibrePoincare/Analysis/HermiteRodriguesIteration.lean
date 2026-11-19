/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteRodriguesIteration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesGaussian

/-! Literal iterated Wirtinger derivatives of the Gaussian. -/

@[expose] public section
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

theorem dholOne_mul {f g : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    dholOne (fun w => f w*g w) z=dholOne f z*g z+f z*dholOne g z := by
  change dholOne (f*g) z = _
  rw [dholOne, dholOne, dholOne, fderiv_mul (hf z) (hg z)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem dholOne_const_mul {f : ℂ → ℂ} (hf : Differentiable ℝ f) (c z : ℂ) :
    dholOne (fun w => c*f w) z = c*dholOne f z := by
  unfold dholOne
  rw [fderiv_const_mul (hf z)]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem dbarOne_const_mul {f : ℂ → ℂ} (hf : Differentiable ℝ f) (c z : ℂ) :
    dbarOnePublic (fun w => c*f w) z = c*dbarOnePublic f z := by
  unfold dbarOnePublic dbarOne
  rw [fderiv_const_mul (hf z)]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem dholOne_conj_pow (q : ℕ) (z : ℂ) :
    dholOne (fun w => conj w^q) z=0 := by
  unfold dholOne
  have h := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt (x:=z)).pow q
  change HasFDerivAt (fun w : ℂ => conj w^q) _ z at h
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
  change (1/2 : ℂ)*((q : ℂ)*conj z^(q-1)*conj 1-
    Complex.I*((q : ℂ)*conj z^(q-1)*conj Complex.I))=0
  simp only [map_one, Complex.conj_I, mul_one]
  linear_combination ((q : ℂ)*conj z^(q-1)/2)*Complex.I_sq

theorem iterate_dholOne_rodriguesGaussian (n q : ℕ) :
    dholOne^[q] (rodriguesGaussian n) =
      fun z => (-(n : ℂ))^q*conj z^q*rodriguesGaussian n z := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih]
    funext z
    have hG := (contDiff_rodriguesGaussian n).differentiable (by simp)
    have hpow : Differentiable ℝ (fun w : ℂ => conj w^q) := Complex.conjCLE.differentiable.pow q
    rw [show (fun z => (-(n : ℂ))^q*conj z^q*rodriguesGaussian n z) =
      (fun z => (-(n : ℂ))^q*(conj z^q*rodriguesGaussian n z)) by funext w; ring,
      dholOne_const_mul (hpow.fun_mul hG), dholOne_mul hpow hG,
      dholOne_conj_pow, dholOne_rodriguesGaussian]
    simp only [zero_mul, zero_add, pow_succ]
    ring

end
end ComplexHermite
end GinibrePoincare

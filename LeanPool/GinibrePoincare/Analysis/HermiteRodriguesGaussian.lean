/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteRodriguesGaussian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteWirtinger
public import LeanPool.GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-! Actual Wirtinger differentiation of the Gaussian in the Rodrigues formula. -/

@[expose] public section
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

/-- The one-variable Gaussian factor `exp (-n |z|²)`, viewed as a complex-valued function. -/
def rodriguesGaussian (n : ℕ) (z : ℂ) : ℂ :=
  (Real.exp (-(n : ℝ)*Complex.normSq z) : ℂ)

/-- The one-variable holomorphic Wirtinger derivative `∂ f = (∂_x f - I ∂_y f) / 2`. -/
def dholOne (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1/2 : ℂ)*(fderiv ℝ f z 1-Complex.I*fderiv ℝ f z Complex.I)

theorem contDiff_rodriguesGaussian (n : ℕ) : ContDiff ℝ ∞ (rodriguesGaussian n) := by
  unfold rodriguesGaussian
  have hN : ContDiff ℝ ∞ (Complex.normSq : ℂ → ℝ) := by
    convert! (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff) using 1
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul hN).exp)

theorem fderiv_rodriguesGaussian (n : ℕ) (z v : ℂ) :
    fderiv ℝ (rodriguesGaussian n) z v =
      ((-(n : ℝ)*(2*z.re*v.re+2*z.im*v.im)) : ℂ)*rodriguesGaussian n z := by
  have hr := Complex.reCLM.hasFDerivAt (x:=z)
  have hi := Complex.imCLM.hasFDerivAt (x:=z)
  have hn := (hr.mul hr).add (hi.mul hi)
  have he : (fun z : ℂ => z.re*z.re+z.im*z.im) = Complex.normSq := by
    funext z
    simp [Complex.normSq_apply]
  change HasFDerivAt (fun w : ℂ => w.re*w.re+w.im*w.im) _ z at hn
  rw [he] at hn
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z ((hn.const_mul (-(n : ℝ))).exp)
  change HasFDerivAt (rodriguesGaussian n) _ z at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    add_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  unfold rodriguesGaussian
  push_cast
  ring

theorem dbarOne_rodriguesGaussian (n : ℕ) (z : ℂ) :
    dbarOnePublic (rodriguesGaussian n) z = -(n : ℂ)*z*rodriguesGaussian n z := by
  unfold dbarOnePublic dbarOne
  rw [fderiv_rodriguesGaussian, fderiv_rodriguesGaussian]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    ]
  push_cast
  have he := Complex.re_add_im z
  linear_combination (-(n : ℂ)*rodriguesGaussian n z)*he

theorem dholOne_rodriguesGaussian (n : ℕ) (z : ℂ) :
    dholOne (rodriguesGaussian n) z = -(n : ℂ)*conj z*rodriguesGaussian n z := by
  unfold dholOne
  rw [fderiv_rodriguesGaussian, fderiv_rodriguesGaussian]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    ]
  push_cast
  have he := congrArg conj (Complex.re_add_im z)
  simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I] at he
  linear_combination (-(n : ℂ)*rodriguesGaussian n z)*he

end
end ComplexHermite
end GinibrePoincare

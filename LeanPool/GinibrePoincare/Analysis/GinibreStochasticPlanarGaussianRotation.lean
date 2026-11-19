/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticPlanarGaussianRotation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOneParticleRadius

/-! # Rotation invariance of the actual independent planar Gaussian noise -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The planar Gaussian on `ℂ` whose real and imaginary parts are independent centred Gaussians
of variance `v`. -/
def ginibrePlanarGaussian (v : ℝ≥0) : Measure ℂ :=
  ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
    (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ))

instance (v : ℝ≥0) : IsProbabilityMeasure (ginibrePlanarGaussian v) :=
  (by unfold ginibrePlanarGaussian; infer_instance)

theorem ginibrePlanarGaussian_charFun (v : ℝ≥0) (t : ℂ) :
    charFun (ginibrePlanarGaussian v) t =
      Complex.exp (- (v : ℂ) * (Complex.normSq t : ℂ) / 2) := by
  rw [charFun_apply]
  unfold ginibrePlanarGaussian
  rw [integral_map (by fun_prop) (by fun_prop)]
  have he (p : ℝ × ℝ) :
      Complex.exp ((inner ℝ ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) t : ℂ) * Complex.I) =
      Complex.exp ((t.re : ℂ) * (p.1 : ℂ) * Complex.I) *
        Complex.exp ((t.im : ℂ) * (p.2 : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    have hir : inner ℝ ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) t = t.re*p.1+t.im*p.2 := by
      change (t * (starRingEnd ℂ) ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))).re = _
      simp [Complex.mul_re, Complex.mul_im]
    rw [hir, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul]
    ring
  simp_rw [he]
  rw [integral_prod_mul (fun x : ℝ => Complex.exp ((t.re : ℂ) * (x : ℂ) * Complex.I))
    (fun y : ℝ => Complex.exp ((t.im : ℂ) * (y : ℂ) * Complex.I)), ← charFun_apply_real, ←
        charFun_apply_real,
    charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add]
  congr 1
  simp [Complex.normSq_apply, Complex.ofReal_add, Complex.ofReal_mul]
  ring

theorem ginibrePlanarGaussian_rotation (v : ℝ≥0) (u : ℂ) (hu : ‖u‖ = 1) :
    (ginibrePlanarGaussian v).map (fun z => u*z) = ginibrePlanarGaussian v := by
  apply Measure.ext_of_charFun
  funext t
  have he (z : ℂ) : inner ℝ (u*z) t = inner ℝ z ((starRingEnd ℂ) u * t) := by
    change (t * (starRingEnd ℂ) (u*z)).re =
      (((starRingEnd ℂ) u * t) * (starRingEnd ℂ) z).re
    rw [map_mul]
    congr 1
    ring
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [he]
  rw [← charFun_apply, ginibrePlanarGaussian_charFun, ginibrePlanarGaussian_charFun,
    Complex.normSq_mul]
  have hnu : Complex.normSq ((starRingEnd ℂ) u) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [hu]
  rw [hnu, one_mul]

end
end GinibrePoincare

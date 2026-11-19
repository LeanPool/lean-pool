/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOneParticleLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOneParticleProjection
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUIndependent

/-! # Concrete Gaussian transition law of the actual one-particle Ginibre path -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The actual planar one-particle transition, with drift rate `2α` and
Langevin noise amplitude `√(2α)`. -/
def ginibreOneParticleOUTransition (α t : ℝ≥0) (z : Configuration 1) : Measure (Configuration 1) :=
  ((ginibreOUTransition (2 * α) t (z 0).re).prod
    (ginibreOUTransition (2 * α) t (z 0).im)).map
      (fun p : ℝ × ℝ => (fun _ : Fin 1 => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)))

theorem ginibreOneParticleBrownianPath_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω s => Br s ω) (fun ω s => Bi s ω) P)
    (α t : ℝ≥0) (z : Configuration 1) :
    HasLaw (ginibreOneParticleBrownianPath Br Bi α z t)
      (ginibreOneParticleOUTransition α t z) P := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  let rate : ℝ≥0 := 2 * α
  let Xr := ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) (z 0).re t
  let Xi := ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) (z 0).im t
  let μ := (ginibreOUTransition rate t (z 0).re).prod (ginibreOUTransition rate t (z 0).im)
  let F : ℝ × ℝ → Configuration 1 := fun p _ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)
  have hp := (ginibreBrownianOU_independent Br Bi P hBr hBi hind rate rate t t
    (z 0).re (z 0).im).hasLaw_prod
    (ginibreBrownianOU_hasLaw Br P hBr rate t (z 0).re)
    (ginibreBrownianOU_hasLaw Bi P hBi rate t (z 0).im)
  have hF : HasLaw F (μ.map F) μ := ⟨by fun_prop, rfl⟩
  have h := hF.comp hp
  apply h.congr
  filter_upwards [ginibreOneParticleBrownianPath_projections Br Bi P hBr hBi α z]
    with ω hω
  ext j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  have hr := (hω t).1
  have hi := (hω t).2
  change ginibreOneParticleBrownianPath Br Bi α z t ω 0 =
    (Xr ω : ℂ) + Complex.I * (Xi ω : ℂ)
  apply Complex.ext
  · simpa only [Xr, rate, NNReal.coe_mul, NNReal.coe_ofNat,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero] using hr
  · simpa only [Xi, rate, NNReal.coe_mul, NNReal.coe_ofNat,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add] using hi

end
end GinibrePoincare

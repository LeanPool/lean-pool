/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCIRTransition.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadiusRotation

/-! # An autonomous radial transition for the actual one-particle process -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The time-`t` transition law of the one-particle squared radius started at `r`: the law of
`|m + W|²` for `m = e^{-2αt} √r` and `W` a planar Gaussian with variance
`ginibreOUVariance (2 * α) t`. -/
def ginibreOneParticleCIRTransition (α t : ℝ≥0) (r : ℝ) : Measure ℝ :=
  ginibreNoncentralRadiusLaw (ginibreOUVariance (2*α) t)
    ((ginibreOUDecay (2*α) t * Real.sqrt r : ℝ) : ℂ)

theorem ginibreOneParticleRadiusTransition_noncentral (α t : ℝ≥0) (z : Configuration 1) :
    ginibreOneParticleRadiusTransition α t z =
      ginibreNoncentralRadiusLaw (ginibreOUVariance (2*α) t)
        ((ginibreOUDecay (2*α) t : ℂ) * z 0) := by
  have hrad := ginibreOneParticleRadius_continuous.measurable
  let rate := 2*α
  let ν := gaussianReal 0 (ginibreOUVariance rate t)
  have hk (y : ℝ) : ginibreOUTransition rate t y =
      ν.map (fun u : ℝ => ginibreOUDecay rate t * y + u) := by
    change gaussianReal (ginibreOUDecay rate t * y) (ginibreOUVariance rate t) = _
    rw [gaussianReal_map_const_add, zero_add]
  unfold ginibreOneParticleRadiusTransition ginibreOneParticleOUTransition
    ginibreNoncentralRadiusLaw ginibrePlanarGaussian
  change (((ginibreOUTransition rate t (z 0).re).prod
    (ginibreOUTransition rate t (z 0).im)).map
    (fun p : ℝ × ℝ => fun _ : Fin 1 => (p.1 : ℂ) + Complex.I * (p.2 : ℂ))).map
      ginibreOneParticleRadius = ((ν.prod ν).map
        (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ))).map
          (fun w => Complex.normSq ((ginibreOUDecay rate t : ℂ) * z 0 + w))
  rw [hk, hk, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  dsimp [ginibreOneParticleRadius]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem ginibreOneParticleRadiusTransition_eq_CIR (α t : ℝ≥0) (z : Configuration 1) :
    ginibreOneParticleRadiusTransition α t z =
      ginibreOneParticleCIRTransition α t (ginibreOneParticleRadius z) := by
  rw [ginibreOneParticleRadiusTransition_noncentral]
  unfold ginibreOneParticleCIRTransition ginibreOneParticleRadius
  apply ginibreNoncentralRadiusLaw_eq_of_normSq_eq
  rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal]
  calc
    _ = (ginibreOUDecay (2*α) t)^2 * Complex.normSq (z 0) := by ring
    _ = (ginibreOUDecay (2*α) t)^2 * (Real.sqrt (Complex.normSq (z 0)))^2 := by
      rw [Real.sq_sqrt (Complex.normSq_nonneg _)]
    _ = _ := by ring

theorem ginibreOneParticleBrownianPath_CIR_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α t : ℝ≥0) (z : Configuration 1) :
    HasLaw (fun ω => ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z t ω))
      (ginibreOneParticleCIRTransition α t (ginibreOneParticleRadius z)) P := by
  rw [← ginibreOneParticleRadiusTransition_eq_CIR]
  exact ginibreOneParticleBrownianPath_radius_hasLaw Br Bi P hBr hBi hind α t z

theorem ginibreOneParticleBrownianPath_CIR_whole_past_markov {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α s t : ℝ≥0) (z : Configuration 1)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ y, ‖f y‖ ≤ C) :
    P[(fun ω => f (ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z (s+t) ω))) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => ∫ r, f r ∂ginibreOneParticleCIRTransition α t
        (ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z s ω))) := by
  have h := ginibreOneParticleBrownianPath_radius_conditional_law Br Bi P hBr hBi hind α s t z f hf
      C hbound
  simpa only [ginibreOneParticleRadiusTransition_eq_CIR] using h

end
end GinibrePoincare

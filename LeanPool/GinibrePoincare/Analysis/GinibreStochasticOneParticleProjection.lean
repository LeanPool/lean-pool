/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOneParticleProjection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOneParticle
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathOUProjection

/-! # Actual real and imaginary OU projections of the one-particle solution -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The real part of the unique particle, as a continuous real-linear map. -/
def ginibreOneParticleRealCLM : Configuration 1 →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.proj 0)
/-- The imaginary part of the unique particle, as a continuous real-linear map. -/
def ginibreOneParticleImagCLM : Configuration 1 →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj 0)

theorem ginibreOneParticleBrownianPath_projections {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (α : ℝ) (z : Configuration 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      (ginibreOneParticleBrownianPath Br Bi α z t ω 0).re =
        ginibreBrownianOU Br (2 * α) (Real.sqrt (2 * α)) (z 0).re t ω ∧
      (ginibreOneParticleBrownianPath Br Bi α z t ω 0).im =
        ginibreBrownianOU Bi (2 * α) (Real.sqrt (2 * α)) (z 0).im t ω := by
  filter_upwards [hBr.cont, hBi.cont] with ω hcr hci
  let N := ginibreOneParticleBrownianNoise Br Bi α ω
  have hN : Continuous N := by
    apply continuous_pi
    intro j
    exact ((Complex.continuous_ofReal.comp (hcr.comp continuous_real_toNNReal)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (hci.comp continuous_real_toNNReal)))).const_smul (Real.sqrt (2 * α))
  have hre : (fun s => ginibreOneParticleRealCLM (N s)) =
      ginibreBrownianNoise Br (Real.sqrt (2 * α)) ω := by
    funext s
    simp [ginibreOneParticleRealCLM, N, ginibreOneParticleBrownianNoise,
      ginibreBrownianNoise, Complex.mul_re]
  have him : (fun s => ginibreOneParticleImagCLM (N s)) =
      ginibreBrownianNoise Bi (Real.sqrt (2 * α)) ω := by
    funext s
    simp [ginibreOneParticleImagCLM, N, ginibreOneParticleBrownianNoise,
      ginibreBrownianNoise, Complex.mul_im]
  intro t
  constructor
  · have h := drivenOUPath_continuousLinearMap ginibreOneParticleRealCLM (2 * α) z N hN t
    rw [hre] at h
    exact h
  · have h := drivenOUPath_continuousLinearMap ginibreOneParticleImagCLM (2 * α) z N hN t
    rw [him] at h
    exact h

end
end GinibrePoincare

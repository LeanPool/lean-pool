/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOneParticle.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUPath

/-! # Actual Brownian-driven one-particle Ginibre paths

Two real Brownian paths give the planar cumulative noise. The explicit
convolution solves the original Ginibre equation globally almost surely.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Planar noise at the exact Langevin amplitude √(2α). -/
def ginibreOneParticleBrownianNoise {Ω : Type*}
    (Br Bi : ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) (t : ℝ) : Configuration 1 :=
  fun _ => Real.sqrt (2 * α) •
    ((Br t.toNNReal ω : ℂ) + Complex.I * (Bi t.toNNReal ω : ℂ))

/-- Actual one-particle solution, constructed from the Brownian paths. -/
def ginibreOneParticleBrownianPath {Ω : Type*}
    (Br Bi : ℝ≥0 → Ω → ℝ) (α : ℝ) (z : Configuration 1)
    (t : ℝ) (ω : Ω) : Configuration 1 :=
  drivenOUPath (2 * α) z (ginibreOneParticleBrownianNoise Br Bi α ω) t

theorem ginibreOneParticleBrownianPath_actual {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (α : ℝ) (z : Configuration 1) :
    ∀ᵐ ω ∂P, Continuous (fun t => ginibreOneParticleBrownianPath Br Bi α z t ω) ∧
      ginibreOneParticleBrownianPath Br Bi α z 0 ω = z ∧
      IsGinibreDrivenPath 1 α (ginibreOneParticleBrownianNoise Br Bi α ω)
        (fun t => ginibreOneParticleBrownianPath Br Bi α z t ω) := by
  filter_upwards [hBr.cont, hBi.cont, hBr.eval_zero_ae_eq_zero,
    hBi.eval_zero_ae_eq_zero] with ω hcr hci hzr hzi
  have hN : Continuous (ginibreOneParticleBrownianNoise Br Bi α ω) := by
    apply continuous_pi
    intro j
    exact ((Complex.continuous_ofReal.comp (hcr.comp continuous_real_toNNReal)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (hci.comp continuous_real_toNNReal)))).const_smul (Real.sqrt (2 * α))
  have hzero : ginibreOneParticleBrownianNoise Br Bi α ω 0 = 0 := by
    ext j
    simp [ginibreOneParticleBrownianNoise, hzr, hzi]
  refine ⟨drivenOUPath_continuous (2 * α) z _ hN, ?_,
    ginibreDrivenPath_one_explicit α z _ hN hzero⟩
  simp [ginibreOneParticleBrownianPath, drivenOUPath, hzero]

end
end GinibrePoincare

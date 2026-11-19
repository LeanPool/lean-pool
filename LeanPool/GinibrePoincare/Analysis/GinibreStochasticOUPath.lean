/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOUPath.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathOU
public import Mathlib.Probability.BrownianMotion.Basic

/-! # Brownian-driven OU sample paths

The process is constructed from the Brownian path using an ordinary Bochner
integral. Almost surely it is continuous and satisfies the actual driven OU
equation. These results do not assume an Itô-equation certificate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Cumulative real Brownian noise, continuously extended to negative time. -/
def ginibreBrownianNoise {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (σ : ℝ)
    (ω : Ω) (t : ℝ) : ℝ := σ * B t.toNNReal ω

/-- Explicit real Brownian-driven OU process. -/
def ginibreBrownianOU {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ σ x : ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  drivenOUPath κ x (ginibreBrownianNoise B σ ω) t

theorem ginibreBrownianOU_actual_path {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (κ σ x : ℝ) :
    ∀ᵐ ω ∂P, Continuous (fun t => ginibreBrownianOU B κ σ x t ω) ∧
      ginibreBrownianOU B κ σ x 0 ω = x ∧
      ∀ t : ℝ, ginibreBrownianOU B κ σ x t ω = x + σ * B t.toNNReal ω +
        ∫ s in (0 : ℝ)..t, -κ * ginibreBrownianOU B κ σ x s ω := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hcont hzero
  have hN : Continuous (ginibreBrownianNoise B σ ω) :=
    continuous_const.mul (hcont.comp continuous_real_toNNReal)
  refine ⟨drivenOUPath_continuous κ x _ hN, ?_, ?_⟩
  · simp [ginibreBrownianOU, drivenOUPath, ginibreBrownianNoise, hzero]
  · intro t
    exact drivenOUPath_integral_equation κ x _ hN t

/-- For one particle the actual Ginibre drift is the linear OU drift. -/
theorem ginibreLangevinDrift_one (α : ℝ) (z : Configuration 1) :
    ginibreLangevinDrift 1 α z = -(2 * α) • z := by
  ext j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  simp [ginibreLangevinDrift, ginibreCoulombInteraction]

/-- Actual global one-particle additive-noise Ginibre solution for every
continuous configuration-valued driving path starting at zero. -/
theorem ginibreDrivenPath_one_explicit (α : ℝ) (x : Configuration 1)
    (N : ℝ → Configuration 1) (hN : Continuous N) (hzero : N 0 = 0) :
    IsGinibreDrivenPath 1 α N (drivenOUPath (2 * α) x N) := by
  have h0 : drivenOUPath (2 * α) x N 0 = x := by simp [drivenOUPath, hzero]
  constructor
  · intro t _
    simp only [ginibreLangevinDrift_one]
    exact ((drivenOUPath_continuous (2 * α) x N hN).const_smul
      (-(2 * α))).intervalIntegrable 0 t
  · intro t _
    rw [h0]
    simp only [ginibreLangevinDrift_one]
    exact drivenOUPath_integral_equation (2 * α) x N hN t

end
end GinibrePoincare

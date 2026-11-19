/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalOUPathElement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalJointOUFunctional

/-!
# Brownian orthogonal OU path element

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreOUPathElement_measurable`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous complex paths `C(ℝ, ℂ)`. -/
local instance instBorelBrownianOrthogonalOUPathElement : MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- The continuous complex Ornstein–Uhlenbeck path with rate `2α/n`, started at `p.1` and driven
by `p.2`, evaluated at time `t.toNNReal`. -/
def ginibreOUPathElement (n : ℕ) (α : ℝ) (p : ℂ × C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => drivenOUPath (2*α/(n : ℝ)) p.1 p.2 (Real.toNNReal t),
    (drivenOUPath_continuous _ _ _ p.2.continuous).comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)⟩

theorem ginibreOUPathElement_measurable (n : ℕ) (α : ℝ) :
    Measurable (ginibreOUPathElement n α) := by
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  exact ginibreOU_initial_noise_joint_measurable n α (Real.toNNReal t)

end
end GinibrePoincare

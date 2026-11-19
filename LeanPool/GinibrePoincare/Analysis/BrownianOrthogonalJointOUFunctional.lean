/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalJointOUFunctional.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalEquilibriumInputs
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianJointEvaluation

/-!
# Brownian orthogonal joint OU functional

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreOU_initial_noise_path_measurable`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous complex paths `C(ℝ, ℂ)`. -/
local instance instBorelBrownianOrthogonalJointOUFunctional : MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- Joint measurability in the initial center and its entire continuous noise. -/
theorem ginibreOU_initial_noise_joint_measurable (n : ℕ) (α : ℝ) (t : ℝ≥0) :
    Measurable (fun p : ℂ × C(ℝ, ℂ) => drivenOUPath (2*α/(n : ℝ)) p.1 p.2 t) := by
  have hj : Continuous (fun p : C(ℝ, ℂ) × ℝ => Real.exp ((2*α/(n : ℝ))*p.2) • p.1 p.2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).smul continuous_eval
  have hInt : Measurable (fun N : C(ℝ, ℂ) => ∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp ((2*α/(n : ℝ))*s) • N s) := by
    have hi := hj.measurable.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
    simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using hi.measurable
  exact ((continuous_eval_const (t : ℝ)).measurable.comp measurable_snd).add
    (measurable_const.smul (measurable_fst.sub (measurable_const.smul (hInt.comp measurable_snd))))

/-- Joint measurable whole OU solution path, with random initial center. -/
theorem ginibreOU_initial_noise_path_measurable (n : ℕ) (α : ℝ) :
    Measurable (fun p : ℂ × C(ℝ, ℂ) => fun t : ℝ≥0 =>
      drivenOUPath (2*α/(n : ℝ)) p.1 p.2 t) := by
  apply Measurable.of_eval
  intro t
  exact ginibreOU_initial_noise_joint_measurable n α t

end
end GinibrePoincare

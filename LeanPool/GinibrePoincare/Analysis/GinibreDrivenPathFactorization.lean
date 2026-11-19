/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDynamicsDrift
public import LeanPool.GinibrePoincare.Analysis.CenterOfMassEigenfunctions
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-! # Pathwise splitting of the additive-noise equation

`IsGinibreDrivenPath` records integrability of the concrete Langevin drift
and its Volterra equation with cumulative noise `N`. The maps
`coordinateSumCLM` and `recenteredCLM` commute with interval integration.
Applying them to the equation and using the drift identities produces the
center OU equation and the autonomous recentered equation.

These results are deterministic: they apply to any driven solution on
nonnegative times. Brownian projection and independence enter later through
`GinibreBrownianProjection`; global path versions and stochastic
factorization are assembled in `BrownianOrthogonalGlobalPathFactorization`
and `BrownianOrthogonalIndependentInitial`. -/

@[expose] public section

open MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- The actual recentering projection as a continuous real-linear map. -/
def recenteredCLM (n : ℕ) : Configuration n →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i -
    ((n : ℝ)⁻¹ • coordinateSumCLM n)

@[simp] theorem recenteredCLM_apply (n : ℕ) (z : Configuration n) :
    recenteredCLM n z = recenteredConfiguration n z := by
  ext i
  simp [recenteredCLM, recenteredConfiguration, projectToOrthogonal,
    Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- The additive-noise Ginibre integral equation with the actual arbitrary-speed drift.
The input `N` is the cumulative driving noise in configuration coordinates. -/
def IsGinibreDrivenPath (n : ℕ) (α : ℝ) (N X : ℝ → Configuration n) : Prop :=
  (∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun s => ginibreLangevinDrift n α (X s)) volume 0 t) ∧
    ∀ t : ℝ, 0 ≤ t → X t = X 0 + N t + ∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (X s)

/-- Every actual additive-noise solution satisfies the autonomous center OU
integral equation driven by the summed noise. -/
theorem ginibreDrivenPath_center_equation (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hX : IsGinibreDrivenPath n α N X)
    (t : ℝ) (ht : 0 ≤ t) :
    coordinateSum (X t) = coordinateSum (X 0) + coordinateSum (N t) +
      ∫ s in (0 : ℝ)..t, -(2 * α / (n : ℝ)) • coordinateSum (X s) := by
  have he := congrArg (coordinateSumCLM n) (hX.2 t ht)
  simp only [map_add] at he
  rw [← (coordinateSumCLM n).intervalIntegral_comp_comm (hX.1 t ht)] at he
  simpa only [coordinateSumCLM_apply, coordinateSum_ginibreLangevinDrift] using he

/-- Every actual additive-noise solution satisfies the autonomous recentered
integral equation driven by the projected noise. -/
theorem ginibreDrivenPath_recentered_equation (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hX : IsGinibreDrivenPath n α N X)
    (t : ℝ) (ht : 0 ≤ t) :
    recenteredConfiguration n (X t) = recenteredConfiguration n (X 0) +
      recenteredConfiguration n (N t) +
      ∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (recenteredConfiguration n (X s)) := by
  have he := congrArg (recenteredCLM n) (hX.2 t ht)
  simp only [map_add] at he
  rw [← (recenteredCLM n).intervalIntegral_comp_comm (hX.1 t ht)] at he
  simpa only [recenteredCLM_apply, recentered_ginibreLangevinDrift] using he

end
end GinibrePoincare

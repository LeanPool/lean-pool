/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/MainProofReduction.lean.
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

public import LeanPool.GinibrePoincare.Concrete.AnalyticStatements
public import Mathlib.Tactic.Linarith
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-!
# Checked endgame of the main proof

After normalizing the ground-state transform, the proof has the scalar shape

* `E = 4 D`;
* `δ_γ ≤ D`;
* `δ_γ = δ_μ`;
* `Var / 2 ≤ δ_μ`.

The first theorem verifies this scalar implication.  The second applies it to
the literal Ginibre quantities.  Its five hypotheses are displayed separately;
there is no bundled certificate argument.
-/

@[expose] public section

namespace GinibrePoincare

/-- Exact scalar implication used in the main proof. -/
theorem mainProof_scalar_endgame
    (variance energy dbarEnergy gaussianDistance ginibreDistance : ℝ)
    (hEnergy : energy = 4 * dbarEnergy)
    (hGaussian : gaussianDistance ≤ dbarEnergy)
    (hIsometry : gaussianDistance = ginibreDistance)
    (hHalf : variance / 2 ≤ ginibreDistance) :
    variance ≤ energy / 2 := by
  linarith

/-- The smooth-core theorem follows from the five concrete analytic statements. -/
theorem smoothGinibrePoincare_of_main_analytic_statements
    (hAdmissible : GroundStateAdmissibilityStatement)
    (hEnergy : GroundStateEnergyIdentityStatement)
    (hGaussian : GaussianDbarEstimateStatement)
    (hDistance : GroundStateDistanceIdentityStatement)
    (hHalf : GinibreHalfDistanceStatement) :
    SmoothGinibrePoincareStatement := by
  intro n hn hProbability f hf
  let g : Configuration n → ℂ :=
    normalizedVandermondeTransform n
      (fun z => (centeredObservable n f z : ℂ))
  have hgAdmissible : IsGaussianDbarAdmissible n g := by
    exact hAdmissible n hn hProbability f hf
  have hgEnergy :
      smoothGinibreEnergy n f = 4 * gaussianDbarEnergy n g := by
    exact hEnergy n hn hProbability f hf
  have hgGaussian :
      gaussianHolomorphicDistanceSq n g ≤ gaussianDbarEnergy n g := by
    exact hGaussian n hn g hgAdmissible
  have hgDistance :
      gaussianHolomorphicDistanceSq n g =
        ginibreHolomorphicDistanceSq n (centeredObservable n f) := by
    exact hDistance n hn hProbability f hf
  have hgHalf :
      smoothGinibreVariance n f / 2 ≤
        ginibreHolomorphicDistanceSq n (centeredObservable n f) := by
    exact hHalf n hn hProbability f hf
  exact mainProof_scalar_endgame
    (smoothGinibreVariance n f)
    (smoothGinibreEnergy n f)
    (gaussianDbarEnergy n g)
    (gaussianHolomorphicDistanceSq n g)
    (ginibreHolomorphicDistanceSq n (centeredObservable n f))
    hgEnergy hgGaussian hgDistance hgHalf

end GinibrePoincare

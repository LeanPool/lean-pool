/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/AnalyticStatements.lean.
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

public import LeanPool.GinibrePoincare.Concrete.HolomorphicDistance
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Exact analytic inputs to the main proof

Each proposition is written using the concrete measures, derivatives, and
normalized ground-state transform.  None is bundled into a certificate and
none is postulated by a declaration.

This module defines the propositions; it does not prove them. Their proofs
are `groundStateAdmissibility` and `groundStateEnergyIdentity` in
`Analysis/GroundStateDbar.lean`. `Endgame/FullMainAnalyticProof.lean` supplies
these proved inputs to the scalar reduction in `MainProofReduction.lean`.
-/


@[expose] public section


namespace GinibrePoincare

noncomputable section

/-- The transformed centered observable belongs to the Gaussian `dbar` domain. -/
def GroundStateAdmissibilityStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    MeasureTheory.IsProbabilityMeasure (ginibreMeasure n) →
    ∀ f : Configuration n → ℝ,
      IsSmoothCompactSymmetric f →
      IsGaussianDbarAdmissible n
        (normalizedVandermondeTransform n
          (fun z => (centeredObservable n f z : ℂ)))

/-- The Dirichlet-form identity after normalized multiplication by `V_n`. -/
def GroundStateEnergyIdentityStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    MeasureTheory.IsProbabilityMeasure (ginibreMeasure n) →
    ∀ f : Configuration n → ℝ,
      IsSmoothCompactSymmetric f →
      smoothGinibreEnergy n f =
        4 * gaussianDbarEnergy n
          (normalizedVandermondeTransform n
            (fun z => (centeredObservable n f z : ℂ)))


end

end GinibrePoincare

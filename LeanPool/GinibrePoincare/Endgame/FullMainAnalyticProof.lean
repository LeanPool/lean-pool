/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/FullMainAnalyticProof.lean.
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

public import LeanPool.GinibrePoincare.Concrete.MainProofReduction
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireDistance
public import LeanPool.GinibrePoincare.Analysis.GinibreEntireProjectionEndpoints

/-! # The original analytic proof of Theorem 1.1
All five analytic inputs are unconditional compiled theorems about the concrete
measures and actual entire representative distance infima.

Read `Concrete/MainProofReduction.lean` for the four scalar relations that
combine into the inequality. Here the five analytic propositions, including
admissibility, are filled by their proved concrete endpoints. Their order is:
domain admissibility, energy transport, Gaussian dbar estimate, isometric
distance transport, and real holomorphic-antiholomorphic half-distance geometry.
The ordinary weak-domain extension and equality classification are separate
endpoints; this theorem itself concerns the symmetric smooth compact core.
-/

@[expose] public section
namespace GinibrePoincare

/-- The paper's original smooth compact symmetric Poincaré proof, with no
analytic fact supplied as a theorem argument. -/
theorem fullMainAnalyticProof : SmoothGinibrePoincareStatement :=
  smoothGinibrePoincare_of_main_analytic_statements
    groundStateAdmissibility groundStateEnergyIdentity gaussianDbarEstimateStatement
    groundStateDistanceIdentityStatement ginibreHalfDistanceStatement

end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityCoordinateBasis.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinateEquation
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradient
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Ginibre transition analytic local regularity coordinate basis

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_coordinate_basis`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_coordinate_basis (n : ℕ) (k : Fin n × Fin 2) :
    (configurationEuclideanEquiv n).symm (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ k) =
      ginibreCoordinateDirection k := by
  classical
  rcases k with ⟨i, j⟩
  fin_cases j <;> ext l <;> by_cases hl : l = i <;>
    simp [configurationEuclideanEquiv_symm_apply, EuclideanSpace.basisFun_apply,
      ginibreCoordinateDirection, realCoordinateDirection,
      imaginaryCoordinateDirection, coordinateDirection, Prod.mk.injEq, hl] <;> rfl

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HolomorphicQuotientPhaseProjection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreConjugationGeometry
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! # Exact phase covariance of closed homogeneous quotient projections -/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

/-- The actual orthogonal projection onto a homogeneous quotient closure
commutes with every unit global phase. -/
theorem ginibreGlobalPhaseL2_comm_quotientDegreeProjection {n : ℕ} (hn : 0 < n)
    (d : ℕ) (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (ginibreMeasure n)) :
    ginibreGlobalPhaseL2 hn u hu
        ((ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule.starProjection x) =
      (ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule.starProjection
        (ginibreGlobalPhaseL2 hn u hu x) := by
  let U := (ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule
  let T := ginibreGlobalPhaseL2 hn u hu
  have he : ∀ y ∈ U, T y = u ^ d • y := fun y hy =>
    ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n d hn hy u hu
  have hu0 : u ≠ 0 := by
    intro hz
    simp [hz] at hu
  have hmap : U.map T.toLinearMap = U := by
    apply le_antisymm
    · rintro y ⟨z, hz, rfl⟩
      change T z ∈ U
      rw [he z hz]
      exact U.smul_mem _ hz
    · intro y hy
      refine ⟨(u ^ d)⁻¹ • y, U.smul_mem _ hy, ?_⟩
      change T ((u ^ d)⁻¹ • y) = y
      rw [he _ (U.smul_mem _ hy), smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hu0), one_smul]
  let : (U.map T.toLinearMap).HasOrthogonalProjection := hmap.symm ▸ inferInstance
  calc
    T (U.starProjection x) = (U.map T.toLinearMap).starProjection (T x) := T.map_starProjection U x
    _ = U.starProjection (T x) := by simp only [hmap]

/-- Projection onto degree d extracts its exact phase character from every
ambient L² vector. -/
theorem ginibre_quotientDegreeProjection_globalPhase {n : ℕ} (hn : 0 < n)
    (d : ℕ) (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (ginibreMeasure n)) :
    (ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule.starProjection
      (ginibreGlobalPhaseL2 hn u hu x) =
      u ^ d • (ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule.starProjection x := by
  rw [← ginibreGlobalPhaseL2_comm_quotientDegreeProjection]
  exact ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n d hn
    (Submodule.starProjection_apply_mem _ _) u hu

end
end GinibrePoincare

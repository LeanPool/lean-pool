/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEntireProjectionGeometry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEntireProjectionBridge
public import LeanPool.GinibrePoincare.Analysis.GinibreComplexProjectionGeometry
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Literal Lemma 2.7 on the paper's actual divisible entire space -/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The actual paper-defined `H_n^div`, bundled as a closed subspace. -/
def ginibreDivisibleEntireClosedSpace (n : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) where
  toSubmodule := ginibreDivisibleEntireL2 n hn
  isClosed' := isClosed_ginibreDivisibleEntireL2 n hn

theorem ginibreDivisibleEntireClosedSpace_eq_holomorphic (n : ℕ) (hn : 0 < n) :
    ginibreDivisibleEntireClosedSpace n hn = ginibreHolomorphicAmbientClosedSpan n hn := by
  ext u
  change u ∈ ginibreDivisibleEntireL2 n hn ↔ u ∈
    (ginibreHolomorphicAmbientClosedSpan n hn).toSubmodule
  rw [ginibreDivisibleEntireL2_eq_holomorphicAmbient]

/-- The actual antiholomorphic space consists precisely of conjugates of
members of the paper-defined divisible entire space. -/
theorem ginibreAntiholomorphic_mem_iff_conjugate_divisibleEntire (n : ℕ) (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) :
    u ∈ ginibreAntiholomorphicAmbientClosedSpan n hn ↔
      star u ∈ ginibreDivisibleEntireL2 n hn := by
  rw [ginibreDivisibleEntireL2_eq_holomorphicAmbient]
  rfl

/-- A projection residual is the literal metric distance to a closed
Hilbert subspace, including the present entire-function spaces. -/
theorem closedSubspace_infDist_eq_projectionNorm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : ClosedSubmodule ℂ E) (u : E) :
    Metric.infDist u (H : Set E) = ‖u - H.starProjection u‖ := by
  apply le_antisymm
  · simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem
      (show H.starProjection u ∈ (H : Set E) from
        Submodule.starProjection_apply_mem _ _)
  · apply (Metric.le_infDist ⟨0, H.zero_mem⟩).mpr
    intro y hy
    have hy0 : H.toSubmoduleᗮ.starProjection y = 0 := by
      rw [Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_eq_self_iff.mpr hy, sub_self]
    have h := H.toSubmoduleᗮ.norm_starProjection_apply_le (u - y)
    simpa only [map_sub, hy0, sub_zero, Submodule.starProjection_orthogonal_val,
      dist_eq_norm] using h

/-- Lemma 2.7(1) for the actual centered entire spaces. Centering is
expressed by the genuine constant orthogonal projection. -/
theorem ginibreDivisibleEntire_centered_orthogonality (n : ℕ) (hn : 0 < n)
    (x y : Lp ℂ 2 (ginibreMeasure n))
    (hx : x ∈ ginibreDivisibleEntireL2 n hn)
    (hy : y ∈ ginibreDivisibleEntireL2 n hn)
    (hxc : (ginibreConstantClosedSubspace n hn).starProjection x = 0)
    (hyc : (ginibreConstantClosedSubspace n hn).starProjection y = 0) :
    inner ℂ x (star y) = 0 := by
  have hxp : x ∈ ginibrePositiveQuotientGradedClosedSpan n hn := by
    have h := ginibreHolomorphicProjection_split n hn x
    rw [ginibreDivisibleEntireL2_eq_holomorphicAmbient] at hx
    rw [Submodule.starProjection_eq_self_iff.mpr hx, hxc, zero_add] at h
    rw [h]
    exact Submodule.starProjection_apply_mem _ _
  have hyp : y ∈ ginibrePositiveQuotientGradedClosedSpan n hn := by
    have h := ginibreHolomorphicProjection_split n hn y
    rw [ginibreDivisibleEntireL2_eq_holomorphicAmbient] at hy
    rw [Submodule.starProjection_eq_self_iff.mpr hy, hyc, zero_add] at h
    rw [h]
    exact Submodule.starProjection_apply_mem _ _
  exact inner_star_eq_zero_of_mem_positiveQuotientGradedClosedSpan hn hxp hyp

/-- Literal equation (2.25) for arbitrary complex L² inputs and actual
entire-space orthogonal projections. -/
theorem ginibreDivisibleEntire_two_projection_bound (n : ℕ) (hn : 0 < n)
    (f : Lp ℂ 2 (ginibreMeasure n)) :
    ‖(ginibreDivisibleEntireClosedSpace n hn).starProjection f‖ ^ 2 +
      ‖(ginibreAntiholomorphicAmbientClosedSpan n hn).starProjection f‖ ^ 2 ≤
    ‖f‖ ^ 2 + ‖(ginibreConstantClosedSubspace n hn).starProjection f‖ ^ 2 := by
  rw [ginibreDivisibleEntireClosedSpace_eq_holomorphic,
    ← ginibreAntiholomorphicProjection_eq_starProjection]
  exact ginibre_complex_two_projection_bound n hn f

/-- Literal equations (2.26)--(2.28), including metric distance to the
actual entire Vandermonde-defined subspace. -/
theorem ginibreDivisibleEntire_real_centered_geometry (n : ℕ) (hn : 0 < n)
    (f : Lp ℂ 2 (ginibreMeasure n)) (hreal : star f = f)
    (hcenter : (ginibreConstantClosedSubspace n hn).starProjection f = 0) :
    let h := (ginibreDivisibleEntireClosedSpace n hn).starProjection f
    let r := f - h - star h
    inner ℂ h (star h) = 0 ∧ inner ℂ h r = 0 ∧ inner ℂ (star h) r = 0 ∧
      ‖f‖ ^ 2 = 2 * ‖h‖ ^ 2 + ‖r‖ ^ 2 ∧
      Metric.infDist f (ginibreDivisibleEntireClosedSpace n hn :
        Set (Lp ℂ 2 (ginibreMeasure n))) ^ 2 = ‖f‖ ^ 2 / 2 + ‖r‖ ^ 2 / 2 ∧
      ‖f‖ ^ 2 / 2 ≤ Metric.infDist f (ginibreDivisibleEntireClosedSpace n hn :
        Set (Lp ℂ 2 (ginibreMeasure n))) ^ 2 := by
  rw [ginibreDivisibleEntireClosedSpace_eq_holomorphic]
  dsimp
  rw [closedSubspace_infDist_eq_projectionNorm]
  exact ginibre_real_centered_projection_geometry n hn f hreal hcenter

end
end GinibrePoincare


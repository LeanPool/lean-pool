/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiBump.lean.
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

public import LeanPool.GinibrePoincare.Analysis.LebesgueL2Mollification
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Non quadratic pi bump

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `piPlanarBump_compact`, `piPlanarBump_integral`, `piPlanarBump_nonneg`,
`piPlanarBump_support_ball`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section

/-- The product bump `x ↦ ∏ i, φ.normed volume (x i)` on `ℂ^d`, built from the normalised planar
bump `φ`. -/
def piPlanarBump (d : ℕ) (φ : ContDiffBump (0 : ℂ)) (x : Configuration d) : ℝ :=
  ∏ i, φ.normed volume (x i)

theorem piPlanarBump_continuous (d : ℕ) (φ : ContDiffBump (0 : ℂ)) : Continuous (piPlanarBump d φ)
    :=
  continuous_finsetProd _ (fun i _ => φ.continuous_normed.comp (continuous_apply i))

theorem piPlanarBump_compact (d : ℕ) (φ : ContDiffBump (0 : ℂ)) : HasCompactSupport (piPlanarBump d
    φ) := by
  have hs : IsCompact {x : Configuration d | ∀ i, x i ∈ tsupport (φ.normed (volume : Measure ℂ))} :=
    isCompact_pi_infinite (fun _ => φ.hasCompactSupport_normed)
  apply hs.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hs.isClosed
  intro x hx i
  apply subset_closure
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem piPlanarBump_integral (d : ℕ) (φ : ContDiffBump (0 : ℂ)) :
    (∫ x : Configuration d, piPlanarBump d φ x) = 1 := by
  change (∫ x : Configuration d, (∏ i, φ.normed volume (x i))
    ∂Measure.pi (fun _ => (volume : Measure ℂ))) = 1
  rw [integral_fintype_prod_eq_prod (fun _ : Fin d => φ.normed volume)]
  simp only [φ.integral_normed, Finset.prod_const_one]

theorem piPlanarBump_nonneg (d : ℕ) (φ : ContDiffBump (0 : ℂ)) (x : Configuration d) :
    0 ≤ piPlanarBump d φ x := Finset.prod_nonneg (fun _ _ => φ.nonneg_normed _)

theorem piPlanarBump_support_ball (d : ℕ) (φ : ContDiffBump (0 : ℂ)) (x : Configuration d)
    (hx : x ∈ Function.support (piPlanarBump d φ)) : dist x 0 < φ.rOut := by
  rw [dist_zero_right]
  apply (pi_norm_lt_iff φ.rOut_pos).mpr
  intro i
  have hm : x i ∈ Function.support (φ.normed (volume : Measure ℂ)) :=
    fun h => hx (Finset.prod_eq_zero (Finset.mem_univ i) h)
  rw [φ.support_normed_eq] at hm
  simpa only [Metric.mem_ball, dist_zero_right] using hm
end
end GinibrePoincare

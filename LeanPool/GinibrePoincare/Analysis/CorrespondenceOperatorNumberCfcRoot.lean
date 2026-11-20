/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberCfcRoot.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberCfc
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberSpectralResolvent
/-!
# Correspondence operator number cfc root

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_shifted_sqrt_cfc`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
open ComplexHermite
/-- Continuous bounded-resolvent coordinate for the literal shifted square root. -/
def correspondenceOperatorRootCoordinate (a : ℝ) (r : ℝ) : ℝ :=
  Real.sqrt r / (Real.sqrt r + Real.sqrt (1 - (a + 1) * r))

theorem correspondenceOperatorRootCoordinate_continuous (a : ℝ) (ha : 0 ≤ a) :
    Continuous (correspondenceOperatorRootCoordinate a) := by
  apply Real.continuous_sqrt.div
    (Real.continuous_sqrt.add (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_const.mul continuous_id))))
  intro r
  have hp : 0 < Real.sqrt r + Real.sqrt (1 - (a + 1) * r) := by
    by_cases h : 0 < r
    · exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr h) (Real.sqrt_nonneg _)
    · have hq : 0 < 1 - (a + 1) * r := by
        have : (a + 1) * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_not_gt h)
        linarith
      exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr hq)
  exact ne_of_gt hp

theorem correspondenceOperatorRootCoordinate_eval (a x : ℝ) (hx : 0 ≤ x) :
    correspondenceOperatorRootCoordinate a (1 + x)⁻¹ = (1 + Real.sqrt (x - a))⁻¹ := by
  unfold correspondenceOperatorRootCoordinate
  have hy : 0 < 1 + x := by linarith
  have hs : Real.sqrt (1 + x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hy)
  have he : 1 - (a + 1) * (1 + x)⁻¹ = (x - a) / (1 + x) := by
    field_simp
    ring
  rw [he, Real.sqrt_inv, Real.sqrt_div' _ (le_of_lt hy)]
  field_simp

/-- The maximal shifted square-root resolvent is actual Mathlib continuous
functional calculus of the genuine number resolvent, on the complete L² space. -/
theorem correspondenceOperatorNumber_shifted_sqrt_cfc (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    correspondenceOperatorNumberSpectralResolvent n hn (fun x => Real.sqrt (x - a))
      (fun _ => Real.sqrt_nonneg _) =
    cfc (correspondenceOperatorRootCoordinate a) (correspondenceOperatorNumberResolvent n hn) := by
  apply ContinuousLinearMap.ext
  intro u
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  rw [correspondenceOperatorNumberSpectralResolvent_coefficient,
    correspondenceOperatorNumber_cfc_coefficient n hn _
      (correspondenceOperatorRootCoordinate_continuous a ha).continuousOn]
  unfold correspondenceOperatorNumberResolventWeight
  rw [correspondenceOperatorRootCoordinate_eval a _ (Nat.cast_nonneg _)]
  simp
end
end GinibrePoincare

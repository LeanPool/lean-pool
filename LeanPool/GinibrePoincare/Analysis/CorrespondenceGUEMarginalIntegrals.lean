/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEMarginalIntegrals.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUESplitVolume
/-!
# Correspondence GUE marginal integrals

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueOrderedRawDensity_partition_ne_zero`,
`gueDoubledOrderedMeasure_real_marginal_integral`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The unnormalized Gaussian density `exp (-(n / 2) * ‖y‖ ^ 2)` of the auxiliary coordinates. -/
def gueAuxGaussianDensity (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-(n : ℝ)/2*‖y‖^2)

theorem gueDoubledOrdered_integral_split (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, gueDoubledOrderedDensity n x*f (gueRealProjection n x)) =
      (∫ x, gueOrderedRawDensity n x*f x)*(∫ y, gueAuxGaussianDensity n y) := by
  have hs := (gueSplit_volume_preserving n).integral_comp
    (gueSplitMeasurableEquiv n).measurableEmbedding
    (fun p => (gueOrderedRawDensity n p.1*f p.1)*gueAuxGaussianDensity n p.2)
  have hs2 := hs.trans
    (integral_prod_mul (fun x => gueOrderedRawDensity n x * f x) (gueAuxGaussianDensity n))
  rw [← hs2]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [gueSplitMeasurableEquiv_apply, gueDoubledOrderedDensity_split]
  unfold gueAuxGaussianDensity
  ring

theorem gueOrderedRawDensity_partition_ne_zero {n : ℕ} (hn : 0 < n) :
    (∫ x, gueOrderedRawDensity n x)≠0 := by
  have h := gueDoubledOrdered_integral_split n (fun _ => 1)
  simp only [mul_one] at h
  intro hz
  rw [hz, zero_mul] at h
  exact (ne_of_gt (gueDoubledOrdered_partition_pos hn)) h

theorem gueAuxGaussianDensity_partition_ne_zero {n : ℕ} (hn : 0 < n) :
    (∫ x, gueAuxGaussianDensity n x)≠0 := by
  have h := gueDoubledOrdered_integral_split n (fun _ => 1)
  simp only [mul_one] at h
  intro hz
  rw [hz, mul_zero] at h
  exact (ne_of_gt (gueDoubledOrdered_partition_pos hn)) h

/-- Exact cancellation of the auxiliary Gaussian normalization, for every real test. -/
theorem gueDoubledOrderedMeasure_real_marginal_integral {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f (gueRealProjection n x) ∂gueDoubledOrderedMeasure n)=
      (∫ x, gueOrderedRawDensity n x*f x)/(∫ x, gueOrderedRawDensity n x) := by
  rw [gueDoubledOrderedMeasure_integral, gueDoubledOrdered_integral_split]
  have hp := gueDoubledOrdered_integral_split n (fun _ => 1)
  simp only [mul_one] at hp
  rw [hp]
  field_simp [gueAuxGaussianDensity_partition_ne_zero hn]

end
end GinibrePoincare

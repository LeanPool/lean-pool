/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUESplitDensity.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEBoundedLSI
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEGeometry
/-!
# Correspondence GUE split density

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueDoubledOrderedDensity_split`.
-/

@[expose] public section
open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The projection `x ↦ (i ↦ x (i, 0))` onto the real coordinates. -/
def gueRealProjection (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => x (i, 0))
/-- The projection `x ↦ (i ↦ x (i, 1))` onto the auxiliary coordinates. -/
def gueAuxProjection (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => x (i, 1))
/-- The unnormalized ordered density
`exp (-(n / 2) * ‖x‖ ^ 2) * ∏_{i < j} gueOrderedPairWeight (x j - x i)`. -/
def gueOrderedRawDensity (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-(n : ℝ)/2*‖x‖^2)*∏p∈guePairs n, gueOrderedPairWeight (x p.2-x p.1)

theorem gueSplit_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    ‖x‖^2=‖gueRealProjection n x‖^2+‖gueAuxProjection n x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, gueRealProjection, gueAuxProjection]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [Finset.sum_add_distrib]

theorem gueDoubledOrderedDensity_split (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    gueDoubledOrderedDensity n x = gueOrderedRawDensity n (gueRealProjection n x)*
      Real.exp (-(n : ℝ)/2*‖gueAuxProjection n x‖^2) := by
  unfold gueDoubledOrderedDensity gueOrderedRawDensity
  rw [gueSplit_norm_sq]
  have he : -(n : ℝ)/2*(‖gueRealProjection n x‖^2+‖gueAuxProjection n x‖^2)=
      -(n : ℝ)/2*‖gueRealProjection n x‖^2+(-(n : ℝ)/2*‖gueAuxProjection n x‖^2) := by ring
  rw [he, Real.exp_add]
  simp only [gueRealProjection]
  ring

end
end GinibrePoincare

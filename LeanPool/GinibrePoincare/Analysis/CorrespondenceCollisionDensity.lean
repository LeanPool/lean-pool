/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCollisionDensity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCollisionVolume

/-!
# Correspondence collision density

Part of the weak Sobolev domains and collision capacity development of the
Ginibre Poincaré formalization.

Main results: `correspondenceCollision_density_bound_compact`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

/-- The genuine density after removing one squared collision factor. -/
def correspondenceCollisionDensityRemainder {n : ℕ} (p : VandermondePair n)
    (z : Configuration n) : ℝ :=
  (((n : ℝ) / Real.pi) ^ n) * gaussianWeight n z *
    ∏ q ∈ Finset.univ.erase p, Complex.normSq (vandermondeFactor q.val.1 q.val.2 z)

theorem correspondenceCollision_density_factor {n : ℕ} (p : VandermondePair n)
    (z : Configuration n) :
    ginibreLebesgueDensityReal n z = ‖z p.val.1 - z p.val.2‖ ^ 2 *
      correspondenceCollisionDensityRemainder p z := by
  classical
  unfold ginibreLebesgueDensityReal correspondenceCollisionDensityRemainder vandermondeWeight
  rw [vandermonde_eq_prod_pair]
  simp only [map_prod]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun q : VandermondePair n => Complex.normSq (vandermondeFactor q.val.1 q.val.2 z))
    (Finset.mem_univ p)]
  simp only [vandermondeFactor, Complex.normSq_eq_norm_sq, norm_sub_rev]
  ring

theorem correspondenceCollision_density_bound_compact {n : ℕ} (p : VandermondePair n)
    (K : Set (Configuration n)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K,
      ginibreLebesgueDensityReal n z ≤ C * ‖z p.val.1 - z p.val.2‖ ^ 2 := by
  classical
  have hg : Continuous (gaussianWeight n) := by
    unfold gaussianWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul contDiff_configurationNormSq.continuous)
  have hr : Continuous (correspondenceCollisionDensityRemainder p) := by
    unfold correspondenceCollisionDensityRemainder
    apply (continuous_const.mul hg).mul
    apply continuous_finsetProd
    intro q hq
    unfold vandermondeFactor
    fun_prop
  obtain ⟨C, hC⟩ := hK.bddAbove_image hr.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  rw [correspondenceCollision_density_factor]
  calc
    _ ≤ ‖z p.val.1 - z p.val.2‖ ^ 2 * max C 0 :=
      mul_le_mul_of_nonneg_left ((hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)) (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end GinibrePoincare


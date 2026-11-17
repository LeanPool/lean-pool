/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MagnitudeNullSets.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MagnitudeGradient

/-!
# Magnitude Null Sets
-/


@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem ginibre_coordinates_ne_zero_ae (n : ℕ) (hn : 0 < n) :
    ∀ᵐ z ∂ginibreMeasure n, ∀ i, z i ≠ 0 := by
  apply (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n).ae_le
  change ∀ᵐ z ∂complexGaussianMeasure n, ∀ i, z i ≠ 0
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  have hs : (complexCoordinateGaussianProbability n : Measure ℂ) {0} = 0 := by
    rw [complexCoordinateGaussianMeasure_eq_withDensity hn]
    exact measure_singleton _
  simpa only [Set.preimage, Set.mem_singleton_iff, not_not] using
    Measure.pi_eval_preimage_null (fun _ : Fin n => (complexCoordinateGaussianProbability n :
      Measure ℂ)) (i := i) hs

/-- Euclidean magnitude of a complex block (the domain carries its usual sup norm). -/
def gaussianBlockMagnitude (k : ℕ) (x : Configuration k) : ℝ :=
  Real.sqrt (configurationNormSq x)

def blockMagnitudes (n : ℕ) (x : GaussianRadialBlocks n) : Fin n → ℝ :=
  fun i => gaussianBlockMagnitude (i.val + 1) (x i)

theorem continuous_blockMagnitudes (n : ℕ) : Continuous (blockMagnitudes n) := by
  unfold blockMagnitudes gaussianBlockMagnitude configurationNormSq
  fun_prop

theorem gammaMagnitudes_blockRadii (n : ℕ) (hn : 0 < n) (x : GaussianRadialBlocks n) :
    gammaMagnitudes n (gaussianBlockRadii n x) = blockMagnitudes n x := by
  ext i
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [gammaMagnitudes, gaussianBlockRadii, gaussianBlockRadius, blockMagnitudes,
    gaussianBlockMagnitude, hnR]

theorem blockMagnitudes_pos_ae (n : ℕ) (hn : 0 < n) :
    ∀ᵐ x ∂gaussianRadialBlockMeasure n, ∀ i, 0 < blockMagnitudes n x i := by
  rw [ae_all_iff]
  intro i
  have ha : ∀ᵐ r ∂(gaussianBlockMeasure n (i.val + 1)).map
      (gaussianBlockRadius n (i.val + 1)), r ≠ 0 := by
    rw [gaussianBlockRadius_gamma n _ hn (Nat.succ_pos _)]
    rw [ae_iff]
    simp only [not_not]
    change ProbabilityTheory.gammaMeasure _ _ {0} = 0
    unfold ProbabilityTheory.gammaMeasure
    exact measure_singleton _
  have hb := (ae_map_iff (continuous_gaussianBlockRadius n _).measurable.aemeasurable
    ((measurableSet_singleton (0 : ℝ)).compl)).mp ha
  have : ∀ j : Fin n, SigmaFinite (gaussianBlockMeasure n (j.val + 1)) :=
    fun j => inferInstance
  have hc := (Measure.quasiMeasurePreserving_eval
    (fun i : Fin n => gaussianBlockMeasure n (i.val + 1)) i).ae hb
  filter_upwards [hc] with x hx
  apply Real.sqrt_pos.mpr
  apply lt_of_le_of_ne (configurationNormSq_nonneg (x i))
  intro hz
  apply hx
  simp [gaussianBlockRadius, hz.symm]

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorCenterEigenvectors.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityFullGenerator
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupEigenvectors

/-!
# Ginibre full generator center eigenvectors

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreFullEvolution_coordinateSum`, `ginibreFullGenerator_coordinateSum_norm_sq`.
-/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped NNReal

theorem ginibreFullGenerator_centerOfMassReal_eigenvector (n : ℕ) (hn : 0 < n) :
    ∃ u : ginibreFullSymmetricValues n,
      (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n] centerOfMassReal ∧
      (ginibreFullSymmetricOfReal n u, (-2 : ℂ) • ginibreFullSymmetricOfReal n u) ∈
        (ginibreFullGenerator n hn).graph := by
  obtain ⟨u, g, hu, hs, hf, heq⟩ := centerOfMassReal_attains_symmetric_weak_poincare n hn
  have hmem : u ∈ ginibreFullSymmetricValues n := fun σ => (hs σ).1
  let U : ginibreFullSymmetricValues n := ⟨u, hmem⟩
  have hm : ginibreL2Mean n u = 0 := by
    unfold ginibreL2Mean
    rw [integral_congr_ae hf]
    have hmap := integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
      Complex.continuous_re.aestronglyMeasurable
    change (∫ z, (coordinateSum z).re ∂ginibreMeasure n) = 0
    rw [← hmap, coordinateSum_ginibre_gaussian n hn]
    exact standardComplexGaussian_real_moments.1
  refine ⟨U, hf, (ginibreEquality_full_generator_iff hn U g hu hs hm).mp ?_⟩
  linarith

theorem ginibreFullGenerator_centerOfMassImag_eigenvector (n : ℕ) (hn : 0 < n) :
    ∃ u : ginibreFullSymmetricValues n,
      (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n] centerOfMassImag ∧
      (ginibreFullSymmetricOfReal n u, (-2 : ℂ) • ginibreFullSymmetricOfReal n u) ∈
        (ginibreFullGenerator n hn).graph := by
  obtain ⟨u, g, hu, hs, hf, heq⟩ := centerOfMassImag_attains_symmetric_weak_poincare n hn
  have hmem : u ∈ ginibreFullSymmetricValues n := fun σ => (hs σ).1
  let U : ginibreFullSymmetricValues n := ⟨u, hmem⟩
  have hm : ginibreL2Mean n u = 0 := by
    unfold ginibreL2Mean
    rw [integral_congr_ae hf]
    have hmap := integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
      Complex.continuous_im.aestronglyMeasurable
    change (∫ z, (coordinateSum z).im ∂ginibreMeasure n) = 0
    rw [← hmap, coordinateSum_ginibre_gaussian n hn]
    exact standardComplexGaussian_imag_moments.1
  refine ⟨U, hf, (ginibreEquality_full_generator_iff hn U g hu hs hm).mp ?_⟩
  linarith

/-- The actual noncompact complex coordinate sum belongs to the full generator
and is a gap eigenfunction. -/
theorem ginibreFullGenerator_coordinateSum_eigenvector (n : ℕ) (hn : 0 < n) :
    ∃ u : ginibreSymmetricL2 n,
      (u.val : Configuration n → ℂ) =ᵐ[ginibreMeasure n] coordinateSum ∧
      (u, (-2 : ℂ) • u) ∈ (ginibreFullGenerator n hn).graph := by
  obtain ⟨ur, hr, hgr⟩ := ginibreFullGenerator_centerOfMassReal_eigenvector n hn
  obtain ⟨ui, hi, hgi⟩ := ginibreFullGenerator_centerOfMassImag_eigenvector n hn
  let r := ginibreFullSymmetricOfReal n ur
  let i := ginibreFullSymmetricOfReal n ui
  let u := r + Complex.I • i
  refine ⟨u, ?_, ?_⟩
  · filter_upwards [ginibreFullComplexOfReal_ae n ur.val, ginibreFullComplexOfReal_ae n ui.val,
      hr, hi, Lp.coeFn_add r.val (Complex.I • i.val),
      Lp.coeFn_smul Complex.I i.val] with z hzr hzi hzre hzim hza hzs
    change (r.val + Complex.I • i.val) z = coordinateSum z
    rw [hza]
    change r.val z + (Complex.I • i.val) z = coordinateSum z
    rw [hzs]
    change r.val z + Complex.I * i.val z = coordinateSum z
    change r.val z = (ur.val z : ℂ) at hzr
    change i.val z = (ui.val z : ℂ) at hzi
    rw [hzr, hzi, hzre, hzim]
    simpa [centerOfMassReal, centerOfMassImag, mul_comm] using Complex.re_add_im (coordinateSum z)
  · have h := (ginibreFullGenerator n hn).graph.add_mem hgr
      ((ginibreFullGenerator n hn).graph.smul_mem Complex.I hgi)
    convert h using 1
    ext <;> simp [u, r, i, smul_add, smul_smul, mul_comm]

/-- The full diffusion acts on the actual coordinate sum by the exact sharp
rate exp(-2t), at every nonnegative time. -/
theorem ginibreFullEvolution_coordinateSum (n : ℕ) (hn : 0 < n) :
    ∃ u : ginibreSymmetricL2 n,
      (u.val : Configuration n → ℂ) =ᵐ[ginibreMeasure n] coordinateSum ∧
      ∀ t : ℝ≥0, ginibreFullEvolution n hn t u = Real.exp (-2 * (t : ℝ)) • u := by
  obtain ⟨u, hu, hg⟩ := ginibreFullGenerator_coordinateSum_eigenvector n hn
  refine ⟨u, hu, ?_⟩
  intro t
  exact resolventCfcEvolution_generator_eigenvector (ginibreFullComplexResolvent n hn)
    (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) t 2 (by norm_num) u hg

/-- Every actual coordinate-sum L² class has unit squared norm; in particular
its exact slow mode is nonzero. -/
theorem ginibreFullGenerator_coordinateSum_norm_sq (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n)
    (hu : (u.val : Configuration n → ℂ) =ᵐ[ginibreMeasure n] coordinateSum) :
    ‖u‖ ^ 2 = 1 := by
  change ‖u.val‖ ^ 2 = 1
  rw [← integral_norm_sq_eq_L2_norm_sq]
  have hae : (fun z => ‖u.val z‖ ^ 2) =ᵐ[ginibreMeasure n]
      fun z => Complex.normSq (coordinateSum z) := by
    filter_upwards [hu] with z hz
    rw [hz, Complex.sq_norm]
  rw [integral_congr_ae hae]
  have hmap := integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
    Complex.continuous_normSq.aestronglyMeasurable
  rw [← hmap, coordinateSum_ginibre_gaussian n hn]
  simpa [standardComplexGaussianMeasure] using integral_normSq_pow_coordinate 1 1 (by norm_num)

end GinibrePoincare

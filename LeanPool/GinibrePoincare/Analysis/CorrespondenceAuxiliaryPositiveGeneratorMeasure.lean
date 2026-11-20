/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryPositiveGeneratorMeasure.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryVectorSemigroupRepresentation

/-!
# Correspondence auxiliary positive generator measure

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreNegativeGeneratorVectorSpectralMeasure_mass`,
`ginibreNegativeGeneratorVectorSpectralMeasure_support`,
`ginibreNegativeGeneratorVectorSpectralMeasure_semigroup`.
-/

@[expose] public section
open MeasureTheory Set
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The paper's nonnegative `-Lₙ` spectral coordinate. -/
def ginibreNegativeGeneratorVectorSpectralMeasure (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : Measure ℝ :=
  (ginibreGeneratorVectorSpectralMeasure n hn u).map (fun x : ℝ => -x)

theorem ginibreNegativeGeneratorVectorSpectralMeasure_mass (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreNegativeGeneratorVectorSpectralMeasure n hn u univ = ENNReal.ofReal (‖u‖^2) := by
  unfold ginibreNegativeGeneratorVectorSpectralMeasure
  rw [Measure.map_apply measurable_neg MeasurableSet.univ]
  simpa using ginibreGeneratorVectorSpectralMeasure_mass n hn u

theorem ginibreNegativeGeneratorVectorSpectralMeasure_support (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreNegativeGeneratorVectorSpectralMeasure n hn u ({0} ∪ Ici (2 : ℝ))ᶜ = 0 := by
  unfold ginibreNegativeGeneratorVectorSpectralMeasure
  rw [Measure.map_apply measurable_neg
    ((measurableSet_singleton 0).union measurableSet_Ici).compl]
  have he : (fun x : ℝ => -x) ⁻¹' ({0} ∪ Ici (2 : ℝ))ᶜ =
      ({0} ∪ Iic (-2 : ℝ))ᶜ := by
    ext x
    have hneg : (2 : ℝ) ≤ -x ↔ x ≤ -2 := by constructor <;> intro h <;> linarith
    simp only [mem_preimage, mem_compl_iff, mem_union, mem_singleton_iff, mem_Ici, mem_Iic,
      neg_eq_zero, hneg]
  rw [he]
  exact ginibreGeneratorVectorSpectralMeasure_support n hn u

theorem ginibreNegativeGeneratorVectorSpectralMeasure_semigroup (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) (t : ℝ≥0) :
    (∫ lam : ℝ, Real.exp (-(t : ℝ)*lam)
      ∂ginibreNegativeGeneratorVectorSpectralMeasure n hn u) =
      (inner ℂ u (ginibreFullEvolution n hn t u)).re := by
  unfold ginibreNegativeGeneratorVectorSpectralMeasure
  rw [integral_map measurable_neg.aemeasurable
    (show AEStronglyMeasurable (fun lam : ℝ => Real.exp (-(t : ℝ)*lam))
      (Measure.map (fun x : ℝ => -x) (ginibreGeneratorVectorSpectralMeasure n hn u)) from
      (by fun_prop : Continuous (fun lam : ℝ => Real.exp (-(t : ℝ)*lam))).aestronglyMeasurable)]
  simp only [neg_mul_neg]
  exact ginibreGeneratorVectorSpectralMeasure_semigroup n hn u t

end
end GinibrePoincare

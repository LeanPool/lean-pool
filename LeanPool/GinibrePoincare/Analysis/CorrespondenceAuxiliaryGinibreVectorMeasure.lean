/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryGinibreVectorMeasure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryVectorSpectralMeasure
public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralSupport

/-!
# Correspondence auxiliary Ginibre vector measure

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreResolventVectorSpectralMeasure_mass`,
`ginibreResolventVectorSpectralMeasure_support`.
-/

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- The actual scalar spectral measure of every vector for the concrete
Ginibre symmetric complex resolvent, on the real spectral line. -/
def ginibreResolventVectorSpectralMeasure (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : Measure ℝ :=
  (vectorSpectralMeasure (ginibreFullComplexResolvent n hn)
    (ginibreFullComplexResolvent_isSelfAdjoint n hn) u).map Subtype.val

theorem ginibreResolventVectorSpectralMeasure_mass (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreResolventVectorSpectralMeasure n hn u univ = ENNReal.ofReal (‖u‖^2) := by
  unfold ginibreResolventVectorSpectralMeasure
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp only [preimage_univ]
  exact vectorSpectralMeasure_mass _ _ _

/-- Literal vector-measure support, rather than only operator graph-spectrum
support: no vector has scalar resolvent spectral mass outside [0,1/3]∪{1}. -/
theorem ginibreResolventVectorSpectralMeasure_support (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreResolventVectorSpectralMeasure n hn u (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ = 0 := by
  unfold ginibreResolventVectorSpectralMeasure
  rw [Measure.map_apply measurable_subtype_coe
    (measurableSet_Icc.union (measurableSet_singleton 1)).compl]
  have he : (Subtype.val : spectrum ℝ (ginibreFullComplexResolvent n hn) → ℝ) ⁻¹'
      (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ = ∅ := by
    ext r
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact spectral_ginibre_resolvent_spectrum_support n hn r.property
  exact measure_mono_null he.le measure_empty

end
end GinibrePoincare

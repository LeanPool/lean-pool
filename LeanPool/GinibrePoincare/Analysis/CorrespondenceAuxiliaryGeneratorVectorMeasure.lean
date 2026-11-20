/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryGeneratorVectorMeasure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryVectorZeroAtom

/-!
# Correspondence auxiliary generator vector measure

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreGeneratorVectorSpectralMeasure_mass`,
`ginibreGeneratorVectorSpectralMeasure_support`.
-/

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- The inverse-resolvent transformation from the positive resolvent spectral
coordinate to the concrete speed-n generator spectral coordinate. -/
def inverseResolventSpectralCoordinate (r : ℝ) : ℝ := 1-r⁻¹

theorem measurable_inverseResolventSpectralCoordinate :
    Measurable inverseResolventSpectralCoordinate := measurable_const.sub measurable_inv

/-- Literal vector spectral measure of the concrete symmetric Ginibre
full generator, obtained from its internally constructed resolvent vector
measure. The totalized value at r=0 is immaterial by the proved zero-atom lemma. -/
def ginibreGeneratorVectorSpectralMeasure (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : Measure ℝ :=
  (ginibreResolventVectorSpectralMeasure n hn u).map inverseResolventSpectralCoordinate

theorem ginibreGeneratorVectorSpectralMeasure_mass (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreGeneratorVectorSpectralMeasure n hn u univ = ENNReal.ofReal (‖u‖^2) := by
  unfold ginibreGeneratorVectorSpectralMeasure
  rw [Measure.map_apply measurable_inverseResolventSpectralCoordinate MeasurableSet.univ]
  simp only [preimage_univ]
  exact ginibreResolventVectorSpectralMeasure_mass n hn u

/-- Section 3's literal scalar vector spectral support: every vector measure
is concentrated on {0}∪(−∞,−2], with no supplied spectral measure hypothesis. -/
theorem ginibreGeneratorVectorSpectralMeasure_support (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreGeneratorVectorSpectralMeasure n hn u ({0} ∪ Iic (-2 : ℝ))ᶜ = 0 := by
  unfold ginibreGeneratorVectorSpectralMeasure
  rw [Measure.map_apply measurable_inverseResolventSpectralCoordinate
    ((measurableSet_singleton 0).union measurableSet_Iic).compl]
  let μ := ginibreResolventVectorSpectralMeasure n hn u
  have hsub : inverseResolventSpectralCoordinate ⁻¹' ({0} ∪ Iic (-2 : ℝ))ᶜ ⊆
      {0} ∪ (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ := by
    intro r hr
    by_cases hz : r = 0
    · exact Or.inl hz
    · right
      intro hs
      apply hr
      rcases hs with hs | hs
      · right
        have hpos : 0 < r := lt_of_le_of_ne hs.1 (Ne.symm hz)
        have hi : 3 ≤ r⁻¹ := (by simpa using one_div_le_one_div_of_le hpos hs.2)
        change 1-r⁻¹ ≤ -2
        linarith
      · left
        change r=1 at hs
        simp [inverseResolventSpectralCoordinate, hs]
  apply le_antisymm _ bot_le
  calc
    _ ≤ μ ({0} ∪ (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ) := measure_mono hsub
    _ ≤ μ {0} + μ (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ := measure_union_le _ _
    _ = 0 := by rw [ginibreResolventVectorSpectralMeasure_zero_atom,
      ginibreResolventVectorSpectralMeasure_support, add_zero]

end
end GinibrePoincare

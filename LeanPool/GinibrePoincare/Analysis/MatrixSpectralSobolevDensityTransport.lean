/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevDensityTransport.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevCoordinates
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevDensity

/-! # Actual Gaussian density and probability transport through entry coordinates

Entry reindexing preserves ordinary volume. The general with-density transport
lemma then shows it preserves the Gaussian laws as well, because the density
on entry coordinates is exactly the pulled-back matrix density. Probability,
strict positivity, continuity, and a finite upper bound for that density are
established here for the later weak-domain approximation argument.
-/

@[expose] public section
open MeasureTheory Matrix Filter
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

theorem measurePreserving_actual_withDensity
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (hf : MeasurePreserving f μ ν)
    (ρ : Y → ℝ≥0∞) (hρ : Measurable ρ) :
    MeasurePreserving f (μ.withDensity (ρ ∘ f)) (ν.withDensity ρ) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs,
    withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator (hf.measurable hs), ← lintegral_indicator hs]
  convert hf.lintegral_comp (hρ.indicator hs) using 1
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ s <;> simp [hx, Function.comp_def]

/-- The Ginibre matrix Gaussian measure in entry coordinates: Lebesgue measure on
configurations with density `matrixGaussianDensity` of the relabelled matrix. -/
def matrixEntryGaussianMeasure {n m : ℕ} (e : Fin m ≃ Fin n × Fin n) :
    Measure (Configuration m) :=
  (volume : Measure (Configuration m)).withDensity
    (fun z => matrixGaussianDensity n (Matrix.of (matrixComplexEntryEquiv e z)))

theorem matrixComplexEntryEquiv_gaussian_preserving {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) :
    MeasurePreserving (matrixComplexEntryEquiv e) (matrixEntryGaussianMeasure e)
      (matrixGaussianMeasure n) := by
  rw [matrixGaussianMeasure_eq_withDensity hn]
  exact measurePreserving_actual_withDensity volume volume (matrixComplexEntryEquiv e)
    (matrixComplexEntryEquiv_volume_preserving e) (matrixGaussianDensity n)
    (measurable_matrixGaussianDensity n)

theorem matrixEntryGaussianMeasure_isProbability {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) : IsProbabilityMeasure (matrixEntryGaussianMeasure e) := by
  constructor
  have he := (matrixComplexEntryEquiv_gaussian_preserving hn e).measure_preimage
    ((MeasurableSet.univ : MeasurableSet (Set.univ : Set (MatrixRealSpace n))).nullMeasurableSet)
  rw [Set.preimage_univ] at he
  exact he.trans (measure_univ (μ := matrixGaussianMeasure n))

/-- The real-valued Ginibre matrix density read in entry coordinates. -/
def matrixEntryGaussianDensityReal {n m : ℕ} (e : Fin m ≃ Fin n × Fin n)
    (z : Configuration m) : ℝ :=
  matrixGaussianDensityReal n (Matrix.of (matrixComplexEntryEquiv e z))

theorem matrixEntryGaussianDensityReal_continuous {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) : Continuous (matrixEntryGaussianDensityReal e) := by
  unfold matrixEntryGaussianDensityReal matrixGaussianDensityReal
  simp only [matrixHSNormSq_eq_sum]
  fun_prop

theorem matrixEntryGaussianDensityReal_pos {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (z : Configuration m) :
    0 < matrixEntryGaussianDensityReal e z :=
  matrixGaussianDensityReal_pos n hn _

theorem matrixEntryGaussianMeasure_eq_real_density {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) : matrixEntryGaussianMeasure e =
    (volume : Measure (Configuration m)).withDensity
      (fun z => ENNReal.ofReal (matrixEntryGaussianDensityReal e z)) := rfl

theorem matrixEntryGaussianMeasure_le_finite_smul_volume {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ matrixEntryGaussianMeasure e ≤
      c • (volume : Measure (Configuration m)) := by
  refine ⟨ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n)), ENNReal.ofReal_ne_top, ?_⟩
  rw [matrixEntryGaussianMeasure, ← withDensity_const]
  exact withDensity_mono (Eventually.of_forall fun z => matrixGaussianDensity_le_const n _)

end
end GinibrePoincare

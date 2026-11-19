/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianInitialMeasureIdentification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianCoordinateLaw
public import LeanPool.GinibrePoincare.Concrete.MeasureModel
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Ginibre Hamiltonian initial measure identification

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibre_completion_weighted_map`,
`ginibreGaussian_completed_coordinates_vandermonde_law`,
`ginibre_completed_initial_noise_initial_law`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

theorem ginibre_map_density_composition {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) (f : A → E) (hf : Measurable f) (w : E → ENNReal) (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hf hs),← lintegral_indicator hs]
  have he : (f ⁻¹' s).indicator (w ∘ f) = (s.indicator w) ∘ f := by
    funext x
    by_cases hx : f x ∈ s <;> simp [hx]
  rw [he]
  exact (lintegral_map (hw.indicator hs) hf).symm

theorem ginibre_map_completion {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) (f : A → E) (hf : Measurable f) :
    μ.completion.map (fun x : NullMeasurableSpace A μ => f x) = μ.map f := by
  ext s hs
  rw [Measure.map_apply hf.nullMeasurable.measurable' hs, Measure.map_apply hf hs]
  rfl

theorem ginibre_lintegral_completion {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → ENNReal) (hg : Measurable g) :
    (∫⁻ x : NullMeasurableSpace A μ, g x ∂μ.completion) = ∫⁻ x, g x ∂μ := by
  have hh := lintegral_map hg
    (measurable_id.nullMeasurable.measurable' : Measurable (fun x : NullMeasurableSpace A μ => (id :
        A → A) x))
    (μ := μ.completion)
  rw [ginibre_map_completion μ id measurable_id, Measure.map_id] at hh
  exact hh.symm

theorem ginibre_completion_weighted_map {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) (f : A → E) (hf : Measurable f) (w : A → ENNReal) (hw : Measurable w) :
    (μ.completion.withDensity (fun x : NullMeasurableSpace A μ => w x)).map
      (fun x : NullMeasurableSpace A μ => f x) = (μ.withDensity w).map f := by
  ext s hs
  rw [Measure.map_apply hf.nullMeasurable.measurable' hs, Measure.map_apply hf hs,
    withDensity_apply (fun x : NullMeasurableSpace A μ => w x) (hf.nullMeasurable.measurable' hs),
    withDensity_apply w (hf hs)]
  have hl := lintegral_indicator (μ := μ.completion) (f := fun x : NullMeasurableSpace A μ => w x)
    (hf.nullMeasurable.measurable' hs)
  have hr := lintegral_indicator (μ := μ) (f := w) (hf hs)
  exact hl.symm.trans ((ginibre_lintegral_completion μ ((f ⁻¹' s).indicator w)
    (hw.indicator (hf hs))).trans hr)

/-- The actual completed Gaussian-coordinate law weighted by the genuine
Vandermonde pushes forward to the unnormalized existing Ginibre measure. -/
theorem ginibreGaussian_completed_coordinates_vandermonde_law {n : ℕ} (hn : 0 < n) :
    let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
    (γ.completion.withDensity (fun x : NullMeasurableSpace ((Fin n × Fin 2) → ℝ) γ =>
      vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x))).map
      (fun x : NullMeasurableSpace ((Fin n × Fin 2) → ℝ) γ => ginibreHamiltonianOUCoordinateAssembly
          n x) =
      rawGinibreMeasure n := by
  dsimp only
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  have hA : Measurable (ginibreHamiltonianOUCoordinateAssembly n) :=
    (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable
  have hw : Measurable (@vandermondeDensity n) :=
    ENNReal.measurable_ofReal.comp (contDiff_vandermondeWeight n).continuous.measurable
  let f : NullMeasurableSpace ((Fin n × Fin 2) → ℝ) γ → Configuration n :=
    fun x => ginibreHamiltonianOUCoordinateAssembly n x
  change (γ.completion.withDensity (vandermondeDensity ∘ f)).map f = _
  rw [ginibre_map_density_composition γ.completion f hA.nullMeasurable.measurable' _ hw]
  change (γ.completion.map (fun x : NullMeasurableSpace ((Fin n × Fin 2) → ℝ) γ =>
    ginibreHamiltonianOUCoordinateAssembly n x)).withDensity vandermondeDensity = _
  rw [ginibre_map_completion γ _ hA, ginibreGaussian_coordinate_assembly_law hn]
  rfl

theorem ginibreGaussian_completed_initial_noise_vandermonde_law {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (P : Measure Ω) [IsProbabilityMeasure P] :
    let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
    let ν := γ.prod P
    (ν.completion.withDensity (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν =>
      vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x.1))).map
      (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν =>
          ginibreHamiltonianOUCoordinateAssembly n x.1) =
      rawGinibreMeasure n := by
  dsimp only
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let ν := γ.prod P
  let f : (((Fin n × Fin 2) → ℝ) × Ω) → Configuration n := fun x =>
      ginibreHamiltonianOUCoordinateAssembly n x.1
  have hA : Measurable (ginibreHamiltonianOUCoordinateAssembly n) :=
    (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable
  have hf : Measurable f := hA.comp measurable_fst
  have hw : Measurable (@vandermondeDensity n) :=
    ENNReal.measurable_ofReal.comp (contDiff_vandermondeWeight n).continuous.measurable
  let fc : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν → Configuration n := f
  change (ν.completion.withDensity (vandermondeDensity ∘ fc)).map fc = _
  rw [ginibre_map_density_composition ν.completion fc hf.nullMeasurable.measurable' _ hw]
  change (ν.completion.map (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν => f
      x)).withDensity vandermondeDensity = _
  rw [ginibre_map_completion ν f hf]
  change ((γ.prod P).map ((ginibreHamiltonianOUCoordinateAssembly n) ∘ Prod.fst)).withDensity
      vandermondeDensity = _
  rw [← Measure.map_map hA measurable_fst, Measure.map_fst_prod, measure_univ, one_smul,
    ginibreGaussian_coordinate_assembly_law hn]
  rfl

/-- Exact existing normalized Ginibre initial law on the completed
Gaussian-initial/noise product space. -/
theorem ginibre_completed_initial_noise_initial_law {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (P : Measure Ω) [IsProbabilityMeasure P] :
    let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
    let ν := γ.prod P
    ((ginibreNormalizingMass n)⁻¹ • ν.completion.withDensity
      (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν =>
        vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x.1))).map
      (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν =>
          ginibreHamiltonianOUCoordinateAssembly n x.1) =
      ginibreMeasure n := by
  dsimp only
  have hA : Measurable (ginibreHamiltonianOUCoordinateAssembly n) :=
    (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable
  have hf : Measurable (fun x : (((Fin n × Fin 2) → ℝ) × Ω) =>
      ginibreHamiltonianOUCoordinateAssembly n x.1) := hA.comp measurable_fst
  rw [Measure.map_smul, ginibreGaussian_completed_initial_noise_vandermonde_law hn P]
  · rfl
  · exact hf.nullMeasurable.measurable'.aemeasurable

end
end GinibrePoincare

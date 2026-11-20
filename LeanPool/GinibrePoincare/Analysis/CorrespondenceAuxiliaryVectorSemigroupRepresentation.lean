/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryVectorSemigroupRepresentation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryGeneratorVectorMeasure

/-!
# Correspondence auxiliary vector semigroup representation

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreGeneratorVectorSpectralMeasure_semigroup`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped Topology CompactlySupported NNReal
namespace GinibrePoincare
noncomputable section

/-- The generic spectral computation behind the semigroup representation: for a self-adjoint
resolvent with spectrum in `[0, 1]` and dense range, the transported vector spectral measure
integrates exponentials to the matrix coefficients of the CFC evolution. -/
private theorem vectorSpectralMeasure_exp_integral {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (hDense : DenseRange R) (u : H) (t : ℝ≥0) :
    (∫ lam : ℝ, Real.exp ((t : ℝ) * lam) ∂(((vectorSpectralMeasure R hR u).map Subtype.val).map
      inverseResolventSpectralCoordinate)) = (inner ℂ u (resolventCfcEvolution R t u)).re := by
  let μ := vectorSpectralMeasure R hR u
  have hmult : (∫ r : spectrum ℝ R, resolventEvolutionMultiplier (t : ℝ) r.val ∂μ) =
      (inner ℂ u (resolventCfcEvolution R t u)).re := by
    let φ : C_c(spectrum ℝ R, ℝ) :=
      ⟨⟨fun r => resolventEvolutionMultiplier (t : ℝ) r.val,
        (resolventEvolutionMultiplier_continuous _).comp continuous_subtype_val⟩,
        HasCompactSupport.of_compactSpace _⟩
    have h := integral_vectorSpectralMeasure R hR u φ
    have hc : (cfcHom hR) φ.toContinuousMap = resolventCfcEvolution R t := by
      unfold resolventCfcEvolution
      exact (cfc_apply _ R hR (resolventEvolutionMultiplier_continuous _).continuousOn).symm
    rw [hc] at h
    exact h
  rw [Measure.map_map measurable_inverseResolventSpectralCoordinate measurable_subtype_coe]
  have hf : AEStronglyMeasurable (fun lam : ℝ => Real.exp ((t : ℝ)*lam))
      (Measure.map (inverseResolventSpectralCoordinate ∘ Subtype.val) μ) :=
    (show Continuous (fun lam : ℝ => Real.exp ((t : ℝ)*lam)) by fun_prop).aestronglyMeasurable
  rw [integral_map (measurable_inverseResolventSpectralCoordinate.comp
      measurable_subtype_coe).aemeasurable hf]
  change (∫ r : spectrum ℝ R, Real.exp ((t : ℝ)*inverseResolventSpectralCoordinate r.val) ∂μ) = _
  rw [← hmult]
  apply integral_congr_ae
  by_cases ht : t = 0
  · subst t
    exact ae_of_all _ (fun r => by simp)
  · have htpos : 0 < (t : ℝ) := by
      exact_mod_cast (lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from zero_le) (Ne.symm ht))
    have hzero : ∀ᵐ r : spectrum ℝ R ∂μ, r.val ≠ 0 := by
      apply ae_iff.mpr
      simpa only [not_not] using vectorSpectralMeasure_zero_atom R hR hSpec hDense u
    filter_upwards [hzero] with r hr
    have hnonneg := (hSpec r.property).1
    have hrpos : 0 < r.val := lt_of_le_of_ne hnonneg (Ne.symm hr)
    rw [resolventEvolutionMultiplier_positive_formula htpos hrpos]
    congr 1
    unfold inverseResolventSpectralCoordinate
    ring

/-- Every vector's actual generator spectral measure represents its concrete
full symmetric diffusion semigroup. This ties the Riesz–Markov measure and
inverse-resolvent transformation to the already identified generator/evolution. -/
theorem ginibreGeneratorVectorSpectralMeasure_semigroup (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) (t : ℝ≥0) :
    (∫ lam : ℝ, Real.exp ((t : ℝ)*lam) ∂ginibreGeneratorVectorSpectralMeasure n hn u) =
      (inner ℂ u (ginibreFullEvolution n hn t u)).re := by
  unfold ginibreGeneratorVectorSpectralMeasure ginibreResolventVectorSpectralMeasure
  exact vectorSpectralMeasure_exp_integral _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_spectrum n hn) (ginibreFullComplexResolvent_denseRange n hn) u t

end
end GinibrePoincare

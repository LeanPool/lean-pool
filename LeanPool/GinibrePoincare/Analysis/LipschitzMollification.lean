/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/LipschitzMollification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianLSIProduct
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Lipschitz Mollification
-/


@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution NNReal
namespace GinibrePoincare
noncomputable section

/-- Mollification differentiates a Lipschitz observable by averaging its actual
almost-everywhere Fréchet derivative. Rademacher supplies the differentiability. -/
theorem fderiv_normed_convolution_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (η : Measure E) [η.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))
    (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E) :
    fderiv ℝ (φ.normed η ⋆[lsmul ℝ ℝ, η] f) x₀ =
      (φ.normed η ⋆[lsmul ℝ ℝ, η] fderiv ℝ f) x₀ := by
  let F : E → E → ℝ := fun x a => φ.normed η a • f (x - a)
  let G : E → E →L[ℝ] ℝ := fun a => φ.normed η a • fderiv ℝ f (x₀ - a)
  have hφc : Continuous (φ.normed η) := (φ.contDiff_normed (n := ⊤)).continuous
  have hφi : Integrable (φ.normed η) η :=
    hφc.integrable_of_hasCompactSupport φ.hasCompactSupport_normed
  have hmeas (x : E) : AEStronglyMeasurable (F x) η := by
    exact (hφc.smul (hf.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hint : Integrable (F x₀) η :=
    (hφc.smul (hf.continuous.comp (continuous_const.sub
      continuous_id))).integrable_of_hasCompactSupport
      φ.hasCompactSupport_normed.smul_right
  have hgmeas : AEStronglyMeasurable G η := by
    apply Measurable.aestronglyMeasurable
    exact hφc.measurable.smul ((measurable_fderiv ℝ f).comp (by fun_prop))
  have hdiff : ∀ᵐ a ∂η, HasFDerivAt (F · a) (G a) x₀ := by
    have ha := (Measure.measurePreserving_sub_left η x₀).quasiMeasurePreserving.ae
      (hf.ae_differentiableAt (μ := η))
    filter_upwards [ha] with a ha
    have hh := ((ha.hasFDerivAt.comp x₀ ((hasFDerivAt_id x₀).sub_const a)).const_smul (φ.normed η
      a))
    convert! hh using 1
  have hlip : ∀ᵐ a ∂η, ∀ x ∈ (Set.univ : Set E),
      ‖F x a - F x₀ a‖ ≤ (φ.normed η a * (K : ℝ)) * ‖x - x₀‖ := by
    apply Eventually.of_forall
    intro a x hx
    have h := hf.dist_le_mul (x - a) (x₀ - a)
    rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right] at h
    simp only [F, smul_eq_mul, ← mul_sub, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (φ.nonneg_normed a)]
    exact (mul_le_mul_of_nonneg_left h (φ.nonneg_normed a)).trans_eq (by ring)
  have hd := (hasFDerivAt_integral_of_dominated_loc_of_lip' (F := F) (F' := G)
    (bound := fun a => φ.normed η a * (K : ℝ)) Filter.univ_mem
    (fun x hx => hmeas x) hint hgmeas hlip (hφi.mul_const _) hdiff).2.fderiv
  change fderiv ℝ (fun x => ∫ a, φ.normed η a • f (x - a) ∂η) x₀ =
    ∫ a, φ.normed η a • fderiv ℝ f (x₀ - a) ∂η
  exact hd

/-- A concrete sequence of compact smooth kernels with radii tending to zero. -/
def lsiMollifier (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) : ContDiffBump (0 : E) :=
  ⟨(1 / (n + 1 : ℝ)) / 2, 1 / (n + 1 : ℝ), by positivity,
    by
      have h : 0 < 1 / (n + 1 : ℝ) := by positivity
      exact half_lt_self h⟩

theorem lsiMollifier_radius_tendsto (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Tendsto (fun n => (lsiMollifier E n).rOut) atTop (𝓝 0) := by
  simpa [lsiMollifier] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The genuine derivatives of smooth mollifications converge almost everywhere
to the actual Fréchet derivative of a Lipschitz observable. -/
theorem ae_fderiv_mollification_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (η : Measure E) [η.IsAddHaarMeasure]
    (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ x ∂η, Tendsto
      (fun n => fderiv ℝ ((lsiMollifier E n).normed η ⋆[lsmul ℝ ℝ, η] f) x)
      atTop (𝓝 (fderiv ℝ f x)) := by
  have hlocal : LocallyIntegrable (fderiv ℝ f) η :=
    (continuous_const : Continuous (fun _ : E => (K : ℝ))).locallyIntegrable.mono
      (measurable_fderiv ℝ f).aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa using norm_fderiv_le_of_lipschitz ℝ hf))
  have ht := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := lsiMollifier E) (K := 2) (lsiMollifier_radius_tendsto E)
    (Eventually.of_forall (fun n => by dsimp [lsiMollifier]; linarith)) hlocal
  simpa only [fderiv_normed_convolution_lipschitz η _ f hf] using ht

/-- Mollification preserves the uniform derivative bound of a Lipschitz function. -/
theorem norm_fderiv_mollification_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (η : Measure E) [η.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))
    (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) (x : E) :
    ‖fderiv ℝ (φ.normed η ⋆[lsmul ℝ ℝ, η] f) x‖ ≤ (K : ℝ) := by
  rw [fderiv_normed_convolution_lipschitz η φ f hf]
  change ‖∫ a, φ.normed η a • fderiv ℝ f (x - a) ∂η‖ ≤ (K : ℝ)
  have hφi : Integrable (φ.normed η) η :=
    (φ.contDiff_normed (n := ⊤)).continuous.integrable_of_hasCompactSupport
      φ.hasCompactSupport_normed
  calc
    _ ≤ ∫ a, ‖φ.normed η a • fderiv ℝ f (x - a)‖ ∂η := norm_integral_le_integral_norm _
    _ ≤ ∫ a, φ.normed η a * (K : ℝ) ∂η := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun a => norm_nonneg _))
        (hφi.mul_const _)
      apply Eventually.of_forall
      intro a
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed a)]
      exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hf) (φ.nonneg_normed a)
    _ = (K : ℝ) := by rw [integral_mul_const, φ.integral_normed, one_mul]

end
end GinibrePoincare

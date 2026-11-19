/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CompactLipschitzLSIExtension.lean.
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

public import LeanPool.GinibrePoincare.Analysis.LipschitzMollification

/-!
# Compact lipschitz LSI extension

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `compactLipschitz_lsi_of_C1`.
-/

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution NNReal
namespace GinibrePoincare
noncomputable section

private theorem norm_mollification_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (η : Measure E) [η.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))
    (f : E → ℝ) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (x : E) :
    ‖(φ.normed η ⋆[lsmul ℝ ℝ, η] f) x‖ ≤ C := by
  change ‖∫ a, φ.normed η a • f (x - a) ∂η‖ ≤ C
  have hφi : Integrable (φ.normed η) η :=
    (φ.contDiff_normed (n := ⊤)).continuous.integrable_of_hasCompactSupport
        φ.hasCompactSupport_normed
  calc
    _ ≤ ∫ a, ‖φ.normed η a • f (x - a)‖ ∂η := norm_integral_le_integral_norm _
    _ ≤ ∫ a, φ.normed η a * C ∂η := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun a => norm_nonneg _)) (hφi.mul_const
          _)
      apply Eventually.of_forall
      intro a
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed a)]
      exact mul_le_mul_of_nonneg_left (hb _) (φ.nonneg_normed a)
    _ = C := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- The actual coordinate energy associated to any finite family of directions. -/
def directionalEnergy {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (d : ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, (fderiv ℝ f x (d i)) ^ 2

private theorem directionalEnergy_bound
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (d : ι → E) (f : E → ℝ) (K : ℝ≥0) (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K) (x : E) :
    ‖directionalEnergy d f x‖ ≤ ∑ i, ((K : ℝ) * ‖d i‖) ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  apply Finset.sum_le_sum
  intro i hi
  have hb : |fderiv ℝ f x (d i)| ≤ (K : ℝ) * ‖d i‖ :=
    ((fderiv ℝ f x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _))
  nlinarith [abs_nonneg (fderiv ℝ f x (d i)), sq_abs (fderiv ℝ f x (d i)),
    mul_nonneg K.coe_nonneg (norm_nonneg (d i))]

/-- A smooth compact-core LSI extends to actual compact Lipschitz functions.
Absolute continuity transfers Rademacher and mollifier convergence from Haar
measure. The energy uses the actual Fréchet derivative, not a certificate. -/
theorem compactLipschitz_lsi_of_C1
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (η : Measure E) [η.IsAddHaarMeasure] (μ : Measure E) [IsProbabilityMeasure μ]
    (hac : μ ≪ η) (d : ι → E) (c : ℝ)
    (hcore : ∀ f : E → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      squareEntropy μ f ≤ c * ∫ x, directionalEnergy d f x ∂μ)
    (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    squareEntropy μ f ≤ c * ∫ x, directionalEnergy d f x ∂μ := by
  let F : ℕ → E → ℝ := fun n => (lsiMollifier E n).normed η ⋆[lsmul ℝ ℝ, η] f
  have hF (n : ℕ) : ContDiff ℝ 1 (F n) :=
    (lsiMollifier E n).hasCompactSupport_normed.contDiff_convolution_left _
      (lsiMollifier E n).contDiff_normed hf.continuous.locallyIntegrable
  have hcF (n : ℕ) : HasCompactSupport (F n) :=
    (lsiMollifier E n).hasCompactSupport_normed.convolution _ hc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
  have hFb (n : ℕ) (x : E) : ‖F n x‖ ≤ C := norm_mollification_le η _ f C hC x
  have hFlim (x : E) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      (lsiMollifier_radius_tendsto E) hf.continuous x
  have hdlim : ∀ᵐ x ∂μ, Tendsto (fun n => fderiv ℝ (F n) x) atTop (𝓝 (fderiv ℝ f x)) :=
    hac.ae_le (ae_fderiv_mollification_tendsto η f hf)
  have hDb (n : ℕ) (x : E) : ‖fderiv ℝ (F n) x‖ ≤ K :=
    norm_fderiv_mollification_le η _ f hf x
  have hmass : Tendsto (fun n => ∫ x, F n x ^ 2 ∂μ) atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C ^ 2)
      (fun n => ((hF n).continuous.pow 2).aestronglyMeasurable) (integrable_const _)
    · intro n
      apply Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := hFb n x
      rw [Real.norm_eq_abs] at hb
      change F n x ^ 2 ≤ C ^ 2
      nlinarith [abs_nonneg (F n x), sq_abs (F n x)]
    · exact Eventually.of_forall (fun x => (hFlim x).pow 2)
  have henergy : Tendsto (fun n => ∫ x, directionalEnergy d (F n) x ∂μ)
      atTop (𝓝 (∫ x, directionalEnergy d f x ∂μ)) := by
    have hmeas (n : ℕ) : AEStronglyMeasurable (directionalEnergy d (F n)) μ := by
      apply Continuous.aestronglyMeasurable
      unfold directionalEnergy
      apply continuous_finsetSum
      intro i hi
      exact (((hF n).continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2
    apply tendsto_integral_of_dominated_convergence
      (fun _ => ∑ i, ((K : ℝ) * ‖d i‖) ^ 2) hmeas (integrable_const _)
    · intro n
      exact Eventually.of_forall (directionalEnergy_bound d (F n) K (hDb n))
    · filter_upwards [hdlim] with x hx
      unfold directionalEnergy
      apply tendsto_finsetSum
      intro i hi
      exact (((continuous_id.clm_apply continuous_const).tendsto (fderiv ℝ f x)).comp hx).pow 2
  exact (squareEntropy_le_of_ae_tendsto μ F f _ _
    (fun n => (hF n).continuous.aestronglyMeasurable) hf.continuous.aestronglyMeasurable
    (fun n => (continuous_square_mul_log (hF n).continuous).integrable_of_hasCompactSupport
      (compactSupport_square_mul_log (hcF n)))
    (Eventually.of_forall hFlim) hmass (henergy.const_mul c)
    (fun n => hcore (F n) (hF n) (hcF n))).2

end
end GinibrePoincare

/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import LeanPool.LiebThirring.Analysis.HardyApproximation
/-!
# One-body Coulomb control by Fourier kinetic energy

Squared Schwartz L² norm, in nonnegative extended-integral form.

Every L² state has its Coulomb expectation bounded by its mass plus four times its Fourier
kinetic energy, uniformly in the pole.
-/
public section
open MeasureTheory Filter FourierTransform
open scoped ENNReal NNReal Topology SchwartzMap FourierTransform
namespace LiebThirring
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Squared Schwartz L² norm, in nonnegative extended-integral form. -/
theorem lintegral_schwartz_norm_sq_eq_enorm_toLp_sq (f : 𝓢(Position, E)) :
    (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2) = ‖f.toLp 2 volume‖ₑ ^ 2 := by
  rw [SchwartzMap.toLp, Lp.enorm_toLp]
  exact lintegral_norm_sq_eq_eLpNorm_sq f.continuous.aestronglyMeasurable

/-- Every L² state has its Coulomb expectation bounded by its mass plus four
times its Fourier kinetic energy, uniformly in the pole. -/
theorem lintegral_coulomb_le_of_fourier (c : Position) (u : Lp E 2 (volume : Measure Position)) :
    (∫⁻ x, coulombKernel x c * (‖u x‖₊ : ℝ≥0∞) ^ 2) ≤
      (‖u‖₊ : ℝ≥0∞) ^ 2 +
        4 * ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
          (‖(Lp.fourierTransformₗᵢ Position E u) ξ‖₊ : ℝ≥0∞) ^ 2 := by
  let v : Lp E 2 (volume : Measure Position) := 𝓕 u
  let K := ENNReal.ofReal ((2 * Real.pi) ^ 2)
  have hK : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have he (g : Position → E) :
      (∫⁻ ξ, K * (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖g ξ‖₊ : ℝ≥0∞) ^ 2) =
        K * ∫⁻ ξ, (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖g ξ‖₊ : ℝ≥0∞) ^ 2 := by
    simp only [mul_assoc]
    exact lintegral_const_mul' K _ hK
  by_cases hT : (∫⁻ ξ, K * (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖v ξ‖₊ : ℝ≥0∞) ^ 2) = ⊤
  · change _ ≤ ‖u‖ₑ ^ 2 + 4 * ∫⁻ ξ, K * (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖v ξ‖₊ : ℝ≥0∞) ^ 2
    rw [hT]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.mul_top, add_top, le_top]
  have hv : (∫⁻ ξ, (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖v ξ‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    rw [he] at hT
    apply ENNReal.lt_top_of_mul_ne_top_right hT
    exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))).ne'
  obtain ⟨f, hf₀, hf₁⟩ := exists_schwartz_weighted_approximation v hv
  let w : ℕ → Lp E 2 (volume : Measure Position) := fun n => (𝓕⁻ (f n)).toLp 2 volume
  have hw : Tendsto w atTop (𝓝 u) := by
    have hh := (Lp.fourierTransformₗᵢ Position E).symm.continuous.tendsto v |>.comp hf₀
    change Tendsto (fun n => 𝓕⁻ ((f n).toLp 2 volume)) atTop (𝓝 (𝓕⁻ v)) at hh
    simpa only [SchwartzMap.toLp_fourierInv_eq, v, fourierInv_fourier_eq] using hh
  have hn : Tendsto (fun n => ‖w n‖ₑ ^ 2) atTop (𝓝 (‖u‖ₑ ^ 2)) := by
    exact ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp hw)
  have hk : Tendsto (fun n => 4 * (K * ∫⁻ ξ, (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖f n ξ‖₊ : ℝ≥0∞) ^ 2))
      atTop (𝓝 (4 * (K * ∫⁻ ξ, (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖v ξ‖₊ : ℝ≥0∞) ^ 2))) :=
    ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul hf₁ (Or.inr hK)) (Or.inr (by finiteness))
  have hb (n : ℕ) : (∫⁻ x, coulombKernel x c * (‖w n x‖₊ : ℝ≥0∞) ^ 2) ≤
      ‖w n‖ₑ ^ 2 + 4 * (K * ∫⁻ ξ, (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖f n ξ‖₊ : ℝ≥0∞) ^ 2) := by
    have hh := lintegral_coulomb_schwartz_fourier_le c (𝓕⁻ (f n))
    rw [lintegral_schwartz_norm_sq_eq_enorm_toLp_sq, fourier_fourierInv_eq, he] at hh
    have he' : (∫⁻ x, coulombKernel x c * (‖w n x‖₊ : ℝ≥0∞) ^ 2) =
        ∫⁻ x, coulombKernel x c * (‖(𝓕⁻ (f n)) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [(𝓕⁻ (f n)).coeFn_toLp 2 volume] with x hx
      rw [show w n x = (𝓕⁻ (f n)) x from hx]
    rw [he']
    exact hh
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hw).exists_seq_tendsto_ae
  have hc : ∀ᵐ x : Position ∂volume, x ≠ c := by rw [ae_iff]; simp
  have hlim : ∀ᵐ x : Position ∂volume,
      Tendsto (fun n => coulombKernel x c * (‖w (ns n) x‖₊ : ℝ≥0∞) ^ 2) atTop
        (𝓝 (coulombKernel x c * (‖u x‖₊ : ℝ≥0∞) ^ 2)) := by
    filter_upwards [hpoint, hc] with x hx hxc
    have hkx : coulombKernel x c ≠ ⊤ := by
      apply ENNReal.inv_ne_top.mpr
      exact (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hxc))).ne'
    apply ENNReal.Tendsto.const_mul _ (Or.inr hkx)
    exact ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp hx)
  have hm (n : ℕ) : AEMeasurable (fun x => coulombKernel x c * (‖w (ns n) x‖₊ : ℝ≥0∞) ^ 2) volume
    := by
    have hkx : Measurable (fun x : Position => coulombKernel x c) := by
      exact (ENNReal.continuous_ofReal.measurable.comp
        ((continuous_norm.comp (continuous_id.sub continuous_const)).measurable)).inv
    exact hkx.aemeasurable.mul
      ((Lp.aestronglyMeasurable (w (ns n))).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)
  have hr := (hn.add hk).comp hns.tendsto_atTop
  have hfat : (∫⁻ x, coulombKernel x c * (‖u x‖₊ : ℝ≥0∞) ^ 2) ≤
      liminf (fun n => ∫⁻ x, coulombKernel x c * (‖w (ns n) x‖₊ : ℝ≥0∞) ^ 2) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => coulombKernel x c * (‖w (ns n) x‖₊ : ℝ≥0∞) ^ 2) atTop :=
        lintegral_congr_ae (hlim.mono (fun x hx => hx.liminf_eq.symm))
      _ ≤ _ := lintegral_liminf_le' hm
  change _ ≤ ‖u‖ₑ ^ 2 + 4 * ∫⁻ ξ, K * (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖v ξ‖₊ : ℝ≥0∞) ^ 2
  rw [he]
  apply hfat.trans
  rw [← hr.liminf_eq]
  exact liminf_le_liminf (Filter.Eventually.of_forall (fun n => hb (ns n)))

end LiebThirring
end

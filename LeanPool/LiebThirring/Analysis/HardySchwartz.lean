/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import LeanPool.LiebThirring.Analysis.HardyRegularized
public import LeanPool.LiebThirring.Fourier.Schwartz
/-!
# Hardy and Coulomb bounds for Schwartz functions

Hardy on the Schwartz core after removing the regularization by Fatou.

The elementary comparison between the Coulomb and inverse-square kernels.
-/
public section
open MeasureTheory Filter
open scoped RealInnerProductSpace SchwartzMap ENNReal NNReal Topology FourierTransform
namespace LiebThirring
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hardy on the Schwartz core after removing the regularization by Fatou. -/
theorem lintegral_coulomb_sq_schwartz_le (c : Position) (f : 𝓢(Position, E)) :
    (∫⁻ x, coulombKernel x c ^ 2 * (‖f x‖₊ : ℝ≥0∞) ^ 2) ≤
      ENNReal.ofReal (4 * ∑ i : Fin 3,
        ∫ x, ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2) := by
  let F := fun (ε : ℝ) (x : Position) =>
    (ENNReal.ofReal (‖x - c‖ ^ 2 + ε ^ 2))⁻¹ * (‖f x‖₊ : ℝ≥0∞) ^ 2
  have hm (ε : ℝ) : Measurable (F ε) := by
    dsimp [F]
    exact ((ENNReal.continuous_ofReal.measurable.comp
      ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2 |>.add
        continuous_const).measurable).inv).mul
      ((ENNReal.continuous_coe.measurable.comp f.continuous.nnnorm.measurable).pow_const 2)
  have ht (x : Position) : Tendsto (fun ε : ℝ => F ε x) (𝓝[>] 0)
      (𝓝 (coulombKernel x c ^ 2 * (‖f x‖₊ : ℝ≥0∞) ^ 2)) := by
    have hh : Tendsto (fun ε : ℝ => ENNReal.ofReal (‖x - c‖ ^ 2 + ε ^ 2))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal (‖x - c‖ ^ 2))) := by
      apply ENNReal.tendsto_ofReal
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => ‖x - c‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (‖x - c‖ ^
          2))).add
          ((show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).pow 2))
    have hh' := ENNReal.Tendsto.mul_const (tendsto_inv_iff.mpr hh)
      (Or.inr (by finiteness : (‖f x‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤))
    simpa only [F, coulombKernel, ENNReal.ofReal_pow (norm_nonneg _), ENNReal.inv_pow] using hh'
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, (∫⁻ x, F ε x) ≤
      ENNReal.ofReal (4 * ∑ i : Fin 3,
        ∫ x, ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hi := integrable_temperate_mul_norm_sq (hasTemperateGrowth_hardy_weight hε' c) f
    have he : (∫⁻ x, F ε x) =
        ENNReal.ofReal (∫ x, (‖x - c‖ ^ 2 + ε ^ 2)⁻¹ * ‖f x‖ ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hi]
      · apply lintegral_congr
        intro x
        have hp := add_pos_of_nonneg_of_pos (sq_nonneg ‖x - c‖) (sq_pos_of_pos hε')
        simp only [F, ENNReal.ofReal_mul (inv_nonneg.mpr hp.le),
          ENNReal.ofReal_inv_of_pos hp, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        rfl
      · exact Filter.Eventually.of_forall (fun x => mul_nonneg (by positivity) (sq_nonneg _))
    rw [he]
    exact ENNReal.ofReal_le_ofReal (integral_hardy_regularized_le hε' c f)
  calc
    _ = ∫⁻ x, liminf (fun ε : ℝ => F ε x) (𝓝[>] 0) :=
      lintegral_congr (fun x => (ht x).liminf_eq.symm)
    _ ≤ liminf (fun ε : ℝ => ∫⁻ x, F ε x) (𝓝[>] 0) := lintegral_liminf_le hm
    _ ≤ _ := liminf_le_of_frequently_le hb.frequently

/-- The elementary comparison between the Coulomb and inverse-square kernels. -/
theorem coulombKernel_le_one_add_sq (x c : Position) :
    coulombKernel x c ≤ 1 + coulombKernel x c ^ 2 := by
  by_cases h : coulombKernel x c ≤ 1
  · exact h.trans le_self_add
  · have h₁ : 1 ≤ coulombKernel x c := (lt_of_not_ge h).le
    rw [pow_two]
    exact (le_mul_of_one_le_right' h₁).trans le_add_self

end LiebThirring

namespace LiebThirring
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The three coordinate derivative energies equal the radial Fourier kinetic integral. -/
theorem schwartz_dirichlet_eq_fourier (f : 𝓢(Position, H)) :
    ENNReal.ofReal (4 * ∑ i : Fin 3,
      ∫ x, ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2) =
      4 * ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
        (‖(𝓕 f) ξ‖₊ : ℝ≥0∞) ^ 2 := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))]
  congr 1
  have hd (i : Fin 3) : ENNReal.ofReal
      (∫ x, ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        ENNReal.ofReal ((inner ℝ ξ (EuclideanSpace.basisFun (Fin 3) ℝ i)) ^ 2) *
        (‖(𝓕 f) ξ‖₊ : ℝ≥0∞) ^ 2 := by
    have hh := Fourier.lintegral_norm_sq_eq_ofReal_integral
      (LineDeriv.lineDerivOp (EuclideanSpace.basisFun (Fin 3) ℝ i) f)
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv] at hh
    rw [← hh]
    exact Fourier.lintegral_fderiv_eq_fourier f _
  simp_rw [hd]
  rw [← lintegral_finsetSum]
  · apply lintegral_congr
    intro ξ
    rw [← Finset.sum_mul, ← Finset.mul_sum,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_sq_inner_left, ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm]
    rfl
  · intro i _
    exact (measurable_const.mul (ENNReal.continuous_ofReal.measurable.comp
      (((continuous_id.inner continuous_const).pow 2).measurable))).mul
      ((ENNReal.continuous_coe.measurable.comp (𝓕 f).continuous.nnnorm.measurable).pow_const 2)

/-- Schwartz Hardy with the exact Mathlib Fourier normalization. -/
theorem lintegral_coulomb_sq_schwartz_fourier_le (c : Position) (f : 𝓢(Position, H)) :
    (∫⁻ x, coulombKernel x c ^ 2 * (‖f x‖₊ : ℝ≥0∞) ^ 2) ≤
      4 * ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
        (‖(𝓕 f) ξ‖₊ : ℝ≥0∞) ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hh := lintegral_coulomb_sq_schwartz_le (E := H) c f
  rw [schwartz_dirichlet_eq_fourier f] at hh
  exact hh

/-- The Schwartz Coulomb expectation is bounded by mass plus four kinetic energies. -/
theorem lintegral_coulomb_schwartz_fourier_le (c : Position) (f : 𝓢(Position, H)) :
    (∫⁻ x, coulombKernel x c * (‖f x‖₊ : ℝ≥0∞) ^ 2) ≤
      (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2) +
      4 * ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
        (‖(𝓕 f) ξ‖₊ : ℝ≥0∞) ^ 2 := by
  calc
    _ ≤ ∫⁻ x, (1 + coulombKernel x c ^ 2) * (‖f x‖₊ : ℝ≥0∞) ^ 2 :=
      lintegral_mono (fun x => mul_le_mul' (coulombKernel_le_one_add_sq x c) le_rfl)
    _ = (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2) +
        ∫⁻ x, coulombKernel x c ^ 2 * (‖f x‖₊ : ℝ≥0∞) ^ 2 := by
      simp only [add_mul, one_mul]
      apply lintegral_add_left
      exact (ENNReal.continuous_coe.measurable.comp f.continuous.nnnorm.measurable).pow_const 2
    _ ≤ _ := add_le_add le_rfl (lintegral_coulomb_sq_schwartz_fourier_le c f)

end LiebThirring
end

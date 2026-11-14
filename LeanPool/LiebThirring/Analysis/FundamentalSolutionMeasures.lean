/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.LiebThirring.Analysis.FundamentalSolutionIntegrability
import all LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Fubini for bounded Coulomb potentials

The real value of the extended kernel is the real inverse norm, including value zero on the
diagonal.

A finite pointwise potential is the Bochner integral of the real kernel.
-/

public section

open MeasureTheory Set InnerProductSpace Laplacian
open scoped ENNReal

namespace LiebThirring

/-- The real value of the extended kernel is the real inverse norm,
including value zero on the diagonal. -/
theorem coulombKernel_toReal_eq_inv_norm (x y : Position) :
    (coulombKernel x y).toReal = ‖x - y‖⁻¹ := by
  simp only [coulombKernel, ENNReal.toReal_inv, ENNReal.toReal_ofReal (norm_nonneg _)]

/-- A finite pointwise potential is the Bochner integral of the real kernel. -/
theorem coulombPotential_toReal_eq_integral (β : Measure Position) (x : Position)
    (hx : coulombPotential β x ≠ ⊤) :
    (coulombPotential β x).toReal = ∫ y, ‖x - y‖⁻¹ ∂β := by
  have hK : Measurable (coulombKernel x) :=
    ((measurable_const.sub measurable_id).norm.ennreal_ofReal).inv
  rw [coulombPotential]
  rw [← integral_toReal hK.aemeasurable (ae_lt_top hK hx)]
  simp only [coulombKernel_toReal_eq_inv_norm]

/-- Absolute Tonelli bound for a compactly supported continuous multiplier. -/
theorem lintegral_abs_mul_coulombKernel_ne_top
    (β : Measure Position) [SFinite β] {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hβ : ∀ x, coulombPotential β x ≤ C)
    {g : Position → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫⁻ p : Position × Position,
      ENNReal.ofReal ‖g p.1‖ * coulombKernel p.1 p.2 ∂volume.prod β) ≠ ⊤ := by
  have hK : Measurable (Function.uncurry coulombKernel) :=
    ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).inv
  have hgm : Measurable g := hg.measurable
  have hgi : (∫⁻ x, ENNReal.ofReal ‖g x‖) ≠ ⊤ := by
    have h := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun x => norm_nonneg (g x)))).mp
      (hg.integrable_of_hasCompactSupport (μ := volume) hgc).norm.hasFiniteIntegral
    exact h.ne
  have heq : (∫⁻ p : Position × Position,
      ENNReal.ofReal ‖g p.1‖ * coulombKernel p.1 p.2 ∂volume.prod β) =
      ∫⁻ x, ENNReal.ofReal ‖g x‖ * coulombPotential β x := by
    have hm : AEMeasurable (fun p : Position × Position =>
        ENNReal.ofReal ‖g p.1‖ * coulombKernel p.1 p.2) (volume.prod β) :=
      ((hgm.comp measurable_fst).norm.ennreal_ofReal.mul hK).aemeasurable
    rw [lintegral_prod (fun p : Position × Position =>
      ENNReal.ofReal ‖g p.1‖ * coulombKernel p.1 p.2) hm]
    apply lintegral_congr
    intro x
    unfold coulombPotential
    exact lintegral_const_mul (μ := β) (ENNReal.ofReal ‖g x‖)
      (show Measurable (coulombKernel x) from
        ((measurable_const.sub measurable_id).norm.ennreal_ofReal).inv)
  rw [heq]
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hgi hC)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖g x‖ * C :=
      lintegral_mono (fun x => mul_le_mul' le_rfl (hβ x))
    _ = _ := lintegral_mul_const _ hgm.norm.ennreal_ofReal

/-- Absolute product integrability licenses the ordinary Fubini exchange in the fundamental
solution. -/
theorem integrable_inv_norm_sub_mul_prod
    (β : Measure Position) [SFinite β] {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hβ : ∀ x, coulombPotential β x ≤ C)
    {g : Position → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun p : Position × Position => ‖p.1 - p.2‖⁻¹ * g p.1)
      (volume.prod β) := by
  have hK : Measurable (Function.uncurry coulombKernel) :=
    ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).inv
  have hgm : Measurable g := hg.measurable
  have hmajor := integrable_toReal_of_lintegral_ne_top
    (((hgm.comp measurable_fst).norm.ennreal_ofReal).mul hK).aemeasurable
    (lintegral_abs_mul_coulombKernel_ne_top β hC hβ hg hgc)
  apply hmajor.mono
    ((((measurable_fst.sub measurable_snd).norm.inv).mul
      (hgm.comp measurable_fst)).aestronglyMeasurable)
  filter_upwards with p
  change ‖‖p.1 - p.2‖⁻¹ * g p.1‖ ≤
    ‖(ENNReal.ofReal ‖g p.1‖ * coulombKernel p.1 p.2).toReal‖
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    coulombKernel_toReal_eq_inv_norm]
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), abs_abs]
  exact le_of_eq (mul_comm _ _)

/-- Unconditional Fubini reduction of bounded-potential pairings to point-charge pairings. -/
theorem integral_coulombPotential_toReal_mul_eq_integral_integral
    (β : Measure Position) [SFinite β] {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hβ : ∀ x, coulombPotential β x ≤ C)
    {g : Position → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ x, (coulombPotential β x).toReal * g x) =
      ∫ y, (∫ x, ‖x - y‖⁻¹ * g x) ∂β := by
  calc
    _ = ∫ x, ∫ y, ‖x - y‖⁻¹ * g x ∂β := by
      apply integral_congr_ae
      filter_upwards with x
      rw [coulombPotential_toReal_eq_integral β x
        (ne_top_of_le_ne_top hC (hβ x)), integral_mul_const]
    _ = _ := integral_integral_swap (integrable_inv_norm_sub_mul_prod β hC hβ hg hgc)

/-- the fundamental solution's Fubini reduction, with the weak-harmonic Laplacian. -/
theorem integral_coulombPotential_toReal_mul_laplacian_eq_integral_integral
    (β : Measure Position) [SFinite β] {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hβ : ∀ x, coulombPotential β x ≤ C)
    {f : Position → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, (coulombPotential β x).toReal * Δ f x) =
      ∫ y, (∫ x, ‖x - y‖⁻¹ * Δ f x) ∂β :=
  integral_coulombPotential_toReal_mul_eq_integral_integral β hC hβ
    (continuous_laplacian_position hf) (hasCompactSupport_laplacian_position hfc)

end LiebThirring

end

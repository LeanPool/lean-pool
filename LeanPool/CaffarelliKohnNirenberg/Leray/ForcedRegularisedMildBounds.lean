/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMildEquation
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierJApproximationOrthogonality

/-!
# Bounds for the forced mild equation in frequency variables

Pointwise bounds for the Duhamel integrands of `eq:reg-mild-forced`, the Abel
kernel integral, and the resulting bound on the frequency form of the right
hand side, uniform on bounded time intervals.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The squared `L²` norm is the integral of the squared pointwise norm. -/
theorem integral_norm_sq_eq_norm_sq_Lp {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Lp E 2 μ) :
    ∫ x, ‖(f : α → E) x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact (inner_self_eq_norm_sq _).symm

/-- A datum in `J` has transform fixed by the Leray symbol almost everywhere. -/
theorem ae_leraySymbol_fourier_of_mildJData (b : RealVectorL2)
    (hb : RegularizedMildJData b) :
    ∀ᵐ ξ ∂volume, leraySymbol ξ
        ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 b) :
          L2Vec3 → ComplexVec3) ξ) =
      (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 b) :
        L2Vec3 → ComplexVec3) ξ := by
  filter_upwards [realVectorL2_fourierOrthogonal_of_isInJ b hb] with ξ hξ
  exact Submodule.starProjection_eq_self_iff.2
    (Submodule.mem_orthogonal_singleton_iff_inner_right.2 hξ)

/-- The integral of the Abel kernel `(s - r)^{-1/2}` over `(0, s]`. -/
theorem integral_abelKernel (s : ℝ) (hs : 0 ≤ s) :
    ∫ r in Ioc 0 s, (s - r) ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt s := by
  rw [← intervalIntegral.integral_of_le hs,
    intervalIntegral.integral_comp_sub_left (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) s]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  have hzero : (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
  have hpow : s ^ (-(1 / 2 : ℝ) + 1) = Real.sqrt s := by
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  rw [hzero, hpow]
  field_simp
  ring

/-- The pointwise bound for the frequency Stokes integrand. -/
theorem norm_forcedFourierStokesIntegrand_le {F : ℝ → ComplexTensorL2} {t s C : ℝ}
    (hs : s ≤ t) (hFC : ‖F s‖ ≤ C) :
    ‖forcedFourierStokesIntegrand F t s‖ ≤
      C / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) := by
  unfold forcedFourierStokesIntegrand
  by_cases hst : s < t
  · rw [dite_eq_left hst]
    refine (stokesFourierMultiplier_norm_le (sub_pos.2 hst) _).trans ?_
    rw [stokes_kernel_eq_rpow (sub_pos.2 hst)]
    have hk : 0 ≤ (t - s) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (sub_pos.2 hst).le _
    calc 1 / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) * ‖F s‖
        ≤ 1 / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) * C := by gcongr
      _ = C / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) := by ring
  · rw [dite_eq_right hst, norm_zero]
    have hst' : s = t := le_antisymm hs (not_lt.1 hst)
    rw [hst', sub_self, Real.zero_rpow (by norm_num), mul_zero]

/-- The pointwise bound for the frequency force integrand. -/
theorem norm_forcedFourierForceIntegrand_le (H : ℝ → ComplexVectorL2) (t s : ℝ) :
    ‖forcedFourierForceIntegrand H t s‖ ≤ ‖H s‖ := by
  unfold forcedFourierForceIntegrand
  by_cases hst : s ≤ t
  · rw [dite_eq_left hst]
    refine (Lp.norm_smul_le _ _).trans ?_
    calc ‖heatMultiplier (t - s) (sub_nonneg.2 hst)‖ * ‖lerayFourierMultiplier (H s)‖
        ≤ 1 * ‖H s‖ := mul_le_mul (heatMultiplier_norm_le_one _ _)
          (lerayFourierMultiplier_norm_le _) (norm_nonneg _) zero_le_one
      _ = ‖H s‖ := one_mul _
  · rw [dite_eq_right hst, norm_zero]
    exact norm_nonneg _

/-- The frequency form of the right-hand side of `eq:reg-mild-forced` is
bounded on `[0, T]` uniformly in time. -/
theorem norm_forcedFourierMild_le (b : ComplexVectorL2) {F : ℝ → ComplexTensorL2}
    {H : ℝ → ComplexVectorL2} {t T C : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hFC : ∀ s ∈ Ioc 0 T, ‖F s‖ ≤ C)
    (hH : IntegrableOn (fun s => ‖H s‖) (Ioc 0 T)) (hC : 0 ≤ C) :
    ‖forcedFourierMild b F H t ht‖ ≤
      ‖b‖ + 2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T +
        ∫ s in Ioc 0 T, ‖H s‖ := by
  unfold forcedFourierMild
  have hheat : ‖heatMultiplier t ht • b‖ ≤ ‖b‖ :=
    (Lp.norm_smul_le _ _).trans (by
      calc ‖heatMultiplier t ht‖ * ‖b‖ ≤ 1 * ‖b‖ :=
            mul_le_mul_of_nonneg_right (heatMultiplier_norm_le_one t ht) (norm_nonneg _)
        _ = ‖b‖ := one_mul _)
  have hkernel : IntegrableOn (fun s => C / Real.sqrt (2 * Real.exp 1) *
      (t - s) ^ (-(1 / 2 : ℝ)) + ‖H s‖) (Ioc 0 t) :=
    ((integrableOn_abelKernel t ht).const_mul _).add (hH.mono_set (Ioc_subset_Ioc_right htT))
  have hint : ‖∫ s in Ioc 0 t, (-forcedFourierStokesIntegrand F t s +
      forcedFourierForceIntegrand H t s)‖ ≤ ∫ s in Ioc 0 t,
        (C / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) + ‖H s‖) := by
    refine norm_integral_le_of_norm_le hkernel ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_forcedFourierForceIntegrand_le H t s))
    rw [norm_neg]
    exact norm_forcedFourierStokesIntegrand_le hs.2 (hFC s ⟨hs.1, hs.2.trans htT⟩)
  have hsplit : ∫ s in Ioc 0 t, (C / Real.sqrt (2 * Real.exp 1) *
      (t - s) ^ (-(1 / 2 : ℝ)) + ‖H s‖) =
      C / Real.sqrt (2 * Real.exp 1) * (2 * Real.sqrt t) + ∫ s in Ioc 0 t, ‖H s‖ := by
    rw [integral_add ((integrableOn_abelKernel t ht).const_mul _)
      (hH.mono_set (Ioc_subset_Ioc_right htT)), integral_const_mul, integral_abelKernel t ht]
  have hsqrt : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hHmono : ∫ s in Ioc 0 t, ‖H s‖ ≤ ∫ s in Ioc 0 T, ‖H s‖ :=
    setIntegral_mono_set hH (Eventually.of_forall fun s => norm_nonneg _)
      (Eventually.of_forall (Ioc_subset_Ioc_right htT))
  have hc : 0 ≤ C / Real.sqrt (2 * Real.exp 1) := by positivity
  calc ‖heatMultiplier t ht • b + ∫ s in Ioc 0 t, (-forcedFourierStokesIntegrand F t s +
        forcedFourierForceIntegrand H t s)‖
      ≤ ‖b‖ + (C / Real.sqrt (2 * Real.exp 1) * (2 * Real.sqrt t) +
          ∫ s in Ioc 0 t, ‖H s‖) :=
      (norm_add_le _ _).trans (add_le_add hheat (hint.trans_eq hsplit))
    _ ≤ ‖b‖ + 2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T + ∫ s in Ioc 0 T, ‖H s‖ := by
        nlinarith only [hsqrt, hHmono, hc]

end CKN.Leray

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatOrbitSolutionDeriv
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatConv

/-!
# The heat orbit of an `L²` datum against the backward heat operator

Writing the heat orbit as `∫ Γ(x - y, t) f(y) dy` and exchanging the order of
integration, its pairing with `-∂ₜφ - Δφ` for a smooth compactly supported
`φ` living in positive times becomes `∫ f(y) φ(y, 0) dy`, because the causal
heat kernel is a fundamental solution of the heat operator
(`heatKernelPlus_backward_heat_pairing`).  Since `φ` vanishes at time zero,
the pairing is zero.  This is the core of the weak heat equation for the heat
orbit in `prop:pv-local-solution`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- A space-time function with compact support has compactly supported time
slices. -/
theorem hasCompactSupport_time_slice {G : Vec3 × ℝ → ℝ} (hG : HasCompactSupport G) (t : ℝ) :
    HasCompactSupport (fun x : Vec3 => G (x, t)) :=
  HasCompactSupport.intro (hG.isCompact.image continuous_fst) fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, t), h, rfl⟩

/-- A compact set of space-time points with positive times lies above a
positive time. -/
theorem exists_pos_le_snd_of_isCompact {K : Set (Vec3 × ℝ)} (hK : IsCompact K)
    (hpos : K ⊆ {z | 0 < z.2}) : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ z.2 := by
  by_cases hne : K.Nonempty
  · obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
    exact ⟨z0.2, hpos hz0, fun z hz => hmin hz⟩
  · exact ⟨1, one_pos, fun z hz => (hne ⟨z, hz⟩).elim⟩

/-- The backward heat operator `-∂ₜφ - Δφ` of a space-time function, written
with directional derivatives on `Vec3 × ℝ`. -/
@[expose] def backwardHeatOp (φ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  -(fderiv ℝ φ z (0, 1)) -
    ∑ j : Fin 3, fderiv ℝ (fun q => fderiv ℝ φ q (basisVec j, 0)) z (basisVec j, 0)

/-- The backward heat operator of a function vanishes outside its support. -/
theorem backwardHeatOp_eq_zero_of_notMem {φ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hz : z ∉ tsupport φ) : backwardHeatOp φ z = 0 := by
  have h0 : φ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz
  have hfirst (v : Vec3 × ℝ) : (fun q => fderiv ℝ φ q v) =ᶠ[𝓝 z] 0 := by
    filter_upwards [h0.eventuallyEq_nhds] with q hq
    rw [hq.fderiv_eq]
    simp
  have hsecond (v : Vec3 × ℝ) : fderiv ℝ (fun q => fderiv ℝ φ q v) z v = 0 := by
    rw [(hfirst v).fderiv_eq]
    simp
  have htime : fderiv ℝ φ z (0, 1) = 0 := by
    rw [h0.fderiv_eq]
    simp
  simp only [backwardHeatOp, htime, hsecond, neg_zero, Finset.sum_const_zero, sub_zero]

/-- The backward heat operator of a smooth function is continuous. -/
theorem backwardHeatOp_continuous {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (backwardHeatOp φ) := by
  have h1 : Continuous (fun z => fderiv ℝ φ z (0, 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have h2 (j : Fin 3) : Continuous
      (fun z => fderiv ℝ (fun q => fderiv ℝ φ q (basisVec j, 0)) z (basisVec j, 0)) :=
    ((contDiff_fderiv_apply_const hφ _).continuous_fderiv (by simp)).clm_apply continuous_const
  exact h1.neg.sub (continuous_finsetSum _ fun j _ => h2 j)

/-- The absolute convolution integral of two `L²` functions is bounded by the
product of their `L²` norms. -/
theorem integral_norm_kernel_le {k f : Vec3 → ℝ} (hk : MemLp k 2 volume)
    (hf : MemLp f 2 volume) (x : Vec3) :
    ∫ y : Vec3, ‖k (x - y) * f y‖ ≤ (eLpNorm k 2 volume * eLpNorm f 2 volume).toReal := by
  have hfin : eLpNorm k 2 volume * eLpNorm f 2 volume ≠ ∞ :=
    (ENNReal.mul_lt_top hk.eLpNorm_lt_top hf.eLpNorm_lt_top).ne
  have hsub := integral_sub_left_eq_self (fun y : Vec3 => ‖k (x - y) * f y‖) volume x
  simp only [sub_sub_cancel] at hsub
  rw [← hsub, ← Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← toReal_enorm]
  apply ENNReal.toReal_mono hfin
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simpa only [enorm_norm, enorm_mul] using
    lintegral_enorm_mul_sub_le hk.aestronglyMeasurable hf.aestronglyMeasurable x

/-- The Gaussian convolution with the kernel evaluated at `x - y`. -/
theorem heatConv_eq_integral_sub (t : ℝ) (f : Vec3 → ℝ) (x : Vec3) :
    heatConv t f x = ∫ y : Vec3, heatKernel (x - y) t * f y := by
  rw [heatConv_eq_integral,
    ← integral_sub_left_eq_self (fun y : Vec3 => heatKernel y t * f (x - y)) volume x]
  simp only [sub_sub_cancel]

private theorem heatKernelPlus_pairing_translate {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (w : Vec3 × ℝ) :
    ∫ z : Vec3 × ℝ, heatKernelPlus (z - w) * backwardHeatOp φ z = φ w := by
  let ψ : Vec3 × ℝ → ℝ := fun z => φ (z + w)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.addRight w)
  have hd1 (z v : Vec3 × ℝ) : fderiv ℝ ψ z v = fderiv ℝ φ (z + w) v := by
    simp only [ψ, fderiv_comp_add_right]
  have hd2 (z v : Vec3 × ℝ) : fderiv ℝ (fun q => fderiv ℝ ψ q v) z v =
      fderiv ℝ (fun q => fderiv ℝ φ q v) (z + w) v := by
    have hfun : (fun q => fderiv ℝ ψ q v) = fun q => (fun q' => fderiv ℝ φ q' v) (q + w) := by
      funext q
      exact hd1 q v
    rw [hfun]
    exact congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ => L v)
      (fderiv_comp_add_right (f := fun q' => fderiv ℝ φ q' v) (x := z) w)
  have hshift : ∫ z : Vec3 × ℝ, heatKernelPlus (z - w) * backwardHeatOp φ z =
      ∫ z : Vec3 × ℝ, heatKernelPlus z * backwardHeatOp φ (z + w) := by
    rw [← integral_sub_right_eq_self
      (fun z : Vec3 × ℝ => heatKernelPlus z * backwardHeatOp φ (z + w)) w]
    simp only [sub_add_cancel]
  have hint (g : Vec3 × ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable (fun z : Vec3 × ℝ => heatKernelPlus z * g z) volume := by
    simpa only [smul_eq_mul] using
      heatKernelPlus_locallyIntegrable_prod_volume.integrable_smul_right_of_hasCompactSupport hg hgc
  have hA : Continuous (fun z => fderiv ℝ ψ z (0, 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hAc : HasCompactSupport (fun z => fderiv ℝ ψ z (0, 1)) := hψc.fderiv_apply (𝕜 := ℝ) _
  have hB (j : Fin 3) : Continuous
      (fun z => fderiv ℝ (fun q => fderiv ℝ ψ q (basisVec j, 0)) z (basisVec j, 0)) :=
    ((contDiff_fderiv_apply_const hψ _).continuous_fderiv (by simp)).clm_apply continuous_const
  have hBc (j : Fin 3) : HasCompactSupport
      (fun z => fderiv ℝ (fun q => fderiv ℝ ψ q (basisVec j, 0)) z (basisVec j, 0)) :=
    (hψc.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _
  have hpair := heatKernelPlus_backward_heat_pairing hψ hψc
  have hrw : (fun z : Vec3 × ℝ => heatKernelPlus z * backwardHeatOp φ (z + w)) =
      fun z : Vec3 × ℝ => -(heatKernelPlus z * fderiv ℝ ψ z (0, 1)) -
        ∑ j : Fin 3, heatKernelPlus z *
          fderiv ℝ (fun q => fderiv ℝ ψ q (basisVec j, 0)) z (basisVec j, 0) := by
    funext z
    rw [backwardHeatOp, hd1 z (0, 1), mul_sub, mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [hd2]
  have hI1 : Integrable (fun z : Vec3 × ℝ => -(heatKernelPlus z * fderiv ℝ ψ z (0, 1))) volume :=
    (hint _ hA hAc).neg
  have hI2 : Integrable (fun z : Vec3 × ℝ => ∑ j : Fin 3, heatKernelPlus z *
      fderiv ℝ (fun q => fderiv ℝ ψ q (basisVec j, 0)) z (basisVec j, 0)) volume :=
    integrable_finsetSum _ fun j _ => hint _ (hB j) (hBc j)
  rw [hshift, hrw, integral_sub hI1 hI2, integral_neg,
    integral_finsetSum _ fun j _ => hint _ (hB j) (hBc j), hpair]
  simp only [ψ, Prod.mk_zero_zero, zero_add]

/-- The heat orbit of an `L²` datum is annihilated by the backward heat
operator of every smooth compactly supported function supported in positive
times. -/
theorem heatConv_backwardHeatOp_integral_eq_zero {f : Vec3 → ℝ} (hf : MemLp f 2 volume)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hpos : tsupport φ ⊆ {z | 0 < z.2}) :
    ∫ z : Vec3 × ℝ, heatConv z.2 f z.1 * backwardHeatOp φ z = 0 := by
  set L : Vec3 × ℝ → ℝ := backwardHeatOp φ with hLdef
  have hLc : Continuous L := backwardHeatOp_continuous hφ
  have hLcs : HasCompactSupport L :=
    HasCompactSupport.intro hφc.isCompact fun z hz => backwardHeatOp_eq_zero_of_notMem hz
  have hLI : Integrable L volume := hLc.integrable_of_hasCompactSupport hLcs
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_snd_of_isCompact hφc.isCompact hpos
  have hLsupp (z : Vec3 × ℝ) (hz : L z ≠ 0) : δ ≤ z.2 := by
    by_contra hlt
    exact hz (backwardHeatOp_eq_zero_of_notMem fun hmem => hlt (hδle z hmem))
  obtain ⟨B, hB, hbd⟩ := heatKernel_eLpNorm_two_uniform hδ
  set C : ℝ := (B * eLpNorm f 2 volume).toReal
  let F : (Vec3 × ℝ) × Vec3 → ℝ := fun p => heatKernel (p.1.1 - p.2) p.1.2 * f p.2 * L p.1
  have hFm : AEStronglyMeasurable F ((volume : Measure (Vec3 × ℝ)).prod volume) := by
    have hK : Measurable (fun p : (Vec3 × ℝ) × Vec3 => heatKernel (p.1.1 - p.2) p.1.2) :=
      heatKernel_vecTime_measurable.comp
        (((measurable_fst.comp measurable_fst).sub measurable_snd).prodMk
          (measurable_snd.comp measurable_fst))
    exact (hK.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
      hLc.aestronglyMeasurable.comp_fst
  have hFint : Integrable F ((volume : Measure (Vec3 × ℝ)).prod volume) := by
    rw [integrable_prod_iff hFm]
    refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
    · by_cases hz : 0 < z.2
      · obtain ⟨hK, -⟩ := heatKernel_memLp_two hz
        have h1 := (integrable_mul_sub_enorm_le hK hf z.1).1.comp_sub_left z.1
        simp only [sub_sub_cancel] at h1
        exact h1.mul_const (L z)
      · have hzero : (fun y : Vec3 => F (z, y)) = fun _ => 0 := by
          funext y
          simp [F, heatKernel_eq_zero_of_nonpos (not_lt.1 hz)]
        rw [hzero]
        exact integrable_zero _ _ _
    · refine (hLI.norm.const_mul C).mono' hFm.norm.integral_prod_right'
        (Eventually.of_forall fun z => ?_)
      have hnn : 0 ≤ ∫ y : Vec3, ‖F (z, y)‖ := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      by_cases hLz : L z = 0
      · simp [F, hLz]
      · have hz := hLsupp z hLz
        obtain ⟨hK, -⟩ := heatKernel_memLp_two (lt_of_lt_of_le hδ hz)
        have heq : (fun y : Vec3 => ‖F (z, y)‖) =
            fun y => ‖heatKernel (z.1 - y) z.2 * f y‖ * ‖L z‖ := by
          funext y
          simp only [F, norm_mul]
        rw [heq, integral_mul_const]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (integral_norm_kernel_le hK hf z.1).trans (ENNReal.toReal_mono ?_ ?_)
        · exact (ENNReal.mul_lt_top hB hf.eLpNorm_lt_top).ne
        · gcongr
          exact (hbd z.2 hz).1
  have hstep1 : ∫ z : Vec3 × ℝ, heatConv z.2 f z.1 * L z =
      ∫ z : Vec3 × ℝ, ∫ y : Vec3, F (z, y) := by
    congr 1
    funext z
    rw [heatConv_eq_integral_sub, ← integral_mul_const]
  have hinner (y : Vec3) : ∫ z : Vec3 × ℝ, F (z, y) = f y * φ (y, 0) := by
    have hrw : (fun z : Vec3 × ℝ => F (z, y)) =
        fun z => f y * (heatKernelPlus (z - (y, 0)) * L z) := by
      funext z
      rw [heatKernelPlus_eq_heatKernel]
      change heatKernel (z.1 - y) z.2 * f y * L z = f y * (heatKernel (z.1 - y) (z.2 - 0) * L z)
      rw [sub_zero]
      ring
    rw [hrw, integral_const_mul]
    rw [show (∫ z : Vec3 × ℝ, heatKernelPlus (z - (y, 0)) * L z) = φ (y, 0) from
      heatKernelPlus_pairing_translate hφ hφc (y, 0)]
  have hzero (y : Vec3) : φ (y, 0) = 0 :=
    image_eq_zero_of_notMem_tsupport fun hmem => lt_irrefl (0 : ℝ) (hpos hmem)
  rw [hstep1, integral_integral_swap hFint]
  simp only [hinner, hzero, mul_zero, integral_zero]

end ESS

end

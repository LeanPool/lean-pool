/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyGradient
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorDerivative
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# The energy estimate for a weak heat solution with `L²` data

A distributional solution `w ∈ L²(ℝ³ × (a, τ))` of `∂ₜ w - Δw = div H + f`,
with `H, f ∈ L²` and initial trace `w₀ ∈ L²`, has a continuous `L²`
representative `Z` on `[a, τ]` with `Z(a) = w₀` and a weak spatial gradient
`D ∈ L²`, and for every `t ∈ [a, τ]`
`‖Z(t)‖² + ∫ₐᵗ ‖D‖² ≤ ‖w₀‖² + ∫ₐᵗ (‖H‖² + ‖w‖² + ‖f‖²)`
(`lem:localized-vorticity-energy`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Topology Interval InnerProductSpace


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

variable {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ} {w₀ : Vec3 → ℝ}

/-- Integration by parts of a kernel convolution against a compactly
supported `C¹` spatial function. -/
theorem vlConv_integral_mul_fderiv {k h g : Vec3 → ℝ} (hk : IsVlKernel k)
    (hh : MemLp h 2 volume) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (j : Fin 3) :
    ∫ x, vlConv k h x * fderiv ℝ g x (CKN.basisVec j) =
      -∫ x, vlConv (vlDeriv k j) h x * g x := by
  have hloc : LocallyIntegrable h volume := hh.locallyIntegrable (by norm_num)
  have hf := vlConv_memLp hk hh
  have hf' := vlConv_memLp (hk.deriv j) hh
  have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  have hg'2 : MemLp (fun x => fderiv ℝ g x (CKN.basisVec j)) 2 volume :=
    ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hgc.fderiv_apply (𝕜 := ℝ) _)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec3)) (f := vlConv k h) (g := g) (v := CKN.basisVec j)
    (by
      simp_rw [vlConv_fderiv_apply hk hloc]
      exact hf'.integrable_mul hg2)
    (hf.integrable_mul hg'2) (hf.integrable_mul hg2)
    (fun x _ => ((vlConv_contDiff hk hloc).differentiable (by simp)).differentiableAt)
    (fun x _ => (hg.differentiable (by simp)).differentiableAt)
  simp_rw [vlConv_fderiv_apply hk hloc] at hibp
  exact hibp

private theorem vlTest_slice_props {a τ : ℝ} {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ)) (s : ℝ) :
    ContDiff ℝ 1 (fun x : Vec3 => φ (x, s)) ∧ HasCompactSupport (fun x : Vec3 => φ (x, s)) := by
  refine ⟨(hφ.1.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp), ?_⟩
  refine HasCompactSupport.intro (hφ.2.1.isCompact.image continuous_fst) ?_
  intro x hx
  by_contra hne
  exact hx ⟨(x, s), subset_tsupport _ hne, rfl⟩

private theorem vlTest_memLp_slab {a τ : ℝ} {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ)) (j : Fin 3) :
    MemLp φ 2 (volume.restrict (vlSlab a τ)) ∧
      MemLp (fun p : Vec3 × ℝ => CKN.spatialPartial φ j p) 2
        (volume.restrict (vlSlab a τ)) := by
  have : IsFiniteMeasureOnCompacts (volume : Measure (Vec3 × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  constructor
  · exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict _
  · have hcont : Continuous (fun p : Vec3 × ℝ => CKN.spatialPartial φ j p) := by
      have h := (hφ.1.continuous_fderiv (by simp)).clm_apply
        (continuous_const (y := ((CKN.basisVec j, (0 : ℝ)) : Vec3 × ℝ)))
      refine h.congr fun p => ?_
      exact (CKN.spatialPartial_eq_joint_fderiv hφ.1 p j).symm
    have hsupp : HasCompactSupport (fun p : Vec3 × ℝ => CKN.spatialPartial φ j p) :=
      CKN.hasCompactSupport_spatialPartial hφ.2.1 j
    exact (hcont.memLp_of_hasCompactSupport hsupp).restrict _

/-- Each mollified slice satisfies the weak-gradient identity. -/
theorem vlGrad_weak_n (sol : VlHeatSolution a τ w H f w₀) (n : ℕ) (j : Fin 3)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ)) :
    ∫ p in vlSlab a τ, vlConvT (vlMoll n) w p.1 p.2 * CKN.spatialPartial φ j p =
      -∫ p in vlSlab a τ, vlGrad w n j p * φ p := by
  obtain ⟨hφ2, hDφ2⟩ := vlTest_memLp_slab hφ j
  have hC := vlConvT_memLp (vlMoll_kernel n) sol.w_meas sol.w_L2
  have hL : Integrable (fun p : Vec3 × ℝ => vlConvT (vlMoll n) w p.1 p.2 *
      CKN.spatialPartial φ j p) (volume.restrict (vlSlab a τ)) := hC.integrable_mul hDφ2
  have hR : Integrable (fun p => vlGrad w n j p * φ p) (volume.restrict (vlSlab a τ)) :=
    (vlGrad_memLp sol n j).integrable_mul hφ2
  rw [vlSlab_integral_eq hL, vlSlab_integral_eq hR, ← integral_neg]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
    (vlSlab_slice_memLp sol.w_meas sol.w_L2)] with s hs hsI
  replace hs := hs hsI
  obtain ⟨hg, hgc⟩ := vlTest_slice_props hφ s
  exact vlConv_integral_mul_fderiv (vlMoll_kernel n) hs hg hgc j

/-- The mollified field as an element of `L²` of the slab. -/
@[expose] def vlMollSlab (sol : VlHeatSolution a τ w H f w₀) (n : ℕ) :
    Lp ℝ 2 (volume.restrict (vlSlab a τ)) :=
  (vlConvT_memLp (vlMoll_kernel n) sol.w_meas sol.w_L2).toLp _

theorem vlMollSlab_tendsto (sol : VlHeatSolution a τ w H f w₀) :
    Tendsto (fun n => vlMollSlab sol n) atTop (𝓝 (sol.w_L2.toLp w)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hsq : ∀ n, ‖vlMollSlab sol n - sol.w_L2.toLp w‖ ^ 2 =
      ∫ s in Ioo a τ, vlMollErr n w s := by
    intro n
    have hd := (vlConvT_memLp (vlMoll_kernel n) sol.w_meas sol.w_L2).sub sol.w_L2
    rw [vlMollSlab, ← MemLp.toLp_sub, vl_norm_toLp_sq, vlSlab_integral_sq hd]
    refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => ?_)
    simp only [vlMollErr, Pi.sub_apply]
  have hlim := vlMoll_slab_tendsto sol.w_meas sol.w_L2
  have hroot : Tendsto (fun n => Real.sqrt (∫ s in Ioo a τ, vlMollErr n w s)) atTop (𝓝 0) := by
    simpa [vlMollErr] using hlim.sqrt
  refine hroot.congr (fun n => ?_)
  rw [← hsq n, Real.sqrt_sq (norm_nonneg _)]

/-- The limit gradient is the weak spatial gradient. -/
theorem vlGradLimit_weak (sol : VlHeatSolution a τ w H f w₀) (j : Fin 3)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ)) :
    ∫ p in vlSlab a τ, w p * CKN.spatialPartial φ j p =
      -∫ p in vlSlab a τ, (vlGradLimit sol j : Vec3 × ℝ → ℝ) p * φ p := by
  obtain ⟨hφ2, hDφ2⟩ := vlTest_memLp_slab hφ j
  have hleft : Tendsto (fun n => ∫ p in vlSlab a τ, vlConvT (vlMoll n) w p.1 p.2 *
      CKN.spatialPartial φ j p) atTop
      (𝓝 (∫ p in vlSlab a τ, w p * CKN.spatialPartial φ j p)) := by
    have h := (vlMollSlab_tendsto sol).inner (𝕜 := ℝ) (tendsto_const_nhds (x := hDφ2.toLp _))
    have hlim : ⟪sol.w_L2.toLp w, hDφ2.toLp _⟫_ℝ =
        ∫ p in vlSlab a τ, w p * CKN.spatialPartial φ j p :=
      (vl_integral_mul_eq_inner sol.w_L2 hDφ2).symm
    rw [hlim] at h
    refine h.congr (fun n => ?_)
    exact (vl_integral_mul_eq_inner _ hDφ2).symm
  have hright : Tendsto (fun n => -∫ p in vlSlab a τ, vlGrad w n j p * φ p) atTop
      (𝓝 (-∫ p in vlSlab a τ, (vlGradLimit sol j : Vec3 × ℝ → ℝ) p * φ p)) := by
    have h := (vlGradLimit_tendsto sol j).inner (𝕜 := ℝ) (tendsto_const_nhds (x := hφ2.toLp _))
    have hD : ⟪vlGradLimit sol j, hφ2.toLp φ⟫_ℝ =
        ∫ p in vlSlab a τ, (vlGradLimit sol j : Vec3 × ℝ → ℝ) p * φ p := by
      rw [vl_integral_mul_eq_inner (Lp.memLp _) hφ2, Lp.toLp_coeFn]
    rw [hD] at h
    refine h.neg.congr (fun n => ?_)
    rw [← vl_integral_mul_eq_inner]
  exact tendsto_nhds_unique hleft (hright.congr (fun n => (vlGrad_weak_n sol n j hφ).symm))

end ESS

end

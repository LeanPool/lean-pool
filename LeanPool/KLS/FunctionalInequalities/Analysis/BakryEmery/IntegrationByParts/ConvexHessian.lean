/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.SmoothBall
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.Integrability
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Hessian integrability and the mean Hessian of a convex potential

Letwin, arXiv:2607.24164v1, Lemma 2.3 (analytic part), for a given smooth convex potential `φ` with
`e^{-φ}` a probability density on a finite-dimensional inner product space and `∇φ ∈ L²(ν)`,
`ν = e^{-φ} dx`: the diagonal Hessian entries are integrable (cutoff integration by parts, uniform
bound, Fatou), hence all mixed entries, and `∫ ∂_u∂_v φ dν = ∫ ∂_uφ ∂_vφ dν`. No Hessian
integrability, regularity, growth or exponential moment is assumed. The isotropy adapter is in
`KLS/Isotropic.lean`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Cutoff integration by parts: `∫ χ_R ∂²_v φ dν = ∫ χ_R (∂_v φ)² dν − ∫ ∂_v χ_R ∂_v φ dν` for
`ν = e^{-φ} dx` (Letwin A.3 with `f = ∂_v φ`, `g = χ_R`). -/
theorem integral_scaled_mul_hessian_tilted_eq (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (v : E) {R : ℝ}
    (hR : 0 < R) :
    (∫ x,
        scaled R x * bilinearIteratedFDerivTwo ℝ φ x v v ∂((volume : Measure E).tilted (-φ))) =
      (∫ x, scaled R x * (fderiv ℝ φ x v) ^ 2 ∂((volume : Measure E).tilted (-φ))) -
        ∫ x, fderiv ℝ (scaled R) x v * fderiv ℝ φ x v ∂((volume : Measure E).tilted (-φ)) := by
  let μ : Measure E := (volume : Measure E).tilted (-φ)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hexp
  let f : E → ℝ := fun x => fderiv ℝ φ x v
  have hf : ContDiff ℝ ∞ f := by
    exact (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hf2 : MemLp f 2 μ := by
    simpa only [f, inner_gradient_left] using hgrad.inner_const (𝕜 := ℝ) v
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdfg : Integrable (fun x => fderiv ℝ f x v * scaled R x) μ :=
    (hdf.mul (continuous_scaled R)).integrable_of_hasCompactSupport
      (hasCompactSupport_scaled hR).mul_left
  have hfdg : Integrable (fun x => f x * fderiv ℝ (scaled R) x v) μ := by
    have hc : Continuous (fun x => fderiv ℝ (scaled R) x v) :=
      ((contDiff_scaled R).continuous_fderiv (by simp)).clm_apply continuous_const
    have hs : HasCompactSupport (fun x => fderiv ℝ (scaled R) x v) :=
      ((hasCompactSupport_scaled hR).fderiv (𝕜 := ℝ)).comp_left (g := fun L : E →L[ℝ] ℝ => L v)
        (by simp)
    exact (hf.continuous.mul hc).integrable_of_hasCompactSupport hs.mul_left
  have hfgrad : Integrable (fun x => f x * scaled R x * fderiv ℝ φ x v) μ := by
    have hsq : Integrable (fun x => f x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hf2.aestronglyMeasurable).mp hf2
    refine
      hsq.mono'
        ((hf.continuous.mul (continuous_scaled R)).mul hf.continuous).aestronglyMeasurable ?_
    filter_upwards [] with x
    change ‖f x * scaled R x * f x‖ ≤ f x ^ 2
    rw [show f x * scaled R x * f x = scaled R x * f x ^ 2 by ring]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (scaled_nonneg _ _) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (scaled_le_one _ _)
  have hfg : Integrable (fun x => f x * scaled R x) μ :=
    (hf.continuous.mul (continuous_scaled R)).integrable_of_hasCompactSupport
      (hasCompactSupport_scaled hR).mul_left
  have hid :=
    integral_fderiv_mul_tilted_eq (volume : Measure E) φ f (scaled R) v hφ hf
      (contDiff_scaled R) hexp hnorm hdfg hfdg hfgrad hfg
  have hsplit :
    (fun x => f x * (fderiv ℝ φ x v * scaled R x - fderiv ℝ (scaled R) x v)) =
      (fun x => f x * scaled R x * fderiv ℝ φ x v) - (fun x => f x * fderiv ℝ (scaled R) x v) := by
    funext x; simp only [Pi.sub_apply]; ring
  rw [hsplit] at hid
  change
    (∫ x, fderiv ℝ f x v * scaled R x ∂μ) =
      (∫ x, (f x * scaled R x * fderiv ℝ φ x v) - (f x * fderiv ℝ (scaled R) x v) ∂μ) at hid
  rw [integral_sub hfgrad hfdg] at hid
  convert hid using 1
  · congr 1
    funext x
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply (hφ.of_le (WithTop.coe_le_coe.mpr le_top))]
    dsimp only [f]
    ring
  · simp only [μ, f, pow_two, mul_comm, mul_left_comm]

/-- The cutoff Hessian integrals are bounded uniformly in `R ≥ 1` by `∫(∂_vφ)² + M‖v‖ ∫|∂_vφ|`. -/
theorem exists_uniform_scaled_hessian_integral_bound (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (v : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      (∫ x, scaled R x * bilinearIteratedFDerivTwo ℝ φ x v v
        ∂((volume : Measure E).tilted (-φ))) ≤ C := by
  let μ : Measure E := (volume : Measure E).tilted (-φ)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hexp
  let f : E → ℝ := fun x => fderiv ℝ φ x v
  have hf : ContDiff ℝ ∞ f :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hf2 : MemLp f 2 μ := by
    simpa only [f, inner_gradient_left] using hgrad.inner_const (𝕜 := ℝ) v
  have hf1 : Integrable f μ := hf2.integrable (by norm_num)
  have hsq : Integrable (fun x => f x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hf2.aestronglyMeasurable).mp hf2
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_bump (E := E)
  let C : ℝ := (∫ x, f x ^ 2 ∂μ) + M * ‖v‖ * ∫ x, ‖f x‖ ∂μ
  refine ⟨C, add_nonneg (integral_nonneg fun x => sq_nonneg _) ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hM0 (norm_nonneg _)) (integral_nonneg fun x => norm_nonneg _)
  intro R hR1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hcof (x : E) : ‖fderiv ℝ (scaled R) x v‖ ≤ M * ‖v‖ := by
    have hi : R⁻¹ ≤ 1 := by
      have he := mul_inv_cancel₀ hR.ne'
      have hn := inv_nonneg.mpr hR.le
      nlinarith [mul_nonneg (sub_nonneg.mpr hR1) hn]
    have hd : ‖fderiv ℝ (scaled R) x‖ ≤ M :=
      (norm_fderiv_scaled_le hR hM x).trans (mul_le_of_le_one_left hM0 hi)
    exact ((fderiv ℝ (scaled R) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  have hdcont : Continuous (fun x => fderiv ℝ (scaled R) x v) :=
    ((contDiff_scaled R).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdcs : HasCompactSupport (fun x => fderiv ℝ (scaled R) x v) :=
    ((hasCompactSupport_scaled hR).fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : E →L[ℝ] ℝ => L v) (by simp)
  have herr : Integrable (fun x => fderiv ℝ (scaled R) x v * f x) μ :=
    (hdcont.mul hf.continuous).integrable_of_hasCompactSupport hdcs.mul_right
  have habserr : |∫ x, fderiv ℝ (scaled R) x v * f x ∂μ| ≤
      M * ‖v‖ * ∫ x, ‖f x‖ ∂μ := by
    calc
      _ ≤ ∫ x, ‖fderiv ℝ (scaled R) x v * f x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, (M * ‖v‖) * ‖f x‖ ∂μ := integral_mono herr.norm
        (hf1.norm.const_mul _) (fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hcof x) (norm_nonneg _))
      _ = _ := integral_const_mul _ _
  have hcut : Integrable (fun x => scaled R x * f x ^ 2) μ := by
    refine hsq.mono' ((continuous_scaled R).mul (hf.continuous.pow 2)).aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (scaled_nonneg _ _) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (scaled_le_one _ _)
  have hfirst : (∫ x, scaled R x * f x ^ 2 ∂μ) ≤ ∫ x, f x ^ 2 ∂μ :=
    integral_mono hcut hsq (fun x => mul_le_of_le_one_left (sq_nonneg _) (scaled_le_one _ _))
  rw [integral_scaled_mul_hessian_tilted_eq φ hφ hexp hnorm hgrad v hR]
  change (∫ x, scaled R x * f x ^ 2 ∂μ) - (∫ x, fderiv ℝ (scaled R) x v * f x ∂μ) ≤ C
  have hsign := neg_le_abs (∫ x, fderiv ℝ (scaled R) x v * f x ∂μ)
  dsimp only [C]
  linarith

/--
**Diagonal Hessian integrability**: for convex smooth `φ` with `e^{-φ}` a probability density and
`∇φ ∈ L²(ν)`, `∂²_v φ ∈ L¹(ν)` (nonnegative, bounded cutoff integrals, Fatou). -/
theorem integrable_hessian_diag_tilted_of_convexOn (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : ConvexOn ℝ Set.univ φ)
    (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (v : E) :
    Integrable (fun x => bilinearIteratedFDerivTwo ℝ φ x v v)
      ((volume : Measure E).tilted (-φ)) := by
  let μ : Measure E := (volume : Measure E).tilted (-φ)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hexp
  let H : E → ℝ := fun x => bilinearIteratedFDerivTwo ℝ φ x v v
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right (by norm_num)
  have hH : Continuous H :=
    ((h1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hHpos : ∀ x, 0 ≤ H x := fun x => bilinearIteratedFDerivTwo_nonneg_of_convexOn hφ2 hc x v
  obtain ⟨C, _hC0, hC⟩ := exists_uniform_scaled_hessian_integral_bound φ hφ hexp hnorm hgrad v
  apply
    Analysis.integrable_of_cutoff_bounds μ hH.aestronglyMeasurable hHpos (c := fun n =>
      scaled ((n : ℝ) + 1)) (fun n x => scaled_nonneg _ _)
  · intro x
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    have heq : (fun n : ℕ => scaled ((n : ℝ) + 1) x) =ᶠ[atTop] fun _ => (1 : ℝ) := by
      apply Filter.eventually_atTop.mpr
      refine ⟨N, fun n hn => ?_⟩
      apply scaled_eq_one (by positivity)
      have hnn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith
    exact tendsto_const_nhds.congr' heq.symm
  · intro n
    exact
      ((continuous_scaled _).mul hH).integrable_of_hasCompactSupport
        (hasCompactSupport_scaled (by positivity : 0 < (n : ℝ) + 1)).mul_right
  · intro n
    exact hC ((n : ℝ) + 1) (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Polarization of the Hessian quadratic form. -/
theorem bilinearIteratedFDerivTwo_polarization {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x u v : E) :
    bilinearIteratedFDerivTwo ℝ φ x u v =
      (bilinearIteratedFDerivTwo ℝ φ x (u + v) (u + v) -
        bilinearIteratedFDerivTwo ℝ φ x (u - v) (u - v)) / 4 := by
  have hs := bilinearIteratedFDerivTwo_symm hφ x v u
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [hs]
  ring

/-- Mixed Hessian entries are integrable (polarization of the diagonal ones). -/
theorem integrable_hessian_tilted_of_convexOn (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : ConvexOn ℝ Set.univ φ)
    (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (u v : E) :
    Integrable (fun x => bilinearIteratedFDerivTwo ℝ φ x u v)
      ((volume : Measure E).tilted (-φ)) := by
  have hp := integrable_hessian_diag_tilted_of_convexOn φ hφ hc hexp hnorm hgrad (u + v)
  have hm := integrable_hessian_diag_tilted_of_convexOn φ hφ hc hexp hnorm hgrad (u - v)
  refine ((hp.sub hm).div_const 4).congr (ae_of_all _ fun x => ?_)
  exact
    (bilinearIteratedFDerivTwo_polarization (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) x u
        v).symm

/--
**Mean Hessian identity** (Letwin Lemma 2.3, analytic part): `∫ ∂_u∂_v φ dν = ∫ ∂_uφ ∂_vφ dν` for
convex smooth `φ` with `e^{-φ}` a probability density and `∇φ ∈ L²(ν)`; all integrability is
derived. -/
theorem integral_hessian_tilted_eq_integral_fderiv_mul_of_convexOn (φ : E → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ Set.univ φ)
    (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (u v : E) :
    (∫ x, bilinearIteratedFDerivTwo ℝ φ x u v ∂((volume : Measure E).tilted (-φ))) =
      ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂((volume : Measure E).tilted (-φ)) := by
  let μ : Measure E := (volume : Measure E).tilted (-φ)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hexp
  have hu : MemLp (fun x => fderiv ℝ φ x u) 2 μ := by
    simpa only [inner_gradient_left] using hgrad.inner_const (𝕜 := ℝ) u
  have hv : MemLp (fun x => fderiv ℝ φ x v) 2 μ := by
    simpa only [inner_gradient_left] using hgrad.inner_const (𝕜 := ℝ) v
  have hdd : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x u) μ := by
    simpa only [bilinearIteratedFDerivTwo_eq_fderiv_apply
          (hφ.of_le (WithTop.coe_le_coe.mpr le_top))] using
      integrable_hessian_tilted_of_convexOn φ hφ hc hexp hnorm hgrad u v
  have hprod : Integrable (fun x => fderiv ℝ φ x v * fderiv ℝ φ x u) μ := hv.integrable_mul hu
  rw [show
      (fun x => bilinearIteratedFDerivTwo ℝ φ x u v) =
        (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x u) by
      funext x
      exact
        bilinearIteratedFDerivTwo_eq_fderiv_apply (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) x u
          v]
  have h :=
    integral_fderiv_fderiv_tilted_eq_integral_mul (volume : Measure E) φ v u hφ hexp hnorm hdd
      hprod (hv.integrable (by norm_num))
  simpa only [mul_comm] using h

end FunctionalInequalities.Analysis.BakryEmery

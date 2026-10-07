/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.HeatKernelFundamentalSolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The causal space-time heat potential

For a smooth compactly supported space-time source `h`, the convolution of the
causal heat kernel `heatKernelPlus` with `h` is smooth, commutes with
derivatives, and solves the forward heat equation with source `h`. These are
the smooth-data facts behind the zero-data response of `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open scoped Convolution ENNReal
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The causal heat potential `W₊ ⋆ h` of a space-time source `h`, the
Duhamel solution with zero data used in `lem:pv-stokes`. -/
@[expose] def causalHeatConv (h : Vec3 × ℝ → ℝ) (v : Vec3 × ℝ) : ℝ :=
  MeasureTheory.convolution (fun p : Vec3 × ℝ => heatKernelPlus p) h
    (ContinuousLinearMap.lsmul ℝ ℝ) volume v

/-- The causal heat potential as an explicit space-time integral. -/
theorem causalHeatConv_eq_integral (h : Vec3 × ℝ → ℝ) (v : Vec3 × ℝ) :
    causalHeatConv h v = ∫ p : Vec3 × ℝ, heatKernelPlus p * h (v - p) := by
  simp only [causalHeatConv, convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]

/-- The causal heat potential of a smooth compactly supported source is smooth. -/
theorem causalHeatConv_contDiff {h : Vec3 × ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h) :
    ContDiff ℝ (⊤ : ℕ∞) (causalHeatConv h) :=
  hc.contDiff_convolution_right _ heatKernelPlus_locallyIntegrable_prod_volume hh

/-- Derivatives of the causal heat potential fall on the source. -/
theorem causalHeatConv_fderiv_apply {h : Vec3 × ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (v w : Vec3 × ℝ) :
    fderiv ℝ (causalHeatConv h) v w =
      causalHeatConv (fun q => fderiv ℝ h q w) v := by
  have hfd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    heatKernelPlus_locallyIntegrable_prod_volume (hh.of_le (by simp)) v
  have hfun : causalHeatConv h =
      MeasureTheory.convolution (fun p : Vec3 × ℝ => heatKernelPlus p) h
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := rfl
  rw [hfun, hfd.fderiv, convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    heatKernelPlus_locallyIntegrable_prod_volume (hc.fderiv (𝕜 := ℝ))
    (hh.continuous_fderiv (by simp))]
  rfl

/-- A directional derivative of a smooth compactly supported function is again
smooth and compactly supported. -/
theorem contDiff_fderiv_apply_const {h : Vec3 × ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (w : Vec3 × ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ h q w) :=
  (hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- Differentiating `q ↦ F (v - q)` reverses the direction. -/
theorem fderiv_comp_sub_left_apply {F : Vec3 × ℝ → ℝ}
    (hF : Differentiable ℝ F) (v p w : Vec3 × ℝ) :
    fderiv ℝ (fun q => F (v - q)) p w = -fderiv ℝ F (v - p) w := by
  have hinner : HasFDerivAt (fun q : Vec3 × ℝ => v - q)
      (-ContinuousLinearMap.id ℝ (Vec3 × ℝ)) p := by
    simpa using (hasFDerivAt_id p).const_sub v
  have hcomp := (hF (v - p)).hasFDerivAt.comp p hinner
  rw [show (fun q => F (v - q)) = F ∘ (fun q : Vec3 × ℝ => v - q) from rfl,
    hcomp.fderiv]
  simp

private theorem backwardTestPotential_origin (f : Vec3 × ℝ → ℝ) :
    backwardTestPotential f (0, 0) =
      ∫ z : Vec3 × ℝ, heatKernelPlus z * f z := by
  rw [backwardTestPotential_eq_backwardHeatPotential]
  unfold backwardHeatPotential backwardHeatKernel
  simp only [sub_zero]
  rfl

/-- The causal heat kernel is a fundamental solution of the heat operator:
pairing it with the backward heat operator applied to a smooth compactly
supported function returns the value at the origin. -/
theorem heatKernelPlus_backward_heat_pairing {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    -(∫ z : Vec3 × ℝ, heatKernelPlus z * fderiv ℝ ψ z (0, 1)) -
      ∑ i : Fin 3, ∫ z : Vec3 × ℝ, heatKernelPlus z *
        fderiv ℝ (fun q => fderiv ℝ ψ q (CKN.basisVec i, 0)) z
          (CKN.basisVec i, 0) = ψ (0, 0) := by
  have hback := backwardTestPotential_heat_equation hψ hψc (0 : Vec3) (0 : ℝ)
  rw [backwardTestPotential_timePartial hψ hψc] at hback
  simp_rw [backwardTestPotential_spatialSecondPartial hψ hψc,
    backwardTestPotential_origin] at hback
  rw [← hback]
  have htime : (fun z : Vec3 × ℝ => heatKernelPlus z *
      CKN.timePartial (show ParabolicPoint → ℝ from ψ) z) =
      fun z => heatKernelPlus z * fderiv ℝ ψ z (0, 1) := by
    funext z
    rw [timePartial_eq_fderiv_apply hψ z.1 z.2]
  have hsecond (i : Fin 3) : (fun z : Vec3 × ℝ => heatKernelPlus z *
      CKN.spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z) =
      fun z => heatKernelPlus z *
        fderiv ℝ (fun q => fderiv ℝ ψ q (CKN.basisVec i, 0)) z
          (CKN.basisVec i, 0) := by
    funext z
    have hfirst : (fun w : ParabolicPoint =>
        CKN.spatialPartial (show ParabolicPoint → ℝ from ψ) i w) =
        fun w : Vec3 × ℝ => fderiv ℝ ψ w (CKN.basisVec i, 0) := by
      funext w
      exact spatialPartial_eq_fderiv_apply hψ i w.1 w.2
    change heatKernelPlus z * CKN.spatialPartial (fun w : ParabolicPoint =>
        CKN.spatialPartial (show ParabolicPoint → ℝ from ψ) i w) i z = _
    rw [hfirst, spatialPartial_eq_fderiv_apply
      (contDiff_fderiv_apply_const hψ _) i z.1 z.2]
  rw [htime]
  simp_rw [hsecond]
  rfl

/-- The causal heat potential solves the forward heat equation with source `h`,
written with directional derivatives on `Vec3 × ℝ`. -/
theorem causalHeatConv_heat_equation {h : Vec3 × ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h) (v : Vec3 × ℝ) :
    fderiv ℝ (causalHeatConv h) v (0, 1) -
      ∑ i : Fin 3, fderiv ℝ (fun q => fderiv ℝ (causalHeatConv h) q
        (CKN.basisVec i, 0)) v (CKN.basisVec i, 0) = h v := by
  let k : Fin 3 → Vec3 × ℝ → ℝ := fun i q => fderiv ℝ h q (CKN.basisVec i, 0)
  have hk (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (k i) := contDiff_fderiv_apply_const hh _
  have hkc (i : Fin 3) : HasCompactSupport (k i) := hc.fderiv_apply (𝕜 := ℝ) _
  have hinner (i : Fin 3) :
      (fun q => fderiv ℝ (causalHeatConv h) q (CKN.basisVec i, 0)) =
        causalHeatConv (k i) := by
    funext q
    exact causalHeatConv_fderiv_apply hh hc q _
  let ψ : Vec3 × ℝ → ℝ := fun p => h (v - p)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hh.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.subLeft v)
  have hdiff : Differentiable ℝ h := hh.differentiable (by simp)
  have hψfirst (w : Vec3 × ℝ) : (fun p => fderiv ℝ ψ p w) =
      fun p => (fun q => -fderiv ℝ h q w) (v - p) := by
    funext p
    exact fderiv_comp_sub_left_apply hdiff v p w
  have hψsecond (i : Fin 3) (p : Vec3 × ℝ) :
      fderiv ℝ (fun q => fderiv ℝ ψ q (CKN.basisVec i, 0)) p (CKN.basisVec i, 0) =
        fderiv ℝ (k i) (v - p) (CKN.basisVec i, 0) := by
    rw [hψfirst]
    have hnegdiff : Differentiable ℝ (fun q => -fderiv ℝ h q (CKN.basisVec i, 0)) :=
      ((hk i).differentiable (by simp)).neg
    rw [fderiv_comp_sub_left_apply hnegdiff v p _]
    have hneg : (fun q => -fderiv ℝ h q (CKN.basisVec i, 0)) = -(k i) := rfl
    rw [hneg, fderiv_neg]
    simp
  have h1 : (∫ z : Vec3 × ℝ, heatKernelPlus z * fderiv ℝ ψ z (0, 1)) =
      -∫ z : Vec3 × ℝ, heatKernelPlus z * fderiv ℝ h (v - z) (0, 1) := by
    rw [← integral_neg]
    congr 1
    funext z
    rw [fderiv_comp_sub_left_apply hdiff v z]
    ring
  have h2 (i : Fin 3) : (∫ z : Vec3 × ℝ, heatKernelPlus z *
      fderiv ℝ (fun q => fderiv ℝ ψ q (CKN.basisVec i, 0)) z (CKN.basisVec i, 0)) =
      ∫ z : Vec3 × ℝ, heatKernelPlus z *
        fderiv ℝ (k i) (v - z) (CKN.basisVec i, 0) := by
    congr 1
    funext z
    rw [hψsecond]
  have hpair := heatKernelPlus_backward_heat_pairing hψ hψc
  rw [h1, neg_neg] at hpair
  simp_rw [h2] at hpair
  rw [causalHeatConv_fderiv_apply hh hc]
  simp_rw [hinner, causalHeatConv_fderiv_apply (hk _) (hkc _),
    causalHeatConv_eq_integral]
  rw [hpair]
  simp only [ψ, Prod.mk_zero_zero, sub_zero]

/-- A source supported in positive times has a causal heat potential that
vanishes at nonpositive times. -/
theorem causalHeatConv_eq_zero_of_nonpos {h : Vec3 × ℝ → ℝ}
    (hpos : ∀ p : Vec3 × ℝ, h p ≠ 0 → 0 < p.2) {v : Vec3 × ℝ} (hv : v.2 ≤ 0) :
    causalHeatConv h v = 0 := by
  rw [causalHeatConv_eq_integral]
  have hzero : (fun p : Vec3 × ℝ => heatKernelPlus p * h (v - p)) = fun _ => 0 := by
    funext p
    by_cases hp : 0 < p.2
    · have hvp : ¬ 0 < (v - p).2 := by
        simp only [Prod.snd_sub, sub_pos, not_lt]
        exact le_of_lt (lt_of_le_of_lt hv hp)
      have hh0 : h (v - p) = 0 := by
        by_contra hne
        exact hvp (hpos _ hne)
      rw [hh0, mul_zero]
    · rw [show heatKernelPlus p = 0 from
        heatKernelPlus_eq_zero_of_nonpos (x := p.1) (le_of_not_gt hp), zero_mul]
  rw [hzero, integral_zero]

end ESS

end

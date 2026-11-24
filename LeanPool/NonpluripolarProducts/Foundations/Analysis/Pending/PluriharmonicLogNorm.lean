/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicDDC
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# `log |f|²` is pluriharmonic for nonvanishing holomorphic `f`

* `smoothDDC_eq_zero_of_fderiv_const`: `ddᶜ` of a function with locally constant derivative
    vanishes.
* `smoothDDC_re_comp_eq_zero`: `ddᶜ Re g = 0` for holomorphic `g`, by naturality of `ddᶜ`
  (`HolomorphicDDC.smoothDDC_comp`) applied to the real-linear `Re` on `ℂ¹`.
* `smoothDDC_log_normSq_eq_zero`: `ddᶜ log |f|² = 0` near a point where the holomorphic `f`
  does not vanish, since there `log |f|² = 2 Re log (f / f z) + log |f z|²`.

These are the transition identities for local weights of a line bundle metric: two local
generators of an invertible ideal differ by a unit `u`, and `ddᶜ log |u|² = 0`.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm

open FirstPass

noncomputable section

variable {n : ℕ}

/-- `ddᶜ` of a function whose derivative is constant near `z` vanishes. -/
theorem smoothDDC_eq_zero_of_fderiv_const {h : ComplexModel n → ℝ} {z : ComplexModel n}
    {L : ComplexModel n →L[ℝ] ℝ} (hL : ∀ᶠ y in 𝓝 z, fderiv ℝ h y = L) :
    smoothDDC h z = 0 := by
  have heq : smoothDc h =ᶠ[𝓝 z] fun _ => smoothDc h z := by
    filter_upwards [hL, hL.eventually_nhds] with y hy _
    simp only [smoothDc, hy, hL.self_of_nhds]
  rw [smoothDDC, heq.extDeriv_eq, extDeriv, fderiv_const_apply]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)

/-- The pluriharmonicity of the real part of a holomorphic function, in coordinates. -/
theorem smoothDDC_re_comp_eq_zero {g : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) {z : ComplexModel n} (hz : z ∈ U) :
    smoothDDC (fun y => (g y).re) z = 0 := by
  set F : ComplexModel n → ComplexModel 1 := fun y => WithLp.toLp 2 fun _ => g y
  set L : ComplexModel 1 →L[ℝ] ℝ := Complex.reCLM.comp
    ((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).restrictScalars ℝ)
  have hFd : DifferentiableOn ℂ F U := by
    intro y hy
    refine DifferentiableAt.differentiableWithinAt ?_
    have hgy := (hg y hy).differentiableAt (hU.mem_nhds hy)
    exact (differentiableAt_piLp 2).2 fun _ => hgy
  have hF : ContDiffOn ℂ ∞ F U := contDiffOn_of_differentiableOn_complex hFd hU
  have hρ : ContDiffOn ℝ ∞ (⇑L) univ := L.contDiff.contDiffOn
  have := HolomorphicDDC.smoothDDC_comp hU isOpen_univ hF hρ (mapsTo_univ _ _) hz
  have hρ0 : smoothDDC (⇑L) (F z) = 0 :=
    smoothDDC_eq_zero_of_fderiv_const (L := L) (Eventually.of_forall fun y => L.fderiv)
  rw [hρ0] at this
  have h0 : (0 : ComplexModel 1 [⋀^Fin 2]→L[ℝ] ℝ).compContinuousLinearMap (fderiv ℝ F z) = 0 := by
    ext v; simp
  rw [h0] at this
  simpa [L, F] using this

/-- **`log |f|²` is pluriharmonic** near a point where the holomorphic `f` does not vanish. -/
theorem smoothDDC_log_normSq_eq_zero {f : ComplexModel n → ℂ} {z : ComplexModel n}
    (hf : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ f y) (hz : f z ≠ 0) :
    smoothDDC (fun y => Real.log (Complex.normSq (f y))) z = 0 := by
  set c := f z
  have hcont : ContinuousAt (fun y => f y / c) z :=
    (hf.self_of_nhds.continuousAt).div_const c
  have hball : ∀ᶠ y in 𝓝 z, f y / c ∈ Metric.ball (1 : ℂ) 1 := by
    refine hcont.eventually (Metric.isOpen_ball.mem_nhds ?_)
    simp [c, div_self hz]
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp (hf.and hball)
  have hslit : ∀ y ∈ U, f y / c ∈ Complex.slitPlane := fun y hy => by
    have h1 := (hUsub hy).2
    rw [Metric.mem_ball, dist_eq_norm] at h1
    have := Complex.mem_slitPlane_of_norm_lt_one (z := f y / c - 1) h1
    rwa [add_sub_cancel] at this
  set g : ComplexModel n → ℂ := fun y =>
    2 * Complex.log (f y / c) + (Real.log (Complex.normSq c) : ℂ)
  have hg : DifferentiableOn ℂ g U := fun y hy => by
    have h0 : DifferentiableAt ℂ f y := (hUsub hy).1
    have h1 : DifferentiableAt ℂ (fun y => f y / c) y := by
      simpa [div_eq_mul_inv] using h0.mul_const c⁻¹
    have h2 : DifferentiableAt ℂ (fun y => Complex.log (f y / c)) y := h1.clog (hslit y hy)
    exact ((h2.const_mul 2).add_const _).differentiableWithinAt
  have heq : (fun y => Real.log (Complex.normSq (f y))) =ᶠ[𝓝 z] fun y => (g y).re := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    have hy0 : f y ≠ 0 := by
      intro h0
      have := hslit y hy
      simp [h0] at this
    have hre : (2 * Complex.log (f y / c)).re = 2 * Real.log ‖f y / c‖ := by
      simp [Complex.mul_re, Complex.log_re]
    simp only [g, Complex.add_re, Complex.ofReal_re, hre]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_div, Real.log_pow,
      Real.log_pow, Real.log_div (norm_ne_zero_iff.mpr hy0) (norm_ne_zero_iff.mpr hz)]
    push_cast
    ring
  rw [smoothDDC_congr heq]
  exact smoothDDC_re_comp_eq_zero hU hg hzU

end

end SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm

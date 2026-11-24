/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PluriharmonicLogNorm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses

/-!
# `ddᶜ log` of the smooth part of a factorized weight

Suppose a nonnegative weight is factorized in two ways as `|h₁|² U₁ = |h₂|² U₂` on an open set
`S`, with `hᵢ` holomorphic, `Uᵢ` smooth and positive, and `h₁` nonvanishing on a dense subset
of `S`.  Then `ddᶜ log U₁ = ddᶜ log U₂` on all of `S` (`smoothDDC_log_eq_of_normSq_mul_eq`):
off the zeros the difference is `log |h₂ / h₁|²`, which is pluriharmonic, and `ddᶜ` of the
smooth difference is continuous.

This is the transition identity for the local weights of `ddᶜ log U` extended across the zero
divisor of `U` (the curvature of the exceptional divisor of a blowup).
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.LogWeightFactorization

open FirstPass

noncomputable section

variable {n : ℕ}

theorem smoothDDC_contDiffOn {h : ComplexModel n → ℝ} {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hh : ContDiffOn ℝ ∞ h U) : ContDiffOn ℝ ∞ (smoothDDC h) U := by
  have hderiv := (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp (smoothDc_contDiffOn hU hh)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ
    (ComplexModel n) ℝ).contDiff.comp_contDiffOn hderiv.2

/-- **Two factorizations of a weight have the same `ddᶜ log` of their smooth parts.** -/
theorem smoothDDC_log_eq_of_normSq_mul_eq {S : Set (ComplexModel n)} (hS : IsOpen S)
    {U₁ U₂ : ComplexModel n → ℝ} {h₁ h₂ : ComplexModel n → ℂ}
    (hU₁ : ContDiffOn ℝ ∞ U₁ S) (hU₂ : ContDiffOn ℝ ∞ U₂ S)
    (hpos₁ : ∀ y ∈ S, 0 < U₁ y) (hpos₂ : ∀ y ∈ S, 0 < U₂ y)
    (hh₁ : DifferentiableOn ℂ h₁ S) (hh₂ : DifferentiableOn ℂ h₂ S)
    (heq : ∀ y ∈ S, Complex.normSq (h₁ y) * U₁ y = Complex.normSq (h₂ y) * U₂ y)
    (hdense : S ⊆ closure {y | y ∈ S ∧ h₁ y ≠ 0}) {z : ComplexModel n} (hz : z ∈ S) :
    smoothDDC (fun y => Real.log (U₁ y)) z = smoothDDC (fun y => Real.log (U₂ y)) z := by
  have hlog₁ : ContDiffOn ℝ ∞ (fun y => Real.log (U₁ y)) S :=
    hU₁.log fun y hy => (hpos₁ y hy).ne'
  have hlog₂ : ContDiffOn ℝ ∞ (fun y => Real.log (U₂ y)) S :=
    hU₂.log fun y hy => (hpos₂ y hy).ne'
  set D : ComplexModel n → ℝ := fun y => Real.log (U₁ y) - Real.log (U₂ y) with hD_def
  have hDs : ContDiffOn ℝ ∞ D S := hlog₁.sub hlog₂
  have hne₂ : ∀ y ∈ S, h₁ y ≠ 0 → h₂ y ≠ 0 := by
    intro y hy h0 h2
    have := heq y hy
    rw [h2, map_zero, zero_mul] at this
    exact (mul_pos (Complex.normSq_pos.mpr h0) (hpos₁ y hy)).ne' this
  have key : ∀ y ∈ S, h₁ y ≠ 0 → smoothDDC D y = 0 := by
    intro y hy h0
    have hc₁ : ContinuousAt h₁ y := (hh₁ y hy).differentiableAt (hS.mem_nhds hy) |>.continuousAt
    have hc₂ : ContinuousAt h₂ y := (hh₂ y hy).differentiableAt (hS.mem_nhds hy) |>.continuousAt
    have hev : ∀ᶠ y' in 𝓝 y, y' ∈ S ∧ h₁ y' ≠ 0 ∧ h₂ y' ≠ 0 :=
      Filter.Eventually.and (hS.mem_nhds hy : ∀ᶠ y' in 𝓝 y, y' ∈ S) ((hc₁.eventually
        (isOpen_ne.mem_nhds h0)).and
        (hc₂.eventually (isOpen_ne.mem_nhds (hne₂ y hy h0))))
    have hq : D =ᶠ[𝓝 y] fun y' => Real.log (Complex.normSq (h₂ y' / h₁ y')) := by
      filter_upwards [hev] with y' hy''
      obtain ⟨hy', h1, h2⟩ := hy''
      have e := heq y' hy'
      have p₁ := Complex.normSq_pos.mpr h1
      have p₂ := Complex.normSq_pos.mpr h2
      have l := congrArg Real.log e
      rw [Real.log_mul p₁.ne' (hpos₁ y' hy').ne', Real.log_mul p₂.ne' (hpos₂ y' hy').ne'] at l
      simp only [hD_def, map_div₀, Real.log_div p₂.ne' p₁.ne']
      linarith
    rw [smoothDDC_congr hq]
    refine PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero ?_ (div_ne_zero (hne₂ y hy h0) h0)
    filter_upwards [hev] with y' hy''
    obtain ⟨hy', h1, -⟩ := hy''
    have := ((hh₂ y' hy').differentiableAt (hS.mem_nhds hy')).mul
      (((hh₁ y' hy').differentiableAt (hS.mem_nhds hy')).inv h1)
    simp only [div_eq_mul_inv]
    exact this
  have hc : ContinuousAt (smoothDDC D) z :=
    ((smoothDDC_contDiffOn hS hDs).continuousOn).continuousAt (hS.mem_nhds hz)
  have hbot := mem_closure_iff_nhdsWithin_neBot.mp (hdense hz)
  have h0 : smoothDDC D z = 0 :=
    tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y (hy : y ∈ {y | y ∈ S ∧ h₁
        y ≠ 0}) =>
        (key y hy.1 hy.2).symm))
  rw [hD_def, PositiveClasses.smoothDDC_sub hS hlog₁ hlog₂ hz] at h0
  exact sub_eq_zero.mp h0

end

end SGPT.Foundations.Analysis.Pending.LogWeightFactorization

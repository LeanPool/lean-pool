/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RadialPolarMass

/-!
# Sign of the cumulative radial kernel difference

For two scales `a ≤ b`, the normalized kernel at scale `b` is the exact
dilation of the kernel at scale `a`.  After passing to the squared-radius
profile, this identifies the weighted cumulative mass at scale `b` up to
radius `s` with the cumulative mass at scale `a` up to the larger radius
`q² s`, where `q = (b + 1) / (a + 1)`.  Positivity of the kernel then gives
the sign needed by the radial Poisson certificate.
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff Topology Interval

namespace SGPT.Foundations.Analysis.Pending.RadialCumulativeSign

open FirstPass
open HolomorphicPullback
open RadialPoissonCertificate

/-- The normalized squared-radius profile is nonnegative. -/
theorem explicitRadialKernelSqProfile_nonneg
    {n : ℕ} (R : ℝ) (hR : 0 < R) (j : ℕ) (s : ℝ) :
    0 ≤ explicitRadialKernelSqProfile (n := n) R hR j s := by
  exact div_nonneg (Real.smoothTransition.nonneg _)
    (explicitRadialRaw_integral_pos (n := n) R hR j).le

/-- In positive complex dimension, dilation of the spatial kernel becomes
the corresponding dilation of its squared-radius profile. -/
theorem explicitRadialKernelSqProfile_scale
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (a b : ℕ)
    {s : ℝ} (hs : 0 ≤ s) :
    explicitRadialKernelSqProfile (n := n) R hR b s =
      (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ (2 * n) *
        explicitRadialKernelSqProfile (n := n) R hR a
          (((((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ 2) * s) := by
  let i : Fin n := ⟨0, hn⟩
  let x : ComplexModel n :=
    EuclideanSpace.single i (Real.sqrt s : ℂ)
  let q : ℝ := ((b : ℝ) + 1) / ((a : ℝ) + 1)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hx : ‖x‖ ^ 2 = s := by
    simp [x, Real.sq_sqrt hs]
  have hqx : ‖q • x‖ ^ 2 = q ^ 2 * s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq, mul_pow, hx]
  have hscale := explicitRadialKernel_scale (n := n) R hR a b x
  rw [explicitRadialKernel_eq_sqProfile_norm_sq,
    explicitRadialKernel_eq_sqProfile_norm_sq,
    finrank_real_complexModel, hx, hqx] at hscale
  exact hscale

/-- Weighted cumulative mass of one normalized squared-radius profile. -/
noncomputable def radialKernelWeightedCumulative
    (n : ℕ) (R : ℝ) (hR : 0 < R) (j : ℕ) (s : ℝ) : ℝ :=
  ∫ t in 0..s, t ^ (n - 1) *
    explicitRadialKernelSqProfile (n := n) R hR j t

/-- Exact scaling law for weighted cumulative radial mass. -/
theorem radialKernelWeightedCumulative_scale
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (a b : ℕ)
    {s : ℝ} (hs : 0 ≤ s) :
    radialKernelWeightedCumulative n R hR b s =
      radialKernelWeightedCumulative n R hR a
        (((((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ 2) * s) := by
  let q : ℝ := ((b : ℝ) + 1) / ((a : ℝ) + 1)
  let c : ℝ := q ^ 2
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  let f : ℝ → ℝ := fun t => t ^ (n - 1) *
    explicitRadialKernelSqProfile (n := n) R hR a t
  calc
    radialKernelWeightedCumulative n R hR b s =
        ∫ t in 0..s, c * f (c * t) := by
      rw [radialKernelWeightedCumulative]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : 0 ≤ t := (uIcc_of_le hs).symm ▸ ht |>.1
      change t ^ (n - 1) *
          explicitRadialKernelSqProfile (n := n) R hR b t =
        c * ((c * t) ^ (n - 1) *
          explicitRadialKernelSqProfile (n := n) R hR a (c * t))
      rw [explicitRadialKernelSqProfile_scale hn R hR a b ht0]
      dsimp [f, c, q]
      have hn' : n = n - 1 + 1 := by omega
      have hpow : (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ (2 * n) =
          ((((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ 2) ^ n :=
        pow_mul _ 2 n
      rw [hpow]
      rw [congrArg (fun k : ℕ =>
        ((((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ 2) ^ k) hn']
      rw [pow_succ, mul_pow]
      ring
    _ = c * ∫ t in 0..s, f (c * t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in 0..c * s, f t := by
      simpa only [smul_eq_mul, mul_zero] using
        (intervalIntegral.smul_integral_comp_mul_left
          (a := (0 : ℝ)) (b := s) f c)
    _ = radialKernelWeightedCumulative n R hR a (c * s) := by
      rfl

/-- Cumulative weighted mass at a fixed scale is monotone on the nonnegative
half-line. -/
theorem radialKernelWeightedCumulative_mono
    {n : ℕ} (R : ℝ) (hR : 0 < R) (j : ℕ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    radialKernelWeightedCumulative n R hR j s ≤
      radialKernelWeightedCumulative n R hR j t := by
  let f : ℝ → ℝ := fun u => u ^ (n - 1) *
    explicitRadialKernelSqProfile (n := n) R hR j u
  have hfcont : Continuous f :=
    (continuous_id.pow _).mul
      (explicitRadialKernelSqProfile_contDiff R hR j).continuous
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 t)] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    simpa [f] using mul_nonneg (pow_nonneg hu.1.le _)
      (explicitRadialKernelSqProfile_nonneg R hR j u)
  unfold radialKernelWeightedCumulative
  exact intervalIntegral.integral_mono_interval le_rfl hs hst
    hf_nonneg
    (hfcont.intervalIntegrable 0 t)

/-- For increasing scale indices, the weighted cumulative difference of the
two normalized radial kernels is nonpositive. -/
theorem radialWeightedCumulative_explicitRadialKernelSqDifference_nonpos
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {s : ℝ} (hs : 0 ≤ s) :
    radialWeightedCumulative n
      (explicitRadialKernelSqDifference (n := n) R hR a b) s ≤ 0 := by
  let q : ℝ := ((b : ℝ) + 1) / ((a : ℝ) + 1)
  have hq : 1 ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) + 1)]
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hqs : s ≤ q ^ 2 * s := by
    nlinarith [sq_nonneg (q - 1)]
  have hmono := radialKernelWeightedCumulative_mono
    (n := n) R hR a hs hqs
  rw [← radialKernelWeightedCumulative_scale hn R hR a b hs] at hmono
  have hka : IntervalIntegrable
      (fun t : ℝ => t ^ (n - 1) *
        explicitRadialKernelSqProfile (n := n) R hR a t)
      volume 0 s :=
    ((continuous_id.pow _).mul
      (explicitRadialKernelSqProfile_contDiff R hR a).continuous).intervalIntegrable 0 s
  have hkb : IntervalIntegrable
      (fun t : ℝ => t ^ (n - 1) *
        explicitRadialKernelSqProfile (n := n) R hR b t)
      volume 0 s :=
    ((continuous_id.pow _).mul
      (explicitRadialKernelSqProfile_contDiff R hR b).continuous).intervalIntegrable 0 s
  change (∫ t in 0..s, t ^ (n - 1) *
    (explicitRadialKernelSqProfile (n := n) R hR a t -
      explicitRadialKernelSqProfile (n := n) R hR b t)) ≤ 0
  rw [show (fun t : ℝ => t ^ (n - 1) *
      (explicitRadialKernelSqProfile (n := n) R hR a t -
        explicitRadialKernelSqProfile (n := n) R hR b t)) =
      fun t => t ^ (n - 1) *
          explicitRadialKernelSqProfile (n := n) R hR a t -
        t ^ (n - 1) *
          explicitRadialKernelSqProfile (n := n) R hR b t by
    funext t
    ring]
  rw [intervalIntegral.integral_sub hka hkb]
  change radialKernelWeightedCumulative n R hR a s -
    radialKernelWeightedCumulative n R hR b s ≤ 0
  linarith

end SGPT.Foundations.Analysis.Pending.RadialCumulativeSign

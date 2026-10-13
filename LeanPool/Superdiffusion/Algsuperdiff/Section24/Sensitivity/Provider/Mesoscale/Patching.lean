/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.DescendantRatio
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Representatives

/-!
# Patching

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Mesoscale patching for the lower coarse-grained ellipticity

The unconditional `lambda` sensitivity estimate applies the conditional per-cube
estimate only on triadic cubes of a *mesoscopic* scale `3^{-h}` and on their
descendants, and then patches the resulting bounds back to the root cube.  On
the coarse depths `0, ..., h-1`, where the conditional estimate is unavailable,
the source uses subadditivity together with `e.bound.one.cube.by.lambdas`.

This module proves the exact Lean form of that patching step.  The multiscale
aggregate `lambda_{t,q}^{-1}(Q; .)` is a normalized weighted aggregate over all
depths `n >= 0` of the descendant maxima

  `M_n(A) = maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - n) A`,

and the two structural facts are:

* `M_h(A) <= 3^{2 t h} lambda_{t,q}^{-1}(Q; A)`, which is exactly
  `e.bound.one.cube.by.lambdas`, obtained by composing CoarseGraining's
  `maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv` with
  `maxDescendant_lambdaSq_inv_le`.

The exact geometric mass `sum_{n<h} w_n = 1 - 3^{-t q h}` of the coarse depths
then makes the coarse block contribute `3^{t q h} - 1` and the mesoscopic block
contribute `1`, so the total factor is exactly `3^{2 t h}` with no further loss.
Combined with `three_rpow_two_mul_mesoscaleDepth_le` this is what produces the
literal constant `6 = 2 * 3` of `lambda_sensitivity_unconditional`; a lossier
patching would produce a larger constant.

It is a *consumption point*, not a proof step of these lemmas, and it must be
discharged at every application.  Every declaration in this module is an
internal helper for the Section 2.4 sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Bridge between CoarseGraining's explicit `Real.rpow` applications and the `^`
notation used by Mathlib's `rpow` lemmas. -/
private theorem rpow_eq_pow' (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## The exact geometric mass of the coarse depths -/

/-- `3^{c n}` as an `n`-th power. -/
private theorem three_rpow_mul_natCast (c : ℝ) (n : ℕ) :
    Real.rpow (3 : ℝ) (c * (n : ℝ)) = (Real.rpow (3 : ℝ) c) ^ n := by
  simp only [rpow_eq_pow']
  rw [← Real.rpow_natCast ((3 : ℝ) ^ c) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- The exact geometric mass of the coarse depths `n = 0, ..., h-1`:
`sum_{n < h} c_{t,q} 3^{-t q n} = 1 - 3^{-t q h}`. -/
theorem sum_geometricWeight_range (t q : ℝ) (htq : 0 < t * q) (h : ℕ) :
    ∑ n ∈ Finset.range h, Ch02.geometricWeight t q n =
      1 - Real.rpow (3 : ℝ) (-(t * q) * (h : ℝ)) := by
  set r : ℝ := Real.rpow (3 : ℝ) (-(t * q)) with hr
  have hrlt : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hw : ∀ n : ℕ, Ch02.geometricWeight t q n = (1 - r) * r ^ n := by
    intro n
    have hpow : Real.rpow (3 : ℝ) (-t * q * (n : ℝ)) = r ^ n := by
      rw [hr, ← three_rpow_mul_natCast]
      congr 1
      ring
    have hdisc : Ch02.geometricDiscount t q = 1 - r := by
      rw [hr, Ch02.geometricDiscount]
      congr 2
      ring
    rw [Ch02.geometricWeight, hdisc, hpow]
  have hpowh : Real.rpow (3 : ℝ) (-(t * q) * (h : ℝ)) = r ^ h := by
    rw [hr, ← three_rpow_mul_natCast]
  rw [hpowh]
  calc ∑ n ∈ Finset.range h, Ch02.geometricWeight t q n
      = ∑ n ∈ Finset.range h, (1 - r) * r ^ n := Finset.sum_congr rfl fun n _ => hw n
    _ = (1 - r) * ∑ n ∈ Finset.range h, r ^ n := by rw [Finset.mul_sum]
    _ = (1 - r) * ((r ^ h - 1) / (r - 1)) := by rw [geom_sum_eq (ne_of_lt hrlt) h]
    _ = 1 - r ^ h := by
        have hne : r - 1 ≠ 0 := sub_ne_zero_of_ne (ne_of_lt hrlt)
        field_simp
        ring

/-! ## `e.bound.one.cube.by.lambdas` at the mesoscopic depth -/

/-- The descendant maximum of the one-cube observable `|sigma_*^{-1}|` at scale
`k` is bounded by the scale weight times the root aggregate.  This is
`e.bound.one.cube.by.lambdas`. -/
theorem maxDescendantSigmaStarInv_le_weight_mul_lambdaSq_inv
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {k : ℤ} {t : ℝ}
    {q : Ch02.MultiscaleExponent} (hk : k ≤ Q.scale) (ht : 0 < t)
    (hq : q.IsAdmissible) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q k A ≤
      multiscaleDescendantWeight Q k t * (Ch02.lambdaSq Q t q A)⁻¹ :=
  (maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv Q A hk ht hq).trans
    (maxDescendant_lambdaSq_inv_le Q A hk ht hq)

/-- The same bound at the mesoscopic depth `h`, with the scale weight computed
as `3^{2 t h}`. -/
theorem maxDescendantSigmaStarInv_mesoscale_le
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) (h : ℕ) {t : ℝ}
    {q : Ch02.MultiscaleExponent} (ht : 0 < t) (hq : q.IsAdmissible) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (h : ℤ)) A ≤
      Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) * (Ch02.lambdaSq Q t q A)⁻¹ := by
  have hk : Q.scale - (h : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le h)
  have hbase := maxDescendantSigmaStarInv_le_weight_mul_lambdaSq_inv Q A hk ht hq
  have hweight : multiscaleDescendantWeight Q (Q.scale - (h : ℤ)) t =
      Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) := by
    rw [multiscaleDescendantWeight]
    congr 1
    have hz : (Q.scale - (Q.scale - (h : ℤ)) : ℤ) = (h : ℤ) := by ring
    rw [hz]
    push_cast
    ring
  rwa [hweight] at hbase

/-! ## Monotonicity of the descendant maxima in the depth -/

/-- The descendant maxima are nondecreasing in the depth: the coarse depths
`n <= h` are dominated by the mesoscopic depth `h`. -/
theorem maxDescendantSigmaStarInv_depth_le
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {n h : ℕ} (hnh : n ≤ h) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A ≤
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (h : ℤ)) A := by
  have hnhz : (n : ℤ) ≤ (h : ℤ) := by exact_mod_cast hnh
  have hlk : Q.scale - (h : ℤ) ≤ Q.scale - (n : ℤ) := by omega
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  exact maxDescendantSigmaStarInvMatrixNormAtScale_le_of_le A Q hlk hk

/-! ## The gauge-free series splitting -/

/-- The exact recombination of the coarse and deep blocks: with
`b = r * G * y`, the coarse mass `1 - G⁻¹` and the deep mass `1` add up to
exactly `b`, with no loss. -/
private theorem coarse_deep_recombine {G b y r : ℝ} (hGpos : 0 < G)
    (hb : b = r * G * y) : (1 - G⁻¹) * b + r * y = b := by
  subst hb
  field_simp
  ring

/-- The gauge-free arithmetic heart of the patching step.  A sequence `M₁` that
is dominated by `M₁ h` on the coarse depths `n <= h` and obeys the ratio bound
`M₁ n <= rho M₀ n` on the deep depths `n >= h` has weighted aggregate bounded by
`(rho * 3^{2 t h} * Y)^{q/2}`, where `Y^{q/2}` is the weighted aggregate of `M₀`
and `M₀ h <= 3^{2 t h} Y`.

The point of the computation is that no constant is lost: the coarse block
carries mass `1 - 3^{-t q h}` and contributes `3^{t q h} - 1`, the deep block
contributes `1`, and the two add up to exactly `3^{t q h}`. -/
private theorem tsum_geometricWeight_le_of_mesoscale_split
    {t q ρ Y : ℝ} (h : ℕ) (M₀ M₁ : ℕ → ℝ)
    (htq : 0 < t * q) (hqpos : 0 < q) (hρ : 0 ≤ ρ) (hY0 : 0 ≤ Y)
    (hM₀ : ∀ n, 0 ≤ M₀ n) (hM₁ : ∀ n, 0 ≤ M₁ n)
    (hs₀ : Summable fun n => Ch02.geometricWeight t q n * Real.rpow (M₀ n) (q / 2))
    (hs₁ : Summable fun n => Ch02.geometricWeight t q n * Real.rpow (M₁ n) (q / 2))
    (hcoarse : ∀ n, n ≤ h → M₁ n ≤ M₁ h)
    (hdeepr : ∀ n, h ≤ n → M₁ n ≤ ρ * M₀ n)
    (hMh : M₀ h ≤ Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) * Y)
    (hYeq : (∑' n : ℕ, Ch02.geometricWeight t q n * Real.rpow (M₀ n) (q / 2)) =
      Real.rpow Y (q / 2)) :
    (∑' n : ℕ, Ch02.geometricWeight t q n * Real.rpow (M₁ n) (q / 2)) ≤
      Real.rpow (ρ * (Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) * Y)) (q / 2) := by
  simp only [rpow_eq_pow'] at hs₀ hs₁ hYeq hMh ⊢
  have hp : (0 : ℝ) < q / 2 := by positivity
  have hwnn : ∀ n : ℕ, 0 ≤ Ch02.geometricWeight t q n := by
    intro n
    simpa [geometricWeight_eq_old] using HCPolySupport.geometricWeight_nonneg n htq.le
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hSnn : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * t * (h : ℝ)) := Real.rpow_nonneg (by norm_num) _
  set G : ℝ := (3 : ℝ) ^ (t * q * (h : ℝ)) with hGdef
  have hG1 : 1 ≤ G := by
    have h0 : ((3 : ℝ) ^ (0 : ℝ)) ≤ (3 : ℝ) ^ (t * q * (h : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_nonneg htq.le hh0)
    rw [Real.rpow_zero] at h0
    rw [hGdef]
    exact h0
  have hGpos : 0 < G := lt_of_lt_of_le zero_lt_one hG1
  have hGpow : ((3 : ℝ) ^ (2 * t * (h : ℝ))) ^ (q / 2) = G := by
    rw [hGdef, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hGinv : (3 : ℝ) ^ (-(t * q) * (h : ℝ)) = G⁻¹ := by
    rw [hGdef, show (-(t * q) * (h : ℝ)) = -(t * q * (h : ℝ)) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  set B : ℝ := ρ * ((3 : ℝ) ^ (2 * t * (h : ℝ)) * Y) with hBdef
  have hB0 : 0 ≤ B := mul_nonneg hρ (mul_nonneg hSnn hY0)
  have hBpow : B ^ (q / 2) = ρ ^ (q / 2) * G * Y ^ (q / 2) := by
    rw [hBdef, Real.mul_rpow hρ (mul_nonneg hSnn hY0), Real.mul_rpow hSnn hY0, hGpow]
    ring
  -- The coarse depths are dominated by `B`.
  have hM1B : ∀ n : ℕ, n ≤ h → M₁ n ≤ B := by
    intro n hn
    refine (hcoarse n hn).trans ((hdeepr h le_rfl).trans ?_)
    rw [hBdef]
    exact mul_le_mul_of_nonneg_left hMh hρ
  -- Head block.
  have hhead : (∑ n ∈ Finset.range h,
        Ch02.geometricWeight t q n * (M₁ n) ^ (q / 2)) ≤ (1 - G⁻¹) * B ^ (q / 2) := by
    have hterm : ∀ n ∈ Finset.range h,
        Ch02.geometricWeight t q n * (M₁ n) ^ (q / 2) ≤
          Ch02.geometricWeight t q n * B ^ (q / 2) := by
      intro n hn
      refine mul_le_mul_of_nonneg_left ?_ (hwnn n)
      exact Real.rpow_le_rpow (hM₁ n) (hM1B n (le_of_lt (Finset.mem_range.mp hn))) hp.le
    calc (∑ n ∈ Finset.range h, Ch02.geometricWeight t q n * (M₁ n) ^ (q / 2))
        ≤ ∑ n ∈ Finset.range h, Ch02.geometricWeight t q n * B ^ (q / 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.range h, Ch02.geometricWeight t q n) * B ^ (q / 2) := by
          rw [← Finset.sum_mul]
      _ = (1 - G⁻¹) * B ^ (q / 2) := by
          rw [sum_geometricWeight_range t q htq h]
          simp only [rpow_eq_pow']
          rw [hGinv]
  -- Deep block.
  have hs₀' : Summable fun m : ℕ =>
      Ch02.geometricWeight t q (m + h) * (M₀ (m + h)) ^ (q / 2) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => Ch02.geometricWeight t q n * (M₀ n) ^ (q / 2)) h).mpr hs₀
  have hs₁' : Summable fun m : ℕ =>
      Ch02.geometricWeight t q (m + h) * (M₁ (m + h)) ^ (q / 2) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => Ch02.geometricWeight t q n * (M₁ n) ^ (q / 2)) h).mpr hs₁
  have htail0 : (∑' m : ℕ,
      Ch02.geometricWeight t q (m + h) * (M₀ (m + h)) ^ (q / 2)) ≤ Y ^ (q / 2) := by
    have hsplit0 := hs₀.sum_add_tsum_nat_add h
    have hhead0 : 0 ≤ ∑ n ∈ Finset.range h,
        Ch02.geometricWeight t q n * (M₀ n) ^ (q / 2) :=
      Finset.sum_nonneg fun n _ => mul_nonneg (hwnn n) (Real.rpow_nonneg (hM₀ n) _)
    rw [← hYeq, ← hsplit0]
    exact le_add_of_nonneg_left hhead0
  have htail : (∑' m : ℕ,
      Ch02.geometricWeight t q (m + h) * (M₁ (m + h)) ^ (q / 2)) ≤
        ρ ^ (q / 2) * Y ^ (q / 2) := by
    have hstep : ∀ m : ℕ,
        Ch02.geometricWeight t q (m + h) * (M₁ (m + h)) ^ (q / 2) ≤
          ρ ^ (q / 2) *
            (Ch02.geometricWeight t q (m + h) * (M₀ (m + h)) ^ (q / 2)) := by
      intro m
      have hle : M₁ (m + h) ≤ ρ * M₀ (m + h) := hdeepr (m + h) (Nat.le_add_left h m)
      have hrp : (M₁ (m + h)) ^ (q / 2) ≤ ρ ^ (q / 2) * (M₀ (m + h)) ^ (q / 2) := by
        rw [← Real.mul_rpow hρ (hM₀ _)]
        exact Real.rpow_le_rpow (hM₁ _) hle hp.le
      calc Ch02.geometricWeight t q (m + h) * (M₁ (m + h)) ^ (q / 2)
          ≤ Ch02.geometricWeight t q (m + h) *
              (ρ ^ (q / 2) * (M₀ (m + h)) ^ (q / 2)) :=
            mul_le_mul_of_nonneg_left hrp (hwnn (m + h))
        _ = ρ ^ (q / 2) *
              (Ch02.geometricWeight t q (m + h) * (M₀ (m + h)) ^ (q / 2)) := by ring
    calc (∑' m : ℕ, Ch02.geometricWeight t q (m + h) * (M₁ (m + h)) ^ (q / 2))
        ≤ ∑' m : ℕ, ρ ^ (q / 2) *
            (Ch02.geometricWeight t q (m + h) * (M₀ (m + h)) ^ (q / 2)) :=
          Summable.tsum_le_tsum hstep hs₁' (hs₀'.mul_left _)
      _ = ρ ^ (q / 2) * ∑' m : ℕ,
            Ch02.geometricWeight t q (m + h) * (M₀ (m + h)) ^ (q / 2) :=
          hs₀'.tsum_mul_left _
      _ ≤ ρ ^ (q / 2) * Y ^ (q / 2) :=
          mul_le_mul_of_nonneg_left htail0 (Real.rpow_nonneg hρ _)
  -- Recombine.
  have hsplit1 := hs₁.sum_add_tsum_nat_add h
  calc (∑' n : ℕ, Ch02.geometricWeight t q n * (M₁ n) ^ (q / 2))
      = (∑ n ∈ Finset.range h, Ch02.geometricWeight t q n * (M₁ n) ^ (q / 2)) +
          ∑' m : ℕ, Ch02.geometricWeight t q (m + h) * (M₁ (m + h)) ^ (q / 2) :=
        hsplit1.symm
    _ ≤ (1 - G⁻¹) * B ^ (q / 2) + ρ ^ (q / 2) * Y ^ (q / 2) := add_le_add hhead htail
    _ = B ^ (q / 2) := coarse_deep_recombine hGpos hBpow

/-! ## The patching estimate -/

/-- **Mesoscale patching, finite exponent.**  If the per-cube ratio estimate
holds on every triadic descendant of `Q` at scales at most `Q.scale - h`, then
the root aggregate `lambda_{t,q}^{-1}` obeys the same ratio bound up to the
single scale factor `3^{2 t h}`. -/
theorem lambdaSqFinite_inv_le_of_deep_descendant_ratio
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {ρ t q : ℝ} (h : ℕ)
    (hρ : 0 ≤ ρ) (ht : 0 < t) (hq : 1 ≤ q)
    (hdeep : ∀ k : ℤ, k ≤ Q.scale - (h : ℤ) → ∀ R ∈ descendantsAtScale Q k,
      coarseSigmaStarInvMatrixNorm R A₁ ≤ ρ * coarseSigmaStarInvMatrixNorm R A₀) :
    (Ch02.lambdaSq Q t (.finite q) A₁)⁻¹ ≤
      ρ * Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
        (Ch02.lambdaSq Q t (.finite q) A₀)⁻¹ := by
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hp : (0 : ℝ) < q / 2 := by positivity
  have htq : (0 : ℝ) < t * q := mul_pos ht hqpos
  have hsq : (0 : ℝ) ≤ t * q := htq.le
  have hqadm : (Ch02.MultiscaleExponent.finite q).IsAdmissible := by simpa using hq
  have hY0 : (0 : ℝ) ≤ (Ch02.lambdaSq Q t (.finite q) A₀)⁻¹ :=
    inv_nonneg.mpr (lambdaSq_finite_nonneg Q A₀ ht hq)
  have hX0 : (0 : ℝ) ≤ (Ch02.lambdaSq Q t (.finite q) A₁)⁻¹ :=
    inv_nonneg.mpr (lambdaSq_finite_nonneg Q A₁ ht hq)
  have hMnn : ∀ (A : TriadicCoeffFamily d) (n : ℕ),
      0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A := by
    intro A n
    exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) A
  have hpow : ∀ A : TriadicCoeffFamily d,
      Real.rpow ((Ch02.lambdaSq Q t (.finite q) A)⁻¹) (q / 2) =
        ∑' n : ℕ, Ch02.geometricWeight t q n *
          Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) A) (q / 2) := by
    intro A
    have hser := lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q t q A hqpos hsq
    simp only [rpow_eq_pow'] at hser ⊢
    rw [← hser, show (-q / 2 : ℝ) = -(q / 2) by ring,
      Real.rpow_neg (lambdaSq_finite_nonneg Q A ht hq),
      Real.inv_rpow (lambdaSq_finite_nonneg Q A ht hq)]
  have hsum : ∀ A : TriadicCoeffFamily d,
      Summable fun n : ℕ => Ch02.geometricWeight t q n *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) A) (q / 2) :=
    fun A => summable_sigmaStarInv_series_pointwiseCoeffField Q A ht hqpos
  -- deep ratio and coarse domination
  have hdeepr : ∀ n : ℕ, h ≤ n →
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁ ≤
        ρ * maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀ := by
    intro n hn
    have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hnz : (h : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    exact maxDescendantSigmaStarInv_le_of_descendant_ratio Q A₀ A₁ hρ hk
      (hdeep (Q.scale - (n : ℤ)) (by omega))
  have hcoarse : ∀ n : ℕ, n ≤ h →
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁ ≤
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (h : ℤ)) A₁ :=
    fun n hn => maxDescendantSigmaStarInv_depth_le Q A₁ hn
  have hMh := maxDescendantSigmaStarInv_mesoscale_le Q A₀ h ht hqadm
  have hkey := tsum_geometricWeight_le_of_mesoscale_split (t := t) (q := q) (ρ := ρ)
    (Y := (Ch02.lambdaSq Q t (.finite q) A₀)⁻¹) h
    (fun n => maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀)
    (fun n => maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁)
    htq hqpos hρ hY0 (hMnn A₀) (hMnn A₁) (hsum A₀) (hsum A₁) hcoarse hdeepr hMh
    (hpow A₀).symm
  rw [← hpow A₁] at hkey
  have hB0 : (0 : ℝ) ≤ ρ * (Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
      (Ch02.lambdaSq Q t (.finite q) A₀)⁻¹) :=
    mul_nonneg hρ (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hY0)
  have hinvpow : ∀ z : ℝ, 0 ≤ z → Real.rpow (Real.rpow z (q / 2)) (2 / q) = z := by
    intro z hz
    simp only [rpow_eq_pow']
    rw [← Real.rpow_mul hz, show q / 2 * (2 / q) = 1 by field_simp]
    exact Real.rpow_one z
  have hfinal : (Ch02.lambdaSq Q t (.finite q) A₁)⁻¹ ≤
      ρ * (Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
        (Ch02.lambdaSq Q t (.finite q) A₀)⁻¹) := by
    calc (Ch02.lambdaSq Q t (.finite q) A₁)⁻¹
        = Real.rpow (Real.rpow ((Ch02.lambdaSq Q t (.finite q) A₁)⁻¹) (q / 2))
            (2 / q) := (hinvpow _ hX0).symm
      _ ≤ Real.rpow (Real.rpow (ρ * (Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
            (Ch02.lambdaSq Q t (.finite q) A₀)⁻¹)) (q / 2)) (2 / q) := by
          simp only [rpow_eq_pow']
          exact Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hkey (by positivity)
      _ = ρ * (Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
            (Ch02.lambdaSq Q t (.finite q) A₀)⁻¹) := hinvpow _ hB0
  calc (Ch02.lambdaSq Q t (.finite q) A₁)⁻¹
      ≤ ρ * (Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
          (Ch02.lambdaSq Q t (.finite q) A₀)⁻¹) := hfinal
    _ = ρ * Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) *
          (Ch02.lambdaSq Q t (.finite q) A₀)⁻¹ := by ring

/-- **Mesoscale patching, endpoint exponent `q = infinity`.** -/
theorem lambdaSqInfinity_inv_le_of_deep_descendant_ratio
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {ρ t : ℝ} (h : ℕ)
    (hρ : 0 ≤ ρ) (ht : 0 < t)
    (hdeep : ∀ k : ℤ, k ≤ Q.scale - (h : ℤ) → ∀ R ∈ descendantsAtScale Q k,
      coarseSigmaStarInvMatrixNorm R A₁ ≤ ρ * coarseSigmaStarInvMatrixNorm R A₀) :
    (Ch02.lambdaSq Q t .infinity A₁)⁻¹ ≤
      ρ * Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) * (Ch02.lambdaSq Q t .infinity A₀)⁻¹ := by
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hS1 : (1 : ℝ) ≤ Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) := by
    simp only [rpow_eq_pow']
    have := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
      (show (0 : ℝ) ≤ 2 * t * (h : ℝ) by positivity)
    simpa using this
  set S : TriadicCoeffFamily d → Set ℝ := fun A =>
    { M : ℝ | ∃ n : ℕ, M = Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A } with hS
  have hval : ∀ A : TriadicCoeffFamily d,
      (Ch02.lambdaSq Q t .infinity A)⁻¹ = sSup (S A) := by
    intro A
    rw [Ch02.lambdaSq_infinity]
    change ((sSup (S A))⁻¹)⁻¹ = sSup (S A)
    exact inv_inv _
  have hbdd0 : BddAbove (S A₀) := lambdaSqInfinity_denominator_valueSet_bddAbove Q A₀ ht.le
  have hne1 : (S A₁).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hMh := maxDescendantSigmaStarInv_mesoscale_le Q A₀ h ht
    (q := Ch02.MultiscaleExponent.infinity) trivial
  rw [hval A₀] at hMh
  have hY0 : (0 : ℝ) ≤ sSup (S A₀) := by
    have hmem : Real.rpow (3 : ℝ) (-2 * t * ((0 : ℕ) : ℝ)) *
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) A₀ ∈ S A₀ :=
      ⟨0, rfl⟩
    refine le_trans ?_ (le_csSup hbdd0 hmem)
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
        (sub_le_self _ (by norm_num)) A₀)
  rw [hval A₁, hval A₀]
  refine csSup_le hne1 ?_
  rintro _ ⟨n, rfl⟩
  have hkn : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hwnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hwle1 : Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) ≤ 1 := by
    simp only [rpow_eq_pow']
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  rcases le_total (h : ℕ) n with hn | hn
  · -- deep depth: use the per-cube ratio
    have hnz : (h : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have hratio := maxDescendantSigmaStarInv_le_of_descendant_ratio Q A₀ A₁ hρ hkn
      (hdeep (Q.scale - (n : ℤ)) (by omega))
    have hmem : Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀ ∈ S A₀ :=
      ⟨n, rfl⟩
    calc Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
            maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁
        ≤ Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
            (ρ * maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀) :=
          mul_le_mul_of_nonneg_left hratio hwnn
      _ = ρ * (Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
            maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀) := by ring
      _ ≤ ρ * sSup (S A₀) := mul_le_mul_of_nonneg_left (le_csSup hbdd0 hmem) hρ
      _ ≤ ρ * Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) * sSup (S A₀) := by
          refine mul_le_mul_of_nonneg_right ?_ hY0
          simpa using mul_le_mul_of_nonneg_left hS1 hρ
  · -- coarse depth: dominate by the mesoscopic depth
    have hmono := maxDescendantSigmaStarInv_depth_le Q A₁ hn
    have hratio := maxDescendantSigmaStarInv_le_of_descendant_ratio Q A₀ A₁ hρ
      (show Q.scale - (h : ℤ) ≤ Q.scale from
        sub_le_self _ (by exact_mod_cast Nat.zero_le h))
      (hdeep (Q.scale - (h : ℤ)) le_rfl)
    have hM1nn : (0 : ℝ) ≤
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁ :=
      maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hkn A₁
    calc Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
            maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁
        ≤ 1 * maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁ :=
          mul_le_mul_of_nonneg_right hwle1 hM1nn
      _ = maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁ := one_mul _
      _ ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (h : ℤ)) A₁ := hmono
      _ ≤ ρ * maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (h : ℤ)) A₀ :=
          hratio
      _ ≤ ρ * (Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) * sSup (S A₀)) :=
          mul_le_mul_of_nonneg_left hMh hρ
      _ = ρ * Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) * sSup (S A₀) := by ring

/-- **Mesoscale patching.**  The per-cube ratio estimate on all triadic
descendants of `Q` at scales at most `Q.scale - h` upgrades to a bound on the
root aggregate `lambda_{t,q}^{-1}` with the single extra factor `3^{2 t h}`, for
every `t > 0` and every admissible `q`, including the endpoint `q = infinity`. -/
theorem lambdaSq_inv_le_of_deep_descendant_ratio
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {ρ t : ℝ}
    {q : Ch02.MultiscaleExponent} (h : ℕ) (hρ : 0 ≤ ρ) (ht : 0 < t)
    (hq : q.IsAdmissible)
    (hdeep : ∀ k : ℤ, k ≤ Q.scale - (h : ℤ) → ∀ R ∈ descendantsAtScale Q k,
      coarseSigmaStarInvMatrixNorm R A₁ ≤ ρ * coarseSigmaStarInvMatrixNorm R A₀) :
    (Ch02.lambdaSq Q t q A₁)⁻¹ ≤
      ρ * Real.rpow (3 : ℝ) (2 * t * (h : ℝ)) * (Ch02.lambdaSq Q t q A₀)⁻¹ := by
  cases q with
  | finite q =>
      exact lambdaSqFinite_inv_le_of_deep_descendant_ratio Q A₀ A₁ h hρ ht
        (by simpa using hq) hdeep
  | infinity =>
      exact lambdaSqInfinity_inv_le_of_deep_descendant_ratio Q A₀ A₁ h hρ ht hdeep

end

end Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale

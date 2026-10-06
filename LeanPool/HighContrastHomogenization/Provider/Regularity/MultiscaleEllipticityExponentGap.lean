/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.ResponseExponentGap
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties

/-!
# High-contrast homogenization: Provider.Regularity.MultiscaleEllipticityExponentGap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exponent-gap control of multiscale ellipticity

The outer-exponent-one ellipticity rows at order `r` are controlled by the
outer-exponent-two rows at every smaller positive order `b`.  The proof is the
same weighted Cauchy--Schwarz argument as the response-error exponent bridge.
-/

namespace HCPolySupport
namespace HighContrast
open scoped BigOperators

noncomputable section

/-- The square of the response-exponent gap factor between orders `b < r`.
This is the whole loss incurred when a `q = 1` quantity at order `r` is read
off the `q = 2` row at the strictly smaller order `b`; it is finite for every
such pair, so no relation between `r` and `2 * b` is ever needed. -/
@[expose]
noncomputable def exponentGapFactor (b r : ℝ) : ℝ :=
  (Book.Ch02.geometricDiscount r 1 *
      (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
      (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹) ^ 2

/-- The response-exponent gap factor is positive on every admissible pair. -/
theorem exponentGapFactor_pos {b r : ℝ} (hb : 0 < b) (hbr : b < r) :
    0 < exponentGapFactor b r := by
  have hr : 0 < r := hb.trans hbr
  have hdisc_r : 0 < Book.Ch02.geometricDiscount r 1 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (by simpa only [mul_one] using hr)
  have hdisc_gap : 0 < Book.Ch02.geometricDiscount (r - b) 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos
        (mul_pos (sub_pos.mpr hbr) (by norm_num : (0 : ℝ) < 2))
  have hdisc_b : 0 < Book.Ch02.geometricDiscount b 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (mul_pos hb (by norm_num : (0 : ℝ) < 2))
  exact pow_pos
    (mul_pos (mul_pos hdisc_r (inv_pos.mpr (Real.sqrt_pos.2 hdisc_gap)))
      (inv_pos.mpr (Real.sqrt_pos.2 hdisc_b))) 2

private theorem sqrt_geometricWeight_two_eq_sqrt_discount_mul_rpow
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Real.sqrt (Book.Ch02.geometricWeight s 2 n) =
      Real.sqrt (Book.Ch02.geometricDiscount s 2) *
        Real.rpow (3 : ℝ) (-s * (n : ℝ)) := by
  have hdisc_nonneg : 0 ≤ Book.Ch02.geometricDiscount s 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      (geometricDiscount_pos (mul_pos hs (by norm_num : (0 : ℝ) < 2))).le
  rw [Book.Ch02.geometricWeight, Real.sqrt_mul hdisc_nonneg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ))) (1 / 2 : ℝ) =
        Real.rpow (3 : ℝ) ((-s * 2 * (n : ℝ)) * (1 / 2 : ℝ)) := by
      exact
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
          (-s * 2 * (n : ℝ)) (1 / 2 : ℝ)).symm
    _ = Real.rpow (3 : ℝ) (-s * (n : ℝ)) := by
      congr 1
      ring

private theorem geometricWeight_one_eq_gap_mul_sqrt_weights
    {b r : ℝ} (hb : 0 < b) (hbr : b < r) (n : ℕ) :
    Book.Ch02.geometricWeight r 1 n =
      (Book.Ch02.geometricDiscount r 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹) *
        Real.sqrt (Book.Ch02.geometricWeight (r - b) 2 n) *
        Real.sqrt (Book.Ch02.geometricWeight b 2 n) := by
  have hgap : 0 < r - b := sub_pos.mpr hbr
  have hdisc_gap_pos : 0 < Book.Ch02.geometricDiscount (r - b) 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (mul_pos hgap (by norm_num : (0 : ℝ) < 2))
  have hdisc_b_pos : 0 < Book.Ch02.geometricDiscount b 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (mul_pos hb (by norm_num : (0 : ℝ) < 2))
  have hsqrt_gap_pos :
      0 < Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2) :=
    Real.sqrt_pos.2 hdisc_gap_pos
  have hsqrt_b_pos : 0 < Real.sqrt (Book.Ch02.geometricDiscount b 2) :=
    Real.sqrt_pos.2 hdisc_b_pos
  have hpow :
      Real.rpow (3 : ℝ) (-r * (n : ℝ)) =
        Real.rpow (3 : ℝ) (-(r - b) * (n : ℝ)) *
          Real.rpow (3 : ℝ) (-b * (n : ℝ)) := by
    calc
      Real.rpow (3 : ℝ) (-r * (n : ℝ)) =
          Real.rpow (3 : ℝ)
            (-(r - b) * (n : ℝ) + -b * (n : ℝ)) := by
        congr 1
        ring
      _ = Real.rpow (3 : ℝ) (-(r - b) * (n : ℝ)) *
          Real.rpow (3 : ℝ) (-b * (n : ℝ)) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
  rw [sqrt_geometricWeight_two_eq_sqrt_discount_mul_rpow hgap,
    sqrt_geometricWeight_two_eq_sqrt_discount_mul_rpow hb]
  unfold Book.Ch02.geometricWeight
  rw [show -r * 1 * (n : ℝ) = -r * (n : ℝ) by ring, hpow]
  field_simp [hsqrt_gap_pos.ne', hsqrt_b_pos.ne']

private theorem weighted_root_series_le
    {b r : ℝ} (hb : 0 < b) (hbr : b < r)
    (M : ℕ → ℝ) (hM : ∀ n, 0 ≤ M n)
    (hsum : Summable (fun n ↦ Book.Ch02.geometricWeight b 2 n * M n)) :
    ∑' n, Book.Ch02.geometricWeight r 1 n * Real.sqrt (M n) ≤
      (Book.Ch02.geometricDiscount r 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹) *
        Real.sqrt (∑' n, Book.Ch02.geometricWeight b 2 n * M n) := by
  let K : ℝ :=
    Book.Ch02.geometricDiscount r 1 *
      (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
      (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹
  let wGap : ℕ → ℝ := fun n ↦ Book.Ch02.geometricWeight (r - b) 2 n
  let wB : ℕ → ℝ := fun n ↦ Book.Ch02.geometricWeight b 2 n
  let f : ℕ → ℝ := fun n ↦ K * Real.sqrt (wGap n)
  let h : ℕ → ℝ := fun n ↦ Real.sqrt (wB n * M n)
  have hgap : 0 < r - b := sub_pos.mpr hbr
  have hdisc_r_pos : 0 < Book.Ch02.geometricDiscount r 1 := by
    have hr : 0 < r := hb.trans hbr
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (by simpa only [mul_one] using hr)
  have hdisc_gap_pos : 0 < Book.Ch02.geometricDiscount (r - b) 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (mul_pos hgap (by norm_num : (0 : ℝ) < 2))
  have hdisc_b_pos : 0 < Book.Ch02.geometricDiscount b 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (mul_pos hb (by norm_num : (0 : ℝ) < 2))
  have hK_pos : 0 < K := by
    dsimp [K]
    exact mul_pos
      (mul_pos hdisc_r_pos (inv_pos.mpr (Real.sqrt_pos.2 hdisc_gap_pos)))
      (inv_pos.mpr (Real.sqrt_pos.2 hdisc_b_pos))
  have hwGap_nonneg : ∀ n, 0 ≤ wGap n := by
    intro n
    dsimp [wGap]
    simpa only [Book.Ch02.geometricWeight_eq_old] using
      (geometricWeight_nonneg n
        (mul_nonneg hgap.le (by norm_num : (0 : ℝ) ≤ 2)))
  have hwB_nonneg : ∀ n, 0 ≤ wB n := by
    intro n
    dsimp [wB]
    simpa only [Book.Ch02.geometricWeight_eq_old] using
      (geometricWeight_nonneg n
        (mul_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 2)))
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact mul_nonneg hK_pos.le (Real.sqrt_nonneg _)
  have hh_nonneg : ∀ n, 0 ≤ h n := fun n ↦ Real.sqrt_nonneg _
  have hf_sq : ∀ n, f n ^ (2 : ℝ) = K ^ 2 * wGap n := by
    intro n
    dsimp [f]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hwGap_nonneg n)]
  have hh_sq : ∀ n, h n ^ (2 : ℝ) = wB n * M n := by
    intro n
    dsimp [h]
    rw [Real.rpow_two,
      Real.sq_sqrt (mul_nonneg (hwB_nonneg n) (hM n))]
  have hfh : ∀ n, f n * h n =
      Book.Ch02.geometricWeight r 1 n * Real.sqrt (M n) := by
    intro n
    dsimp [f, h]
    rw [Real.sqrt_mul (hwB_nonneg n)]
    have hweight := geometricWeight_one_eq_gap_mul_sqrt_weights hb hbr n
    change K * Real.sqrt (wGap n) *
        (Real.sqrt (wB n) * Real.sqrt (M n)) =
      Book.Ch02.geometricWeight r 1 n * Real.sqrt (M n)
    rw [hweight]
    ring
  have hsumGap : Summable wGap := by
    simpa only [wGap, Book.Ch02.geometricWeight_eq_old] using
      (summable_geometricWeight
        (mul_pos hgap (by norm_num : (0 : ℝ) < 2)))
  have hfsum : Summable fun n ↦ f n ^ (2 : ℝ) := by
    have hscaled : Summable (fun n ↦ K ^ 2 * wGap n) :=
      hsumGap.mul_left (K ^ 2)
    convert hscaled using 1
    ext n
    exact hf_sq n
  have hhsum : Summable fun n ↦ h n ^ (2 : ℝ) := by
    convert hsum using 1
    ext n
    exact hh_sq n
  have hcs :=
    Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
      hf_nonneg hh_nonneg hfsum hhsum
  have hweightsGap : ∑' n, wGap n = 1 := by
    simpa only [wGap, Book.Ch02.geometricWeight_eq_old] using
      (tsum_geometricWeight_eq_one
        (mul_pos hgap (by norm_num : (0 : ℝ) < 2)))
  have hfs : ∑' n, f n ^ (2 : ℝ) = K ^ 2 := by
    calc
      ∑' n, f n ^ (2 : ℝ) = ∑' n, K ^ 2 * wGap n := tsum_congr hf_sq
      _ = K ^ 2 * ∑' n, wGap n := by rw [tsum_mul_left]
      _ = K ^ 2 := by rw [hweightsGap, mul_one]
  have hKroot : (K ^ 2) ^ (1 / (2 : ℝ)) = K := by
    simpa only [Real.sqrt_eq_rpow] using Real.sqrt_sq hK_pos.le
  calc
    ∑' n, Book.Ch02.geometricWeight r 1 n * Real.sqrt (M n) =
        ∑' n, f n * h n := by
      apply tsum_congr
      intro n
      exact (hfh n).symm
    _ ≤ (∑' n, f n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' n, h n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hcs
    _ = K * Real.sqrt (∑' n, Book.Ch02.geometricWeight b 2 n * M n) := by
      rw [hfs, hKroot]
      congr 1
      rw [Real.sqrt_eq_rpow]
      congr 1
      apply tsum_congr
      exact hh_sq

/-- The upper `q = 1` ellipticity at order `r` is controlled by the upper
`q = 2` ellipticity at every smaller positive order `b`. -/
theorem LambdaS_le_exponentGap_mul_LambdaSq_finite_two
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {b r : ℝ}
    (hb : 0 < b) (hbr : b < r) :
    Book.Ch02.LambdaS Q r a ≤
      (Book.Ch02.geometricDiscount r 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹) ^ 2 *
        Book.Ch02.LambdaSq Q b (.finite 2) a := by
  let K : ℝ :=
    Book.Ch02.geometricDiscount r 1 *
      (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
      (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹
  let M : ℕ → ℝ := fun n ↦
    Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
  have hM : ∀ n, 0 ≤ M n := by
    intro n
    dsimp [M]
    exact Book.Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hsum : Summable (fun n ↦ Book.Ch02.geometricWeight b 2 n * M n) := by
    simpa [M] using
      (Book.Ch02.summable_B_series_pointwiseCoeffField Q a hb
        (by norm_num : (0 : ℝ) < 2))
  have hroot := weighted_root_series_le hb hbr M hM hsum
  have hleft : Real.rpow (Book.Ch02.LambdaS Q r a) (1 / 2 : ℝ) =
      ∑' n, Book.Ch02.geometricWeight r 1 n * Real.sqrt (M n) := by
    have hseries := Book.Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum
      Q r 1 a (by norm_num : (0 : ℝ) < 1)
        (mul_nonneg (hb.trans hbr).le (by norm_num : (0 : ℝ) ≤ 1))
    simpa only [Book.Ch02.LambdaS, M, Real.sqrt_eq_rpow] using! hseries
  have hright : ∑' n, Book.Ch02.geometricWeight b 2 n * M n =
      Book.Ch02.LambdaSq Q b (.finite 2) a := by
    have hseries := Book.Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum
      Q b 2 a (by norm_num : (0 : ℝ) < 2)
        (mul_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 2))
    simpa [M] using hseries.symm
  have hLambdaS : 0 ≤ Book.Ch02.LambdaS Q r a :=
    Book.Ch02.LambdaSq_finite_nonneg Q a (hb.trans hbr)
      (by norm_num : (1 : ℝ) ≤ 1)
  have hLambdaSq : 0 ≤ Book.Ch02.LambdaSq Q b (.finite 2) a :=
    Book.Ch02.LambdaSq_finite_nonneg Q a hb (by norm_num : (1 : ℝ) ≤ 2)
  have hK_pos : 0 < K := by
    dsimp [K]
    have hr : 0 < r := hb.trans hbr
    have hgap : 0 < r - b := sub_pos.mpr hbr
    exact mul_pos
      (mul_pos
        (by
          simpa only [Book.Ch02.geometricDiscount_eq_old] using
            geometricDiscount_pos (by simpa only [mul_one] using hr))
        (inv_pos.mpr (Real.sqrt_pos.2 (by
          simpa only [Book.Ch02.geometricDiscount_eq_old] using
            geometricDiscount_pos
              (mul_pos hgap (by norm_num : (0 : ℝ) < 2))))))
      (inv_pos.mpr (Real.sqrt_pos.2 (by
        simpa only [Book.Ch02.geometricDiscount_eq_old] using
          geometricDiscount_pos
            (mul_pos hb (by norm_num : (0 : ℝ) < 2)))))
  rw [← hleft, hright] at hroot
  calc
    Book.Ch02.LambdaS Q r a =
        (Real.rpow (Book.Ch02.LambdaS Q r a) (1 / 2 : ℝ)) ^ 2 := by
      symm
      exact HCPolySupport.sq_rpow_half_eq_self_of_nonneg hLambdaS
    _ ≤ (K * Real.sqrt (Book.Ch02.LambdaSq Q b (.finite 2) a)) ^ 2 :=
      (sq_le_sq₀ (Real.rpow_nonneg hLambdaS _) (mul_nonneg hK_pos.le
        (Real.sqrt_nonneg _))).2 hroot
    _ = K ^ 2 * Book.Ch02.LambdaSq Q b (.finite 2) a := by
      rw [mul_pow, Real.sq_sqrt hLambdaSq]
    _ = (Book.Ch02.geometricDiscount r 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹) ^ 2 *
        Book.Ch02.LambdaSq Q b (.finite 2) a := rfl

/-- The inverse lower `q = 1` ellipticity at order `r` is controlled by the
inverse lower `q = 2` ellipticity at every smaller positive order `b`. -/
theorem lambdaS_inv_le_exponentGap_mul_lambdaSq_finite_two_inv
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {b r : ℝ}
    (hb : 0 < b) (hbr : b < r) :
    (Book.Ch02.lambdaS Q r a)⁻¹ ≤
      (Book.Ch02.geometricDiscount r 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹) ^ 2 *
        (Book.Ch02.lambdaSq Q b (.finite 2) a)⁻¹ := by
  let K : ℝ :=
    Book.Ch02.geometricDiscount r 1 *
      (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
      (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹
  let M : ℕ → ℝ := fun n ↦
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
      (Q.scale - (n : ℤ)) a
  have hM : ∀ n, 0 ≤ M n := by
    intro n
    dsimp [M]
    exact Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hsum : Summable (fun n ↦ Book.Ch02.geometricWeight b 2 n * M n) := by
    simpa [M] using
      (Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q a hb
        (by norm_num : (0 : ℝ) < 2))
  have hroot := weighted_root_series_le hb hbr M hM hsum
  have hleft : Real.rpow (Book.Ch02.lambdaS Q r a) (-1 / 2 : ℝ) =
      ∑' n, Book.Ch02.geometricWeight r 1 n * Real.sqrt (M n) := by
    have hseries := Book.Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum
      Q r 1 a (by norm_num : (0 : ℝ) < 1)
        (mul_nonneg (hb.trans hbr).le (by norm_num : (0 : ℝ) ≤ 1))
    simpa only [Book.Ch02.lambdaS, M, Real.sqrt_eq_rpow] using! hseries
  have hright : ∑' n, Book.Ch02.geometricWeight b 2 n * M n =
      (Book.Ch02.lambdaSq Q b (.finite 2) a)⁻¹ := by
    have hseries := Book.Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum
      Q b 2 a (by norm_num : (0 : ℝ) < 2)
        (mul_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 2))
    simpa [M, Real.rpow_neg_one] using hseries.symm
  have hlambdaS : 0 ≤ Book.Ch02.lambdaS Q r a :=
    Book.Ch02.lambdaSq_finite_nonneg Q a (hb.trans hbr)
      (by norm_num : (1 : ℝ) ≤ 1)
  have hlambdaSq : 0 ≤ Book.Ch02.lambdaSq Q b (.finite 2) a :=
    Book.Ch02.lambdaSq_finite_nonneg Q a hb (by norm_num : (1 : ℝ) ≤ 2)
  have hK_pos : 0 < K := by
    dsimp [K]
    have hr : 0 < r := hb.trans hbr
    have hgap : 0 < r - b := sub_pos.mpr hbr
    exact mul_pos
      (mul_pos
        (by
          simpa only [Book.Ch02.geometricDiscount_eq_old] using
            geometricDiscount_pos (by simpa only [mul_one] using hr))
        (inv_pos.mpr (Real.sqrt_pos.2 (by
          simpa only [Book.Ch02.geometricDiscount_eq_old] using
            geometricDiscount_pos
              (mul_pos hgap (by norm_num : (0 : ℝ) < 2))))))
      (inv_pos.mpr (Real.sqrt_pos.2 (by
        simpa only [Book.Ch02.geometricDiscount_eq_old] using
          geometricDiscount_pos
            (mul_pos hb (by norm_num : (0 : ℝ) < 2)))))
  rw [← hleft, hright] at hroot
  calc
    (Book.Ch02.lambdaS Q r a)⁻¹ =
        (Real.rpow (Book.Ch02.lambdaS Q r a) (-1 / 2 : ℝ)) ^ 2 := by
      symm
      exact HCPolySupport.sq_rpow_neg_half_eq_inv_of_nonneg hlambdaS
    _ ≤ (K * Real.sqrt ((Book.Ch02.lambdaSq Q b (.finite 2) a)⁻¹)) ^ 2 :=
      (sq_le_sq₀ (Real.rpow_nonneg hlambdaS _) (mul_nonneg hK_pos.le
        (Real.sqrt_nonneg _))).2 hroot
    _ = K ^ 2 * (Book.Ch02.lambdaSq Q b (.finite 2) a)⁻¹ := by
      rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hlambdaSq)]
    _ = (Book.Ch02.geometricDiscount r 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹) ^ 2 *
        (Book.Ch02.lambdaSq Q b (.finite 2) a)⁻¹ := rfl

end

end HighContrast
end HCPolySupport

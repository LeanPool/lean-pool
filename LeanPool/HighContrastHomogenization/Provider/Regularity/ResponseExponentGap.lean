/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodTail
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.InfinityOne

/-!
# High-contrast homogenization: Provider.Regularity.ResponseExponentGap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Changing the summability exponent of the response error

The normalized response error with outer exponent one is controlled by the
outer-exponent-two error at any strictly smaller fractional order.  The loss is
the geometric-series factor associated with the gap between the two orders.
-/

namespace HCPolySupport
namespace HighContrast

open scoped BigOperators

noncomputable section

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

/-- The `q = 1` response error at order `r` is controlled by the `q = 2`
response error at every smaller positive order `b`. -/
theorem homogenizationErrorOnCube_infinity_one_le_gap_mul_infinity_two
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {b r : ℝ} (hb : 0 < b) (hbr : b < r) :
    Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1) a a0 ≤
      (Book.Ch02.geometricDiscount r 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹) *
        Book.Ch02.HomogenizationErrorOnCube Q b .infinity (.finite 2) a a0 := by
  let K : ℝ :=
    Book.Ch02.geometricDiscount r 1 *
      (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
      (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹
  let wGap : ℕ → ℝ := fun n => Book.Ch02.geometricWeight (r - b) 2 n
  let wB : ℕ → ℝ := fun n => Book.Ch02.geometricWeight b 2 n
  let M : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
      (Q.scale - (n : ℤ)) a a0
  let f : ℕ → ℝ := fun n => K * Real.sqrt (wGap n)
  let g : ℕ → ℝ := fun n => Real.sqrt (wB n * M n)
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
  have hM_nonneg : ∀ n, 0 ≤ M n := by
    intro n
    dsimp [M]
    exact Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (sub_le_self _ (Nat.cast_nonneg n)) a a0
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact mul_nonneg hK_pos.le (Real.sqrt_nonneg _)
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => Real.sqrt_nonneg _
  have hf_sq : ∀ n, f n ^ (2 : ℝ) = K ^ 2 * wGap n := by
    intro n
    dsimp [f]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hwGap_nonneg n)]
  have hg_sq : ∀ n, g n ^ (2 : ℝ) = wB n * M n := by
    intro n
    dsimp [g]
    rw [Real.rpow_two,
      Real.sq_sqrt (mul_nonneg (hwB_nonneg n) (hM_nonneg n))]
  have hfg : ∀ n, f n * g n =
      Book.Ch02.geometricWeight r 1 n * Real.sqrt (M n) := by
    intro n
    dsimp [f, g]
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
  have hsumWM : Summable (fun n => wB n * M n) := by
    simpa only [wB, M] using
      (Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 hb)
  have hfsum : Summable fun n => f n ^ (2 : ℝ) := by
    have hscaled : Summable (fun n => K ^ 2 * wGap n) :=
      hsumGap.mul_left (K ^ 2)
    convert hscaled using 1
    ext n
    exact hf_sq n
  have hgsum : Summable fun n => g n ^ (2 : ℝ) := by
    convert hsumWM using 1
    ext n
    exact hg_sq n
  have hcs :=
    Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
      hf_nonneg hg_nonneg hfsum hgsum
  have hweightsGap : ∑' n, wGap n = 1 := by
    simpa only [wGap, Book.Ch02.geometricWeight_eq_old] using
      (tsum_geometricWeight_eq_one
        (mul_pos hgap (by norm_num : (0 : ℝ) < 2)))
  have hleft : ∑' n, f n * g n =
      Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1) a a0 := by
    rw [Book.Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
    apply tsum_congr
    intro n
    rw [hfg]
    dsimp [M]
    rw [Real.sqrt_eq_rpow]
  have hright : (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      Book.Ch02.HomogenizationErrorOnCube Q b .infinity (.finite 2) a a0 := by
    unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
      Book.Ch02.HomogenizationErrorFinite
    change (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (∑' n, Book.Ch02.geometricWeight b 2 n *
        (Book.Ch02.scaleResponseAtScale Q (Q.scale - (n : ℤ))
          .infinity a a0) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
    congr 1
    apply tsum_congr
    intro n
    rw [hg_sq]
    have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
      sub_le_self _ (Nat.cast_nonneg n)
    have hresponse : M n =
        (Book.Ch02.scaleResponseAtScale Q (Q.scale - (n : ℤ))
          .infinity a a0) ^ (2 : ℝ) := by
      dsimp [M]
      calc
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
            (Q.scale - (n : ℤ)) a a0 =
            (Book.Ch02.scaleResponseAtScale Q (Q.scale - (n : ℤ))
              .infinity a a0) ^ 2 :=
          (Book.Ch02.scaleResponseAtScale_infinity_sq_eq Q hk a a0).symm
        _ = (Book.Ch02.scaleResponseAtScale Q (Q.scale - (n : ℤ))
              .infinity a a0) ^ (2 : ℝ) :=
          (Real.rpow_two _).symm
    exact congrArg
      (fun x : ℝ => Book.Ch02.geometricWeight b 2 n * x) hresponse
  have hfs : ∑' n, f n ^ (2 : ℝ) = K ^ 2 := by
    calc
      ∑' n, f n ^ (2 : ℝ) = ∑' n, K ^ 2 * wGap n := tsum_congr hf_sq
      _ = K ^ 2 * ∑' n, wGap n := by rw [tsum_mul_left]
      _ = K ^ 2 := by rw [hweightsGap, mul_one]
  have hKroot : (K ^ 2) ^ (1 / (2 : ℝ)) = K := by
    simpa only [Real.sqrt_eq_rpow] using Real.sqrt_sq hK_pos.le
  change Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1) a a0 ≤
    K * Book.Ch02.HomogenizationErrorOnCube Q b .infinity (.finite 2) a a0
  rw [← hleft]
  calc
    ∑' n, f n * g n ≤
        (∑' n, f n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hcs
    _ = K * Book.Ch02.HomogenizationErrorOnCube Q b .infinity
        (.finite 2) a a0 := by rw [hfs, hKroot, hright]

end

end HighContrast
end HCPolySupport

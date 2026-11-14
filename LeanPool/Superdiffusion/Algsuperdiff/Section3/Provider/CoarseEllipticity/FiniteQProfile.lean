/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.DiscountBounds
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# FiniteQProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The finite-`q` deterministic profile

This file isolates the geometric-series arithmetic in the lower
coarse-ellipticity estimate of ABK26.  The per-depth deterministic profile is
`C * 3^(gamma n)`.  At every positive finite exponent `q`, its weighted
`ell^(q/2)` aggregate is computed exactly and bounded by

```text
C * (2 * s / (2 * s - gamma))^(2 / q).
```

For `2 <= q`, the outer exponent is at most one and the base is at least one,
so this is at most the printed first-order pole `2 * C * s * (2 * s -
gamma)⁻¹`.  For `q < 2`, the exponent `2 / q` cannot be dropped; this is the
correction adopted in `S33-CGLOWER-POLE-a/b`.  The `q >= 2` specialization is
the deterministic leg vindicated.

## Main declarations

* `finiteQGeometricProfile`: the extremal deterministic depth profile.
* `summable_geometricWeight_mul_finiteQGeometricProfile_rpow`: summability of
  its weighted `q/2` powers.
* `tsum_geometricWeight_mul_finiteQGeometricProfile_rpow_eq`: the exact
  geometric sum.
* `finiteQGeometricProfile_aggregate_eq`: the exact value after the `2/q`
  root.
* `finiteQGeometricProfile_aggregate_le`: the corrected positive-`q` pole.
* `finiteQGeometricProfile_aggregate_le_of_two_le`: the printed pole on
  `2 <= q`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport

noncomputable section

/-- The extremal deterministic profile from the lower multiscale input:
`C * 3^(gamma n)` at depth `n`. -/
def finiteQGeometricProfile (C gamma : ℝ) (n : ℕ) : ℝ :=
  C * (3 : ℝ) ^ (gamma * (n : ℝ))

theorem finiteQGeometricProfile_nonneg {C : ℝ} (hC : 0 ≤ C)
    (gamma : ℝ) (n : ℕ) :
    0 ≤ finiteQGeometricProfile C gamma n :=
  mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)

/-- The common ratio left after the collar `3^(gamma n)` cancels part of the
weight `3^(-s q n)`. -/
def finiteQProfileRatio (s gamma q : ℝ) : ℝ :=
  (3 : ℝ) ^ (-((2 * s - gamma) * (q / 2)))

private theorem finiteQProfileRatio_pos (s gamma q : ℝ) :
    0 < finiteQProfileRatio s gamma q :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem finiteQProfileRatio_lt_one {s gamma q : ℝ}
    (hgap : 0 < 2 * s - gamma) (hq : 0 < q) :
    finiteQProfileRatio s gamma q < 1 := by
  refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
  have hprod : 0 < (2 * s - gamma) * (q / 2) :=
    mul_pos hgap (half_pos hq)
  linarith

private theorem one_sub_finiteQProfileRatio_pos {s gamma q : ℝ}
    (hgap : 0 < 2 * s - gamma) (hq : 0 < q) :
    0 < 1 - finiteQProfileRatio s gamma q := by
  linarith [finiteQProfileRatio_lt_one hgap hq]

private theorem geometricWeight_mul_finiteQGeometricProfile_rpow_eq
    {s q gamma C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma n ^ (q / 2) =
      Book.Ch02.geometricDiscount s q * C ^ (q / 2) *
        finiteQProfileRatio s gamma q ^ n := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hprofile : finiteQGeometricProfile C gamma n ^ (q / 2) =
      C ^ (q / 2) * (3 : ℝ) ^ (gamma * (n : ℝ) * (q / 2)) := by
    rw [finiteQGeometricProfile,
      Real.mul_rpow hC (Real.rpow_nonneg h3.le _),
      ← Real.rpow_mul h3.le]
  have hratio : finiteQProfileRatio s gamma q ^ n =
      (3 : ℝ) ^ (-((2 * s - gamma) * (q / 2)) * (n : ℝ)) := by
    rw [finiteQProfileRatio,
      ← Real.rpow_natCast
        ((3 : ℝ) ^ (-((2 * s - gamma) * (q / 2)))) n,
      ← Real.rpow_mul h3.le]
  calc
    Book.Ch02.geometricWeight s q n *
          finiteQGeometricProfile C gamma n ^ (q / 2) =
        Book.Ch02.geometricDiscount s q * C ^ (q / 2) *
          ((3 : ℝ) ^ (-s * q * (n : ℝ)) *
            (3 : ℝ) ^ (gamma * (n : ℝ) * (q / 2))) := by
      rw [Book.Ch02.geometricWeight, hprofile]
      calc
        _ = Book.Ch02.geometricDiscount s q *
            ((3 : ℝ) ^ (-s * q * (n : ℝ)) *
              (C ^ (q / 2) *
                (3 : ℝ) ^ (gamma * (n : ℝ) * (q / 2)))) :=
          mul_assoc _ _ _
        _ = Book.Ch02.geometricDiscount s q *
            (C ^ (q / 2) *
              ((3 : ℝ) ^ (-s * q * (n : ℝ)) *
                (3 : ℝ) ^ (gamma * (n : ℝ) * (q / 2)))) :=
          congrArg (fun x : ℝ => Book.Ch02.geometricDiscount s q * x)
            (mul_left_comm _ _ _)
        _ = _ := (mul_assoc _ _ _).symm
    _ = Book.Ch02.geometricDiscount s q * C ^ (q / 2) *
          (3 : ℝ) ^
            (-s * q * (n : ℝ) + gamma * (n : ℝ) * (q / 2)) := by
      rw [← Real.rpow_add h3]
    _ = Book.Ch02.geometricDiscount s q * C ^ (q / 2) *
          finiteQProfileRatio s gamma q ^ n := by
      rw [hratio]
      congr 2
      ring

/-- The weighted `q/2` powers of the deterministic profile form a summable
geometric series whenever `q > 0` and `2s - gamma > 0`. -/
theorem summable_geometricWeight_mul_finiteQGeometricProfile_rpow
    {s q gamma C : ℝ} (hC : 0 ≤ C) (hgap : 0 < 2 * s - gamma)
    (hq : 0 < q) :
    Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma n ^ (q / 2) := by
  refine Summable.congr
    ((summable_geometric_of_lt_one
      (finiteQProfileRatio_pos s gamma q).le
      (finiteQProfileRatio_lt_one hgap hq)).mul_left
        (Book.Ch02.geometricDiscount s q * C ^ (q / 2))) ?_
  intro n
  exact (geometricWeight_mul_finiteQGeometricProfile_rpow_eq hC n).symm

/-- Exact geometric-profile aggregation before the outer `2/q` root. -/
theorem tsum_geometricWeight_mul_finiteQGeometricProfile_rpow_eq
    {s q gamma C : ℝ} (hC : 0 ≤ C) (hgap : 0 < 2 * s - gamma)
    (hq : 0 < q) :
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma n ^ (q / 2)) =
      Book.Ch02.geometricDiscount s q * C ^ (q / 2) *
        (1 - finiteQProfileRatio s gamma q)⁻¹ := by
  rw [tsum_congr fun n =>
    geometricWeight_mul_finiteQGeometricProfile_rpow_eq hC n,
    tsum_mul_left,
    tsum_geometric_of_lt_one
      (finiteQProfileRatio_pos s gamma q).le
      (finiteQProfileRatio_lt_one hgap hq)]

/-- Exact geometric-profile aggregation after the outer `2/q` root. -/
theorem finiteQGeometricProfile_aggregate_eq {s q gamma C : ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (hq : 0 < q)
    (hgap : 0 < 2 * s - gamma) :
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma n ^ (q / 2)) ^ (2 / q) =
      C * (Book.Ch02.geometricDiscount s q *
        (1 - finiteQProfileRatio s gamma q)⁻¹) ^ (2 / q) := by
  have hdiscount : 0 ≤ Book.Ch02.geometricDiscount s q :=
    Book.Ch02.book_geometricDiscount_nonneg
      (mul_nonneg hs.le hq.le)
  have hinv : 0 ≤ (1 - finiteQProfileRatio s gamma q)⁻¹ :=
    inv_nonneg.mpr (one_sub_finiteQProfileRatio_pos hgap hq).le
  rw [tsum_geometricWeight_mul_finiteQGeometricProfile_rpow_eq hC hgap hq]
  have hfactor : Book.Ch02.geometricDiscount s q * C ^ (q / 2) *
      (1 - finiteQProfileRatio s gamma q)⁻¹ =
        C ^ (q / 2) * (Book.Ch02.geometricDiscount s q *
          (1 - finiteQProfileRatio s gamma q)⁻¹) := by
    ring
  rw [hfactor,
    Real.mul_rpow (Real.rpow_nonneg hC _) (mul_nonneg hdiscount hinv)]
  congr 1
  rw [← Real.rpow_mul hC]
  have hcancel : q / 2 * (2 / q) = 1 := by
    field_simp
  rw [hcancel, Real.rpow_one]

/-- The geometric-discount ratio is bounded by the algebraic pole
`2s / (2s - gamma)`. -/
private theorem geometricDiscount_mul_profileRatio_inv_le
    {s q gamma : ℝ} (hgamma : 0 ≤ gamma) (hq : 0 < q)
    (hgap : 0 < 2 * s - gamma) :
    Book.Ch02.geometricDiscount s q *
        (1 - finiteQProfileRatio s gamma q)⁻¹ ≤
      2 * s / (2 * s - gamma) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hgapne : 2 * s - gamma ≠ 0 := ne_of_gt hgap
  have hbase1 : (1 : ℝ) ≤ 2 * s / (2 * s - gamma) :=
    (one_le_div hgap).2 (by linarith)
  have hratioPos : 0 < finiteQProfileRatio s gamma q :=
    finiteQProfileRatio_pos s gamma q
  have hden : 0 < 1 - finiteQProfileRatio s gamma q :=
    one_sub_finiteQProfileRatio_pos hgap hq
  have hratioRpow :
      finiteQProfileRatio s gamma q ^ (2 * s / (2 * s - gamma)) =
        (3 : ℝ) ^ (-(s * q)) := by
    rw [finiteQProfileRatio, ← Real.rpow_mul h3.le]
    congr 1
    field_simp
  have hbernoulli := one_add_mul_self_le_rpow_one_add
    (s := finiteQProfileRatio s gamma q - 1) (by linarith)
    (p := 2 * s / (2 * s - gamma)) hbase1
  rw [show (1 : ℝ) + (finiteQProfileRatio s gamma q - 1) =
      finiteQProfileRatio s gamma q by ring,
    hratioRpow] at hbernoulli
  have hnumerator : 1 - (3 : ℝ) ^ (-(s * q)) ≤
      2 * s / (2 * s - gamma) *
        (1 - finiteQProfileRatio s gamma q) := by
    linarith
  calc
    Book.Ch02.geometricDiscount s q *
          (1 - finiteQProfileRatio s gamma q)⁻¹ =
        (1 - (3 : ℝ) ^ (-(s * q))) *
          (1 - finiteQProfileRatio s gamma q)⁻¹ := by
      rw [Book.Ch02.geometricDiscount]
      congr 3
      ring
    _ ≤ (2 * s / (2 * s - gamma) *
          (1 - finiteQProfileRatio s gamma q)) *
          (1 - finiteQProfileRatio s gamma q)⁻¹ :=
      mul_le_mul_of_nonneg_right hnumerator (inv_nonneg.mpr hden.le)
    _ = 2 * s / (2 * s - gamma) := by
      field_simp

/-- The corrected deterministic finite-`q` profile bound.  Its pole order is
`2/q`, and the statement is valid for every `q > 0`. -/
theorem finiteQGeometricProfile_aggregate_le {s q gamma C : ℝ}
    (hC : 0 ≤ C) (hgamma : 0 ≤ gamma) (hs : 0 < s) (hq : 0 < q)
    (hgap : 0 < 2 * s - gamma) :
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma n ^ (q / 2)) ^ (2 / q) ≤
      C * (2 * s / (2 * s - gamma)) ^ (2 / q) := by
  rw [finiteQGeometricProfile_aggregate_eq hC hs hq hgap]
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow ?_
    (geometricDiscount_mul_profileRatio_inv_le hgamma hq hgap)
    (by positivity)
  exact mul_nonneg
    (Book.Ch02.book_geometricDiscount_nonneg
      (mul_nonneg hs.le hq.le))
    (inv_nonneg.mpr (one_sub_finiteQProfileRatio_pos hgap hq).le)

/-- On the ruled range `2 <= q`, the corrected positive-`q` profile reduces to
the printed first-order pole, with the dimension-independent multiplier `2`. -/
theorem finiteQGeometricProfile_aggregate_le_of_two_le
    {s q gamma C : ℝ} (hC : 0 ≤ C) (hgamma : 0 ≤ gamma)
    (hs : 0 < s) (hq : 2 ≤ q) (hgap : 0 < 2 * s - gamma) :
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma n ^ (q / 2)) ^ (2 / q) ≤
      2 * C * s * (2 * s - gamma)⁻¹ := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hbase1 : (1 : ℝ) ≤ 2 * s / (2 * s - gamma) :=
    (one_le_div hgap).2 (by linarith)
  have hexponent : 2 / q ≤ 1 := by
    rw [div_le_one hq0]
    exact hq
  calc
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma n ^ (q / 2)) ^ (2 / q) ≤
        C * (2 * s / (2 * s - gamma)) ^ (2 / q) :=
      finiteQGeometricProfile_aggregate_le hC hgamma hs hq0 hgap
    _ ≤ C * (2 * s / (2 * s - gamma)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_self_of_one_le hbase1 hexponent) hC
    _ = 2 * C * s * (2 * s - gamma)⁻¹ := by
      ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity

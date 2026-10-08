/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormEnergy

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormSummation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scale summation for the diagonal weak estimate

The estimates here perform the geometric summations of the weak-norm bound on
the bad event and of the contribution of the old scales.  They are
stated separately from the variational estimates so that the extended-real
seminorm is converted from scale-by-scale bounds only after summability has
been established.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## From scale bounds to the extended-real seminorm -/

/-- A summable real majorant for the normalized scale terms bounds the
extended-real weak seminorm by the image of its real sum. -/
theorem normalized_adaptedWeakSeminorm_le_of_summable
    {q : Mat d} {t : ℤ} {s : ℝ} {F : Vec d → BlockVec d} {b : ℕ → ℝ}
    (hb0 : ∀ j : ℕ, 0 ≤ b j) (hbsum : Summable b)
    (hscale : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) F) ≤ b j) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm q t s F ≤
      ENNReal.ofReal (∑' j, b j) := by
  rw [ofReal_rpow_mul_adaptedWeakSeminorm]
  calc
    (∑' j : ℕ, ENNReal.ofReal
        ((3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) F))) ≤
        ∑' j : ℕ, ENNReal.ofReal (b j) :=
      ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (hscale j)
    _ = ENNReal.ofReal (∑' j, b j) :=
      (ENNReal.ofReal_tsum_of_nonneg hb0 hbsum).symm

/-! ## The bad branch -/

/-- The two geometric rows in the all-scale estimate have the printed bad
branch bound.  The harmless numerical factor eight is absorbed by the
dimension-only constant in the final lemma. -/
theorem tsum_diagonalWeak_bad_majorant_le
    {s rho delta M : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hbad : delta < M) :
    ∑' j : ℕ,
        ((3 : ℝ) ^ (-(s * (j : ℝ))) +
          Real.sqrt M * (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ)))) ≤
      8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) * Real.sqrt M := by
  set a : ℝ := s - rho / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith only [hs]
  have ha1 : a ≤ 1 := by rw [ha]; linarith only [hs1, hrho]
  have has : a ≤ s := by rw [ha]; linarith only [hrho]
  have hM0 : 0 ≤ M := le_trans hdelta.le hbad.le
  have hsqrtM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hsqrtDelta0 : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta
  have hdeltaSqrt1 : Real.sqrt delta ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hdelta1
  have hinv1 : 1 ≤ (Real.sqrt delta)⁻¹ := by
    exact one_le_inv_iff₀.mpr ⟨hsqrtDelta0, hdeltaSqrt1⟩
  have hsqrtDeltaM : Real.sqrt delta ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt hbad.le
  have hone : 1 ≤ (Real.sqrt delta)⁻¹ * Real.sqrt M := by
    rw [inv_mul_eq_div, le_div_iff₀ hsqrtDelta0]
    simpa using hsqrtDeltaM
  have hMle : Real.sqrt M ≤ (Real.sqrt delta)⁻¹ * Real.sqrt M := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv1 hsqrtM0
  have hcoef : 1 + Real.sqrt M ≤
      2 * ((Real.sqrt delta)⁻¹ * Real.sqrt M) := by
    linarith only [hone, hMle]
  have hsummS := summable_rpow_three_neg (a := s)
    (lt_trans (by linarith only [hrho]) hs) hs1
  have hsummA := summable_rpow_three_neg ha0 ha1
  have hweight : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ))) ≤
        (3 : ℝ) ^ (-(a * (j : ℝ))) := by
    intro j
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      ((neg_le_neg_iff.mpr <|
        mul_le_mul_of_nonneg_right has (Nat.cast_nonneg j)))
  have hsumS : (∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ)))) ≤ 2 / a := by
    exact (hsummS.tsum_le_tsum hweight hsummA).trans
      (tsum_rpow_three_neg_le ha0 ha1)
  have hsumA : (∑' j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ)))) ≤ 2 / a :=
    tsum_rpow_three_neg_le ha0 ha1
  have hsummMA : Summable fun j : ℕ =>
      Real.sqrt M * (3 : ℝ) ^ (-(a * (j : ℝ))) := hsummA.mul_left _
  calc
    (∑' j : ℕ,
        ((3 : ℝ) ^ (-(s * (j : ℝ))) +
          Real.sqrt M * (3 : ℝ) ^ (-(a * (j : ℝ))))) =
        (∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ)))) +
          Real.sqrt M * ∑' j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ))) := by
      rw [Summable.tsum_add hsummS hsummMA, tsum_mul_left]
    _ ≤ 2 / a + Real.sqrt M * (2 / a) :=
      add_le_add hsumS (mul_le_mul_of_nonneg_left hsumA hsqrtM0)
    _ = (1 + Real.sqrt M) * (2 / a) := by ring
    _ ≤ (2 * ((Real.sqrt delta)⁻¹ * Real.sqrt M)) * (2 / a) := by
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) * Real.sqrt M := by
      rw [ha]
      field_simp [ha0.ne']
      ring

/-! ## The good old-scale branch -/

/-- The tail of the two scale-energy rows has the printed good-branch decay.
The shift `n` is the number of scales omitted from the recent window. -/
theorem tsum_diagonalWeak_good_tail_majorant_le
    {s rho delta M : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hgood : M ≤ delta) (n : ℕ) :
    ∑' j : ℕ,
        ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
          Real.sqrt M *
            (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ))))) ≤
      8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
        (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ))) := by
  set a : ℝ := s - rho / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith only [hs]
  have ha1 : a ≤ 1 := by rw [ha]; linarith only [hs1, hrho]
  have has : a ≤ s := by rw [ha]; linarith only [hrho]
  have hs0 : 0 < s := lt_trans (by linarith only [hrho]) hs
  have hsqrtDelta0 : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta
  have hsqrtDelta1 : Real.sqrt delta ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hdelta1
  have hinv1 : 1 ≤ (Real.sqrt delta)⁻¹ :=
    one_le_inv_iff₀.mpr ⟨hsqrtDelta0, hsqrtDelta1⟩
  have hsqrtMDelta : Real.sqrt M ≤ Real.sqrt delta :=
    Real.sqrt_le_sqrt hgood
  have hsqrtM1 : Real.sqrt M ≤ 1 := hsqrtMDelta.trans hsqrtDelta1
  have hsummS0 := summable_rpow_three_neg hs0 hs1
  have hsummA0 := summable_rpow_three_neg ha0 ha1
  have hfactorS : (fun j : ℕ =>
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ))))) =
      fun j : ℕ =>
        (3 : ℝ) ^ (-(s * (n : ℝ))) *
          (3 : ℝ) ^ (-(s * (j : ℝ))) := by
    funext j
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hfactorA : (fun j : ℕ =>
      (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ))))) =
      fun j : ℕ =>
        (3 : ℝ) ^ (-(a * (n : ℝ))) *
          (3 : ℝ) ^ (-(a * (j : ℝ))) := by
    funext j
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hsummS : Summable fun j : ℕ =>
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) := by
    rw [hfactorS]
    exact hsummS0.mul_left _
  have hsummA : Summable fun j : ℕ =>
      (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))) := by
    rw [hfactorA]
    exact hsummA0.mul_left _
  have hweight : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) ≤
        (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))) := by
    intro j
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_le_neg_iff.mpr <|
        mul_le_mul_of_nonneg_right has (by positivity))
  set T : ℝ := (3 : ℝ) ^ (-(a * (n : ℝ))) * (2 / a) with hT
  have hT0 : 0 ≤ T := by
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (div_nonneg (by norm_num) ha0.le)
  have hsumA : (∑' j : ℕ,
      (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ))))) ≤ T :=
    tsum_rpow_three_neg_shift_le ha0 ha1 n
  have hsumS : (∑' j : ℕ,
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ))))) ≤ T :=
    (hsummS.tsum_le_tsum hweight hsummA).trans hsumA
  have hsummMA : Summable fun j : ℕ =>
      Real.sqrt M * (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))) :=
    hsummA.mul_left _
  have hden : 0 < 2 * s - rho := by linarith only [hs]
  have hnum : (8 : ℝ) ≤ 8 * (Real.sqrt delta)⁻¹ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hinv1 (by norm_num : (0 : ℝ) ≤ 8)
  have hquot : (8 : ℝ) / (2 * s - rho) ≤
      8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) :=
    (div_le_div_iff_of_pos_right hden).2 hnum
  have hMT : Real.sqrt M * T ≤ T := by
    calc
      Real.sqrt M * T ≤ 1 * T := mul_le_mul_of_nonneg_right hsqrtM1 hT0
      _ = T := one_mul T
  calc
    (∑' j : ℕ,
        ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
          Real.sqrt M * (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))))) =
        (∑' j : ℕ,
          (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ))))) +
          Real.sqrt M * (∑' j : ℕ,
            (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ))))) := by
      rw [Summable.tsum_add hsummS hsummMA, tsum_mul_left]
    _ ≤ T + Real.sqrt M * T :=
      add_le_add hsumS (mul_le_mul_of_nonneg_left hsumA (Real.sqrt_nonneg _))
    _ ≤ T + T := add_le_add le_rfl hMT
    _ = 2 * T := by ring
    _ = 8 / (2 * s - rho) *
        (3 : ℝ) ^ (-(a * (n : ℝ))) := by
      rw [hT, ha]
      field_simp [ha0.ne']
      ring
    _ ≤ 8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
        (3 : ℝ) ^ (-(a * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hquot (Real.rpow_nonneg (by norm_num) _)

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The bad branch at a released split level. -/
theorem tsum_diagonalWeak_bad_majorant_at_level_le
    {s rho delta M : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1) (hdelta : 0 < delta) (hbad : delta < M) :
    ∑' j : ℕ,
        ((3 : ℝ) ^ (-(s * (j : ℝ))) +
          Real.sqrt M * (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ)))) ≤
      4 * (1 + Real.sqrt delta) * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
        Real.sqrt M := by
  set a : ℝ := s - rho / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith only [hs]
  have ha1 : a ≤ 1 := by rw [ha]; linarith only [hs1, hrho]
  have has : a ≤ s := by rw [ha]; linarith only [hrho]
  have hM0 : 0 ≤ M := le_trans hdelta.le hbad.le
  have hsqrtM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hsqrtDelta0 : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta
  have hsqrtDeltaM : Real.sqrt delta ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt hbad.le
  have hone : 1 ≤ (Real.sqrt delta)⁻¹ * Real.sqrt M := by
    rw [inv_mul_eq_div, le_div_iff₀ hsqrtDelta0]
    simpa using hsqrtDeltaM
  have hcoef : 1 + Real.sqrt M ≤
      (1 + Real.sqrt delta) * ((Real.sqrt delta)⁻¹ * Real.sqrt M) := by
    have hexp : (1 + Real.sqrt delta) *
        ((Real.sqrt delta)⁻¹ * Real.sqrt M) =
        (Real.sqrt delta)⁻¹ * Real.sqrt M + Real.sqrt M := by
      field_simp
    rw [hexp]
    linarith only [hone]
  have hs0 : 0 < s := lt_trans (by linarith only [hrho]) hs
  have hsummS := summable_rpow_three_neg hs0 hs1
  have hsummA := summable_rpow_three_neg ha0 ha1
  have hweight : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ))) ≤ (3 : ℝ) ^ (-(a * (j : ℝ))) := by
    intro j
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      ((neg_le_neg_iff.mpr <|
        mul_le_mul_of_nonneg_right has (Nat.cast_nonneg j)))
  have hsumA : (∑' j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ)))) ≤ 2 / a :=
    tsum_rpow_three_neg_le ha0 ha1
  have hsumS : (∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ)))) ≤ 2 / a :=
    (hsummS.tsum_le_tsum hweight hsummA).trans hsumA
  have hsummMA : Summable fun j : ℕ =>
      Real.sqrt M * (3 : ℝ) ^ (-(a * (j : ℝ))) := hsummA.mul_left _
  calc
    (∑' j : ℕ,
        ((3 : ℝ) ^ (-(s * (j : ℝ))) +
          Real.sqrt M * (3 : ℝ) ^ (-(a * (j : ℝ))))) =
        (∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ)))) +
          Real.sqrt M * ∑' j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ))) := by
      rw [Summable.tsum_add hsummS hsummMA, tsum_mul_left]
    _ ≤ 2 / a + Real.sqrt M * (2 / a) :=
      add_le_add hsumS (mul_le_mul_of_nonneg_left hsumA hsqrtM0)
    _ = (1 + Real.sqrt M) * (2 / a) := by ring
    _ ≤ ((1 + Real.sqrt delta) *
        ((Real.sqrt delta)⁻¹ * Real.sqrt M)) * (2 / a) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 4 * (1 + Real.sqrt delta) * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
        Real.sqrt M := by
      rw [ha]
      field_simp
      ring

/-- The good old-scale tail at a released split level. -/
theorem tsum_diagonalWeak_good_tail_majorant_at_level_le
    {s rho delta M : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1) (hgood : M ≤ delta) (n : ℕ) :
    ∑' j : ℕ,
        ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
          Real.sqrt M *
            (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ))))) ≤
      4 * (1 + Real.sqrt delta) / (2 * s - rho) *
        (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ))) := by
  set a : ℝ := s - rho / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith only [hs]
  have ha1 : a ≤ 1 := by rw [ha]; linarith only [hs1, hrho]
  have has : a ≤ s := by rw [ha]; linarith only [hrho]
  have hs0 : 0 < s := lt_trans (by linarith only [hrho]) hs
  have hsqrtMD : Real.sqrt M ≤ Real.sqrt delta := Real.sqrt_le_sqrt hgood
  have hsummS0 := summable_rpow_three_neg hs0 hs1
  have hsummA0 := summable_rpow_three_neg ha0 ha1
  have hfactorS : (fun j : ℕ =>
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ))))) =
      fun j : ℕ =>
        (3 : ℝ) ^ (-(s * (n : ℝ))) * (3 : ℝ) ^ (-(s * (j : ℝ))) := by
    funext j
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hfactorA : (fun j : ℕ =>
      (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ))))) =
      fun j : ℕ =>
        (3 : ℝ) ^ (-(a * (n : ℝ))) * (3 : ℝ) ^ (-(a * (j : ℝ))) := by
    funext j
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hsummS : Summable fun j : ℕ =>
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) := by
    rw [hfactorS]; exact hsummS0.mul_left _
  have hsummA : Summable fun j : ℕ =>
      (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))) := by
    rw [hfactorA]; exact hsummA0.mul_left _
  have hweight : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) ≤
        (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))) := by
    intro j
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_le_neg_iff.mpr <|
        mul_le_mul_of_nonneg_right has (by positivity))
  set T : ℝ := (3 : ℝ) ^ (-(a * (n : ℝ))) * (2 / a) with hT
  have hT0 : 0 ≤ T := by
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (div_nonneg (by norm_num) ha0.le)
  have hsumA : (∑' j : ℕ,
      (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ))))) ≤ T :=
    tsum_rpow_three_neg_shift_le ha0 ha1 n
  have hsumS : (∑' j : ℕ,
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ))))) ≤ T :=
    (hsummS.tsum_le_tsum hweight hsummA).trans hsumA
  have hsummMA : Summable fun j : ℕ =>
      Real.sqrt M * (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))) :=
    hsummA.mul_left _
  have hMT : Real.sqrt M * T ≤ Real.sqrt delta * T :=
    mul_le_mul_of_nonneg_right hsqrtMD hT0
  calc
    (∑' j : ℕ,
        ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
          Real.sqrt M * (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))))) =
        (∑' j : ℕ, (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ))))) +
          Real.sqrt M * (∑' j : ℕ,
            (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ))))) := by
      rw [Summable.tsum_add hsummS hsummMA, tsum_mul_left]
    _ ≤ T + Real.sqrt M * T :=
      add_le_add hsumS (mul_le_mul_of_nonneg_left hsumA (Real.sqrt_nonneg _))
    _ ≤ T + Real.sqrt delta * T := add_le_add le_rfl hMT
    _ = (1 + Real.sqrt delta) * T := by ring
    _ = 4 * (1 + Real.sqrt delta) / (2 * s - rho) *
        (3 : ℝ) ^ (-(a * (n : ℝ))) := by
      rw [hT, ha]
      field_simp
      ring

end

end Response
end HighContrast
end HCPolySupport

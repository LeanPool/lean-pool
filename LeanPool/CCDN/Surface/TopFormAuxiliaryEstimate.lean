/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer

/-! Uniform coefficient absorption and affine-box estimates for the
auxiliary theorem with an irreducible leading homogeneous form. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For a nonzero integer polynomial `f` of degree `d > 0` with coefficient height `H` and for
`r > 0`, the bad-prime factor of `f` divided by `H^(1/(r d d^(1/r)))` is bounded by a constant
depending only on `r` and the number of variables. -/
theorem hypersurface_badPrime_fractional_height_bound {m r d : ℕ}
    (f : MvPolynomial (Fin (m + 1)) ℤ) (hf : f ≠ 0)
    (hdegree : f.totalDegree = d) (hr : 0 < r) (hd : 0 < d) :
    hypersurfaceBadPrimeFactor f /
        (integerCoefficientHeight f : ℝ) ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      r * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (m + 1) := by
  let H := (integerCoefficientHeight f : ℝ)
  let q := 1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))
  let K := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (m + 1)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hH : 1 ≤ H := by dsimp only [H]; exact_mod_cast integerCoefficientHeight_pos f hf
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  have hb : hypersurfaceBadPrimeFactor f ≤ K * (1 + Real.log H / (d : ℝ) ^ 2) := by
    simpa only [hdegree] using hypersurfaceBadPrimeFactor_le_height f H hH
      (coefficient_abs_le_integerCoefficientHeight f)
  have hratio : (Real.log H + (d : ℝ) ^ 2) / H ^ q ≤ r * (d : ℝ) ^ 2 := by
    simpa only [Real.log_one, zero_add, Real.one_rpow, div_one] using
      hypersurface_logarithmic_height_transfer hr hd (Y := 1) le_rfl hH
  calc
    _ ≤ (K / (d : ℝ) ^ 2) * ((Real.log H + (d : ℝ) ^ 2) / H ^ q) := by
      have hh := div_le_div_of_nonneg_right hb (show 0 ≤ H ^ q by positivity)
      convert hh using 1
      field_simp
      ring
    _ ≤ (K / (d : ℝ) ^ 2) * (r * (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by dsimp only [K]; field_simp

private lemma affine_auxiliary_lower_terms_bound (n : ℕ) {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) ≤
      2 * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hn1 : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hexp : (1 : ℝ) ≤ 4 - 1 / (n + 1 : ℝ) := by
    have hh := (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr hn1
    linarith
  have hdD : (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1 hexp
  let Q := B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hlog : Real.log B ≤ (d : ℝ) ^ (1 / (n + 1 : ℝ)) * Q := by
    have hh := Real.log_le_rpow_div (by linarith : 0 ≤ B)
      (by positivity : (0 : ℝ) < 1 / (d : ℝ) ^ (1 / (n + 1 : ℝ)))
    simpa only [Q, one_div, div_inv_eq_mul, mul_comm] using hh
  have hpowers : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) *
      (d : ℝ) ^ (1 / (n + 1 : ℝ)) = d := by
    rw [← Real.rpow_add hd0, sub_add_cancel, Real.rpow_one]
  have hfirst : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B ≤
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * Q := by
    calc
      _ ≤ (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) *
          ((d : ℝ) ^ (1 / (n + 1 : ℝ)) * Q) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = d * Q := by rw [← mul_assoc, hpowers]
      _ ≤ _ := mul_le_mul_of_nonneg_right hdD (by positivity)
  have hsecond : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) ≤
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * Q :=
    le_mul_of_one_le_right (by positivity) hQ
  change _ ≤ 2 * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * Q
  linarith

/-- A uniform bound on the coefficient-weighted bad-prime factor removes
both the coefficient dependence and the logarithmic box term. -/
theorem affineAuxiliaryDegreeExpression_le_of_badPrime_ratio (n : ℕ) {d : ℕ}
    (hd : 0 < d) {B L b K : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hratio : b / L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) ≤ K) :
    affineAuxiliaryDegreeExpression n d B L b ≤
      (K + 2) * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) *
        B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let Q := B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  have hpowers : (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ 2 =
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) :=
    (rpow_four_sub_eq_mul_sq hd0 n).symm
  have hmain :
      (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
        min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) * Q / L ^ q ≤
      K * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * Q := by
    calc
      _ ≤ (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) * Q / L ^ q := by
        gcongr
        exact min_le_right _ _
      _ = ((d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ 2) * Q * (b / L ^ q) := by ring
      _ ≤ ((d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ 2) * Q * K :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by rw [hpowers]; ring
  have hlower := affine_auxiliary_lower_terms_bound n hd hB
  unfold affineAuxiliaryDegreeExpression
  dsimp only [q, Q] at hmain
  nlinarith only [hmain, hlower]

end
end CCDN

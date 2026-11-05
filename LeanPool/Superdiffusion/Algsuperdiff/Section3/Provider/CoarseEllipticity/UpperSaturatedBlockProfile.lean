/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridWeights
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperSaturatedProfile

/-!
# UpperSaturatedBlockProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Saturated upper-profile budgets after the triadic grid maximum

This module performs deterministic arithmetic on a proposed per-descendant
saturated amplitude.  If the ordinary lane on the strict descendant row
`m - 1 - k` has scale

`C * cstar⁻¹ * min 1 (gamma * (k + 1)) * 3^(gamma * (k + 1))`,

then the `Gamma_1` grid price contributes
`gridNetConst d 1 * (k + 1)`.  Their product is exactly
`upperSaturatedProfile` with a head whose grid multiplier is dimension-only
and whose remaining dependence is `C * cstar⁻¹ * 3^gamma`.  On
`gamma <= 1`, the last factor is at most three.

The row index `k` corresponds to literal source depth `r = k + 1`, so the
source strict-tail weight is `geometricWeight s q (k + 1)`.  The convenient
`k`-weighted profile sum is a deliberate enlargement: it drops the additional
one-step factor `3^(-s*q)` but retains the source normalizer `c_{s,q}`.  The
depth-zero/root term `r = 0` is separate and is not bounded here.

The analytic per-descendant estimate and the root estimate are not proved here.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

/-- The algebraic saturated scale assigned to strict-descendant row `k`.
This definition does not assert an analytic estimate for that row. -/
def upperSaturatedPerCubeAmplitude
    (C cstar gamma : ℝ) (k : ℕ) : ℝ :=
  C * cstar⁻¹ * min 1 (gamma * ((k : ℝ) + 1)) *
    (3 : ℝ) ^ (gamma * ((k : ℝ) + 1))

/-- The algebraic head constant after factoring the `Gamma_1` grid price. -/
def upperSaturatedGridProfileConst
    (d : ℕ) (C cstar gamma : ℝ) : ℝ :=
  gridNetConst d 1 * C * cstar⁻¹ * (3 : ℝ) ^ gamma

/-- An enlargement of the exact head on `gamma <= 1`; it retains the explicit
`C * cstar⁻¹` dependence and only its grid multiplier is dimension-only. -/
def upperSaturatedGridProfileBound
    (d : ℕ) (C cstar : ℝ) : ℝ :=
  3 * gridNetConst d 1 * C * cstar⁻¹

/-- A plain factor `gamma` fits inside the saturated depth factor on
`0 <= gamma <= 1`. -/
theorem gamma_le_min_one_mul_natCast_succ
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) (k : ℕ) :
    gamma ≤ min 1 (gamma * ((k : ℝ) + 1)) := by
  refine le_min hgamma1 ?_
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
  calc
    gamma = gamma * 1 := by ring
    _ ≤ gamma * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hk hgamma

/-- Consequently, an ordinary per-cube term carrying a bare `gamma` is
dominated by the saturated target amplitude. -/
theorem plainGammaPerCubeAmplitude_le_upperSaturated
    {C cstar gamma : ℝ} (hC : 0 ≤ C) (hcstar : 0 ≤ cstar⁻¹)
    (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) (k : ℕ) :
    C * cstar⁻¹ * gamma * (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) ≤
      upperSaturatedPerCubeAmplitude C cstar gamma k := by
  rw [upperSaturatedPerCubeAmplitude]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (gamma_le_min_one_mul_natCast_succ hgamma hgamma1 k)
      (mul_nonneg hC hcstar))
    (Real.rpow_nonneg (by norm_num) _)

theorem upperSaturatedPerCubeAmplitude_nonneg
    {C cstar gamma : ℝ} (hC : 0 ≤ C) (hcstar : 0 ≤ cstar⁻¹)
    (hgamma : 0 ≤ gamma) (k : ℕ) :
    0 ≤ upperSaturatedPerCubeAmplitude C cstar gamma k := by
  rw [upperSaturatedPerCubeAmplitude]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hC hcstar)
      (le_min (by norm_num) (mul_nonneg hgamma (by positivity))))
    (Real.rpow_nonneg (by norm_num) _)

theorem upperSaturatedPerCubeAmplitude_pos
    {C cstar gamma : ℝ} (hC : 0 < C) (hcstar : 0 < cstar)
    (hgamma : 0 < gamma) (k : ℕ) :
    0 < upperSaturatedPerCubeAmplitude C cstar gamma k := by
  rw [upperSaturatedPerCubeAmplitude]
  have hmin : 0 < min 1 (gamma * ((k : ℝ) + 1)) :=
    lt_min one_pos (mul_pos hgamma (by positivity))
  positivity

theorem upperSaturatedGridProfileConst_nonneg
    (d : ℕ) {C cstar gamma : ℝ} (hC : 0 ≤ C)
    (hcstar : 0 ≤ cstar⁻¹) :
    0 ≤ upperSaturatedGridProfileConst d C cstar gamma := by
  rw [upperSaturatedGridProfileConst]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (gridNetConst_nonneg d 1) hC) hcstar)
    (Real.rpow_nonneg (by norm_num) _)


/-- Exact algebraic identity for the grid-priced row.  This indexes the
enlarged profile by `k`; literal source depth for the row is `k + 1`. -/
theorem gridNetConst_mul_upperSaturatedPerCubeAmplitude_eq
    (d : ℕ) (C cstar gamma : ℝ) (k : ℕ) :
    gridNetConst d 1 * (((k : ℝ) + 1) ^ (1 : ℝ)⁻¹) *
        upperSaturatedPerCubeAmplitude C cstar gamma k =
      upperSaturatedProfile
        (upperSaturatedGridProfileConst d C cstar gamma) gamma k := by
  rw [upperSaturatedPerCubeAmplitude, upperSaturatedGridProfileConst,
    upperSaturatedProfile]
  simp only [inv_one, Real.rpow_one]
  rw [show gamma * ((k : ℝ) + 1) = gamma + gamma * (k : ℝ) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring


/-- On the standing small-`gamma` range, the exact grid-profile head is at
most the enlargement retaining `C * cstar⁻¹`; only the grid multiplier is
dimension-only. -/
theorem upperSaturatedGridProfileConst_le_bound
    (d : ℕ) {C cstar gamma : ℝ} (hC : 0 ≤ C)
    (hcstar : 0 ≤ cstar⁻¹) (hgamma1 : gamma ≤ 1) :
    upperSaturatedGridProfileConst d C cstar gamma ≤
      upperSaturatedGridProfileBound d C cstar := by
  have hpow : (3 : ℝ) ^ gamma ≤ 3 := by
    calc
      (3 : ℝ) ^ gamma ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hgamma1
      _ = 3 := Real.rpow_one 3
  have hhead : 0 ≤ gridNetConst d 1 * C * cstar⁻¹ :=
    mul_nonneg
      (mul_nonneg (gridNetConst_nonneg d 1) hC) hcstar
  rw [upperSaturatedGridProfileConst, upperSaturatedGridProfileBound]
  calc
    gridNetConst d 1 * C * cstar⁻¹ * (3 : ℝ) ^ gamma ≤
        gridNetConst d 1 * C * cstar⁻¹ * 3 :=
      mul_le_mul_of_nonneg_left hpow hhead
    _ = 3 * gridNetConst d 1 * C * cstar⁻¹ := by ring


/-- Advancing literal source depth by one extracts exactly one factor
`3^(-s*q)` from the geometric weight.  The normalizer `c_{s,q}` remains on
both sides. -/
theorem geometricWeight_succ_eq_decay_mul
    (s q : ℝ) (k : ℕ) :
    HCPolySupport.Book.Ch02.geometricWeight s q (k + 1) =
      (3 : ℝ) ^ (-s * q) *
        HCPolySupport.Book.Ch02.geometricWeight s q k := by
  rw [HCPolySupport.Book.Ch02.geometricWeight,
    HCPolySupport.Book.Ch02.geometricWeight]
  rw [show -s * q * (((k + 1 : ℕ) : ℝ)) =
      -s * q + (-s * q * (k : ℝ)) by
    push_cast
    ring]
  have hpow :
      Real.rpow (3 : ℝ) (-s * q + (-s * q * (k : ℝ))) =
        Real.rpow (3 : ℝ) (-s * q) *
          Real.rpow (3 : ℝ) (-s * q * (k : ℝ)) := by
    simpa only using!
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
        (-s * q) (-s * q * (k : ℝ)))
  rw [hpow]
  change
    HCPolySupport.Book.Ch02.geometricDiscount s q *
          (Real.rpow (3 : ℝ) (-s * q) *
            Real.rpow (3 : ℝ) (-s * q * (k : ℝ))) =
      Real.rpow (3 : ℝ) (-s * q) *
        (HCPolySupport.Book.Ch02.geometricDiscount s q *
          Real.rpow (3 : ℝ) (-s * q * (k : ℝ)))
  ring

/-- On `0 <= s*q`, the literal strict-tail weight at source depth `k+1` is at
most the enlarged budget weight at index `k`. -/
theorem geometricWeight_succ_le_self
    {s q : ℝ} (hsq : 0 ≤ s * q) (k : ℕ) :
    HCPolySupport.Book.Ch02.geometricWeight s q (k + 1) ≤
      HCPolySupport.Book.Ch02.geometricWeight s q k := by
  have hdecay : (3 : ℝ) ^ (-s * q) ≤ 1 := by
    calc
      (3 : ℝ) ^ (-s * q) ≤ (3 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 := Real.rpow_zero 3
  rw [geometricWeight_succ_eq_decay_mul]
  exact mul_le_of_le_one_left
    (HCPolySupport.geometricWeight_nonneg k hsq) hdecay


/-- The normalized `1 <= q <= 2` aggregate of the `k`-weighted enlarged
strict-tail budget has the cubic pole.  This theorem is about the displayed
enlargement, not the literal source-depth carrier. -/
theorem upperSaturatedGridProfile_enlarged_aggregate_le
    (d : ℕ) {C cstar gamma s q : ℝ}
    (hC : 0 ≤ C) (hcstar : 0 ≤ cstar⁻¹)
    (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hgap : 0 < 2 * s - gamma) :
    (∑' k : ℕ, HCPolySupport.Book.Ch02.geometricWeight s q k *
        (gridNetConst d 1 * (((k : ℝ) + 1) ^ (1 : ℝ)⁻¹) *
          upperSaturatedPerCubeAmplitude C cstar gamma k) ^ (q / 2)) ^
        (2 / q) ≤
      3072 * upperSaturatedGridProfileBound d C cstar * s * gamma *
        (2 * s - gamma)⁻¹ ^ 3 := by
  have hconst : 0 ≤ upperSaturatedGridProfileConst d C cstar gamma :=
    upperSaturatedGridProfileConst_nonneg d hC hcstar
  have hmain :=
    upperSaturatedProfile_aggregate_le_of_one_le_of_le_two
      hconst hgamma hs hs1 hq1 hq2 hgap
  have hrewrite :
      (∑' k : ℕ, HCPolySupport.Book.Ch02.geometricWeight s q k *
          (gridNetConst d 1 * (((k : ℝ) + 1) ^ (1 : ℝ)⁻¹) *
            upperSaturatedPerCubeAmplitude C cstar gamma k) ^ (q / 2)) =
        ∑' k : ℕ, HCPolySupport.Book.Ch02.geometricWeight s q k *
          upperSaturatedProfile
            (upperSaturatedGridProfileConst d C cstar gamma) gamma k ^
              (q / 2) := by
    refine tsum_congr fun k => ?_
    rw [gridNetConst_mul_upperSaturatedPerCubeAmplitude_eq]
  rw [hrewrite]
  refine hmain.trans ?_
  have htail : 0 ≤ s * gamma * (2 * s - gamma)⁻¹ ^ 3 := by
    positivity
  have hhead := upperSaturatedGridProfileConst_le_bound
    d hC hcstar hgamma1
  have hmul := mul_le_mul_of_nonneg_right hhead htail
  calc
    3072 * upperSaturatedGridProfileConst d C cstar gamma * s * gamma *
          (2 * s - gamma)⁻¹ ^ 3 =
        3072 * (upperSaturatedGridProfileConst d C cstar gamma *
          (s * gamma * (2 * s - gamma)⁻¹ ^ 3)) := by ring
    _ ≤ 3072 * (upperSaturatedGridProfileBound d C cstar *
          (s * gamma * (2 * s - gamma)⁻¹ ^ 3)) :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ = 3072 * upperSaturatedGridProfileBound d C cstar * s * gamma *
          (2 * s - gamma)⁻¹ ^ 3 := by ring


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity

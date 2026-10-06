/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.ProjectiveMetric
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridComparison
public import LeanPool.HighContrastHomogenization.Entry.Source.AdaptedBound

/-!
# High-contrast homogenization: Entry.Geometry.BridgeEccentricity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Eccentricities in the successful short bridge

Ordinary support for `p.successful.short.bridge`.
The logarithmic eccentricity comparison follows from the existing projective
triangle inequality, with the identity as its first endpoint. The spectral
positivity receipts are discharged inside that metric API on positive matrices.

The scalar bracket lemmas make the positive length explicit. The final bridge
must supply it from its choice of `L₀ ≥ 1`; it is not a new source hypothesis.
The dimension instance excludes the empty matrix, whose norm product is zero.
All constants in the grid-ratio conclusion precede the coarse exponent and law.

-/

open HCPolySupport.HighContrast (gridRatio)
namespace HCPolySupport.HighContrast.Geometry

open scoped Matrix.Norms.L2Operator

/-- The condition-number expression has positive base on the source domain. -/
theorem one_le_norm_mul_norm_inv {d : ℕ} [NeZero d] {m : Mat d}
    (hm : m.PosDef) : 1 ≤ ‖m‖ * ‖m⁻¹‖ := by
  have h := Source.one_le_source_eccentricity hm
  have hs := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) h
  simpa only [one_mul, Real.mul_self_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    using hs

/-- The logarithm in the bridge hypothesis is nonnegative, with positive argument. -/
theorem log_norm_mul_norm_inv_nonneg {d : ℕ} [NeZero d] {m : Mat d}
    (hm : m.PosDef) : 0 ≤ Real.log (‖m‖ * ‖m⁻¹‖) :=
  Real.log_nonneg (one_le_norm_mul_norm_inv hm)

/-- The square root is the exponential of half the logarithm on the positive domain. -/
theorem eccentricity_eq_exp_half_log {d : ℕ} [NeZero d] {m : Mat d}
    (hm : m.PosDef) :
    Real.sqrt (‖m‖ * ‖m⁻¹‖) = Real.exp (1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖)) := by
  have hp : 0 < ‖m‖ * ‖m⁻¹‖ := zero_lt_one.trans_le (one_le_norm_mul_norm_inv hm)
  have he := Real.exp_log (Real.sqrt_pos.mpr hp)
  rw [Real.log_sqrt hp.le] at he
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using he.symm

/-- The eccentricity assumption forces the source-separation bracket to be nonnegative.
The coefficient is positive because the length is positive. -/
theorem bracket_nonneg_of_eccentricity {d : ℕ} [NeZero d] {m : Mat d}
    (hm : m.PosDef) {c₀ : ℝ} (hc₀ : 0 < c₀) {L : ℕ} (hL : 1 ≤ L)
    {k jStar : ℤ} {B₀ Pi : ℝ}
    (hecc : Real.log (‖m‖ * ‖m⁻¹‖) ≤
      c₀ / (L : ℝ) * ((k : ℝ) - (jStar : ℝ) -
        (⌈B₀ * Real.logb 3 (2 + Pi)⌉ : ℤ))) :
    0 ≤ (k : ℝ) - (jStar : ℝ) - (⌈B₀ * Real.logb 3 (2 + Pi)⌉ : ℤ) := by
  have hLp : 0 < (L : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hL)
  exact (mul_nonneg_iff_of_pos_left (div_pos hc₀ hLp)).mp
    ((log_norm_mul_norm_inv_nonneg hm).trans hecc)

/-- The first printed eccentricity bound. Dropping the factor one half is
legitimate because the exponent is nonnegative. -/
theorem eccentricity_le_exp_of_log_le {d : ℕ} [NeZero d] {m : Mat d}
    (hm : m.PosDef) {t : ℝ} (hecc : Real.log (‖m‖ * ‖m⁻¹‖) ≤ t) :
    Real.sqrt (‖m‖ * ‖m⁻¹‖) ≤ Real.exp t := by
  rw [eccentricity_eq_exp_half_log hm]
  apply Real.exp_le_exp.mpr
  have hlog := log_norm_mul_norm_inv_nonneg hm
  linarith only [hecc, hlog]

/-- Eccentricity changes by at most the exponential of the projective distance.
The positive-definiteness hypotheses feed the attained spectral extrema used by
`projectiveDistance_triangle` and `projectiveDistance_one_eq_log_eccentricity`. -/
theorem eccentricity_le_exp_projectiveDistance_mul {d : ℕ} [NeZero d]
    {m mPlus : Mat d} (hm : m.PosDef) (hmPlus : mPlus.PosDef) :
    Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ≤
      Real.exp (projectiveDistance m mPlus) * Real.sqrt (‖m‖ * ‖m⁻¹‖) := by
  have htri := projectiveDistance_triangle
    (Matrix.PosDef.one : (1 : Mat d).PosDef) hm hmPlus
  rw [projectiveDistance_one_eq_log_eccentricity hm,
    projectiveDistance_one_eq_log_eccentricity hmPlus] at htri
  rw [eccentricity_eq_exp_half_log hmPlus, eccentricity_eq_exp_half_log hm,
    ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa only [add_comm] using htri)

/-- The second eccentricity bound of `p.successful.short.bridge`. -/
theorem eccentricity_le_of_projectiveDistance_le {d : ℕ} [NeZero d]
    {m mPlus : Mat d} (hm : m.PosDef) (hmPlus : mPlus.PosDef)
    (hpr : projectiveDistance m mPlus ≤ 1) :
    Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ≤
      Real.exp 1 * Real.sqrt (‖m‖ * ‖m⁻¹‖) :=
  (eccentricity_le_exp_projectiveDistance_mul hm hmPlus).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hpr) (Real.sqrt_nonneg _))

/-- Choose the Whitney distortion constant using dimension alone, before every
law and geometry parameter. Enlarging it to at least one preserves the bound. -/
theorem exists_gridRatio_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
          projectiveDistance m mPlus ≤ 1 →
            gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ := by
  obtain ⟨C, _hC, hbound⟩ := gridRatio_roundedGrid_le_of_projectiveDistance_le d hd
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro jStar hj m mPlus hm hmPlus hpr
  exact (hbound jStar hj m mPlus hm hmPlus hpr).trans (le_max_right _ _)

end HCPolySupport.HighContrast.Geometry

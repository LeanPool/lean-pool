/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyRowAggregation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyPositiveRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positive fractional energy on convex Whitney rows

The positive fractional row energy consists of the inverse-scale local
`L²` term and the same-cell Gagliardo double integral.  The local `L²`
term splits into its centered part and the contribution of the domain
average.  Cross-row disjointness embeds the diagonal double integrals into
the fractional energy on the whole domain.

The final existential estimate chooses its finite coefficient before the
domain, the Whitney system, and the function.  Thus the coefficient depends
only on the displayed dimension, fractional order, and sandwich radii.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Function

noncomputable section

variable {d : ℕ}

/-- Volume restricted to `U` and rescaled by the inverse of `volume U`. -/
@[expose]
public noncomputable def positiveRowNormalizedDomainMeasure
    (U : Set (Vec d)) : Measure (Vec d) :=
  (volume U)⁻¹ • volume.restrict U

private theorem isProbabilityMeasure_positiveRowNormalizedDomainMeasure
    {U : Set (Vec d)} (hUpos : 0 < volume U) (hUtop : volume U ≠ ⊤) :
    IsProbabilityMeasure (positiveRowNormalizedDomainMeasure U) := by
  refine ⟨?_⟩
  rw [positiveRowNormalizedDomainMeasure, Measure.smul_apply,
    Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hUpos.ne' hUtop

private theorem positiveRow_eLpNorm_two_eq_rpow
    {A : Type*} [MeasurableSpace A]
    {E : Type*} [NormedAddCommGroup E] (f : A → E) (mu : Measure A)
    (hf : AEStronglyMeasurable f mu) :
    eLpNorm f 2 mu =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num

private theorem integral_positiveRowNormalizedDomainMeasure_eq_volumeAverageVec
    {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : Integrable F (volume.restrict U)) :
    ∫ x, F x ∂positiveRowNormalizedDomainMeasure U = volumeAverageVec U F := by
  funext i
  have hproj : ∫ x in U, F x i ∂volume = (∫ x in U, F x ∂volume) i := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) i).integral_comp_comm hF
  rw [positiveRowNormalizedDomainMeasure, integral_smul_measure,
    volumeAverageVec, volumeAverage, Pi.smul_apply, smul_eq_mul,
    ENNReal.toReal_inv, hproj]

private theorem enorm_hilbertVec_sq_positiveRow (v : Vec d) :
    ‖HilbertVec.ofVec v‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (vecNormSq v) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  congr 1
  simpa [vecNormSq, vecDot, HilbertVec.ofVec, PiLp.toLp_apply, pow_two] using
    HilbertVec.norm_sq_eq_sum_sq (HilbertVec.ofVec v)

/-- Jensen's inequality for the domain volume average, in the extended-real
normalization used by the fractional norms. -/
theorem ofReal_vecNormSq_volumeAverageVec_le_eVolumeAverage
    {U : Set (Vec d)} (hUpos : 0 < volume U) (hUtop : volume U ≠ ⊤)
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict U)) :
    ENNReal.ofReal (vecNormSq (volumeAverageVec U F)) ≤
      eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (F x))) := by
  let mu := positiveRowNormalizedDomainMeasure U
  let FH : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (F x)
  have : IsProbabilityMeasure mu :=
    isProbabilityMeasure_positiveRowNormalizedDomainMeasure hUpos hUtop
  have hFHvol : Integrable FH (volume.restrict U) :=
    (HilbertVec.ofVecL d).integrable_comp hF
  have hFHmu : Integrable FH mu := by
    change Integrable FH (positiveRowNormalizedDomainMeasure U)
    exact hFHvol.smul_measure (ENNReal.inv_ne_top.mpr hUpos.ne')
  have hFmu : Integrable F mu := by
    change Integrable F (positiveRowNormalizedDomainMeasure U)
    exact hF.smul_measure (ENNReal.inv_ne_top.mpr hUpos.ne')
  have hL1 : ‖∫ x, FH x ∂mu‖ₑ ≤ ∫⁻ x, ‖FH x‖ₑ ∂mu :=
    enorm_integral_le_lintegral_enorm _
  have hL2 : (∫⁻ x, ‖FH x‖ₑ ∂mu) ≤
      (∫⁻ x, ‖FH x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    have hcmp := eLpNorm_le_eLpNorm_of_exponent_le
      (μ := mu) (p := 1) (q := 2) (f := FH)
      (by norm_num)
    rwa [eLpNorm_one_eq_lintegral_enorm hFHmu.aestronglyMeasurable,
      positiveRow_eLpNorm_two_eq_rpow _ _ hFHmu.aestronglyMeasurable] at hcmp
  have hpow := ENNReal.rpow_le_rpow (hL1.trans hL2)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hmean : ∫ x, FH x ∂mu =
      HilbertVec.ofVec (volumeAverageVec U F) := by
    rw [show ∫ x, FH x ∂mu = HilbertVec.ofVec (∫ x, F x ∂mu) by
      simpa [FH] using (HilbertVec.ofVecL d).integral_comp_comm
        hFmu]
    rw [show ∫ x, F x ∂mu = volumeAverageVec U F by
      exact integral_positiveRowNormalizedDomainMeasure_eq_volumeAverageVec hF]
  rw [← ENNReal.rpow_mul] at hpow
  norm_num at hpow
  rw [hmean] at hpow
  dsimp only [FH] at hpow
  simp_rw [enorm_hilbertVec_sq_positiveRow] at hpow
  simpa [mu, positiveRowNormalizedDomainMeasure, eVolumeAverage,
    lintegral_smul_measure, ENNReal.div_eq_inv_mul, mul_comm] using hpow

/-- A common coefficient for the domain-average and centered fractional
parts of the complete positive row energy. -/
@[expose]
def convexHardyPositiveRowAggregationFactor
    (d : ℕ) (rho Rad s beta : ℝ) (K : ℕ) (n : ℤ) : ℝ≥0∞ :=
  2 * convexHardyCoreRowMassFactor d rho s n +
    (2 * convexHardyWhitneyRowAggregationFactor
      d rho Rad s beta K n + 1)

/-- The shape factor that absorbs the squared domain average into the
volume-scaled `L²` term of the normalized fractional norm. -/
@[expose]
def convexHardyPositiveRowHsShapeFactor
    (d : ℕ) (Rad s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Rad) ^ d) ^ (2 * s / (d : ℝ)) + 1

/-- The shape factor for the normalized fractional norm is finite. -/
theorem convexHardyPositiveRowHsShapeFactor_ne_top
    (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (Rad : ℝ) :
    convexHardyPositiveRowHsShapeFactor d Rad s ≠ ⊤ := by
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hp : 0 ≤ 2 * s / (d : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hs) hdreal.le
  rw [convexHardyPositiveRowHsShapeFactor]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top, by norm_num⟩

/-- The domain mean and fractional seminorm are jointly controlled by the
normalized `Hˢ` norm with a factor depending only on the outer radius. -/
theorem ConvexHardyWhitneySystem.mean_add_fracSeminormSq_le_hsNormSq
    (hd : 1 ≤ d) {U : Set (Vec d)} {rho Rad : ℝ}
    (hRad : 0 < Rad) (system : ConvexHardyWhitneySystem U rho Rad)
    (hUpos : 0 < volume U) (hUtop : volume U ≠ ⊤)
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict U))
    {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (vecNormSq (volumeAverageVec U F)) +
        fracSeminormSq U s F ≤
      convexHardyPositiveRowHsShapeFactor d Rad s * hsNormSq U s F := by
  let p : ℝ := 2 * s / (d : ℝ)
  let B : ℝ≥0∞ := ENNReal.ofReal ((2 * Rad) ^ d) ^ p
  let L : ℝ≥0∞ :=
    eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (F x)))
  let E : ℝ≥0∞ := fracSeminormSq U s F
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hp : 0 ≤ p := by
    dsimp only [p]
    exact div_nonneg (mul_nonneg (by norm_num) hs.le) hdreal.le
  have hvol : volume U ≤ ENNReal.ofReal ((2 * Rad) ^ d) := by
    calc
      volume U ≤ volume (Metric.ball system.center Rad) :=
        measure_mono (system.outer_ball.trans
          (euclideanBallAt_subset_metricBall system.center hRad))
      _ = ENNReal.ofReal ((2 * Rad) ^ d) := volume_ball_eq system.center hRad
  have hvolPow : volume U ^ p ≤ B := by
    exact ENNReal.rpow_le_rpow hvol hp
  have hcancel : volume U ^ p * volume U ^ (-p) = 1 := by
    rw [← ENNReal.rpow_add p (-p) hUpos.ne' hUtop]
    simp only [add_neg_cancel, ENNReal.rpow_zero]
  have hmean : ENNReal.ofReal (vecNormSq (volumeAverageVec U F)) ≤ L := by
    exact ofReal_vecNormSq_volumeAverageVec_le_eVolumeAverage hUpos hUtop hF
  have hscaled : L ≤ B * (volume U ^ (-p) * L) := by
    calc
      L = (volume U ^ p * volume U ^ (-p)) * L := by
        rw [hcancel, one_mul]
      _ = volume U ^ p * (volume U ^ (-p) * L) := by ac_rfl
      _ ≤ B * (volume U ^ (-p) * L) :=
        by simpa only [mul_comm] using
          mul_le_mul_right hvolPow (volume U ^ (-p) * L)
  have hB : B ≤ B + 1 := le_add_right le_rfl
  have hone : (1 : ℝ≥0∞) ≤ B + 1 := le_add_left le_rfl
  have hneg : -(2 * s) / (d : ℝ) = -p := by
    dsimp only [p]
    ring
  calc
    ENNReal.ofReal (vecNormSq (volumeAverageVec U F)) + E ≤ L + E :=
      add_le_add hmean le_rfl
    _ ≤ B * (volume U ^ (-p) * L) + E := add_le_add hscaled le_rfl
    _ = B * (volume U ^ (-p) * L) + 1 * E := by rw [one_mul]
    _ ≤ (B + 1) * (volume U ^ (-p) * L) + (B + 1) * E :=
      add_le_add
        (by simpa only [mul_comm] using
          mul_le_mul_right hB (volume U ^ (-p) * L))
        (by simpa only [mul_comm] using mul_le_mul_right hone E)
    _ = convexHardyPositiveRowHsShapeFactor d Rad s * hsNormSq U s F := by
      rw [convexHardyPositiveRowHsShapeFactor, hsNormSq, hneg, mul_add]

end

end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.TestNorms
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalMeanOscillation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalMeanJump

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fractional control of jumps between volume averages

The difference of the volume averages on two positive finite sets is the
average of the cross differences.  Jensen's inequality on the two normalized
volume measures therefore controls the squared mean jump by the cross
Gagliardo energy.  A union estimate records the volume factor in a form suited
to chains of comparable cells.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

@[expose]
public noncomputable def normalizedSetMeasure (E : Set (Vec d)) :
    Measure (Vec d) :=
  (volume E)⁻¹ • volume.restrict E

private theorem isProbabilityMeasure_normalizedSetMeasure {E : Set (Vec d)}
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤) :
    IsProbabilityMeasure (normalizedSetMeasure E) := by
  refine ⟨?_⟩
  rw [normalizedSetMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hEpos.ne' hEtop

private theorem integrable_normalizedSetMeasure
    {E : Type*} [NormedAddCommGroup E] {V : Set (Vec d)}
    (hVpos : 0 < volume V) {F : Vec d → E}
    (hF : Integrable F (volume.restrict V)) :
    Integrable F (normalizedSetMeasure V) :=
  hF.smul_measure (ENNReal.inv_ne_top.mpr hVpos.ne')

private theorem integral_normalizedSetMeasure_eq_volumeAverageVec
    {E : Set (Vec d)} {G : Vec d → Vec d}
    (hG : Integrable G (volume.restrict E)) :
    ∫ x, G x ∂normalizedSetMeasure E = volumeAverageVec E G := by
  funext i
  have hproj : ∫ x in E, G x i ∂volume = (∫ x in E, G x ∂volume) i := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) i).integral_comp_comm hG
  rw [normalizedSetMeasure, integral_smul_measure, volumeAverageVec, volumeAverage,
    Pi.smul_apply, smul_eq_mul, ENNReal.toReal_inv, hproj]

private theorem eLpNorm_two_eq_rpow
    {A : Type*} [MeasurableSpace A]
    {E : Type*} [NormedAddCommGroup E] (f : A → E) (mu : Measure A)
    (hf : AEStronglyMeasurable f mu) :
    eLpNorm f 2 mu = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num

private theorem enorm_integral_rpow_two_le
    {A : Type*} [MeasurableSpace A]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure A) [IsProbabilityMeasure mu]
    {f : A → E} (hf : Integrable f mu) :
    ‖∫ x, f x ∂mu‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu := by
  have hL1 : ‖∫ x, f x ∂mu‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂mu :=
    enorm_integral_le_lintegral_enorm _
  have hL2 : (∫⁻ x, ‖f x‖ₑ ∂mu) ≤
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    have hcmp := eLpNorm_le_eLpNorm_of_exponent_le
      (μ := mu) (p := 1) (q := 2) (f := f)
      (by norm_num)
    rwa [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
      eLpNorm_two_eq_rpow _ _ hf.aestronglyMeasurable] at hcmp
  have hpow := ENNReal.rpow_le_rpow (hL1.trans hL2) (by norm_num : (0 : ℝ) ≤ 2)
  refine hpow.trans (le_of_eq ?_)
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem enorm_sub_integral_rpow_two_le
    {A : Type*} [MeasurableSpace A]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure A) [IsProbabilityMeasure mu]
    {f : A → E} (hf : Integrable f mu) (x : A) :
    ‖f x - ∫ y, f y ∂mu‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ y, ‖f x - f y‖ₑ ^ (2 : ℝ) ∂mu := by
  have hdiff : Integrable (fun y => f x - f y) mu :=
    (integrable_const _).sub hf
  have hint : ∫ y, (f x - f y) ∂mu = f x - ∫ y, f y ∂mu := by
    rw [integral_sub (integrable_const _) hf, integral_const]
    simp
  rw [← hint]
  exact enorm_integral_rpow_two_le mu hdiff

private theorem enorm_hilbertVec_sub_sq (v w : Vec d) :
    ‖HilbertVec.ofVec v - HilbertVec.ofVec w‖ₑ ^ (2 : ℕ) =
      ENNReal.ofReal (vecNormSq (v - w)) := by
  have hsub : HilbertVec.ofVec v - HilbertVec.ofVec w =
      HilbertVec.ofVec (v - w) :=
    ((HilbertVec.ofVecL d).map_sub v w).symm
  rw [hsub, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  congr 1
  simpa [vecNormSq, vecDot, HilbertVec.ofVec, PiLp.toLp_apply, pow_two] using
    HilbertVec.norm_sq_eq_sum_sq (HilbertVec.ofVec (v - w))

/-- The squared jump between two volume averages is bounded by the normalized
cross average of the pointwise squared differences. -/
theorem ofReal_vecNormSq_sub_volumeAverageVec_le_crossAverage
    {E F : Set (Vec d)}
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    (hFpos : 0 < volume F) (hFtop : volume F ≠ ⊤)
    {G : Vec d → Vec d}
    (hGE : Integrable G (volume.restrict E))
    (hGF : Integrable G (volume.restrict F)) :
    ENNReal.ofReal
        (vecNormSq (volumeAverageVec E G - volumeAverageVec F G)) ≤
      (volume E)⁻¹ * (volume F)⁻¹ *
        ∫⁻ x in E, ∫⁻ y in F,
          ENNReal.ofReal (vecNormSq (G x - G y)) ∂volume := by
  let muE := normalizedSetMeasure E
  let muF := normalizedSetMeasure F
  let GH : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (G x)
  let mF : HilbertVec d := ∫ y, GH y ∂muF
  have hmuE : IsProbabilityMeasure muE :=
    isProbabilityMeasure_normalizedSetMeasure hEpos hEtop
  have hmuF : IsProbabilityMeasure muF :=
    isProbabilityMeasure_normalizedSetMeasure hFpos hFtop
  have hGHEvol : Integrable GH (volume.restrict E) :=
    (HilbertVec.ofVecL d).integrable_comp hGE
  have hGHFvol : Integrable GH (volume.restrict F) :=
    (HilbertVec.ofVecL d).integrable_comp hGF
  have hGHE : Integrable GH muE := by
    exact integrable_normalizedSetMeasure hEpos hGHEvol
  have hGHF : Integrable GH muF := by
    exact integrable_normalizedSetMeasure hFpos hGHFvol
  have houterInt : Integrable (fun x => GH x - mF) muE :=
    hGHE.sub (integrable_const _)
  have houter := enorm_integral_rpow_two_le muE houterInt
  have hinner : ∀ x,
      ‖GH x - mF‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ y, ‖GH x - GH y‖ₑ ^ (2 : ℝ) ∂muF :=
    enorm_sub_integral_rpow_two_le muF hGHF
  have hmeans :
      ∫ x, (GH x - mF) ∂muE =
        HilbertVec.ofVec
          (volumeAverageVec E G - volumeAverageVec F G) := by
    rw [integral_sub hGHE (integrable_const _), integral_const]
    simp
    change (∫ x, GH x ∂muE) - (∫ y, GH y ∂muF) = _
    rw [show ∫ x, GH x ∂muE =
        HilbertVec.ofVec (∫ x, G x ∂muE) by
          simpa [GH] using (HilbertVec.ofVecL d).integral_comp_comm
            (integrable_normalizedSetMeasure hEpos hGE),
      show ∫ y, GH y ∂muF =
        HilbertVec.ofVec (∫ y, G y ∂muF) by
          simpa [GH] using (HilbertVec.ofVecL d).integral_comp_comm
            (integrable_normalizedSetMeasure hFpos hGF),
      integral_normalizedSetMeasure_eq_volumeAverageVec hGE,
      integral_normalizedSetMeasure_eq_volumeAverageVec hGF]
  have hjensen :
      ‖HilbertVec.ofVec
          (volumeAverageVec E G - volumeAverageVec F G)‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ x, (∫⁻ y, ‖GH x - GH y‖ₑ ^ (2 : ℝ) ∂muF) ∂muE := by
    rw [← hmeans]
    exact houter.trans (lintegral_mono hinner)
  norm_num at hjensen
  dsimp only [GH] at hjensen
  simp_rw [enorm_hilbertVec_sub_sq] at hjensen
  calc
    ENNReal.ofReal
        (vecNormSq (volumeAverageVec E G - volumeAverageVec F G)) ≤
        ∫⁻ x, (∫⁻ y,
          ENNReal.ofReal (vecNormSq (G x - G y)) ∂muF) ∂muE := hjensen
    _ = (volume E)⁻¹ * (volume F)⁻¹ *
        ∫⁻ x in E, ∫⁻ y in F,
          ENNReal.ofReal (vecNormSq (G x - G y)) ∂volume := by
      simp only [muE, muF, normalizedSetMeasure, lintegral_smul_measure,
        smul_eq_mul]
      rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hFpos.ne')]
      ac_rfl

private theorem ofReal_le_cross_diameter_kernel
    {a r s D : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hD : 0 < D) (hs : 0 ≤ s) (hd : 1 ≤ d)
    (hrD : r ≤ D) (hrzero : r = 0 → a = 0) :
    ENNReal.ofReal a ≤
      ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s)) *
        ENNReal.ofReal (a / r ^ ((d : ℝ) + 2 * s)) := by
  have hexp : 0 ≤ (d : ℝ) + 2 * s := by
    have hdreal : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  by_cases hr0 : r = 0
  · rw [hrzero hr0]
    simp only [ENNReal.ofReal_zero]
    exact bot_le
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hrpowpos : 0 < r ^ ((d : ℝ) + 2 * s) :=
      Real.rpow_pos_of_pos hrpos _
    have hreal :
        a ≤ D ^ ((d : ℝ) + 2 * s) *
          (a / r ^ ((d : ℝ) + 2 * s)) := by
      calc
        a = r ^ ((d : ℝ) + 2 * s) *
            (a / r ^ ((d : ℝ) + 2 * s)) := by
          rw [mul_div_cancel₀ a hrpowpos.ne']
        _ ≤ D ^ ((d : ℝ) + 2 * s) *
            (a / r ^ ((d : ℝ) + 2 * s)) := by
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hr hrD hexp)
            (div_nonneg ha hrpowpos.le)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- A cross-diameter bound inserts the fractional Gagliardo kernel into the
mean-jump estimate. -/
theorem ofReal_vecNormSq_sub_volumeAverageVec_le_crossFracIntegral
    (hd : 1 ≤ d) {E F : Set (Vec d)}
    (hEmeas : MeasurableSet E) (hFmeas : MeasurableSet F)
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    (hFpos : 0 < volume F) (hFtop : volume F ≠ ⊤)
    {G : Vec d → Vec d}
    (hGE : Integrable G (volume.restrict E))
    (hGF : Integrable G (volume.restrict F))
    {s D : ℝ} (hs : 0 ≤ s) (hD : 0 < D)
    (hcrossDiam : ∀ x ∈ E, ∀ y ∈ F,
      Real.sqrt (vecNormSq (x - y)) ≤ D) :
    ENNReal.ofReal
        (vecNormSq (volumeAverageVec E G - volumeAverageVec F G)) ≤
      (volume E)⁻¹ * (volume F)⁻¹ *
        ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s)) *
          ∫⁻ x in E, ∫⁻ y in F, ENNReal.ofReal
            (vecNormSq (G x - G y) /
              Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume := by
  let C : ℝ≥0∞ := ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s))
  have hinner : ∀ x ∈ E,
      (∫⁻ y in F, ENNReal.ofReal (vecNormSq (G x - G y)) ∂volume) ≤
        C * ∫⁻ y in F, ENNReal.ofReal
          (vecNormSq (G x - G y) /
            Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume := by
    intro x hx
    calc
      (∫⁻ y in F, ENNReal.ofReal (vecNormSq (G x - G y)) ∂volume) ≤
          ∫⁻ y in F, C * ENNReal.ofReal
            (vecNormSq (G x - G y) /
              Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume := by
        exact setLIntegral_mono' hFmeas fun y hy => by
          apply ofReal_le_cross_diameter_kernel
          · exact vecNormSq_nonneg (G x - G y)
          · exact Real.sqrt_nonneg _
          · exact hD
          · exact hs
          · exact hd
          · exact hcrossDiam x hx y hy
          · intro hzero
            have hsq : vecNormSq (x - y) = 0 :=
              (Real.sqrt_eq_zero (vecNormSq_nonneg (x - y))).mp hzero
            have hxy : x = y := sub_eq_zero.mp (vecNormSq_eq_zero_iff.mp hsq)
            rw [hxy, sub_self, vecNormSq_eq_zero_iff.mpr rfl]
      _ = C * ∫⁻ y in F, ENNReal.ofReal
          (vecNormSq (G x - G y) /
            Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume :=
        lintegral_const_mul' C _ ENNReal.ofReal_ne_top
  have hcross :
      (∫⁻ x in E, ∫⁻ y in F,
          ENNReal.ofReal (vecNormSq (G x - G y)) ∂volume) ≤
        C * ∫⁻ x in E, ∫⁻ y in F, ENNReal.ofReal
          (vecNormSq (G x - G y) /
            Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume := by
    calc
      (∫⁻ x in E, ∫⁻ y in F,
          ENNReal.ofReal (vecNormSq (G x - G y)) ∂volume) ≤
          ∫⁻ x in E, C * ∫⁻ y in F, ENNReal.ofReal
            (vecNormSq (G x - G y) /
              Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume :=
        setLIntegral_mono' hEmeas hinner
      _ = C * ∫⁻ x in E, ∫⁻ y in F, ENNReal.ofReal
          (vecNormSq (G x - G y) /
            Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume :=
        lintegral_const_mul' C _ ENNReal.ofReal_ne_top
  calc
    ENNReal.ofReal
        (vecNormSq (volumeAverageVec E G - volumeAverageVec F G)) ≤
        (volume E)⁻¹ * (volume F)⁻¹ *
          ∫⁻ x in E, ∫⁻ y in F,
            ENNReal.ofReal (vecNormSq (G x - G y)) ∂volume :=
      ofReal_vecNormSq_sub_volumeAverageVec_le_crossAverage
        hEpos hEtop hFpos hFtop hGE hGF
    _ ≤ (volume E)⁻¹ * (volume F)⁻¹ *
        (C * ∫⁻ x in E, ∫⁻ y in F, ENNReal.ofReal
          (vecNormSq (G x - G y) /
            Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume) :=
      mul_le_mul_right hcross _
    _ = _ := by simp only [C, mul_assoc]

/-- On the union of two sets, the cross mean jump is controlled by the
fractional seminorm with the exact symmetric volume factor
`volume(E)⁻¹ + volume(F)⁻¹`. -/
theorem ofReal_vecNormSq_sub_volumeAverageVec_le_unionFracSeminormSq
    (hd : 1 ≤ d) {E F : Set (Vec d)}
    (hEmeas : MeasurableSet E) (hFmeas : MeasurableSet F)
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    (hFpos : 0 < volume F) (hFtop : volume F ≠ ⊤)
    {G : Vec d → Vec d}
    (hGE : Integrable G (volume.restrict E))
    (hGF : Integrable G (volume.restrict F))
    {s D : ℝ} (hs : 0 ≤ s) (hD : 0 < D)
    (hcrossDiam : ∀ x ∈ E, ∀ y ∈ F,
      Real.sqrt (vecNormSq (x - y)) ≤ D) :
    ENNReal.ofReal
        (vecNormSq (volumeAverageVec E G - volumeAverageVec F G)) ≤
      ((volume E)⁻¹ + (volume F)⁻¹) *
        ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s)) *
          fracSeminormSq (E ∪ F) s G := by
  let K : Vec d → Vec d → ℝ≥0∞ := fun x y => ENNReal.ofReal
    (vecNormSq (G x - G y) /
      Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s))
  have hWpos : 0 < volume (E ∪ F) :=
    hEpos.trans_le (measure_mono Set.subset_union_left)
  have hWtop : volume (E ∪ F) ≠ ⊤ :=
    ne_top_of_le_ne_top ((ENNReal.add_ne_top).2 ⟨hEtop, hFtop⟩)
      (measure_union_le E F)
  have hcrossUnion :
      (∫⁻ x in E, ∫⁻ y in F, K x y ∂volume) ≤
        ∫⁻ x in E ∪ F, ∫⁻ y in E ∪ F, K x y ∂volume := by
    calc
      (∫⁻ x in E, ∫⁻ y in F, K x y ∂volume) ≤
          ∫⁻ x in E, ∫⁻ y in E ∪ F, K x y ∂volume := by
        exact setLIntegral_mono' hEmeas fun _x _hx =>
          lintegral_mono_set Set.subset_union_right
      _ ≤ ∫⁻ x in E ∪ F, ∫⁻ y in E ∪ F, K x y ∂volume :=
        lintegral_mono_set Set.subset_union_left
  have hraw :
      (∫⁻ x in E ∪ F, ∫⁻ y in E ∪ F, K x y ∂volume) =
        volume (E ∪ F) * fracSeminormSq (E ∪ F) s G := by
    rw [fracSeminormSq, eVolumeAverage, ENNReal.mul_div_cancel hWpos.ne' hWtop]
  have hcoef :
      (volume E)⁻¹ * (volume F)⁻¹ * volume (E ∪ F) ≤
        (volume E)⁻¹ + (volume F)⁻¹ := by
    calc
      (volume E)⁻¹ * (volume F)⁻¹ * volume (E ∪ F) ≤
          (volume E)⁻¹ * (volume F)⁻¹ * (volume E + volume F) :=
        mul_le_mul_right (measure_union_le E F) _
      _ = (volume E)⁻¹ + (volume F)⁻¹ := by
        rw [mul_add]
        calc
          (volume E)⁻¹ * (volume F)⁻¹ * volume E +
              (volume E)⁻¹ * (volume F)⁻¹ * volume F =
              (volume F)⁻¹ * ((volume E)⁻¹ * volume E) +
                (volume E)⁻¹ * ((volume F)⁻¹ * volume F) := by ac_rfl
          _ = (volume E)⁻¹ + (volume F)⁻¹ := by
            rw [ENNReal.inv_mul_cancel hEpos.ne' hEtop,
              ENNReal.inv_mul_cancel hFpos.ne' hFtop]
            simp only [mul_one, add_comm]
  have hbase := ofReal_vecNormSq_sub_volumeAverageVec_le_crossFracIntegral
    hd hEmeas hFmeas hEpos hEtop hFpos hFtop hGE hGF hs hD hcrossDiam
  calc
    ENNReal.ofReal
        (vecNormSq (volumeAverageVec E G - volumeAverageVec F G)) ≤
        (volume E)⁻¹ * (volume F)⁻¹ *
          ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s)) *
            (∫⁻ x in E, ∫⁻ y in F, K x y ∂volume) := hbase
    _ ≤ (volume E)⁻¹ * (volume F)⁻¹ *
        ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s)) *
          (∫⁻ x in E ∪ F, ∫⁻ y in E ∪ F, K x y ∂volume) :=
      mul_le_mul_right hcrossUnion _
    _ = ((volume E)⁻¹ * (volume F)⁻¹ * volume (E ∪ F)) *
        ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s)) *
          fracSeminormSq (E ∪ F) s G := by rw [hraw]; ac_rfl
    _ ≤ ((volume E)⁻¹ + (volume F)⁻¹) *
        ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s)) *
          fracSeminormSq (E ∪ F) s G := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_right
          (mul_le_mul_right hcoef
            (ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s))))
          (fracSeminormSq (E ∪ F) s G)

end

end HighContrast
end HCPolySupport

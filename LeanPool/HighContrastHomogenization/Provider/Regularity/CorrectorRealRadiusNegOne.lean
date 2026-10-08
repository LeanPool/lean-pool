/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineNegSobolevNorm
public import LeanPool.HighContrastHomogenization.Analytic.WeakPairing
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorOriginCubeFields
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusGeometry
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorRealRadiusNegOne

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quotient-safe negative-one restriction to centered real cubes

This module restricts a Hilbert-vector `L²` class from an outer domain to a
measurable subdomain and compares the normalized negative-one dual norms.  A
compactly supported test on the inner domain is also a test on the outer
domain.  Exact support identities for its value and gradient energies produce
the inner-to-outer volume ratio in the squared test norm, hence the square root
of the reciprocal ratio in the dual norm.

The final specialization uses the canonical real-radius origin cube from
`CorrectorRealRadiusGeometry`.  No corrector decay or tail estimate is used.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Restriction of local Hilbert-vector classes -/

/-- The real linear restriction map for Hilbert-vector `L²` classes along the inclusion
`U ⊆ V`. -/
@[expose]
public noncomputable def localHilbertVectorL2RestrictLinear {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    HilbertVectorL2 V →ₗ[ℝ] HilbertVectorL2 U where
  toFun F :=
    ((Lp.memLp F).mono_measure
      (Measure.restrict_mono_set volume hUV)).toLp F
  map_add' F G := by
    let hμ : volumeMeasureOn U ≤ volumeMeasureOn V :=
      Measure.restrict_mono_set volume hUV
    change
      ((Lp.memLp (F + G)).mono_measure hμ).toLp (F + G) =
        ((Lp.memLp F).mono_measure hμ).toLp F +
          ((Lp.memLp G).mono_measure hμ).toLp G
    exact
      (MemLp.toLp_congr
        ((Lp.memLp (F + G)).mono_measure hμ)
        (((Lp.memLp F).mono_measure hμ).add
          ((Lp.memLp G).mono_measure hμ))
        ((Lp.coeFn_add F G).filter_mono (ae_mono hμ))).trans
      (MemLp.toLp_add
        ((Lp.memLp F).mono_measure hμ)
        ((Lp.memLp G).mono_measure hμ))
  map_smul' c F := by
    let hμ : volumeMeasureOn U ≤ volumeMeasureOn V :=
      Measure.restrict_mono_set volume hUV
    change
      ((Lp.memLp (c • F)).mono_measure hμ).toLp (c • F) =
        c • ((Lp.memLp F).mono_measure hμ).toLp F
    exact
      (MemLp.toLp_congr
        ((Lp.memLp (c • F)).mono_measure hμ)
        (((Lp.memLp F).mono_measure hμ).const_smul c)
        ((Lp.coeFn_smul c F).filter_mono (ae_mono hμ))).trans
      (MemLp.toLp_const_smul c ((Lp.memLp F).mono_measure hμ))

theorem localHilbertVectorL2RestrictLinear_norm_le {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V) (F : HilbertVectorL2 V) :
    ‖localHilbertVectorL2RestrictLinear hUV F‖ ≤ ‖F‖ := by
  let hμ : volumeMeasureOn U ≤ volumeMeasureOn V :=
    Measure.restrict_mono_set volume hUV
  change ‖((Lp.memLp F).mono_measure hμ).toLp F‖ ≤ ‖F‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top F)
    (eLpNorm_mono_measure F hμ)

/-- Continuous restriction of a Hilbert-vector `L²` class to an arbitrary
set contained in its original domain. -/
@[expose]
noncomputable def localHilbertVectorL2Restrict {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    HilbertVectorL2 V →L[ℝ] HilbertVectorL2 U :=
  LinearMap.mkContinuous (localHilbertVectorL2RestrictLinear hUV) 1 fun F => by
    simpa only [one_mul] using localHilbertVectorL2RestrictLinear_norm_le hUV F

/-- Local Hilbert-vector restriction agrees almost everywhere with the outer
representative on the inner domain. -/
theorem localHilbertVectorL2Restrict_coeFn_ae {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V) (F : HilbertVectorL2 V) :
    localHilbertVectorL2Restrict hUV F =ᵐ[volumeMeasureOn U] F := by
  exact MemLp.coeFn_toLp
    ((Lp.memLp F).mono_measure
      (Measure.restrict_mono_set volume hUV))

/-! ## Compact support and normalized test energies -/

/-- A local vector test remains a local test after enlarging its domain. -/
theorem IsLocalVecTest.mono_set {d : ℕ} {U V : Set (Vec d)}
    {psi : Vec d → Vec d} (hpsi : IsLocalVecTest U psi) (hUV : U ⊆ V) :
    IsLocalVecTest V psi where
  contDiff := hpsi.contDiff
  hasCompactSupport := hpsi.hasCompactSupport
  tsupport_subset := hpsi.tsupport_subset.trans hUV

private theorem support_testValueIntegrand_subset {d : ℕ}
    {U : Set (Vec d)} {psi : Vec d → Vec d}
    (hpsi : IsLocalVecTest U psi) :
    Function.support (fun x => ENNReal.ofReal (vecNormSq (psi x))) ⊆ U := by
  intro x hx
  apply hpsi.tsupport_subset
  apply subset_tsupport
  rw [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  simp only [hzero, vecNormSq, vecDot, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, ENNReal.ofReal_zero]

private theorem support_testGradientIntegrand_subset {d : ℕ}
    {U : Set (Vec d)} {psi : Vec d → Vec d}
    (hpsi : IsLocalVecTest U psi) :
    Function.support (fun x => ENNReal.ofReal
      (∑ j, vecNormSq (smoothGrad (fun y => psi y j) x))) ⊆ U := by
  intro x hx
  apply hpsi.tsupport_subset
  by_contra hxt
  have hfd : fderiv ℝ psi x = 0 :=
    fderiv_of_notMem_tsupport ℝ hxt
  have hdiff : Differentiable ℝ psi :=
    hpsi.contDiff.differentiable (by simp)
  have hgrad : ∀ j : Fin d,
      smoothGrad (fun y => psi y j) x = 0 := by
    intro j
    have hcomp :
        fderiv ℝ (fun y => psi y j) x =
          (ContinuousLinearMap.proj
            (R := ℝ) (φ := fun _ : Fin d => ℝ) j).comp (fderiv ℝ psi x) := by
      exact
        ((ContinuousLinearMap.proj
          (R := ℝ) (φ := fun _ : Fin d => ℝ) j).hasFDerivAt.comp x
            (hdiff x).hasFDerivAt).fderiv
    funext i
    change fderiv ℝ (fun y => psi y j) x (basisVec i) = 0
    rw [hcomp, hfd]
    rfl
  rw [Function.mem_support] at hx
  apply hx
  simp only [hgrad, vecNormSq, vecDot, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, ENNReal.ofReal_zero]

private theorem setLIntegral_eq_of_support_subset_of_subset {d : ℕ}
    {U V : Set (Vec d)} {f : Vec d → ℝ≥0∞}
    (hUV : U ⊆ V) (hfs : Function.support f ⊆ U) :
    ∫⁻ x in V, f x ∂volume = ∫⁻ x in U, f x ∂volume := by
  rw [setLIntegral_eq_of_support_subset (hfs.trans hUV),
    setLIntegral_eq_of_support_subset hfs]

private theorem eVolumeAverage_eq_volumeRatio_mul_of_support_subset
    {d : ℕ} {U V : Set (Vec d)} {f : Vec d → ℝ≥0∞}
    (hUV : U ⊆ V) (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hfs : Function.support f ⊆ U) :
    eVolumeAverage V f =
      (volume U / volume V) * eVolumeAverage U f := by
  have hint := setLIntegral_eq_of_support_subset_of_subset hUV hfs
  unfold eVolumeAverage
  rw [hint]
  simp only [ENNReal.div_eq_inv_mul]
  symm
  calc
    (volume V)⁻¹ * volume U *
          ((volume U)⁻¹ * ∫⁻ x in U, f x ∂volume) =
        (volume V)⁻¹ * (volume U * (volume U)⁻¹) *
          ∫⁻ x in U, f x ∂volume := by
      ac_rfl
    _ = (volume V)⁻¹ * ∫⁻ x in U, f x ∂volume := by
      rw [ENNReal.mul_inv_cancel hU0 hUtop, mul_one]

private theorem volume_rpow_antitone_of_subset {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ∞)
    {z : ℝ} (hz : z ≤ 0) :
    volume V ^ z ≤ volume U ^ z := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.rpow_ne_top_of_ne_zero hV0 hVtop)
    (ENNReal.rpow_ne_top_of_ne_zero hU0 hUtop)).mp
  rw [← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
  exact Real.rpow_le_rpow_of_nonpos
    (ENNReal.toReal_pos hU0 hUtop)
    ((ENNReal.toReal_le_toReal hUtop hVtop).mpr (measure_mono hUV)) hz

/-- Enlarging the domain decreases the normalized squared `H¹` test norm
by at least the inner-to-outer volume ratio for a test supported in the inner
domain. -/
theorem h1NormSq_outer_le_volumeRatio_mul {d : ℕ} [NeZero d]
    {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ∞)
    {psi : Vec d → Vec d} (hpsi : IsLocalVecTest U psi) :
    h1NormSq V psi ≤ (volume U / volume V) * h1NormSq U psi := by
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hz : -(2 : ℝ) / (d : ℝ) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hd.le
  have hpre := volume_rpow_antitone_of_subset hUV
    hU0 hUtop hV0 hVtop hz
  have hvalue := eVolumeAverage_eq_volumeRatio_mul_of_support_subset
    hUV hU0 hUtop (support_testValueIntegrand_subset hpsi)
  have hgradient := eVolumeAverage_eq_volumeRatio_mul_of_support_subset
    hUV hU0 hUtop (support_testGradientIntegrand_subset hpsi)
  unfold h1NormSq
  rw [hvalue, hgradient]
  calc
    volume V ^ (-(2 : ℝ) / (d : ℝ)) *
          ((volume U / volume V) *
            eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (psi x)))) +
        (volume U / volume V) *
          eVolumeAverage U (fun x => ENNReal.ofReal
            (∑ j, vecNormSq (smoothGrad (fun y => psi y j) x))) =
        (volume U / volume V) *
          (volume V ^ (-(2 : ℝ) / (d : ℝ)) *
            eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (psi x)))) +
          (volume U / volume V) *
            eVolumeAverage U (fun x => ENNReal.ofReal
              (∑ j, vecNormSq (smoothGrad (fun y => psi y j) x))) := by
      ac_rfl
    _ ≤ (volume U / volume V) *
          (volume U ^ (-(2 : ℝ) / (d : ℝ)) *
            eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (psi x)))) +
          (volume U / volume V) *
            eVolumeAverage U (fun x => ENNReal.ofReal
              (∑ j, vecNormSq (smoothGrad (fun y => psi y j) x))) := by
      exact add_le_add_left
        (mul_le_mul_right (mul_le_mul_left hpre _) _) _
    _ = (volume U / volume V) *
          (volume U ^ (-(2 : ℝ) / (d : ℝ)) *
              eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (psi x))) +
            eVolumeAverage U (fun x => ENNReal.ofReal
              (∑ j, vecNormSq (smoothGrad (fun y => psi y j) x)))) := by
      rw [mul_add]

/-! ## The normalized negative-one restriction -/

/-- A local test whose squared `H¹` norm is at most `K` pairs by at most
`sqrt K` times the negative-one norm. -/
theorem dualPairing_le_negOneNorm_of_h1NormSq_le {d : ℕ}
    {V : Set (Vec d)} (F psi : Vec d → Vec d) {K : ℝ} (hK : 0 < K)
    (htest : IsLocalVecTest V psi)
    (hnorm : h1NormSq V psi ≤ ENNReal.ofReal K) :
    dualPairing V F psi ≤
      ENNReal.ofReal (Real.sqrt K) * negOneNorm V F := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have hscaledTest :
      IsLocalVecTest V (fun x => (Real.sqrt K)⁻¹ • psi x) :=
    htest.const_smul _
  have hdiff : Differentiable ℝ psi :=
    htest.contDiff.differentiable (by simp)
  have hscaledNorm :
      h1NormSq V (fun x => (Real.sqrt K)⁻¹ • psi x) ≤ 1 := by
    rw [h1NormSq_smul V _ hdiff]
    refine le_trans (mul_le_mul_right hnorm _) (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (sq_nonneg _), inv_pow, hsq,
      inv_mul_cancel₀ hK.ne', ENNReal.ofReal_one]
  have hmember :
      dualPairing V F (fun x => (Real.sqrt K)⁻¹ • psi x) ≤
        negOneNorm V F :=
    le_iSup
      (f := fun p : {psi' : Vec d → Vec d //
        IsLocalVecTest V psi' ∧ h1NormSq V psi' ≤ 1} =>
          dualPairing V F p.1)
      ⟨_, hscaledTest, hscaledNorm⟩
  have hrecover :
      (fun x => Real.sqrt K • (Real.sqrt K)⁻¹ • psi x) = psi := by
    funext x
    rw [smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul]
  calc
    dualPairing V F psi =
        dualPairing V F
          (fun x => Real.sqrt K • (Real.sqrt K)⁻¹ • psi x) := by
      rw [hrecover]
    _ = ENNReal.ofReal (Real.sqrt K) *
          dualPairing V F (fun x => (Real.sqrt K)⁻¹ • psi x) :=
      dualPairing_const_smul V F _ hsqrt
    _ ≤ ENNReal.ofReal (Real.sqrt K) * negOneNorm V F :=
      mul_le_mul_right hmember _

private theorem setIntegral_eq_of_support_subset_of_subset {d : ℕ}
    {U V : Set (Vec d)} {f : Vec d → ℝ}
    (hUV : U ⊆ V) (hfs : Function.support f ⊆ U) :
    ∫ x in V, f x ∂volume = ∫ x in U, f x ∂volume := by
  have hzeroU : ∀ x, x ∉ U → f x = 0 := by
    intro x hxU
    by_contra hne
    exact hxU (hfs hne)
  have hzeroV : ∀ x, x ∉ V → f x = 0 := by
    intro x hxV
    exact hzeroU x fun hxU => hxV (hUV hxU)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroV,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzeroU]

private theorem volumeAverage_eq_toRealRatio_mul_of_support_subset
    {d : ℕ} {U V : Set (Vec d)} {f : Vec d → ℝ}
    (hUV : U ⊆ V) (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ∞)
    (hfs : Function.support f ⊆ U) :
    volumeAverage U f =
      ((volume V).toReal / (volume U).toReal) * volumeAverage V f := by
  have hIntegral := setIntegral_eq_of_support_subset_of_subset hUV hfs
  have hUpos := ENNReal.toReal_pos hU0 hUtop
  have hVpos := ENNReal.toReal_pos hV0 hVtop
  unfold volumeAverage
  rw [hIntegral]
  field_simp [hUpos.ne', hVpos.ne']

private theorem support_vecDot_right_subset {d : ℕ}
    {U : Set (Vec d)} (F psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest U psi) :
    Function.support (fun x => vecDot (F x) (psi x)) ⊆ U := by
  intro x hx
  apply hpsi.tsupport_subset
  apply subset_tsupport
  rw [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  simp only [hzero, vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem memVectorL2_toVec_hilbertVectorL2 {d : ℕ}
    {V : Set (Vec d)} (F : HilbertVectorL2 V) :
    MemVectorL2 V (fun x => (F x).toVec) := by
  exact MemLp.ae_eq
    (coeFn_hilbertVectorL2ToVectorL2 (U := V) F)
    (Lp.memLp (hilbertVectorL2ToVectorL2 (U := V) F))

private theorem memVectorL2_isLocalVecTest {d : ℕ}
    {V : Set (Vec d)} {psi : Vec d → Vec d}
    (hpsi : IsLocalVecTest V psi) : MemVectorL2 V psi := by
  have hglobal : MemLp psi 2 volume :=
    hpsi.contDiff.continuous.memLp_of_hasCompactSupport
      hpsi.hasCompactSupport
  simpa only [volumeMeasureOn] using
    hglobal.mono_measure (Measure.restrict_le_self)

private theorem dualPairing_eq_toRealRatio_mul_of_subset {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ∞)
    (F psi : Vec d → Vec d) (hF : MemVectorL2 V F)
    (hpsi : IsLocalVecTest U psi) :
    dualPairing U F psi =
      ENNReal.ofReal ((volume V).toReal / (volume U).toReal) *
        dualPairing V F psi := by
  have hpsiV := hpsi.mono_set hUV
  have hintV : IntegrableOn (fun x => vecDot (F x) (psi x)) V volume :=
    integrableOn_vecDot_of_memVectorL2 hF (memVectorL2_isLocalVecTest hpsiV)
  have hintU : IntegrableOn (fun x => vecDot (F x) (psi x)) U volume :=
    hintV.mono_set hUV
  have hAvg := volumeAverage_eq_toRealRatio_mul_of_support_subset
    hUV hU0 hUtop hV0 hVtop
      (support_vecDot_right_subset F psi hpsi)
  rw [dualPairing_eq_ofReal U F psi hintU,
    dualPairing_eq_ofReal V F psi hintV, hAvg,
    ENNReal.ofReal_mul
      (div_nonneg (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg))]

private theorem volume_div_eq_ofReal_toReal_div {d : ℕ}
    {U V : Set (Vec d)} (hUtop : volume U ≠ ∞)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ∞) :
    volume U / volume V =
      ENNReal.ofReal ((volume U).toReal / (volume V).toReal) := by
  symm
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hV0 hVtop),
    ENNReal.ofReal_toReal hUtop, ENNReal.ofReal_toReal hVtop]

private theorem reciprocal_sqrt_factor {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    (v / u) * Real.sqrt (u / v) = Real.sqrt (v / u) := by
  have hK : 0 < v / u := div_pos hv hu
  have hinv : u / v = (v / u)⁻¹ := by
    field_simp [hu.ne', hv.ne']
  rw [hinv, Real.sqrt_inv]
  calc
    (v / u) * (Real.sqrt (v / u))⁻¹ =
        (Real.sqrt (v / u) * Real.sqrt (v / u)) *
          (Real.sqrt (v / u))⁻¹ := by
      rw [Real.mul_self_sqrt hK.le]
    _ = Real.sqrt (v / u) := by
      rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr hK).ne', mul_one]

/-- A raw local `L²` field restricted from `V` to `U` has normalized
negative-one norm at most the square root of the outer-to-inner volume ratio
times its outer norm. -/
theorem negOneNorm_le_sqrt_volumeRatio_of_subset {d : ℕ} [NeZero d]
    {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ∞)
    (F : Vec d → Vec d) (hF : MemVectorL2 V F) :
    negOneNorm U F ≤
      ENNReal.ofReal
          (Real.sqrt ((volume V).toReal / (volume U).toReal)) *
        negOneNorm V F := by
  unfold negOneNorm
  apply iSup_le
  rintro ⟨psi, hpsi, hpsiNorm⟩
  have hUpos := ENNReal.toReal_pos hU0 hUtop
  have hVpos := ENNReal.toReal_pos hV0 hVtop
  have hratioPos :
      0 < (volume U).toReal / (volume V).toReal :=
    div_pos hUpos hVpos
  have hnormOuter :
      h1NormSq V psi ≤
        ENNReal.ofReal ((volume U).toReal / (volume V).toReal) := by
    calc
      h1NormSq V psi ≤
          (volume U / volume V) * h1NormSq U psi :=
        h1NormSq_outer_le_volumeRatio_mul
          hUV hU0 hUtop hV0 hVtop hpsi
      _ ≤ (volume U / volume V) * 1 :=
        mul_le_mul_right hpsiNorm _
      _ = ENNReal.ofReal
          ((volume U).toReal / (volume V).toReal) := by
        rw [mul_one, volume_div_eq_ofReal_toReal_div hUtop hV0 hVtop]
  have houter := dualPairing_le_negOneNorm_of_h1NormSq_le
    F psi hratioPos (hpsi.mono_set hUV) hnormOuter
  have hpair := dualPairing_eq_toRealRatio_mul_of_subset
    hUV hU0 hUtop hV0 hVtop F psi hF hpsi
  calc
    dualPairing U F psi =
        ENNReal.ofReal ((volume V).toReal / (volume U).toReal) *
          dualPairing V F psi := hpair
    _ ≤ ENNReal.ofReal ((volume V).toReal / (volume U).toReal) *
          (ENNReal.ofReal
              (Real.sqrt ((volume U).toReal / (volume V).toReal)) *
            negOneNorm V F) :=
      mul_le_mul_right houter _
    _ = (ENNReal.ofReal ((volume V).toReal / (volume U).toReal) *
          ENNReal.ofReal
            (Real.sqrt ((volume U).toReal / (volume V).toReal))) *
          negOneNorm V F := by rw [mul_assoc]
    _ = ENNReal.ofReal
          (((volume V).toReal / (volume U).toReal) *
            Real.sqrt ((volume U).toReal / (volume V).toReal)) *
          negOneNorm V F := by
      rw [ENNReal.ofReal_mul (div_nonneg hVpos.le hUpos.le)]
    _ = ENNReal.ofReal
          (Real.sqrt ((volume V).toReal / (volume U).toReal)) *
          negOneNorm V F := by
      rw [reciprocal_sqrt_factor hUpos hVpos]

/-- Quotient-safe restriction of a local Hilbert-vector class costs the same
square-root volume ratio in the normalized negative-one norm. -/
theorem localNegOneNorm_restrict_le_sqrt_volumeRatio {d : ℕ} [NeZero d]
    {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ∞)
    (F : HilbertVectorL2 V) :
    localNegOneNorm U (localHilbertVectorL2Restrict hUV F) ≤
      ENNReal.ofReal
          (Real.sqrt ((volume V).toReal / (volume U).toReal)) *
        localNegOneNorm V F := by
  have hrep :
      (fun x => (localHilbertVectorL2Restrict hUV F x).toVec) =ᵐ[
        volumeMeasureOn U] fun x => (F x).toVec :=
    (localHilbertVectorL2Restrict_coeFn_ae hUV F).mono fun _ hx =>
      congrArg HilbertVec.toVec hx
  unfold localNegOneNorm
  rw [negOneNorm_eq_of_ae_eq_on hrep]
  exact negOneNorm_le_sqrt_volumeRatio_of_subset hUV
    hU0 hUtop hV0 hVtop _ (memVectorL2_toVec_hilbertVectorL2 F)

/-! ## Canonical centered-real-cube specialization -/

end

end HighContrast
end HCPolySupport

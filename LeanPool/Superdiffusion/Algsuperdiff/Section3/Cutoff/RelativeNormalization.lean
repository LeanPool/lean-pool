/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.RangeNormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LawCarrier

/-!
# RelativeNormalization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Same-cutoff relative normalization

The canonical normalization used elsewhere is indexed by a natural dilation
depth.  Section 3.5 instead compares arbitrary integer cutoff and observation
scales.  This file keeps the cutoff index fixed and rescales space by the
integer-dependent factor `3^(m+c)`, where the dimension-only shift `c` leaves
strict room for CoarseGraining's unit-range bridge.

No covariance between different cutoff indices is asserted.  The normalized
law is exactly a spatial pushforward of `coefficientCutoffLaw M m` at the same
`m`.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport HCPolySupport.Book MeasureTheory Metric ProbabilityTheory
open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-- The law of the genuine cutoff after the spatial change `a(x) ↦ a(r x)`. -/
def scaledCoefficientCutoffLaw (M : ABKModel d) (m : ℤ) (r : ℝ) (hr : r ≠ 0) :
    HCPolySupport.Book.Ch04.RestrictionCoeffLaw d :=
  Measure.map (smulReg r hr) (coefficientCutoffLaw M m)

instance scaledCoefficientCutoffLaw_isProbabilityMeasure (M : ABKModel d)
    (m : ℤ) (r : ℝ) (hr : r ≠ 0) :
    IsProbabilityMeasure (scaledCoefficientCutoffLaw M m r hr) := by
  unfold scaledCoefficientCutoffLaw; infer_instance

private theorem translateReg_smulReg (r : ℝ) (hr : r ≠ 0) (z : Vec d)
    (a : RegCoeffField d) :
    translateReg z (smulReg r hr a) = smulReg r hr (translateReg (r • z) a) := by
  refine RegCoeffField.ext fun x => ?_
  rw [translateReg_apply, smulReg_apply, smulReg_apply, translateReg_apply,
    smul_add]

/-- Real-translation stationarity survives every nonzero spatial scaling. -/
theorem scaledCoefficientCutoffLaw_stationary_real (M : ABKModel d) (m : ℤ)
    {r : ℝ} (hr : r ≠ 0) (z : Vec d) :
    Measure.map (translateReg z) (scaledCoefficientCutoffLaw M m r hr) =
      scaledCoefficientCutoffLaw M m r hr := by
  have key : translateReg z ∘ smulReg r hr =
      smulReg r hr ∘ translateReg (r • z) := by
    funext a
    exact translateReg_smulReg r hr z a
  rw [scaledCoefficientCutoffLaw,
    Measure.map_map (measurable_translateReg z) (measurable_smulReg r hr), key,
    ← Measure.map_map (measurable_smulReg r hr) (measurable_translateReg (r • z)),
    coefficientCutoffLaw_stationary_real M m (r • z)]

/-- CoarseGraining's integer-translation stationarity for a spatially scaled cutoff
law. -/
theorem scaledCoefficientCutoffLaw_stationary (M : ABKModel d) (m : ℤ)
    {r : ℝ} (hr : r ≠ 0) :
    HCPolySupport.Book.Ch04.RestrictionStationaryLaw
      (scaledCoefficientCutoffLaw M m r hr) :=
  fun z => scaledCoefficientCutoffLaw_stationary_real M m hr (intVecToRealVec z)

private theorem rotateReg_smulReg (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (r : ℝ) (hr : r ≠ 0) (a : RegCoeffField d) :
    rotateReg R hR (smulReg r hr a) = smulReg r hr (rotateReg R hR a) := by
  apply RegCoeffField.ext
  intro x
  simp only [rotateReg_apply, smulReg_apply, matVecMul_smul]

/-- Signed-permutation isotropy survives every nonzero spatial scaling. -/
theorem scaledCoefficientCutoffLaw_isotropic (M : ABKModel d) (m : ℤ)
    {r : ℝ} (hr : r ≠ 0) :
    Ch04.RestrictionIsotropicLaw (scaledCoefficientCutoffLaw M m r hr) := by
  intro R hR
  have key : rotateReg R hR ∘ smulReg r hr =
      smulReg r hr ∘ rotateReg R hR := by
    funext a
    exact rotateReg_smulReg R hR r hr a
  rw [scaledCoefficientCutoffLaw,
    Measure.map_map (measurable_rotateReg R hR) (measurable_smulReg r hr), key,
    ← Measure.map_map (measurable_smulReg r hr) (measurable_rotateReg R hR),
    coefficientCutoffLaw_isotropic M m R hR]

private theorem adjointReg_smulReg (r : ℝ) (hr : r ≠ 0)
    (a : RegCoeffField d) :
    adjointReg (smulReg r hr a) = smulReg r hr (adjointReg a) := by
  apply RegCoeffField.ext
  intro x
  simp only [adjointReg_apply, smulReg_apply]

/-- Adjoint invariance survives every nonzero spatial scaling. -/
theorem scaledCoefficientCutoffLaw_adjoint_invariant (M : ABKModel d) (m : ℤ)
    {r : ℝ} (hr : r ≠ 0) :
    Ch04.RestrictionAdjointInvariantLaw
      (scaledCoefficientCutoffLaw M m r hr) := by
  change Measure.map adjointReg (scaledCoefficientCutoffLaw M m r hr) =
    scaledCoefficientCutoffLaw M m r hr
  have key : adjointReg (d := d) ∘ smulReg r hr =
      smulReg r hr ∘ adjointReg := by
    funext a
    exact adjointReg_smulReg r hr a
  rw [scaledCoefficientCutoffLaw,
    Measure.map_map (measurable_adjointReg (d := d)) (measurable_smulReg r hr), key,
    ← Measure.map_map (measurable_smulReg r hr) (measurable_adjointReg (d := d)),
    coefficientCutoffLaw_adjoint_invariant M m]

private theorem vecNorm_smul (c : ℝ) (v : Vec d) :
    HCPolySupport.Book.Ch02.vecNorm (c • v) =
      |c| * HCPolySupport.Book.Ch02.vecNorm v := by
  change ‖(WithLp.toLp 2 (c • v) : EuclideanSpace ℝ (Fin d))‖ =
    |c| * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖
  have h : (WithLp.toLp 2 (c • v) : EuclideanSpace ℝ (Fin d)) =
      c • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := by
    ext i
    rfl
  rw [h, norm_smul, Real.norm_eq_abs]

private theorem cutoff_range_on_scaled_thickenings (d : ℕ) (m : ℤ) {r : ℝ}
    (hrpos : 0 < r) (U V : Set (Vec d)) (hUV : AreUnitSeparated U V)
    (hslack : cutoffNaturalRange d m < r * (1 - 2 * cutoffBridgeEpsilon)) :
    ∀ ⦃x y : Vec d⦄,
      x ∈ r • thickening cutoffBridgeEpsilon U →
      y ∈ r • thickening cutoffBridgeEpsilon V →
      cutoffNaturalRange d m ≤ HCPolySupport.Book.Ch02.vecNorm (x - y) := by
  rintro x y ⟨x0, hx0, rfl⟩ ⟨y0, hy0, rfl⟩
  have hgap :=
    Algsuperdiff.Section3.Annealed.one_sub_two_mul_lt_vecNorm_sub_of_mem_thickenings
      (d := d) hUV (epsilon := cutoffBridgeEpsilon) hx0 hy0
  have hstrict : cutoffNaturalRange d m <
      HCPolySupport.Book.Ch02.vecNorm (r • x0 - r • y0) := by
    rw [← smul_sub, vecNorm_smul, abs_of_pos hrpos]
    exact hslack.trans (mul_lt_mul_of_pos_left hgap hrpos)
  exact hstrict.le

private theorem continuous_coefficientCutoff_entry (nu : ℝ) (m : ℤ)
    (omega : CutoffSample d) (i j : Fin d) :
    Continuous (fun x : Vec d => coefficientCutoff nu m omega x i j) := by
  simpa only [coefficientCutoff_apply, Matrix.add_apply, Matrix.smul_apply] using!
    (continuous_const.add (continuous_cutoff_entry m omega i j))

/-- Any positive scaling that leaves the fixed thickening slack turns the literal
cutoff range into CoarseGraining's exact unit-range dependence predicate. -/
theorem scaledCoefficientCutoffLaw_unitRangeDependent (M : ABKModel d) (m : ℤ)
    {r : ℝ} (hr : r ≠ 0) (hrpos : 0 < r)
    (hslack : cutoffNaturalRange d m < r * (1 - 2 * cutoffBridgeEpsilon)) :
    HCPolySupport.Book.Ch04.RestrictionUnitRangeDependentLaw
      (scaledCoefficientCutoffLaw M m r hr) := by
  intro U V hU hV hUV
  let S : Set (Vec d) := thickening cutoffBridgeEpsilon U
  let T : Set (Vec d) := thickening cutoffBridgeEpsilon V
  have hS : MeasurableSet S := isOpen_thickening.measurableSet
  have hT : MeasurableSet T := isOpen_thickening.measurableSet
  have hrS : MeasurableSet (r • S) := hS.const_smul_of_ne_zero hr
  have hrT : MeasurableSet (r • T) := hT.const_smul_of_ne_zero hr
  have hsep : ∀ ⦃x y : Vec d⦄, x ∈ r • S → y ∈ r • T →
      cutoffNaturalRange d m ≤ HCPolySupport.Book.Ch02.vecNorm (x - y) := by
    simpa only [S, T] using
      cutoff_range_on_scaled_thickenings d m hrpos U V hUV hslack
  let A : CutoffSample d → RegCoeffField d :=
    fun omega => smulReg r hr (coefficientCutoff M.nu m omega)
  have hAmeas : Measurable A :=
    (measurable_smulReg r hr).comp (measurable_coefficientCutoff M.nu m)
  have hAcont : ∀ omega i j, Continuous (fun x : Vec d => A omega x i j) := by
    intro omega i j
    exact (continuous_coefficientCutoff_entry M.nu m omega i j).comp
      ((continuous_const : Continuous (fun _ : Vec d => r)).smul
        (continuous_id : Continuous (fun x : Vec d => x)))
  have hlocalSource :=
    indep_cutoffSampleLocalSigma_of_indep_completion M m (r • S) (r • T)
      (indep_lowerShellLocalCompletion_of_cutoff_separation M m hrS hrT hsep)
  have hA_local_S : @Measurable (CutoffSample d) (RegCoeffField d)
      (cutoffSampleLocalSigma M m (r • S)) (LocalSigmaR S) A :=
    (measurable_smulReg_local r hr S).comp
      (measurable_coefficientCutoff_local M m (r • S))
  have hA_local_T : @Measurable (CutoffSample d) (RegCoeffField d)
      (cutoffSampleLocalSigma M m (r • T)) (LocalSigmaR T) A :=
    (measurable_smulReg_local r hr T).comp
      (measurable_coefficientCutoff_local M m (r • T))
  have hlocal : Indep (MeasurableSpace.comap A (LocalSigmaR S))
      (MeasurableSpace.comap A (LocalSigmaR T)) (cutoffSampleLaw M).toMeasure :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hlocalSource hA_local_S.comap_le)
      hA_local_T.comap_le
  have hbridge :=
    Algsuperdiff.Section3.Annealed.indep_restrictionSigmaR_map_of_indep_localSigmaR_thickenings
      A hAmeas hAcont U V hU hV cutoffBridgeEpsilon cutoffBridgeEpsilon_pos hlocal
  have hmap : Measure.map A (cutoffSampleLaw M).toMeasure =
      scaledCoefficientCutoffLaw M m r hr := by
    rw [scaledCoefficientCutoffLaw, coefficientCutoffLaw_eq_map]
    exact (Measure.map_map (measurable_smulReg r hr)
      (measurable_coefficientCutoff M.nu m)).symm
  simpa [A, S, T] using hmap ▸ hbridge

/-- Dimension-only buffer used by the same-cutoff relative normalization. -/
def cutoffRelativeNormalizationShift (d : ℕ) : ℕ :=
  cutoffNormalizationDepth d 0

/-- The relative normalization factor `3^(m+c)`. -/
def cutoffRelativeNormalizationScale (d : ℕ) (m : ℤ) : ℝ :=
  (3 : ℝ) ^ (m + (cutoffRelativeNormalizationShift d : ℤ))

theorem cutoffRelativeNormalizationScale_pos (d : ℕ) (m : ℤ) :
    0 < cutoffRelativeNormalizationScale d m := by
  rw [cutoffRelativeNormalizationScale]
  positivity

theorem cutoffRelativeNormalizationScale_ne_zero (d : ℕ) (m : ℤ) :
    cutoffRelativeNormalizationScale d m ≠ 0 :=
  (cutoffRelativeNormalizationScale_pos d m).ne'

theorem cutoffRelativeNormalizationScale_strict_slack (d : ℕ) (m : ℤ) :
    cutoffNaturalRange d m < cutoffRelativeNormalizationScale d m *
      (1 - 2 * cutoffBridgeEpsilon) := by
  have hspec : 2 * Real.sqrt (d : ℝ) <
      (3 : ℝ) ^ cutoffRelativeNormalizationShift d := by
    simpa [cutoffRelativeNormalizationShift, cutoffNaturalRange_zero] using
      cutoffNormalizationDepth_spec d 0
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hsplit : cutoffRelativeNormalizationScale d m =
      (3 : ℝ) ^ m * (3 : ℝ) ^ cutoffRelativeNormalizationShift d := by
    rw [cutoffRelativeNormalizationScale,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  rw [hsplit, one_sub_two_mul_cutoffBridgeEpsilon, cutoffNaturalRange]
  nlinarith [hspec, h3m]

/-- The same-cutoff relative law.  Its spatial scaling depends on `m`, but its
cutoff-law index remains exactly `m`. -/
def relativeNormalizedCutoffLaw (M : ABKModel d) (m : ℤ) :
    HCPolySupport.Book.Ch04.RestrictionCoeffLaw d :=
  scaledCoefficientCutoffLaw M m (cutoffRelativeNormalizationScale d m)
    (cutoffRelativeNormalizationScale_ne_zero d m)

instance relativeNormalizedCutoffLaw_isProbabilityMeasure (M : ABKModel d)
    (m : ℤ) : IsProbabilityMeasure (relativeNormalizedCutoffLaw M m) :=
  scaledCoefficientCutoffLaw_isProbabilityMeasure M m _ _

theorem relativeNormalizedCutoffLaw_stationary_real (M : ABKModel d) (m : ℤ)
    (z : Vec d) :
    Measure.map (translateReg z) (relativeNormalizedCutoffLaw M m) =
      relativeNormalizedCutoffLaw M m :=
  scaledCoefficientCutoffLaw_stationary_real M m _ z

theorem relativeNormalizedCutoffLaw_stationary (M : ABKModel d) (m : ℤ) :
    HCPolySupport.Book.Ch04.RestrictionStationaryLaw
      (relativeNormalizedCutoffLaw M m) :=
  scaledCoefficientCutoffLaw_stationary M m _

theorem relativeNormalizedCutoffLaw_unitRangeDependent (M : ABKModel d)
    (m : ℤ) :
    HCPolySupport.Book.Ch04.RestrictionUnitRangeDependentLaw
      (relativeNormalizedCutoffLaw M m) :=
  scaledCoefficientCutoffLaw_unitRangeDependent M m _
    (cutoffRelativeNormalizationScale_pos d m)
    (cutoffRelativeNormalizationScale_strict_slack d m)

/-- The relative law is exactly the integer dilation proposed by the
source-relative scale arithmetic. -/
theorem relativeNormalizedCutoffLaw_eq_map_dilateReg (M : ABKModel d) (m : ℤ) :
    relativeNormalizedCutoffLaw M m =
      Measure.map
        (dilateReg (-(m + (cutoffRelativeNormalizationShift d : ℤ))))
        (coefficientCutoffLaw M m) := by
  rw [relativeNormalizedCutoffLaw, scaledCoefficientCutoffLaw]
  congr 1
  funext a
  apply RegCoeffField.ext
  intro x
  simp only [smulReg_apply, dilateReg_apply]
  have hscale : ((((3 : ℝ) ^
      (-(m + (cutoffRelativeNormalizationShift d : ℤ))))⁻¹)) =
      cutoffRelativeNormalizationScale d m := by
    rw [zpow_neg]
    simp [cutoffRelativeNormalizationScale]
  rw [hscale]

private theorem dilatedCoeffFamily_coeffOn_ae_eq_dilateReg
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) (Q : TriadicCube d) :
    ((Ch02.TriadicCoeffFamily.dilate k
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)).coeffOn Q).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet Q)] (dilateReg k a).toFun := by
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Qsrc : TriadicCube d := Ch02.dilateCube (-k) Q
  have htarget : Ch02.dilateCube k Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_dilateCube_neg k Q
  have hD := Ch02.TriadicCoeffFamily.isDilation_dilate k F Qsrc
  have hcoeff' :
      ((Ch02.TriadicCoeffFamily.dilate k F).coeffOn
          (Ch02.dilateCube k Qsrc)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
          Ch02.dilateCoeffField k a.toFun := by
    simpa [F, Qsrc, htarget] using hD.coeff_ae_eq
  have hcast := hcoeff'
  rw [htarget] at hcast
  simpa [F, Ch04.dilateReg_toFun] using hcast

/-- Local a.e. uniform ellipticity is preserved by every integer triadic
dilation, with no sign restriction on the dilation exponent. -/
theorem aelocallyUniformlyEllipticField_dilateReg
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) : Ch04.AELocallyUniformlyEllipticField (dilateReg k a) := by
  intro Q
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate k F
  let bQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := B.coeffOn Q
  have hcoeff : bQ.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (dilateReg k a).toFun := by
    simpa [bQ, B] using dilatedCoeffFamily_coeffOn_ae_eq_dilateReg ha k Q
  refine ⟨bQ.lam, bQ.Lam, bQ.lam_pos, bQ.lam_le_Lam, ?_⟩
  refine ⟨measurableSet_openCubeSet Q, ?_, ?_⟩
  · intro i j
    refine (bQ.aeStronglyMeasurable i j).congr ?_
    filter_upwards [hcoeff] with x hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [restrictCoeffField, hxQ, hx]
    · simp [restrictCoeffField, hxQ]
  · filter_upwards [bQ.aeElliptic, hcoeff] with x hxEll hx
    simpa [hx] using hxEll

/-- The canonical Chapter 4 family of an integer-dilated field agrees a.e.
with the literal Chapter 2 dilation of the original canonical family. -/
theorem triadicCoeffFamily_dilateReg_aeeq_dilate
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) :
    Ch02.TriadicCoeffFamily.AEEq
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (dilateReg k a) (aelocallyUniformlyEllipticField_dilateReg ha k))
      (Ch02.TriadicCoeffFamily.dilate k
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)) := by
  intro Q
  change (dilateReg k a).toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
    ((Ch02.TriadicCoeffFamily.dilate k
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)).coeffOn Q).toCoeffField
  simpa [Ch02.cubeDomain_coe] using
    (dilatedCoeffFamily_coeffOn_ae_eq_dilateReg ha k Q).symm

/-- Triadic dilation of regular coefficient fields as a measurable equivalence. -/
noncomputable def dilateRegMeasurableEquiv (k : ℤ) :
    RegCoeffField d ≃ᵐ RegCoeffField d where
  toEquiv :=
    { toFun := dilateReg k
      invFun := dilateReg (-k)
      left_inv := by
        intro a
        apply RegCoeffField.ext
        intro x
        simp only [dilateReg_apply, smul_smul, zpow_neg]
        rw [inv_inv,
          inv_mul_cancel₀ (zpow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)), one_smul]
      right_inv := by
        intro a
        apply RegCoeffField.ext
        intro x
        simp only [dilateReg_apply, smul_smul, zpow_neg]
        rw [inv_inv,
          mul_inv_cancel₀ (zpow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)), one_smul] }
  measurable_toFun := measurable_dilateReg k
  measurable_invFun := measurable_dilateReg (-k)

/-- The relative law is supported on the exact Chapter 4 local ellipticity
carrier. -/
theorem relativeNormalizedCutoffLaw_aeLocallyUniformlyElliptic
    (M : ABKModel d) (m : ℤ) :
    Ch04.AELocallyUniformlyEllipticLaw (relativeNormalizedCutoffLaw M m) := by
  rw [relativeNormalizedCutoffLaw_eq_map_dilateReg]
  let k : ℤ := -(m + (cutoffRelativeNormalizationShift d : ℤ))
  exact ((dilateRegMeasurableEquiv (d := d) k).measurableEmbedding.ae_map_iff).2 <| by
    filter_upwards [(coefficientCutoffLaw_lawCarrier M m).ae_locallyUniformlyEllipticField]
      with a ha
    exact aelocallyUniformlyEllipticField_dilateReg ha k

/-- The relative law is a Chapter 4 restriction-law carrier. -/
theorem relativeNormalizedCutoffLaw_lawCarrier (M : ABKModel d) (m : ℤ) :
    Ch04.RestrictionLawCarrier (relativeNormalizedCutoffLaw M m) :=
  Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
    (relativeNormalizedCutoffLaw_aeLocallyUniformlyElliptic M m)

/-- Full structural package for the same-cutoff relative normalization. -/
theorem relativeNormalizedCutoffLaw_structuralLaw (M : ABKModel d) (m : ℤ) :
    Ch04.RestrictionStructuralLaw (relativeNormalizedCutoffLaw M m) where
  stationary := relativeNormalizedCutoffLaw_stationary M m
  unit_range := relativeNormalizedCutoffLaw_unitRangeDependent M m
  isotropic := scaledCoefficientCutoffLaw_isotropic M m _
  adjoint_invariant := scaledCoefficientCutoffLaw_adjoint_invariant M m _

end

end Algsuperdiff.Section3.Cutoff

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AffineAnnealedCutoffEnergyComponent

/-!
# High-contrast homogenization: Provider.Response.AffineAnnealedCutoffEnergyAdjointComponent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adjoint annealed cutoff-energy component on adapted cells

The affine reference family for the transposed recentered coefficient is
chosen independently of the primal family.  The transported loads and the
physical adjoint optimizer remain explicit throughout the identification.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory Book.Ch02
open Book.Ch05.Section53.JUpperBoundWeakNorms

open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem cutoffWeightedTopHalfEnergy_affineAdjointResponse
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      (a.transpose.coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) :
    cubeAverage (originCube d t) (fun y ↦
        adaptedPreYoungCutoff q hq t (matVecMul q y) *
          topHalfEnergyDensityOnCube (originCube d t) aRef
            (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) y) =
      Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t) a p r).toH1.grad x)
            (matVecMul ((a.transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer
                (adaptedDomain hq t) a p r).toH1.grad x)))) := by
  have h := cutoffProductTermOnCube_affineResponseOptimizer
    hq t a.transpose haRef (adaptedPreYoungCutoff q hq t) p r 0 0
  simpa [cutoffProductTermOnCube, centeredProductDensityOnCube,
    topHalfEnergyDensityOnCube, canonicalMaximizerGradientOnCube,
    canonicalMaximizerFluxOnCube, centeredAdjointOptimizer, matVecMul_zero,
    Book.Ch02.variationEnergyIntegrand, vecDot_matVecMul_symmPart] using h

private theorem ofReal_abs_integral_le_adjointCutoffEnergyComponent_of_meanZero
    {P : Measure (CoeffSpace d)} {X W J D T : CoeffSpace d → ℝ}
    {Ccut expo EJ tau : ℝ}
    (hX : Integrable X P) (hW : Integrable W P)
    (hJ : Integrable J P) (hT : Integrable T P)
    (hJnn : 0 ≤ᵐ[P] J) (hTnn : 0 ≤ᵐ[P] T) (hDT : D =ᵐ[P] T)
    (hpoint : ∀ a, |X a + W a| ≤ Ccut * expo * J a +
      Real.sqrt (D a) * Real.sqrt (4 * J a + 2 * T a))
    (hzero : ∫ a, W a ∂P = 0) (hEJ : ∫ a, J a ∂P = EJ)
    (htau : ∫ a, T a ∂P = tau) (hCcut : 0 ≤ Ccut)
    (hexpo : 0 ≤ expo) :
    ENNReal.ofReal |∫ a, X a ∂P| ≤
      ENNReal.ofReal 2 * ENNReal.ofReal (Real.sqrt tau) *
          ENNReal.ofReal (Real.sqrt tau) +
        ENNReal.ofReal 4 * ENNReal.ofReal (Real.sqrt tau) *
          ENNReal.ofReal (Real.sqrt EJ) +
        ENNReal.ofReal Ccut * ENNReal.ofReal expo *
          ENNReal.ofReal (Real.sqrt EJ) * ENNReal.ofReal (Real.sqrt EJ) := by
  have hD : Integrable D P := hT.congr hDT.symm
  have hDnn : 0 ≤ᵐ[P] D := by
    filter_upwards [hTnn, hDT] with a hTa hDa
    rw [hDa]
    exact hTa
  have hsum : Integrable (fun a ↦ 4 * J a + 2 * T a) P :=
    (hJ.const_mul 4).add (hT.const_mul 2)
  have hsumnn : 0 ≤ᵐ[P] fun a ↦ 4 * J a + 2 * T a := by
    filter_upwards [hJnn, hTnn] with a hJa hTa
    change 0 ≤ J a at hJa
    change 0 ≤ T a at hTa
    change 0 ≤ 4 * J a + 2 * T a
    exact add_nonneg (mul_nonneg (by norm_num) hJa)
      (mul_nonneg (by norm_num) hTa)
  have hprod : Integrable (fun a ↦
      Real.sqrt (D a) * Real.sqrt (4 * J a + 2 * T a)) P :=
    integrable_sqrt_mul_sqrt hD hsum hDnn hsumnn
  have hbound : Integrable (fun a ↦ Ccut * expo * J a +
      Real.sqrt (D a) * Real.sqrt (4 * J a + 2 * T a)) P :=
    (hJ.const_mul _).add hprod
  have hannealed := abs_integral_le_of_integral_eq_zero
    hX hW hbound hpoint hzero
  have hreduce := integral_cutoffEnergyBound_le hJnn hTnn hDT hJ hT hbound
    hEJ htau
  have hEJnn : 0 ≤ EJ := by
    rw [← hEJ]
    exact integral_nonneg_of_ae hJnn
  have htaunn : 0 ≤ tau := by
    rw [← htau]
    exact integral_nonneg_of_ae hTnn
  exact ofReal_abs_le_cutoffEnergyComponent hCcut hexpo hEJnn htaunn
    (hannealed.trans hreduce)

/-- The adjoint cutoff-energy contribution on the adapted terminal cell has
the same three-term bound, using a separately chosen affine reference family
for the transposed recentered coefficient. -/
theorem ofReal_abs_integral_affineAdjointSubSkewCutoffEnergyDefect_le_component
    [NeZero d] {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l s t H : ℤ} (hqGrid : IsRoundedGrid l q)
    (hls : l ≤ s) (j : ℕ) (hscale : t - (j : ℤ) = s)
    (hH : H = t - s) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hs : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq s)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq s)) p r) P)
    (ht : Integrable (fun a ↦ Book.Ch02.responseJ (adaptedDomain hq t)
      (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)) p r) P)
    (hcutoff : Integrable (fun a ↦
      Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) -
        Book.Ch02.responseJ (adaptedDomain hq t)
          (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)) p r) P) :
    ENNReal.ofReal |∫ a, (Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) -
      Book.Ch02.responseJ (adaptedDomain hq t)
        (((a.subSkew g hg).transpose).coeffOn (adaptedDomain hq t)) p r) ∂P| ≤
      ENNReal.ofReal 2 * ENNReal.ofReal
          (Real.sqrt (profileAdjointResponseDefect P hq g hg s t p r)) *
          ENNReal.ofReal (Real.sqrt
            (profileAdjointResponseDefect P hq g hg s t p r)) +
        ENNReal.ofReal 4 * ENNReal.ofReal
          (Real.sqrt (profileAdjointResponseDefect P hq g hg s t p r)) *
          ENNReal.ofReal (Real.sqrt (∫ a, Book.Ch02.responseJ
            (adaptedDomain hq t) (((a.subSkew g hg).transpose).coeffOn
              (adaptedDomain hq t)) p r ∂P)) +
        ENNReal.ofReal (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound) *
          ENNReal.ofReal ((3 : ℝ) ^ (-H)) *
          ENNReal.ofReal (Real.sqrt (∫ a, Book.Ch02.responseJ
            (adaptedDomain hq t) (((a.subSkew g hg).transpose).coeffOn
              (adaptedDomain hq t)) p r ∂P)) *
          ENNReal.ofReal (Real.sqrt (∫ a, Book.Ch02.responseJ
            (adaptedDomain hq t) (((a.subSkew g hg).transpose).coeffOn
              (adaptedDomain hq t)) p r ∂P)) := by
  obtain ⟨A, hA, hchild, hbase, hDint⟩ :=
    exists_integral_affineAdjointSubSkewDifferenceEnergy_eq_profileAdjoint
      hP hq hqGrid hls j hscale g hg p r hs ht
  let pRef := matVecMul (matTranspose q) p
  let rRef := matVecMul q⁻¹ r
  let Q := originCube d t
  let J : CoeffSpace d → ℝ := fun a ↦
    Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) ((A a).coeffOn Q) pRef rRef
  let T : CoeffSpace d → ℝ := fun a ↦
    responseJPartitionDefectOnFamilyAtDepth (A a) Q j pRef rRef
  let D : CoeffSpace d → ℝ := fun a ↦ descendantsAverage Q j (fun R ↦
    cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube
      (A a) Q R pRef rRef))
  let W : CoeffSpace d → ℝ := fun a ↦
    cutoffWeightedChildResponseJOnFamilyAtDepth (A a) Q j
      (fun y ↦ adaptedPreYoungCutoff q hq t (matVecMul q y)) pRef rRef
  let X : CoeffSpace d → ℝ := fun a ↦ cubeAverage Q (fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y) *
        topHalfEnergyDensityOnCube Q ((A a).coeffOn Q) pRef rRef y) - J a
  have hJInt : Integrable J P := ht.congr (_root_.Filter.Eventually.of_forall fun a ↦
    (responseJ_affineResponse hq t (hA a Q) p r).symm)
  have hchildren : Integrable (fun a ↦ descendantsAverage Q j (fun R ↦
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R) ((A a).coeffOn R)
        pRef rRef)) P := by
    unfold descendantsAverage
    exact (integrable_finsetSum _ fun R hR ↦ hchild R hR).const_mul _
  have hTInt : Integrable T P := by
    simpa [T, childResponseJAverageOnFamilyAtDepth] using! hchildren.sub hJInt
  have hWInt : Integrable W P := by
    unfold W cutoffWeightedChildResponseJOnFamilyAtDepth descendantsAverage
    exact (integrable_finsetSum _ fun R hR ↦
      (hchild R hR).const_mul _).const_mul _
  have hXeq : ∀ a, X a =
      Book.Ch02.average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) -
        Book.Ch02.responseJ (adaptedDomain hq t)
          (((a.subSkew g hg).transpose).coeffOn
            (adaptedDomain hq t)) p r := by
    intro a
    unfold X J Q pRef rRef
    rw [cutoffWeightedTopHalfEnergy_affineAdjointResponse hq t
      (a.subSkew g hg) (hA a (originCube d t)) p r,
      responseJ_affineResponse hq t (hA a (originCube d t)) p r]
  have hXInt : Integrable X P :=
    hcutoff.congr (_root_.Filter.Eventually.of_forall fun a ↦ (hXeq a).symm)
  have hDT : D =ᵐ[P] T := _root_.Filter.Eventually.of_forall fun a ↦ by
    exact descendantsAverage_additivityDiffHalfEnergy_eq_responseJPartitionDefect_of_commonCoeff
      (A a) Q j pRef rRef (fun R _ ↦ by rw [hA a R, hA a Q])
  have hJnn : 0 ≤ᵐ[P] J := _root_.Filter.Eventually.of_forall fun a ↦
    Book.Ch02.responseJ_nonneg (Book.Ch02.cubeDomain Q) ((A a).coeffOn Q)
      pRef rRef
  have hTnn : 0 ≤ᵐ[P] T := _root_.Filter.Eventually.of_forall fun a ↦
    Book.Ch05.Section53.WeakNormsMaximizer.responseJPartitionDefectOnFamilyAtDepth_nonneg
      (A a) Q j pRef rRef
  have hpoint : ∀ a, |X a + W a| ≤
      (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound) *
          (3 : ℝ) ^ (-H) * J a + Real.sqrt (D a) *
            Real.sqrt (4 * J a + 2 * T a) := by
    intro a
    exact abs_cutoff_weighted_energy_sub_responseJ_add_cutoffWeightedChild_le
      hq (A a) Q j hscale hH pRef rRef
        (fun R _ ↦ by rw [hA a Q, hA a R])
  have hzero : ∫ a, W a ∂P = 0 := by
    exact integral_cutoffWeighted_affineAdjointSubSkewResponseJ_eq_zero
      hP hq hqGrid j hscale hls g hg A hA p r hchild hbase
        (integrableOn_adaptedPreYoungCutoff_pullback hq t Q)
        (cubeAverage_adaptedPreYoungCutoff_pullback_eq_one hq t)
  have hEJ := integral_affineAdjointSubSkewResponseJ_eq_physical
    (P := P) hq t g hg A hA p r
  have htau : ∫ a, T a ∂P =
      profileAdjointResponseDefect P hq g hg s t p r := by
    calc
      ∫ a, T a ∂P = ∫ a, D a ∂P := (integral_congr_ae hDT).symm
      _ = profileAdjointResponseDefect P hq g hg s t p r := hDint
  have hmain := ofReal_abs_integral_le_adjointCutoffEnergyComponent_of_meanZero
    hXInt hWInt hJInt hTInt hJnn hTnn hDT hpoint hzero hEJ htau
      (sharpCutoffCoefficient_nonneg d) (by positivity)
  rw [integral_congr_ae (_root_.Filter.Eventually.of_forall hXeq)] at hmain
  exact hmain

end

end HCPolySupport.HighContrast.Response

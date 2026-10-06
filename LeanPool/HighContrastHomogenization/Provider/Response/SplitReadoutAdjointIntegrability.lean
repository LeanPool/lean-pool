/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.SplitReadoutIntegrability

/-!
# High-contrast homogenization: Provider.Response.SplitReadoutAdjointIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability of adjoint adapted cutoff-split readouts

The adjoint terminal weak quantity controls the child means and cutoff
oscillations required by the adjoint five-term split.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem integrable_of_enorm_le_finite_mul_root
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → ℝ} {root : Ω → ℝ≥0∞} {C : ℝ≥0∞}
    (hZ : AEStronglyMeasurable Z μ) (hC : C ≠ ⊤)
    (hroot : eLpNorm root 2 μ ≠ ⊤)
    (hbound : ∀ a, ENNReal.ofReal |Z a| ≤ C * root a) :
    Integrable Z μ := by
  have hnorm : eLpNorm Z 2 μ ≤ C * eLpNorm root 2 μ := by
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (μ := μ)
      (f := Z) (g := root) (c := C.toNNReal) (p := (2 : ℝ≥0∞)) hZ
      (_root_.Filter.Eventually.of_forall fun a ↦ by
        simpa only [Real.enorm_eq_ofReal_abs, enorm_eq_self,
          ENNReal.coe_toNNReal hC] using hbound a)
    simpa only [ENNReal.smul_def, ENNReal.coe_toNNReal hC] using h
  have hlt : C * eLpNorm root 2 μ < ⊤ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC)
      (lt_top_iff_ne_top.mpr hroot)
  exact (show MemLp Z 2 μ from hnorm.trans_lt hlt).integrable (by norm_num)

/-- Every adjoint child mean and cutoff-oscillation readout required by the
adapted five-term split is integrable under finiteness of the adjoint profile
weak quantity. -/
theorem integrable_adjoint_adaptedFiveTermSplit_readouts [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {q m0 : Mat d}
    (hq : q.PosDef) (hm0 : m0.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hweak : profileAdjointWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    (∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w)
        (diagonalWeakAdjointState hq t (a.subSkew g hg) p r)) alpha) P) ∧
    (∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ volumeAverage
      (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
          toFullBlockVec
            (diagonalWeakAdjointState hq t (a.subSkew g hg) p r x) alpha)) P) := by
  let center := profileAdjointCenter P hq t (fun a ↦ a.subSkew g hg) p r
  let root := profileAdjointWeakRoot m0 hq t (fun a ↦ a.subSkew g hg) p r center
  have hp : eLpNorm root 2 P ^ (2 : ℕ) ≠ ⊤ := by
    simpa only [root, center, profileAdjointWeakQuantity_eq] using hweak
  have hroot : eLpNorm root 2 P ≠ ⊤ :=
    (ENNReal.pow_ne_top_iff.mp hp).resolve_right (by norm_num)
  refine ⟨?_, ?_⟩ <;> intro w hw alpha
  · let C := ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ))
        (translateCube w (originCube d s)))⁻¹ *
      ENNReal.ofReal (Real.sqrt ((descendantsAtDepth (originCube d t)
        (Int.toNat (t - s))).card : ℝ)) *
      ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
      ENNReal.ofReal (Real.sqrt (max (matrixFrobeniusNormSq (matSqrt m0)⁻¹)
        (matrixFrobeniusNormSq (matSqrt m0))))
    have hC : C ≠ ⊤ := by
      dsimp only [C]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top
    have hcentered := integrable_of_enorm_le_finite_mul_root
      ((Selection.aestronglyMeasurable_alignedCellAverage_diagonalAdjointState
        hq hst P g hg p r hw alpha).sub aestronglyMeasurable_const)
      hC hroot (fun a ↦ by
        simpa only [C, root, center, profileAdjointWeakRoot,
          diagonalWeakAdjointState_eq, Pi.sub_apply] using
          (centeredChild_readout_enorm_bounds hq hm0 hst hw
            (a.subSkew g hg).transpose p r center alpha).1)
    exact (hcentered.add (integrable_const _)).congr
      (_root_.Filter.Eventually.of_forall fun _ ↦ by dsimp; ring)
  · let C := ENNReal.ofReal (1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 *
        (3 : ℝ) ^ (-(t - s)) *
        (cubeBesovCircDepthWeight (translateCube w (originCube d s)) (1 / 2) 1)⁻¹) *
      ENNReal.ofReal (Real.sqrt ((descendantsAtDepth (originCube d t)
        (Int.toNat (t - s))).card : ℝ)) *
      ENNReal.ofReal (cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t)) *
      ENNReal.ofReal (Real.sqrt (max (matrixFrobeniusNormSq (matSqrt m0)⁻¹)
        (matrixFrobeniusNormSq (matSqrt m0))))
    have hC : C ≠ ⊤ := by
      dsimp only [C]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top
    let eta := fun x ↦ adaptedPreYoungCutoff q hq t x -
      volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)
    let : IsFiniteMeasure (volumeMeasureOn (adaptedCell q t)) :=
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isFiniteMeasure_restrict_volume
    exact integrable_of_enorm_le_finite_mul_root
      (Selection.aestronglyMeasurable_weightedCellAverage_diagonalAdjointState
        hq hst P g hg p r hw alpha
          (Selection.memScalarL2_indicator_cutoffOscillation hq t
            (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen.measurableSet))
      hC hroot (fun a ↦ by
        simpa only [C, root, center, eta, profileAdjointWeakRoot,
          diagonalWeakAdjointState_eq] using
          (centeredChild_readout_enorm_bounds hq hm0 hst hw
            (a.subSkew g hg).transpose p r center alpha).2)

end

end HCPolySupport.HighContrast.Response

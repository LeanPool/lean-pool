/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PrintFaithfulPost109CapSurface
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.UniformFluxScheduledRateExtraction

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.CdualConditionalTerminalProducer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Terminal producer conditional on domain duality

The quantitative flux row is complete.  The only remaining analytic input in
this terminal adapter is the ruled arbitrary-domain flux-defect duality.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem memVectorL2_of_localVecTest
    {U : Set (Vec d)} {G : Vec d → Vec d}
    (hG : IsLocalVecTest U G) : MemVectorL2 U G := by
  have hGlobal : MemLp G 2 volume :=
    hG.contDiff.continuous.memLp_of_hasCompactSupport hG.hasCompactSupport
  simpa only [volumeMeasureOn] using
    hGlobal.mono_measure (Measure.restrict_le_self)

private theorem hsNormSq_ruledCell_ne_top [NeZero d]
    {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hs : 0 < s) (hsHalf : s < 1 / 2) {G : Vec d → Vec d}
    (hG : IsLocalVecTest U G) (i : system.CellIndex) :
    hsNormSq (system.cell i) s G ≠ ⊤ := by
  have hs0 : 0 ≤ (d : ℝ) + 2 * s := by positivity
  have hs1 : s < 1 := hsHalf.trans (by norm_num)
  have hVtop : volume (system.cell i) ≠ ⊤ :=
    ne_of_lt (by simpa only [openCubeSet_whitneyCellCube] using
      (isBoundedDomain_openCubeSet (whitneyCellCube system i)).volume_lt_top)
  have hV0 : volume (system.cell i) ≠ 0 := by
    intro hzero
    have hvolume := volume_openCubeSet_toReal (whitneyCellCube system i)
    rw [openCubeSet_whitneyCellCube, hzero] at hvolume
    exact (cubeVolume_pos (whitneyCellCube system i)).ne'
      (by simpa using hvolume.symm)
  have hweight : volume (system.cell i) ^ (-(2 * s) / (d : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hV0 hVtop
  have hL2 : eVolumeAverage (system.cell i)
      (fun x ↦ ENNReal.ofReal (vecNormSq (G x))) ≠ ⊤ :=
    ne_of_lt (eVolumeAverage_lt_top hV0
      (lintegral_vecNormSq_ne_top
        (by simpa only [openCubeSet_whitneyCellCube] using
          isBoundedDomain_openCubeSet (whitneyCellCube system i))
        hG.contDiff.continuous hG.hasCompactSupport))
  have hFractional : fracSeminormSq (system.cell i) s G ≠ ⊤ := by
    refine ne_of_lt (eVolumeAverage_lt_top hV0 ?_)
    exact lintegral_fracSeminorm_ne_top (measurableSet_whitneyCell system i)
      (by simpa only [openCubeSet_whitneyCellCube] using
        isBoundedDomain_openCubeSet (whitneyCellCube system i))
      hs0 hs1 hG.contDiff hG.hasCompactSupport
  simp only [hsNormSq]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top hweight hL2, hFractional⟩

/-- A finite printed full-dual flux row controls its compact-test negative
Sobolev norm through the pure Hardy row. -/
theorem negSobolevNorm_le_of_rowConvertedFluxCap [NeZero d]
    {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U) (hUnonempty : U.Nonempty)
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : Vec d → Vec d) (hF : MemVectorL2 U F)
    {cap hardyConstant : ℝ≥0∞}
    (hRow : normalizedWhitneyRowEnergy system
      (physicalFullDualWhitneyFamilyCellEnergy system s (fun _ ↦ F)) ≤ cap)
    (hHardy : ∀ G : Vec d → Vec d,
      Integrable G (volume.restrict U) →
        PrintFaithfulPositiveTestRow system s G hardyConstant) :
    negSobolevNorm U s F ≤
      ((fractionalDualToBesovConstant d) ^ (2 : ℕ) * cap) ^
          (1 / 2 : ℝ) * hardyConstant ^ (1 / 2 : ℝ) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hUpos : 0 < volume U :=
    volume_pos_of_isOpenBoundedConvexDomain hU hUnonempty
  have hUtop : volume U ≠ ⊤ := hU.volume_lt_top.ne
  unfold negSobolevNorm
  refine iSup_le fun test ↦ ?_
  let G : Vec d → Vec d := test.1
  have hGtest : IsLocalVecTest U G := test.2.1
  have hGGlobal : Integrable G volume :=
    hGtest.contDiff.continuous.integrable_of_hasCompactSupport
      hGtest.hasCompactSupport
  have hGL2 : MemVectorL2 U G := memVectorL2_of_localVecTest hGtest
  have hPair : IntegrableOn (fun y ↦ vecDot (F y) (G y)) U volume :=
    integrableOn_vecDot_of_memVectorL2 hF hGL2
  rw [dualPairing_eq_ofReal U F G hPair]
  calc
    ENNReal.ofReal (volumeAverage U fun y ↦ vecDot (F y) (G y)) ≤
        ENNReal.ofReal |volumeAverage U fun y ↦ vecDot (F y) (G y)| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ((fractionalDualToBesovConstant d) ^ (2 : ℕ) * cap) ^
          (1 / 2 : ℝ) *
        (hardyConstant * hsNormSq U s G) ^ (1 / 2 : ℝ) := by
      exact ofReal_abs_globalPairing_le_printFaithfulFullDualCap system hd hU
        hUpos hUtop hs hsHalf (fun _ ↦ F) G
        (fun y ↦ vecDot (F y) (G y)) hPair (fun _ ↦ rfl)
        (fun i ↦ hF.mono_measure
          (Measure.restrict_mono (system.cell_subset i) le_rfl))
        (fun _ ↦ hGGlobal.mono_measure Measure.restrict_le_self)
        (hsNormSq_ruledCell_ne_top system hs hsHalf hGtest) hRow
        (hHardy G hGGlobal.integrableOn)
    _ ≤ ((fractionalDualToBesovConstant d) ^ (2 : ℕ) * cap) ^
          (1 / 2 : ℝ) * hardyConstant ^ (1 / 2 : ℝ) := by
      apply mul_le_mul le_rfl
      · apply ENNReal.rpow_le_rpow
        simpa only [mul_one] using
          (mul_le_mul_right test.2.2 hardyConstant)
        norm_num
      · exact bot_le
      · exact bot_le

/-- Once the converted flux rate is supplied, the domain comparison is
conditional only on the printed arbitrary-domain duality statement. -/
theorem rowConvertedTerminalBound_of_domainDuality [NeZero d]
    {U : Set (Vec d)} {rho Rad s epsilon Xval outputFactor : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U) (hUnonempty : U.Nonempty)
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (aPhysical : CoeffField d) (u h : H1Function U)
    (hF : MemVectorL2 U (fun x ↦ matVecMul (aPhysical x - 1) (u.grad x)))
    {capFlux hardyConstant boundaryEnergy : ℝ≥0∞} {Cdual : ℝ}
    (hRow : normalizedWhitneyRowEnergy system
      (physicalFullDualWhitneyFamilyCellEnergy system s
        (ruledPhysicalFluxDefectOnCell system aPhysical
          (fun _ ↦ identityConstantCoeffMatrix d) u)) ≤ capFlux)
    (hHardy : ∀ G : Vec d → Vec d,
      Integrable G (volume.restrict U) →
        PrintFaithfulPositiveTestRow system s G hardyConstant)
    (hDual : PrintFaithfulDomainFluxDefectDuality U s aPhysical u h Cdual)
    {C₀ : ℝ → ℝ → ℝ → ℝ} {g kappaRate : ℝ}
    (hRate : RowConvertedFluxScheduledRateAtWitness d C₀ g kappaRate Cdual
      capFlux hardyConstant boundaryEnergy s rho Rad epsilon Xval outputFactor) :
    ENNReal.ofReal outputFactor *
        (negSobolevNorm U s (fun x ↦ u.grad x - h.grad x) +
          negSobolevNorm U s (fun x ↦
            matVecMul (aPhysical x) (u.grad x) - h.grad x)) ≤
      ENNReal.ofReal (C₀ s rho Rad * (epsilon * Xval) ^ kappaRate) *
        boundaryEnergy ^ (1 / 2 : ℝ) := by
  have hfun : (fun _ x ↦ matVecMul (aPhysical x - 1) (u.grad x)) =
      ruledPhysicalFluxDefectOnCell system aPhysical
        (fun _ ↦ identityConstantCoeffMatrix d) u := by
    funext i x
    unfold ruledPhysicalFluxDefectOnCell
    rw [identityConstantCoeffMatrix_matrix]
  have hFluxNorm : negSobolevNorm U s
      (fun x ↦ matVecMul (aPhysical x - 1) (u.grad x)) ≤
      ((fractionalDualToBesovConstant d) ^ (2 : ℕ) * capFlux) ^
        (1 / 2 : ℝ) * hardyConstant ^ (1 / 2 : ℝ) := by
    apply negSobolevNorm_le_of_rowConvertedFluxCap system hU hUnonempty hs
      hsHalf _ hF
    · simpa only [hfun] using hRow
    · exact hHardy
  have hComparison := hDual.2.trans (mul_le_mul_right hFluxNorm _)
  have hOneRow :
      ((fractionalDualToBesovConstant d) ^ (2 : ℕ) * capFlux) ^
          (1 / 2 : ℝ) * hardyConstant ^ (1 / 2 : ℝ) ≤
        ruledScheduledTwoRowCap d hardyConstant capFlux := by
    unfold ruledScheduledTwoRowCap
    exact le_self_add
  calc
    ENNReal.ofReal outputFactor *
        (negSobolevNorm U s (fun x ↦ u.grad x - h.grad x) +
          negSobolevNorm U s (fun x ↦
            matVecMul (aPhysical x) (u.grad x) - h.grad x)) ≤
      ENNReal.ofReal outputFactor *
        (ENNReal.ofReal Cdual *
          (((fractionalDualToBesovConstant d) ^ (2 : ℕ) *
            capFlux) ^ (1 / 2 : ℝ) * hardyConstant ^ (1 / 2 : ℝ))) :=
        mul_le_mul_right hComparison _
    _ ≤ ENNReal.ofReal outputFactor *
        (ENNReal.ofReal Cdual *
          ruledScheduledTwoRowCap d hardyConstant capFlux) := by
      exact mul_le_mul_right (mul_le_mul_right hOneRow _) _
    _ ≤ ENNReal.ofReal (C₀ s rho Rad * (epsilon * Xval) ^ kappaRate) *
        boundaryEnergy ^ (1 / 2 : ℝ) := hRate.2

end

end RowSupply
end HighContrast
end HCPolySupport

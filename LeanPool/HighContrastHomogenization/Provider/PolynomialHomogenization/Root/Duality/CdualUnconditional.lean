/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.CubeProjectionStabilityDischarge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.CdualGaugeWitnessTerminal
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.GaugeWitnessPremiseTransport
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.AdaptedCellGaugeGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CdualConditionalTerminalProducer

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Duality.CdualUnconditional

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `Cdual` at the gauge witness, from consumer-supplied data only

Both exports below fix the constant **before** the comparison matrix, the cube
index, the translation, the domain and the order: `Cdual` depends on the
dimension alone, through the cube Calderón--Zygmund constant.  That is the
uniformity the frozen clause needs, since its `C₀` is fixed before `U`.

Every hypothesis is supplied by the consumer surface: the geometry, the order,
the gauge coefficient and the flux-defect `L²` membership come from the
frozen clause's binder surface, and the two PDE hypotheses of the printed lemma — `u − v ∈
H₀^{1−s}(U)`
and `∇·(a∇u − a₁∇v) = 0` — are taken at the **physical** domain, exactly as
`ScheduledLocalizationRowSupply` states them, and transported to the gauge
image here.  Every analytic input is proved.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The printed two-row duality at the gauge witness.**  `Cdual` is fixed
before the comparison matrix, the domain and the order; the two PDE premises are
consumed at the physical domain and transported here. -/
theorem exists_printFaithfulDomainFluxDefectDuality_gaugeWitness
    (d : ℕ) [NeZero d] :
    ∃ Cdual : ℝ, 0 ≤ Cdual ∧
      ∀ {abar : Mat d} (hS : (symmPart abar).PosDef) (zc : Vec d) (m : ℤ)
        {Uphys Uhat : Set (Vec d)},
        Uphys = (fun x => zc + matVecMul (matSqrt (symmPart abar)) x) ''
            openCubeSet (originCube d m) →
        Uhat = matImage (matSqrt (symmPart abar))⁻¹ Uphys →
        ∀ {s : ℝ}, 0 < s → s < 1 / 2 →
        ∀ (aPhysical : CoeffField d) (u h : H1Function Uphys)
          (uHat hHat : H1Function Uhat),
          uHat.grad = (fun y => matVecMul (matSqrt (symmPart abar))
            (u.grad (matVecMul (matSqrt (symmPart abar)) y))) →
          hHat.grad = (fun y => matVecMul (matSqrt (symmPart abar))
            (h.grad (matVecMul (matSqrt (symmPart abar)) y))) →
          MemAffineH10 Uphys h u →
          IsWeakSolutionOn aPhysical Uphys u.grad →
          IsWeakSolutionOn (fun _ => abar) Uphys h.grad →
          ∀ {aHat : CoeffField d},
            aHat = affineCoefficient (matSqrt (symmPart abar))
                (isUnit_det_matSqrt hS)
                (fun x => aPhysical x - skewPart abar) →
            MemVectorL2 Uhat
              (fun y => matVecMul (aHat y - 1) (uHat.grad y)) →
            PrintFaithfulDomainFluxDefectDuality Uhat s aHat uHat hHat Cdual := by
  obtain ⟨Cproj, hCproj, hstab⟩ :=
    exists_cubeGradientProjectionHsStability_originCube d
  refine ⟨2 * Cproj + 1, by linarith only [hCproj], ?_⟩
  intro abar hS zc m Uphys Uhat hUphys hUhat s hs hsHalf aPhysical u h uHat hHat
    huHat hhHat haff huPhys hhPhys aHat haHat hFdefect
  subst hUphys
  subst hUhat
  have hL : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hLsymm : matTranspose (matSqrt (symmPart abar)) =
      matSqrt (symmPart abar) := matTranspose_matSqrt hS
  have hUopen : IsOpen
      ((fun x => zc + matVecMul (matSqrt (symmPart abar)) x) ''
        openCubeSet (originCube d m)) :=
    isOpen_affineImage hL zc (isOpen_openCubeSet (originCube d m))
  have hgauge : matImage (matSqrt (symmPart abar))⁻¹
      ((fun x => zc + matVecMul (matSqrt (symmPart abar)) x) ''
        openCubeSet (originCube d m)) =
      translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ zc)
        (openCubeSet (originCube d m)) :=
    matImage_inv_affineImage hL zc (openCubeSet (originCube d m))
  have hVopen : IsOpen (matImage (matSqrt (symmPart abar))⁻¹
      ((fun x => zc + matVecMul (matSqrt (symmPart abar)) x) ''
        openCubeSet (originCube d m))) := by
    rw [hgauge]
    exact isOpen_translateSet (isOpen_openCubeSet (originCube d m)) _
  have hVfin : volume (matImage (matSqrt (symmPart abar))⁻¹
      ((fun x => zc + matVecMul (matSqrt (symmPart abar)) x) ''
        openCubeSet (originCube d m))) ≠ ⊤ := by
    rw [hgauge, volume_translateSet_eq]
    exact (volume_openCubeSet_lt_top (originCube d m)).ne
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn
      (matImage (matSqrt (symmPart abar))⁻¹
        ((fun x => zc + matVecMul (matSqrt (symmPart abar)) x) ''
          openCubeSet (originCube d m)))) := by
    constructor
    rw [volumeMeasureOn, Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hVfin
  have hpot := isPotentialZeroTraceOn_gaugeGradSub hL hLsymm
    hUopen.measurableSet u h haff uHat hHat huHat hhHat
  have hsolHat := isSolenoidalOn_gaugeFluxDefect hS hUopen.measurableSet hVopen
    aPhysical u h huPhys hhPhys uHat hHat huHat hhHat haHat hFdefect
  exact printFaithfulDomainFluxDefectDuality_of_cubeProjection_of_potential hL zc
    (originCube d m) rfl rfl hs hsHalf (hstab m hs hsHalf) aHat uHat hHat
    hFdefect hpot hsolHat

end

end RowSupply
end HighContrast
end HCPolySupport

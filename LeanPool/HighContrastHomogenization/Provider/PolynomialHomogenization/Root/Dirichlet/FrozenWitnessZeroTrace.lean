/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.CoefficientLocality
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessCubeSolutionData
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessClassBRows
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ScheduledLocalizationGaugeReduction

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessZeroTrace

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The zero-trace datum at the gauge cube

The cube solution takes its `zeroTraceDifference` as a binder.  This module
discharges it from the hole's own `MemH1a0` premise, through E15's
`exists_h10Function_gaugeCube_of_memH1a0` — the one matrix-and-translation
composite for `H10Function`, which until now had **no consumer anywhere in the
repository**.

The premises E15 asks for are all in hand at the frozen witness:

* `MeasurableSet U`, `volume U ≠ ⊤` — the `isOpen_witnessDomain` premise and the
`frozenWitness_physicalDomain_isOpenBoundedConvexDomain` premise;
* the a.e. ellipticity of a field agreeing with `scaledCoeff ε a` almost
  everywhere on the bounded witness domain — the globally elliptic companion of
  `IsAELocallyUniformlyElliptic.exists_ae_isEllipticMatrix_ae_eq_restrict`,
  which `memH1a0_congr_coeff` lets the `MemH1a0` datum be read at;
* the a.e. ellipticity of its affine pullback — the **public**
  `aeElliptic_affineCoefficient`,
  with `affineLowerEllipticity_pos` for the lower constant;
* the gauge identification and the convexity of the translated cube — that module and
  that module.

The value identity is then exact, not merely a.e.: E15 returns
`w.toFun y = (uFun - g₀.toFun) (S (y + c))`, and pullbacks give
`uObs.toFun y = uFun (S (y + c))` and `gObs.toFun y = g₀.toFun (S (y + c))`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-- **the analytic inputs (b), completed.**  The zero-trace difference of cube
solution, from the hole's `MemH1a0` datum. -/
theorem exists_frozenWitnessZeroTraceDifference [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} {j : ℤ} {z : Vec d} {epsilon : ℝ} {a : CoeffSpace d}
    (hepsilon : 0 < epsilon)
    (hU : U = (fun y : Vec d => z + matVecMul (matSqrt (symmPart abar)) y) ''
      openCubeSet (originCube d j))
    (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d) (g₀ : H1Function U)
    (hu0 : MemH1a0 (scaledCoeff epsilon a) U
      (fun x ↦ uFun x - g₀.toFun x) (fun x ↦ uGrad x - g₀.grad x))
    (uObs gObs : H1Function (openCubeSet (originCube d j)))
    (huObsFun : ∀ y : Vec d, uObs.toFun y =
      uFun (matVecMul (matSqrt (symmPart abar))
        (y + matVecMul (matSqrt (symmPart abar))⁻¹ z)))
    (hgObsFun : ∀ y : Vec d, gObs.toFun y =
      g₀.toFun (matVecMul (matSqrt (symmPart abar))
        (y + matVecMul (matSqrt (symmPart abar))⁻¹ z))) :
    ∃ w : H10Function (openCubeSet (originCube d j)),
      w.toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet (originCube d j))]
        fun x => uObs.toFun x - gObs.toFun x := by
  obtain ⟨lam, Lam, c, hlam, -, hell, hac⟩ :=
    (isAELocallyUniformlyElliptic_scaledCoeff hepsilon a
      ).exists_ae_isEllipticMatrix_ae_eq_restrict
      (frozenWitness_physicalDomain_isOpenBoundedConvexDomain hS hU
        ).isBoundedDomain.isBounded
  have hgauge := matImage_matSqrtInv_witness_eq_translateSet hS hU
  have hUmeas : MeasurableSet U := (isOpen_witnessDomain hS hU).measurableSet
  have hUfin : volume U ≠ ⊤ :=
    (frozenWitness_physicalDomain_isOpenBoundedConvexDomain hS hU
      ).volume_lt_top.ne
  have hGconv : IsOpenBoundedConvexDomain
      (translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z)
        (openCubeSet (originCube d j))) := by
    rw [← hgauge]
    exact frozenWitness_gaugeDomain_isOpenBoundedConvexDomain hS hU
  have hellG := aeElliptic_affineCoefficient (matSqrt (symmPart abar))
    (isUnit_det_matSqrt hS) hell
  obtain ⟨w, hwf, -⟩ :=
    EnergyPrice.exists_h10Function_gaugeCube_of_memH1a0
      (isUnit_det_matSqrt hS) hUmeas hUfin hlam hell
      (affineLowerEllipticity_pos hlam) hellG hgauge hGconv
      ((memH1a0_congr_coeff hac _ _).1 hu0)
  refine ⟨w, Filter.Eventually.of_forall fun y => ?_⟩
  simp only [hwf y, huObsFun y, hgObsFun y]

end

end RowSupply
end HighContrast
end HCPolySupport

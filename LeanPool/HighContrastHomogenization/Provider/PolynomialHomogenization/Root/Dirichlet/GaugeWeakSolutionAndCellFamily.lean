/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessGaugePullback
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CellFamilyAndFluxRow
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ScheduledLocalizationGaugeReduction

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.GaugeWeakSolutionAndCellFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Row 4′ (the gauge weak solution) and composed row 7

Rows 6 and 7 are built here.  Row 7's family producer lives in
`HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.CellFamilyAndFluxRow`.
The `HCPoly` tree carries only the **non-`_v2`** producer, whose
conclusion is `RuledCellPhysicalForcedFamily` rather than the older predicate
that the module consumes — which is why the search failed.

The real obstruction was neither producer but a step neither row states: both
want the weak-solution premise in the **gauge** frame, at `aHat` on `Uhat`,
while the module (row 4) delivers it in the **physical** frame.  That step —
row 4′ — is `exists_frozenWitnessGaugeWeakSolution` below, and it is exactly the
affine transfer `isWeakSolutionOn_skewCentered_matSqrtPullback_iff`
applied through `huHat`.  With it, row 7 is one composition.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## Row 4′ -/

/-- **Row 4′ — the gauge weak solution.**  Module physical weak solution
transports to the gauge frame at `aHat` and `uHat`, with no new
analytic input: the skew-centred square-root pullback is an
*equivalence*, and the `huHat` premise is precisely its pullback gradient. -/
theorem exists_frozenWitnessGaugeWeakSolution
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {Uphys : Set (Vec d)} (hUphys : IsOpenBoundedConvexDomain Uphys)
    {epsilon : ℝ} {a : CoeffSpace d}
    (u : H1Function Uphys)
    (huPhys : IsWeakSolutionOn (scaledCoeff epsilon a) Uphys u.grad)
    (uHat : H1Function (matImage (matSqrt (symmPart abar))⁻¹ Uphys))
    (huHat : uHat.grad = fun y ↦ matVecMul (matSqrt (symmPart abar))
      (u.grad (matVecMul (matSqrt (symmPart abar)) y))) :
    IsWeakSolutionOn
        (affineCoefficient (matSqrt (symmPart abar)) (isUnit_det_matSqrt hS)
          (fun z ↦ scaledCoeff epsilon a z - skewPart abar))
        (matImage (matSqrt (symmPart abar))⁻¹ Uphys) uHat.grad := by
  let : IsFiniteMeasure (volumeMeasureOn Uphys) :=
    hUphys.isFiniteMeasure_restrict_volume
  rw [huHat]
  exact (isWeakSolutionOn_skewCentered_matSqrtPullback_iff hS hUphys.isOpen
    (scaledCoeff epsilon a) u.memL2 u.gradMemL2 u.hasWeakGradient).mp huPhys

/-! ## Composed row 7 -/

/-- **Row 7 — `aCell`, `wCell`, `hfamily`.**  With the gauge weak solution of
row 4′ and the gauge-reduced source of
`exists_gaugeReducedSource`, the `_v2` cell family exists over the frozen
witness's ruled system.  This is the `aCell` premise/`wCell`/`hfamily` triple. -/
theorem exists_frozenWitnessCellFamily [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {a : CoeffSpace d}
    {Uhat : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem Uhat rho Rad)
    {aHat : CoeffField d}
    (haHat : aHat = affineCoefficient (matSqrt (symmPart abar))
      (isUnit_det_matSqrt hS)
      (fun z ↦ scaledCoeff epsilon a z - skewPart abar))
    (uHat : H1Function Uhat)
    (hWeak : IsWeakSolutionOn aHat Uhat uHat.grad) :
    ∃ (aCell : system.CellIndex → CoeffFamily d)
      (wCell : ∀ i, ForcedCubeSolution (whitneyCellCube system i) (aCell i)
        (0 : Vec d → Vec d)),
      RuledCellPhysicalForcedFamily system aHat uHat aCell wCell := by
  obtain ⟨aSource, haSource, haeSource⟩ :=
    exists_gaugeReducedSource hS hepsilon a
  refine exists_ruledCellPhysicalForcedFamily system aSource haSource aHat
    ?_ uHat hWeak
  rw [haHat]
  exact haeSource

end

end RowSupply
end HighContrast
end HCPolySupport

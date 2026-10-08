/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessPriceAtPrintOrder
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.ResidualScaledCoeffTransport
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RealTranslationCoeffSpace

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.EpsilonLambdaFrameReconciliation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The ε/λ reconciliation for the ENERGY leg recorded a microscopic-parameter mismatch as the
load-bearing open
item: the module prices at `scaledCoeff lambda a` with `lambda ∈ Icc 1 3`,
while the restated clause and the modules carry `scaledCoeff epsilon a`
with `epsilon ≤ 1`.

**The reconciliation is at a fixed generation, and it costs nothing.**  One
might expect the two samples to agree "on the cell of generation `j + N`, up to
the exact triadic dilation by `3 ^ N`".  That is *not* what
the ε-frame transport does, and the cell never moves: the λ-route dilates
the **coefficient sample**, not the cell.  With `lambda = epsilon * 3 ^ N` and
`aScaled = Quenched.physical_scale_coeff N a` (the restored sample
`x ↦ a (3 ^ N x)`),

```
scaledCoeff lambda aScaled  x = aScaled ((epsilon * 3 ^ N)⁻¹ • x)
                              = a (3 ^ N • ((epsilon * 3 ^ N)⁻¹ • x))
                              = a (epsilon⁻¹ • x) = scaledCoeff epsilon a x
```

almost everywhere — `RowSupply.scaledCoeff_mul_pow_physicalScaleCoeff_ae`
where the a.e. is forced only by the `AEEqFun` quotient in
`physical_scale_coeff`.  So the two coefficient fields are **equal**, not merely
comparable, and no constant and no generation shift appear.

This module carries that identity through the two wrappers the frozen witness
puts around it — the affine gauge `affineCoefficient (matSqrt (symmPart abar))`
and the translation by the gauge centre `matVecMul (matSqrt (symmPart abar))⁻¹ z`
— exactly as the RATE leg does at `158:89-120`, and delivers module the `hObs` premise binder from
the hole's own ε-shaped observation identification.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## The identity, under the affine gauge and a translation -/

/-- **The ε/λ frame identity, gauged and translated.**  The λ-route's
microscopic parameter `lambda = epsilon * 3 ^ N` applied to the restored sample
`Quenched.physical_scale_coeff N a` gives, almost everywhere on any set, the
same skew-centred affine coefficient as `epsilon` applied to `a`. -/
theorem affineTranslatedScaledCoeff_lambda_ae_epsilon
    {L : Mat d} (hL : IsUnit L.det) (b : Mat d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (N : ℕ) (a : CoeffSpace d)
    (c : Vec d) (V : Set (Vec d)) :
    (fun y : Vec d ↦ affineCoefficient L hL
        (fun w ↦ scaledCoeff (epsilon * (3 : ℝ) ^ N)
          (Quenched.physicalScaleCoefficient N a) w - b) (y + c))
      =ᵐ[volumeMeasureOn V]
      fun y : Vec d ↦ affineCoefficient L hL
        (fun w ↦ scaledCoeff epsilon a w - b) (y + c) :=
  affineTranslatedCenteredCoeff_congr_ae L hL b
    (scaledCoeff_mul_pow_physicalScaleCoeff_ae hepsilon N a) c V

/-! ## Module observation binder, from the hole's own -/

/-- **The energy leg's ε/λ reconciliation.**  The hole supplies the observation
family identified against `scaledCoeff epsilon a`; the module asks for it
against `scaledCoeff lambda aScaled`.  They are the same statement, on the same
cube of the same generation `j`, with the same centre — **no constant, no
generation shift, and no hypothesis beyond `0 < epsilon` and the λ-route's own
two equations**. -/
theorem witnessObservation_lambdaScaled_of_epsilon
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {N : ℕ} {lambda : ℝ}
    (hlambda : lambda = epsilon * (3 : ℝ) ^ N)
    {a aScaled : CoeffSpace d}
    (haScaled : aScaled = Quenched.physicalScaleCoefficient N a)
    {aFam : Book.Ch03.CoeffFamily d} {j : ℤ} {c : Vec d}
    (hObs : (aFam.coeffOn (originCube d j)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d j))]
      fun y ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun w ↦ scaledCoeff epsilon a w - skewPart abar) (y + c)) :
    (aFam.coeffOn (originCube d j)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d j))]
      fun y ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun w ↦ scaledCoeff lambda aScaled w - skewPart abar) (y + c) := by
  subst hlambda
  subst haScaled
  exact hObs.trans
    (affineTranslatedScaledCoeff_lambda_ae_epsilon (isUnit_det_matSqrt hS)
      (skewPart abar) hepsilon N a c (openCubeSet (originCube d j))).symm

end

end RowSupply
end HighContrast
end HCPolySupport

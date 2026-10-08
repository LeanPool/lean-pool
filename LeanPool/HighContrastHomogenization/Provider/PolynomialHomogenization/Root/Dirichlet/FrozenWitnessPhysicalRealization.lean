/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessClassBRows
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PhysicalH1Realization

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessPhysicalRealization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The composed row `u`/`huGrad`/`haff`/`huPhys`

This is the row whose producer,
`exists_h1Function_memAffineH10_of_memH1a0`, needs an `AEUniformlyEllipticField`
witness for `scaledCoeff ε a` that "exists only as a `private` helper from the modules named above
and must be re-proved".

It is re-proved here, from two **public** lemmas of
`HCPoly.Analytic.ScaledCoeff` — `aestronglyMeasurable_scaledCoeff` and
`isAELocallyUniformlyElliptic_scaledCoeff` — so the row composes with no new
mathematics, exactly as predicted.

The physical domain's convexity, which that module does not state, is recovered from
the gauge domain's: `Uphys = matImage (matSqrt (symmPart abar)) Uhat` and
`isOpenBoundedConvexDomain_matImage`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The scaled representative defines a source field with the same local
ellipticity data. -/
theorem exists_scaledCoeff_sourceField {ε : ℝ} (hε : 0 < ε) (a : CoeffSpace d) :
    ∃ aε : Source.AKL.Field d,
      AEUniformlyEllipticField aε ∧
        (⇑aε : CoeffField d) =ᵐ[volume] scaledCoeff ε a := by
  have hf : AEStronglyMeasurable (scaledCoeff ε a) volume :=
    aestronglyMeasurable_scaledCoeff hε a
  have hae : (⇑(AEEqFun.mk (scaledCoeff ε a) hf) : CoeffField d)
      =ᵐ[volume] scaledCoeff ε a :=
    AEEqFun.coeFn_mk (scaledCoeff ε a) hf
  exact ⟨AEEqFun.mk (scaledCoeff ε a) hf,
    (isAELocallyUniformlyElliptic_scaledCoeff hε a).congr hae.symm, hae⟩

/-- The physical frozen witness domain is a bounded open convex domain. -/
theorem frozenWitness_physicalDomain_isOpenBoundedConvexDomain
    {abar : Mat d} (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ}
    {z : Vec d}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j)) :
    IsOpenBoundedConvexDomain U := by
  have hback : matImage (matSqrt (symmPart abar))
      (matImage (matSqrt (symmPart abar))⁻¹ U) = U :=
    matImage_matSqrt_matImage_inv hS U
  rw [← hback]
  exact isOpenBoundedConvexDomain_matImage (isUnit_det_matSqrt hS)
    (frozenWitness_gaugeDomain_isOpenBoundedConvexDomain hS hU)

/-- **Row `u`/`huGrad`/`haff`/`huPhys`.**  The frozen clause's `MemH1a0` datum
is realized as an `H1Function` on the physical witness domain, with the frozen
affine boundary relation and the frozen weak-solution property transported to
it. -/
theorem exists_frozenWitnessPhysicalRealization [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ}
    {z : Vec d} {epsilon : ℝ} {a : CoeffSpace d}
    (hepsilon : 0 < epsilon)
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (g₀ h : H1Function U) (hgh : MemAffineH10 U g₀ h)
    (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d)
    (hu0 : MemH1a0 (scaledCoeff epsilon a) U
      (fun x ↦ uFun x - g₀.toFun x)
      (fun x ↦ uGrad x - g₀.grad x))
    (hweak : IsWeakSolutionOn (scaledCoeff epsilon a) U uGrad) :
    ∃ u : H1Function U,
      u.toFun = uFun ∧ u.grad = uGrad ∧ MemAffineH10 U h u ∧
        IsWeakSolutionOn (scaledCoeff epsilon a) U u.grad := by
  obtain ⟨aeps, haeps, haeq⟩ := exists_scaledCoeff_sourceField hepsilon a
  obtain ⟨u, hufun, hugrad, haff⟩ :=
    exists_h1Function_memAffineH10_of_memH1a0
      (frozenWitness_physicalDomain_isOpenBoundedConvexDomain hS hU) haeps haeq
      g₀ h hgh uFun uGrad hu0
  refine ⟨u, hufun, hugrad, haff, ?_⟩
  rw [hugrad]
  exact hweak

end

end RowSupply
end HighContrast
end HCPolySupport

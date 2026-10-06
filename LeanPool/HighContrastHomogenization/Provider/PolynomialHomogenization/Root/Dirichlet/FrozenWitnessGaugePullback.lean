/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessPhysicalRealization
public import LeanPool.HighContrastHomogenization.Analytic.AffineH10

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessGaugePullback

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The composed row `uHat`/`hHat`/`huHat`/`hhHat`

`exists_memAffineH10_affinePullback` pulls both the boundary datum and the
solution back through an invertible matrix, producing gradients
`fun y ↦ matVecMul (matTranspose L) (·.grad (matVecMul L y))`.  At
`L := matSqrt (symmPart abar)` the transpose is the matrix itself, because the
symmetric square root of a positive definite matrix is Hermitian, so the two
gradients land in exactly the `huHat` premise/`hhHat` shape.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The symmetric square root of a positive definite matrix is its own
transpose. -/
theorem matTranspose_matSqrt_symmPart {abar : Mat d}
    (hS : (symmPart abar).PosDef) :
    matTranspose (matSqrt (symmPart abar)) = matSqrt (symmPart abar) :=
  isSymm_of_isHermitian (matSqrt_spec hS.posSemidef).1.isHermitian

/-- **Row `uHat`/`hHat`/`huHat`/`hhHat`.**  The frozen affine boundary pair on
the physical witness domain pulls back to the gauge domain with exactly the
gradient identities that module requires. -/
theorem exists_frozenWitnessGaugePullback [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ}
    {z : Vec d}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (h u : H1Function U) (haff : MemAffineH10 U h u) :
    ∃ uHat hHat : H1Function (matImage (matSqrt (symmPart abar))⁻¹ U),
      uHat.grad = (fun y ↦ matVecMul (matSqrt (symmPart abar))
        (u.grad (matVecMul (matSqrt (symmPart abar)) y))) ∧
      hHat.grad = (fun y ↦ matVecMul (matSqrt (symmPart abar))
        (h.grad (matVecMul (matSqrt (symmPart abar)) y))) ∧
      MemAffineH10 (matImage (matSqrt (symmPart abar))⁻¹ U) hHat uHat := by
  have hL : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hUmeas : MeasurableSet U :=
    (frozenWitness_physicalDomain_isOpenBoundedConvexDomain hS hU).isOpen.measurableSet
  obtain ⟨hHat, uHat, -, hhgrad, -, hugrad, haffHat⟩ :=
    exists_memAffineH10_affinePullback hL hUmeas h u haff
  refine ⟨uHat, hHat, ?_, ?_, haffHat⟩
  · rw [hugrad, matTranspose_matSqrt_symmPart hS]
  · rw [hhgrad, matTranspose_matSqrt_symmPart hS]

end

end RowSupply
end HighContrast
end HCPolySupport

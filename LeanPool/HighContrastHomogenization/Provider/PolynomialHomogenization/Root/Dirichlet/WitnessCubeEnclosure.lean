/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.AnchoredCommonResidualParent
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.AdaptedCellGaugeGeometry

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeEnclosure

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The witness-cube enclosure

The `λ`-route composition at the frozen witness reduces to one named
geometric lemma: the witness-cube analogue of
`residualObservationTarget_subset_matImage`.  The ruled analogue proves that a
*ruled observation cube* of a Whitney system, pushed into residual affine
coordinates, lies inside the affine image of the gauge domain.  At the frozen
witness there is no Whitney system: the domain *is* a single affine cube,

```
U = (fun x => z + matSqrt (symmPart abar) x) '' openCubeSet (originCube d j)
```

and the target cube is the same cube at the same generation `j`, centred at the
gauge centre `matSqrt (symmPart abar)⁻¹ z`.  The gauge image of `U` is then the
*translate* of the open triadic cube by that centre
(`RowSupply.matImage_inv_affineImage`), and the enclosure is an identity
rather than a Whitney margin estimate.

After it, `exists_anchored_common_matImage_enclosingParent` composes and the
`hEnclose` binder of `observationHomogenizationError_le_referencePowerTail_fixedParent`
is discharged, at a parent generation chosen above both the reference tail shift
and the witness generation itself.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The witness-cube enclosure.**  In residual affine coordinates the frozen
witness target at generation `j`, anchored at the gauge centre, is contained in
the affine image of the gauge domain.  This is the witness analogue of
`residualObservationTarget_subset_matImage`. -/
theorem witnessObservationTarget_subset_matImage
    {abar : Mat d} (hS : (symmPart abar).PosDef) (lambda : ℝ) {j : ℤ}
    {z : Vec d} {U : Set (Vec d)}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j)) :
    adaptedCellTranslate (epsilonAffineGrid lambda abar) j
        (lambda⁻¹ • matVecMul (matSqrt (symmPart abar))
            (matVecMul (matSqrt (symmPart abar))⁻¹ z) +
          adaptedCellCenter (epsilonAffineGrid lambda abar) j 0) ⊆
      matImage (epsilonAffineGrid lambda abar)
        (matImage (matSqrt (symmPart abar))⁻¹ U) := by
  have hu : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hgauge : matImage (matSqrt (symmPart abar))⁻¹ U =
      translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z)
        (openCubeSet (originCube d j)) := by
    rw [hU]
    exact matImage_inv_affineImage hu z _
  have hcenterZero :
      adaptedCellCenter (epsilonAffineGrid lambda abar) j 0 = 0 := by
    rw [Recurrence.adaptedCellCenter_eq]
    have hz : standardCellCenter (d := d) j 0 = 0 := by
      funext i
      simp [standardCellCenter]
    rw [hz, matVecMul_zero]
  have hpsum : lambda⁻¹ • matVecMul (matSqrt (symmPart abar))
        (matVecMul (matSqrt (symmPart abar))⁻¹ z) =
      matVecMul (epsilonAffineGrid lambda abar)
        (matVecMul (matSqrt (symmPart abar))⁻¹ z) := by
    simp only [epsilonAffineGrid, smul_matVecMul]
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  rcases hv with ⟨w, hw, rfl⟩
  rw [hcenterZero, add_zero, hpsum]
  change matVecMul (epsilonAffineGrid lambda abar)
        (matVecMul (matSqrt (symmPart abar))⁻¹ z) +
      matVecMul (epsilonAffineGrid lambda abar) w ∈
    matImage (epsilonAffineGrid lambda abar)
      (matImage (matSqrt (symmPart abar))⁻¹ U)
  rw [← matVecMul_add]
  refine ⟨matVecMul (matSqrt (symmPart abar))⁻¹ z + w, ?_, rfl⟩
  rw [hgauge, mem_translateSet_iff_sub_mem, add_sub_cancel_left]
  exact hw

/-- The gauge domain of the frozen witness sits inside the normalized Euclidean
sublevel set, from the inner-ellipsoid normalization outer premise `U ⊆ ellipsoid abar 1` alone. -/
theorem gaugeDomain_subset_normalizedSublevel
    {abar : Mat d} (hS : (symmPart abar).PosDef) {U : Set (Vec d)}
    (hUsub : U ⊆ ellipsoid abar 1) :
    matImage (matSqrt (symmPart abar))⁻¹ U ⊆
      {y : Vec d | vecNormSq y ≤ specBound ((symmPart abar)⁻¹)} := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hmem : matVecMul (matSqrt (symmPart abar))⁻¹ x ∈
      matImage (matSqrt (symmPart abar))⁻¹ (ellipsoid abar 1) :=
    ⟨x, hUsub hx, rfl⟩
  rw [matImage_matSqrt_inv_ellipsoid_eq hS 1] at hmem
  have hmem' : vecNormSq (matVecMul (matSqrt (symmPart abar))⁻¹ x) ≤
      specBound ((symmPart abar)⁻¹) * 1 ^ 2 := hmem
  change vecNormSq (matVecMul (matSqrt (symmPart abar))⁻¹ x) ≤
    specBound ((symmPart abar)⁻¹)
  simpa only [one_pow, mul_one] using hmem'

/-- **The composed `hEnclose` at the frozen witness.**  The anchored selector's
common parent, taken above both a requested generation `n` and the witness
generation `j`, encloses the witness target.  This is exactly the last
hypothesis of
`observationHomogenizationError_le_referencePowerTail_fixedParent`
at `epsilon := lambda`, `K := j`,
`center := matVecMul (matSqrt (symmPart abar))⁻¹ z`. -/
theorem exists_witnessEnclosingParent [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) {lambda : ℝ}
    (hlambda : lambda ∈ Set.Icc (1 : ℝ) 3) {j : ℤ} {z : Vec d}
    {U : Set (Vec d)}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hUsub : U ⊆ ellipsoid abar 1) (n : ℤ) :
    ∃ M : ℤ, M = max (max n j) 1 ∧ n ≤ M ∧ j ≤ M ∧ (1 : ℤ) ≤ M ∧
      adaptedCellTranslate (epsilonAffineGrid lambda abar) j
          (lambda⁻¹ • matVecMul (matSqrt (symmPart abar))
              (matVecMul (matSqrt (symmPart abar))⁻¹ z) +
            adaptedCellCenter (epsilonAffineGrid lambda abar) j 0) ⊆
        adaptedCell (Selection.normalizedRoot (symmPart abar)) M := by
  obtain ⟨M, hMeq, _hle, hparent⟩ :=
    exists_anchored_common_matImage_enclosingParent hlambda hS
      (gaugeDomain_subset_normalizedSublevel hS hUsub) (max n j)
  refine ⟨M, hMeq, ?_, ?_, ?_, ?_⟩
  · rw [hMeq]
    exact le_trans (le_max_left n j) (le_max_left _ _)
  · rw [hMeq]
    exact le_trans (le_max_right n j) (le_max_left _ _)
  · rw [hMeq]
    exact le_max_right _ _
  · exact (witnessObservationTarget_subset_matImage hS lambda hU).trans hparent

end

end RowSupply
end HighContrast
end HCPolySupport

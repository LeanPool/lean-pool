/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedWeakSolutionPullback
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffSpace
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootPullback

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The exact-root affine pullback

The terminal cube solution exists only for the **base-rounded**
family: its coefficient-corrector-family premise does not accept the exact-root
`aRef`.  The obstruction is not analytic: the chain

```
isWeakSolutionOn_add_constSkew_iff → isWeakSolutionOn_smul_coefficient_iff
                                  → isWeakSolutionOn_affinePullback_iff
```

is entirely generic in the pullback matrix, and the rounded modules merely
instantiate it at
`baseRoundedGrid (symmPart abar)`.  This module instantiates the *same* chain at
`Selection.normalizedRoot (symmPart abar)` — the exact root — and identifies the
resulting coefficient with the large-scale C¹ slope approximation terminal's `bRef`.

Two facts make the exact-root instance no harder than the rounded one:

* the exact root is symmetric, because it is a positive scalar multiple of
  `matSqrt`, so the transpose in the general affine chain rule disappears
  exactly as it does for the rounded grid;
* the scalar normalizer `specBound ((symmPart abar)⁻¹)` is the *same* one
  `normalizedCenteredCoeff` applies, so the pulled-back coefficient is
  almost everywhere `affineCoefficient (Selection.normalizedRoot (symmPart abar)) _
  ⇑(normalizedCenteredCoeff a abar hS).1`, which is literally the terminal's
  `bRef`.

Nothing here is an estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The exact root as a pullback matrix -/

/-- The exact normalized root is invertible on a positive-definite symmetric
part. -/
theorem isUnit_det_exactRoot [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) :
    IsUnit (Selection.normalizedRoot (symmPart abar)).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (normalizedRoot_posDef_of_posDef hS).isUnit

/-- The exact normalized root is symmetric: it is a positive scalar multiple of
the symmetric square root. -/
theorem matTranspose_exactRoot [NeZero d] (m : Mat d) :
    matTranspose (Selection.normalizedRoot m) = Selection.normalizedRoot m := by
  have hsq : Matrix.transpose (matSqrt m) = matSqrt m := (isSymm_matSqrt m).eq
  show Matrix.transpose (Selection.normalizedRoot m) = Selection.normalizedRoot m
  rw [Selection.normalizedRoot_eq, Matrix.transpose_smul, hsq]

/-! ## The `H¹` pullback -/

/-- Pull back an `H¹` representative by the exact normalized root. -/
@[expose]
noncomputable def exactRootH1Pullback [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)}
    (hU : MeasurableSet U) (u : H1Function U) :
    H1Function (matImage (Selection.normalizedRoot (symmPart abar))⁻¹ U) :=
  Classical.choose
    (exists_h1Function_affinePullback (isUnit_det_exactRoot hS) hU u)

/-- Symmetry of the exact root turns the general transpose chain rule into the
exact-root gradient action. -/
theorem exactRootH1Pullback_grad [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)}
    (hU : MeasurableSet U) (u : H1Function U) :
    (exactRootH1Pullback abar hS hU u).grad =
      fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
        (u.grad (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) := by
  have hgrad := (Classical.choose_spec
    (exists_h1Function_affinePullback (isUnit_det_exactRoot hS) hU u)).2
  change (Classical.choose (exists_h1Function_affinePullback
    (isUnit_det_exactRoot hS) hU u)).grad = _
  calc
    _ = fun y ↦ matVecMul (matTranspose (Selection.normalizedRoot (symmPart abar)))
        (u.grad (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) := hgrad
    _ = _ := by rw [matTranspose_exactRoot]

/-! ## The exact-root centered coefficient -/

/-- The exact-root analogue of `roundedCenteredCoefficient`: skew recentering,
scalar normalization, exact-root pullback. -/
@[expose]
def exactRootCenteredCoefficient [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) (a : CoeffField d) : CoeffField d :=
  affineCoefficient (Selection.normalizedRoot (symmPart abar))
    (isUnit_det_exactRoot hS)
    (fun x ↦ specBound ((symmPart abar)⁻¹) • (a x - skewPart abar))

/-- **The exact-root centered coefficient is the large-scale C¹ slope approximation terminal's
`bRef`,
almost everywhere.**  The scalar normalizer is exactly the one
`normalizedCenteredCoeff` applies, so no factor survives. -/
theorem exactRootCenteredCoefficient_ae [NeZero d] (a : CoeffSpace d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    exactRootCenteredCoefficient abar hS (⇑a.1) =ᵐ[volume]
      affineCoefficient (Selection.normalizedRoot (symmPart abar))
        (isUnit_det_exactRoot hS) (⇑(normalizedCenteredCoeff a abar hS).1) :=
  affineCoefficient_congr_ae _ _ (normalizedCenteredCoeff_ae a abar hS).symm

/-! ## The weak-solution transfer -/

/-- **A physical weak solution is equivalent to its exact-root, skew-centered,
scalar-normalized affine pullback.**  This is the rounded centered-pullback
equivalence with `baseRoundedGrid` replaced by the exact root; every step of
the proof is generic in the matrix. -/
theorem isWeakSolutionOn_exactRootCenteredPullback_iff [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpen U) (a : CoeffField d) {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (hu : MemScalarL2 U u)
    (hDu : ∀ i, MemScalarL2 U fun x ↦ Du x i)
    (hweak : HasWeakGradientOn U u Du) :
    IsWeakSolutionOn a U Du ↔
      IsWeakSolutionOn (exactRootCenteredCoefficient abar hS a)
        (matImage (Selection.normalizedRoot (symmPart abar))⁻¹ U)
        (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
          (Du (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let b : CoeffField d := fun x ↦ a x - skewPart abar
  let mu : ℝ := specBound ((symmPart abar)⁻¹)
  have hmu : mu ≠ 0 := (specBound_inv_symmPart_pos hd hS).ne'
  have hk : IsSkewMat (skewPart abar) := matTranspose_skewPart abar
  have hfield : (fun x ↦ b x + skewPart abar) = a := by
    funext x
    simp only [b, sub_add_cancel]
  have hgauge :=
    isWeakSolutionOn_add_constSkew_iff hU b hu hDu hweak (skewPart abar) hk
  rw [hfield] at hgauge
  have hscale :=
    (isWeakSolutionOn_smul_coefficient_iff (U := U) b Du hmu).symm
  have haffine := isWeakSolutionOn_affinePullback_iff
    (isUnit_det_exactRoot hS) hU.measurableSet (fun x ↦ mu • b x) Du
  have hchain := hgauge.trans (hscale.trans haffine)
  have htranspose := matTranspose_exactRoot (d := d) (symmPart abar)
  simpa only [b, mu, exactRootCenteredCoefficient, htranspose] using hchain

end

end CorrectorComposition
end HighContrast
end HCPolySupport

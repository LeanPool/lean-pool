/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Attainment
public import LeanPool.HighContrastHomogenization.Setup.SchurPositivity
public import LeanPool.HighContrastHomogenization.Setup.SpectralNorm

/-!
# High-contrast homogenization: Consistency.PrintedForm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The intrinsic contrast and `Λ_0` in exactly their printed form

This module checks the definitions `blockContrast` and `bigLambdaRef`, together
with the derived constants `lambdaRef` and `aspectRatio`: the development's
encodings of the intrinsic contrast, the reference constant `Λ_0`, the reciprocal
`λ_0`, and the aspect ratio `Π` of `e.Theta.m` and `e.reference.aspect.ratio`.

If that check failed, those encodings would be infima of Loewner scalings with
nothing tying them to the objects the reference text prints, and the mismatch
would propagate through the development.  The intrinsic contrast `blockContrast`
could read `0` for a reason unrelated to the block, so the annealed contrast
`annealedContrast` of `e.Theta.m` would not be the paper's `Θ_m`, and the
conclusion `annealedContrast P mEnt - 1 ≤ δ` of `p.response.transfer` would
constrain the wrong quantity and could hold vacuously; the aspect ratio
`aspectRatio` would be the quotient of two quantities the paper does not name, so
the `Π`-bounds of `t.polynomial.entry` would bound the wrong constant.

This module is a consistency check of those definitions and is not a result of
the paper.  The reference text defines the intrinsic contrast and the reference
constant `Λ_0` as *minima over skew matrices of spectral norms*, while the
encodings are infima of Loewner scalings.  Three separate facts are needed to
identify the two readings, and all three are available on a symmetric positive
definite doubled block matrix:

* the Loewner-scaling infimum is the infimum of the family of conjugated norms;
* that infimum is attained, so it is a minimum;
* the members of the family are spectral norms, because the conjugated
  skew-corrected Schur form is symmetric positive semidefinite.

This file composes them, so that the encodings are stated to be the printed
objects with nothing left implicit.
-/

namespace HCPolySupport
namespace HighContrast

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **`Λ_0` is exactly the printed object**: the least value of
`|σ_0 + (k_0 - h)ᵗ σ_{*,0}^{-1} (k_0 - h)|` over the skew matrices, the bars
being the spectral norm. -/
theorem isLeast_norm_bigLambdaRef {E : BlockMat d} (hsymm : IsSymmetricBlockMat E)
    (hpos : Book.Ch02.BlockPosDef E) :
    IsLeast ((fun h => ‖skewCorrectedForm E h‖) '' {h : Mat d | IsSkewMat h})
      (bigLambdaRef E) := by
  have himage : (fun h => specBound (skewCorrectedForm E h)) ''
      {h : Mat d | IsSkewMat h} =
      (fun h => ‖skewCorrectedForm E h‖) '' {h : Mat d | IsSkewMat h} :=
    Set.image_congr fun h _ => specBound_eq_norm (posSemidef_skewCorrectedForm hsymm hpos h)
  rw [← himage]
  exact isLeast_bigLambdaRef hpos

/-- **The intrinsic contrast is exactly the printed object**: the least value of
`|σ_*^{-1/2} (σ + (k - h)ᵗ σ_*⁻¹ (k - h)) σ_*^{-1/2}|` over the skew matrices,
the bars being the spectral norm. -/
theorem isLeast_norm_blockContrast {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hpos : Book.Ch02.BlockPosDef H) :
    IsLeast ((fun h => ‖matSqrt H.lowerRight * skewCorrectedForm H h *
        matSqrt H.lowerRight‖) '' {h : Mat d | IsSkewMat h})
      (blockContrast H) := by
  have himage : (fun h => specBound (matSqrt H.lowerRight * skewCorrectedForm H h *
        matSqrt H.lowerRight)) '' {h : Mat d | IsSkewMat h} =
      (fun h => ‖matSqrt H.lowerRight * skewCorrectedForm H h *
        matSqrt H.lowerRight‖) '' {h : Mat d | IsSkewMat h} :=
    Set.image_congr fun h _ =>
      specBound_eq_norm (posSemidef_matSqrt_mul_skewCorrectedForm_mul hsymm hpos h)
  rw [← himage]
  exact isLeast_blockContrast hsymm hpos

/-- The printed value of `Λ_0` is realized at some skew matrix. -/
theorem exists_isSkewMat_bigLambdaRef_eq_norm {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) :
    ∃ h : Mat d, IsSkewMat h ∧ bigLambdaRef E = ‖skewCorrectedForm E h‖ := by
  obtain ⟨h, hskew, heq⟩ := (isLeast_norm_bigLambdaRef hsymm hpos).1
  exact ⟨h, hskew, heq.symm⟩

/-- The printed value of the intrinsic contrast is realized at some skew
matrix. -/
theorem exists_isSkewMat_blockContrast_eq_norm {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : Book.Ch02.BlockPosDef H) :
    ∃ h : Mat d, IsSkewMat h ∧ blockContrast H =
      ‖matSqrt H.lowerRight * skewCorrectedForm H h * matSqrt H.lowerRight‖ := by
  obtain ⟨h, hskew, heq⟩ := (isLeast_norm_blockContrast hsymm hpos).1
  exact ⟨h, hskew, heq.symm⟩

/-- The lower reference constant `λ_0 = |σ_{*,0}^{-1}|^{-1}` of
`e.reference.aspect.ratio` reads its spectral norm on the lower-right block, which
is positive semidefinite on a symmetric positive definite reference block. -/
theorem lambdaRef_eq_inv_norm {E : BlockMat d} (hsymm : IsSymmetricBlockMat E)
    (hpos : Book.Ch02.BlockPosDef E) : lambdaRef E = ‖E.lowerRight‖⁻¹ := by
  rw [lambdaRef, specBound_eq_norm (posSemidef_lowerRight hsymm hpos)]

/-- **The reference aspect ratio `Π` is exactly the printed quotient**
`Λ_0 / λ_0` of `e.reference.aspect.ratio`: both constants are read as printed, the
numerator being a minimum of spectral norms realized at a skew matrix and the
denominator the reciprocal spectral norm of the lower-right block. -/
theorem exists_isSkewMat_aspectRatio_eq_norm {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) :
    ∃ h : Mat d, IsSkewMat h ∧
      aspectRatio E = ‖skewCorrectedForm E h‖ / ‖E.lowerRight‖⁻¹ := by
  obtain ⟨h, hskew, hmin⟩ := exists_isSkewMat_bigLambdaRef_eq_norm hsymm hpos
  refine ⟨h, hskew, ?_⟩
  rw [aspectRatio, hmin, lambdaRef_eq_inv_norm hsymm hpos]

end

end HighContrast
end HCPolySupport

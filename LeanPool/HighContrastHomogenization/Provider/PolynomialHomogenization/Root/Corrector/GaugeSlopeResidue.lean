/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.IntrinsicCorrectorEvent
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGradientCubeIntegralTranslationStability
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.EquivariantPhysicalCorrectorFamilyWrapper
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PhysicalLiouvilleGauge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootAssembly
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1EquivariantPullbackEliminator
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.AffineLiouvilleClass
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleReverseValueGradient

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Corrector.GaugeSlopeResidue

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The gauge identification reduced to one slope equality

The normalized-root pullback of the marked pair is a Liouville-class solution
of the normalized affine coefficient, so reverse Liouville classification
already identifies it with the reference family's joint local limit — at
*some* slope, together with an additive constant.  What is not supplied by any
available ingredient is that the slope produced there is the pulled-back slope.

This module isolates exactly that.  Everything else in the gauge
identification of the corrector family is discharged: the elliptic
representative, the
Liouville input, the coefficient bridge, the value identity and the gradient
identity.  Two named inputs remain, one certificate-side and one analytic.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The normalized root is symmetric -/

/-- The normalized root of a positive-definite matrix is symmetric.  (The same
fact is proved privately upstream; it is restated here because the upstream
copy is `private`.) -/
theorem matTranspose_normalizedRoot [NeZero d] {m : Mat d} (hm : m.PosDef) :
    matTranspose (Selection.normalizedRoot m) = Selection.normalizedRoot m := by
  have hq := normalizedRoot_posDef_of_posDef hm
  simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using!
    hq.isHermitian

/-! ## The tolerance of the reverse classification at the private exponents -/

/-! ## The two named inputs -/

/-! ## The reduction -/

end

end Root
end HighContrast
end HCPolySupport

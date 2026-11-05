/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_Isogeny_ConditionalCurrency

import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_transcendental_j
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charZero
import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField

/-!
# Integer endomorphisms for a transcendental j-invariant

Over an algebraically closed field of characteristic zero, a finite integral self-embedding of an
elliptic function field induces a point-group endomorphism via divisor pushforward and `Pic0`.
`WeierstrassCurve.isogenyPointEnd` constructs this endomorphism, including the point/place
correspondence, Abel's theorem and the norm formula. None of these auxiliary structures is an
assumption of the public interface.

`WeierstrassCurve.isogenyEnd_eq_zsmul_of_transcendental_j` proves that this endomorphism is integer
multiplication when the j-invariant is transcendental over `ℚ`. This is a statement about the
endomorphisms represented by `Affine.IsogenyEndDatum`, not about arbitrary abstract group
endomorphisms of the points, nor a comparison with a separate scheme-theoretic endomorphism ring.
-/

namespace WeierstrassCurve

open Affine AlgebraicCurve

private noncomputable def isogenyEndGeometry
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    {g : GenusOnePlaceGate W.toAffine //
      @GenusOnePlaceGate.IsCentred F _ W.toAffine g ∧ @AbelTheorem F _ _ g _} := by
  classical
  have : IsDedekindDomain W.toAffine.CoordinateRing := CoordinateRing.isDedekindDomain W
  have : HasPrincipalDivisors F W.toAffine.FunctionField := hasPrincipalDivisors_functionField _
  exact Classical.indefiniteDescription _ exists_genusOnePlaceGate_isCentred_and_abelTheorem

public section

/-- The point-group endomorphism induced by a finite integral self-embedding of the function
field, with the divisor-theoretic infrastructure constructed rather than assumed. -/
noncomputable def isogenyPointEnd
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (D : IsogenyEndDatum W.toAffine) :
    AddMonoid.End W.toAffine.Point := by
  let geometry := isogenyEndGeometry W
  let : GenusOnePlaceGate W.toAffine := geometry.val
  have : GenusOnePlaceGate.IsCentred W.toAffine := geometry.property.1
  have : AbelTheorem W.toAffine := geometry.property.2
  exact D.pointEnd (forall_normFormulaAlong_of_isAlgClosed_of_charZero W.toAffine D)

/-- An elliptic curve with transcendental j-invariant has only integer endomorphisms among the
point-group endomorphisms induced by finite integral self-embeddings of its function field. -/
theorem isogenyEnd_eq_zsmul_of_transcendental_j
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (ht : Transcendental ℚ W.j)
    (D : IsogenyEndDatum W.toAffine) :
    ∃ m : ℤ, ∀ P : W.toAffine.Point, isogenyPointEnd W D P = m • P := by
  let geometry := isogenyEndGeometry W
  let : GenusOnePlaceGate W.toAffine := geometry.val
  have : GenusOnePlaceGate.IsCentred W.toAffine := geometry.property.1
  have : AbelTheorem W.toAffine := geometry.property.2
  exact IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j W
    (forall_normFormulaAlong_of_isAlgClosed_of_charZero W.toAffine) ht D

end

end WeierstrassCurve

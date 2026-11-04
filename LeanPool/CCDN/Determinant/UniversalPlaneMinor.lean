/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfacePositioning
public import LeanPool.CCDN.Determinant.GenericPlaneSmoothness
public import LeanPool.CCDN.Noether.UniversalPlane
import LeanPool.CCDN.Determinant.ClosedFormIntegerMinor
import LeanPool.CCDN.Noether.ClosedFormScaling
import LeanPool.CCDN.Noether.ShearNormalization

/-! The constructed positioned family is a specialization of the universal
family of all affine planes. Its nonzero minor therefore proves that a
universal parameter polynomial is nonzero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The second direction has zero first coordinate and generic transverse slopes. -/
def genericTransverseDirection (K F σ : Type*) [Field K] [Field F]
    [Algebra (MvPolynomial σ K) F] : Option σ → F :=
  fun i => Option.elim i 0 (fun j => algebraMap (MvPolynomial σ K) F (X j))

private lemma genericPlaneMap_affineCoordinates {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    genericPlaneMap K F σ (hypersurfaceAffineCoordinates a b hb f) =
      MvPolynomial.map (planeParameterEval (algebraMap K F)
        (algebraMap K F ∘ a) (algebraMap K F ∘ b) (genericTransverseDirection K F σ))
        (universalPlaneMap K (Option σ) f) := by
  rw [universalPlaneMap_specialize]
  have he : (genericPlaneMap K F σ).toRingHom.comp
      (hypersurfaceAffineCoordinates a b hb).toRingHom =
      eval₂Hom (C.comp (algebraMap K F))
        (fun i => C (algebraMap K F (a i)) + C (algebraMap K F (b i)) * X 0 +
          C (genericTransverseDirection K F σ i) * X 1) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change genericPlaneMap K F σ (hypersurfaceAffineCoordinates a b hb (C r)) = _
      rw [show hypersurfaceAffineCoordinates a b hb (C r) = C r from
        (hypersurfaceAffineCoordinates a b hb).commutes r]
      simp [genericPlaneMap]
    · intro i
      change genericPlaneMap K F σ (hypersurfaceAffineCoordinates a b hb (X i)) = _
      rw [hypersurfaceAffineCoordinates_X]
      cases i <;> simp [genericPlaneMap, genericTransverseDirection]
  exact RingHom.congr_fun he f

/-- Monic normalization changes the specialized equation only by a scalar. -/
lemma normalized_genericPlane_universal_specialization
    {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    [IsScalarTower K (MvPolynomial σ K) F]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    bivariateMap (algebraMap (MvPolynomial σ K) F)
      (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f)) =
      algebraMap K F (eval b (homogeneousComponent f.totalDegree f))⁻¹ •
        bivariateMap (planeParameterEval (algebraMap K F)
          (algebraMap K F ∘ a) (algebraMap K F ∘ b) (genericTransverseDirection K F σ))
          (universalPlanePolynomial f) := by
  rw [← genericPlaneMap_bivariate, normalizedHypersurfaceCoordinates, map_mul,
    genericPlaneMap_affineCoordinates, map_mul]
  rw [bivariate_smul_eq_constant_mul, universalPlanePolynomial, bivariatePolynomialEquiv_map]
  congr 1
  simp [genericPlaneMap, bivariatePolynomialEquiv_C]

/-- Every irreducible positive-degree hypersurface over an algebraically closed
field of characteristic zero or >2*d^2 has a nonzero minor in the UNIVERSAL affine-plane
parameter ring, not merely in a family through a fixed line. -/
theorem exists_universalPlane_minor
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    (closedFormCoefficientMatrix f.totalDegree (universalPlanePolynomial f)).HasNonzeroMinor
      (2 * f.totalDegree ^ 2 - 1) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨a, b, hb, _, rows, cols, hdet⟩ :=
    exists_positioned_genericPlane_minor f hf hpos hchar
  let R := MvPolynomial σ K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  have hne : φ (((closedFormCoefficientMatrix f.totalDegree
      (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).submatrix
        rows cols).det) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hdet
  rw [closedForm_minor_map, normalized_genericPlane_universal_specialization,
    closedForm_minor_smul, ← closedForm_minor_map] at hne
  refine ⟨rows, cols, ?_⟩
  intro he
  exact hne (by rw [he, map_zero, mul_zero])

end
end CCDN

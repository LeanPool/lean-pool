/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import LeanPool.CCDN.Algebra.BoundedLinearSeparation
import Mathlib.FieldTheory.PrimitiveElement

/-! Quantitative primitive elements and separation by affine coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A finite separating coordinate tuple has a primitive integer linear
combination with coefficients (1,k,...), where k<=n*[F:R]^2. -/
theorem exists_bounded_primitive_element {R F : Type*} [Field R] [CharZero R] [Field F]
    [Algebra R F] [Module.Finite R F] {n : ℕ} (a : Fin n → F)
    (hsep : Function.Injective (fun φ : F →ₐ[R] AlgebraicClosure R => fun j => φ (a j))) :
    ∃ k : ℕ, k ≤ n * (Module.finrank R F) ^ 2 ∧
      IntermediateField.adjoin R {∑ j : Fin n, a j * (k : F) ^ j.val} = ⊤ := by
  classical
  obtain ⟨k, hk, hinj⟩ := exists_bounded_moment_separation
    (fun φ : F →ₐ[R] AlgebraicClosure R => fun j => φ (a j)) hsep
  refine ⟨k, ?_, ?_⟩
  · simpa only [AlgHom.card R F (AlgebraicClosure R)] using hk
  · apply (Field.primitive_element_iff_algHom_eq_of_eval' R (AlgebraicClosure R)
      (fun x => IsAlgClosed.splits _) _).mpr
    intro φ ψ he
    apply hinj
    simpa only [map_sum, map_mul, map_pow, map_natCast] using he

/-- Maps from a fraction field are determined by the images of the
original affine coordinates, even when the scalar field contains a parameter. -/
private theorem curve_coordinate_embeddings_injective {K R F L σ : Type*}
    [Field K] [Field R] [Field F] [Field L]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
    [Algebra K L] [Algebra R L] [IsScalarTower K R L]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F] :
    Function.Injective (fun φ : F →ₐ[R] L => fun j : σ =>
      φ (algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (MvPolynomial.X j)))) := by
  intro φ ψ he
  let q := (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ I) F).comp (Ideal.Quotient.mkₐ K I)
  have hpoly : (φ.restrictScalars K).comp q = (ψ.restrictScalars K).comp q := by
    apply MvPolynomial.algHom_ext
    intro j
    exact congrFun he j
  have hfield : φ.toRingHom = ψ.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial σ K ⧸ I)
    intro a
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact AlgHom.congr_fun hpoly h
  ext x
  exact RingHom.congr_fun hfield x

/-- The quantitative primitive element applies to the original coordinates of
a curve's function field, with no coordinate-generation hypothesis left over. -/
theorem exists_bounded_curve_primitive_element {K R F : Type*}
    [Field K] [Field R] [CharZero R] [Field F]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
    [Module.Finite R F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F] :
    ∃ k : ℕ, k ≤ n * (Module.finrank R F) ^ 2 ∧
      IntermediateField.adjoin R
        {∑ j : Fin n, algebraMap (MvPolynomial (Fin n) K ⧸ I) F
          ((Ideal.Quotient.mk I) (MvPolynomial.X j)) * (k : F) ^ j.val} = ⊤ := by
  exact exists_bounded_primitive_element _ (curve_coordinate_embeddings_injective I)

end
end CCDN

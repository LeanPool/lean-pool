/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialLinearDescent
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
import LeanPool.CCDN.Algebra.IdealScalarDescent

/-! Scalar extension commutes with a polynomial image ideal.
Consequently a polynomial projection of a geometrically integral source
has a geometrically integral image. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Coefficient functionals commute with substitution of polynomials defined
over the base field, even though they need not preserve multiplication. -/
theorem polynomialCoefficientLinear_aeval
    {K L : Type*} [Field K] [Field L] [Algebra K L] {m n : ℕ}
    (φ : L →ₗ[K] K) (a : Fin m → MvPolynomial (Fin n) K)
    (g : MvPolynomial (Fin m) L) :
    polynomialCoefficientLinear φ
        (aeval (fun i => map (algebraMap K L) (a i)) g) =
      aeval a (polynomialCoefficientLinear φ g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp only [aeval_C, algebraMap_eq, polynomialCoefficientLinear_C]
  | add g h hg hh =>
      simp only [map_add, map_add, hg, hh]
  | mul_X g i hg =>
      rw [map_mul, aeval_X, polynomialCoefficientLinear_mul_map, hg]
      have hX : (X i : MvPolynomial (Fin m) L) =
          map (algebraMap K L) (X i) := by simp
      rw [hX, polynomialCoefficientLinear_mul_map, map_mul, aeval_X]

private lemma map_aeval_polynomial_substitution
    {K L : Type*} [Field K] [Field L] [Algebra K L] {m n : ℕ}
    (a : Fin m → MvPolynomial (Fin n) K) (f : MvPolynomial (Fin m) K) :
    map (algebraMap K L) (aeval a f) =
      aeval (fun i => map (algebraMap K L) (a i)) (map (algebraMap K L) f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, aeval_X, map_X, hf]

/-- A polynomial `f` lies in the kernel of the coordinate map `Y i ↦ a i` into
`MvPolynomial (Fin n) K ⧸ I` if and only if the substitution `aeval a f` lies in `I`. -/
lemma mem_projectionCoordinateMap_ker
    {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (a : Fin m → MvPolynomial (Fin n) K) (f : MvPolynomial (Fin m) K) :
    f ∈ RingHom.ker (projectionCoordinateMap I a) ↔ aeval a f ∈ I := by
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The scalar-extended image ideal is the image ideal of the scalar-extended
source. The substitution need not be linear, finite or birational. -/
theorem projection_kernel_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (a : Fin m → MvPolynomial (Fin n) K) :
    (RingHom.ker (projectionCoordinateMap I a)).map (map (algebraMap K L)) =
      RingHom.ker (projectionCoordinateMap (I.map (map (algebraMap K L)))
        (fun i => map (algebraMap K L) (a i))) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, mem_projectionCoordinateMap_ker,
      ← map_aeval_polynomial_substitution]
    exact Ideal.mem_map_of_mem _ ((mem_projectionCoordinateMap_ker I a f).mp hf)
  · intro g hg
    by_contra hnot
    obtain ⟨φ, hφ⟩ := exists_polynomialCoefficientLinear_not_mem
      (RingHom.ker (projectionCoordinateMap I a)) g hnot
    apply hφ
    rw [mem_projectionCoordinateMap_ker, ← polynomialCoefficientLinear_aeval]
    exact polynomialCoefficientLinear_mem_scalar_extension I _
      ((mem_projectionCoordinateMap_ker _ _ g).mp hg) φ

/-- If the ideal `I` stays prime after extending scalars from `K` to `L`, then so does the
kernel of the coordinate map `Y i ↦ a i` into `MvPolynomial (Fin n) K ⧸ I`, that is, the ideal
of the image of the polynomial map `a`. -/
theorem projection_kernel_geometrically_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K L))).IsPrime]
    (a : Fin m → MvPolynomial (Fin n) K) :
    ((RingHom.ker (projectionCoordinateMap I a)).map
      (map (algebraMap K L))).IsPrime := by
  rw [projection_kernel_scalar_extension]
  exact RingHom.ker_isPrime _

/-- A nonzero equation generating the image ideal remains
irreducible over every field extension where the source ideal stays prime. -/
theorem projection_equation_irreducible_map
    {K L : Type*} [Field K] [Field L] [Algebra K L] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K L))).IsPrime]
    (a : Fin m → MvPolynomial (Fin n) K)
    (f : MvPolynomial (Fin m) K) (hf : f ≠ 0)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    Irreducible (map (algebraMap K L) f) := by
  have hp := projection_kernel_geometrically_prime (L := L) I a
  rw [hker, Ideal.map_span, Set.image_singleton] at hp
  have hne : map (algebraMap K L) f ≠ 0 :=
    (map_ne_zero_iff _ (map_injective _ (algebraMap K L).injective)).mpr hf
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

end
end CCDN

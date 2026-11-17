/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Defs
import LeanPool.CCDN.Hilbert.FunctionFieldRank
import LeanPool.CCDN.Hilbert.PlaneHilbert
import LeanPool.CCDN.Projection.PlaneProjectionDegree
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.FieldTheory.PrimitiveElement

/-! A primitive plane coordinate gives a lower bound for the image equation's
 degree. Combined with the filtered upper bound, a parameter of full field
 degree forces a linear projection to preserve the affine Hilbert degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A plane relation bounds the algebraic degree of either coordinate over a
field containing a transcendental linear parameter. -/
private theorem minpoly_degree_le_plane_relation {K R F : Type*}
    [Field K] [Field R] [Field F] [Algebra K R] [Algebra R F] [Algebra K F]
    [IsScalarTower K R F] (ψ : MvPolynomial (Fin 2) K →ₐ[K] F)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hzero : ψ f = 0)
    (j k : Fin 2) (u : R) (hu : Transcendental K u)
    (he : ψ (X j) = algebraMap R F u) :
    (minpoly R (ψ (X k))).natDegree ≤ f.totalDegree := by
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  have hI : ∀ g ∈ I, ψ g = 0 := by
    intro g hg
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hg
    rw [map_mul, hzero, zero_mul]
  let φ : (MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] F := Ideal.Quotient.liftₐ I ψ hI
  have hφ (g : MvPolynomial (Fin 2) K) : φ ((Ideal.Quotient.mk I) g) = ψ g := rfl
  have hdegree : HasFilteredCurveDegree I f.totalDegree :=
    ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
      fun n hn => principal_plane_hilbert_function f hf hn⟩
  have hi : LinearIndependent R (fun i : Fin (minpoly R (ψ (X k))).natDegree =>
      φ ((Ideal.Quotient.mk I) ((X k) ^ i.val))) := by
    simpa only [hφ, map_pow] using (linearIndependent_pow (K := R) (ψ (X k)))
  have h := polynomial_parameter_rank_le (K := K) (R := R) (F := F)
    (ι := Fin (minpoly R (ψ (X k))).natDegree) I f.totalDegree hdegree φ (X j)
    (by simp) u hu (by rw [hφ]; exact he)
    (fun i : Fin (minpoly R (ψ (X k))).natDegree => (X k) ^ i.val) hi
  simpa only [Fintype.card_fin] using h

/-- The degree of a plane equation is at least the degree of a function-field
extension when its second coordinate is primitive over the parameter field. -/
private theorem primitive_field_degree_le_plane_relation {K R F : Type*}
    [Field K] [Field R] [Field F] [Algebra K R] [Algebra R F] [Algebra K F]
    [IsScalarTower K R F] [Module.Finite R F]
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] F)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hzero : ψ f = 0)
    (j k : Fin 2) (u : R) (hu : Transcendental K u)
    (he : ψ (X j) = algebraMap R F u)
    (hprim : IntermediateField.adjoin R {ψ (X k)} = ⊤) :
    Module.finrank R F ≤ f.totalDegree := by
  rw [← (Field.primitive_element_iff_minpoly_natDegree_eq R (ψ (X k))).mp hprim]
  exact minpoly_degree_le_plane_relation ψ f hf hzero j k u hu he

/-- Once the linear parameter has full field degree and the other coordinate
is primitive, the irreducible image equation preserves degree. -/
theorem plane_projection_degree_eq_of_full_parameter {K R F τ : Type*}
    [Field K] [Field R] [Field F] [Algebra K R] [Algebra R F] [Algebra K F]
    [IsScalarTower K R F] [Module.Finite R F] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (d : ℕ)
    (hdegree : HasFilteredCurveDegree I d)
    (φ : (MvPolynomial τ K ⧸ I) →ₐ[K] F)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f})
    (j k : Fin 2) (u : R) (hu : Transcendental K u)
    (he : φ ((Ideal.Quotient.mk I) (a j)) = algebraMap R F u)
    (hprim : IntermediateField.adjoin R {φ ((Ideal.Quotient.mk I) (a k))} = ⊤)
    (hrank : Module.finrank R F = d) : f.totalDegree = d := by
  classical
  let := Fintype.ofFinite τ
  apply Nat.le_antisymm (plane_projection_equation_degree_le I a ha d hdegree f hf hker)
  rw [← hrank]
  let ψ := φ.comp (projectionCoordinateMap I a)
  have hψ (i : Fin 2) : ψ (X i) = φ ((Ideal.Quotient.mk I) (a i)) := by
    simp [ψ, projectionCoordinateMap]
  have hz : projectionCoordinateMap I a f = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton f)
  exact primitive_field_degree_le_plane_relation ψ f hf (by simp [ψ, hz])
    j k u hu (by rw [hψ]; exact he) (by rw [hψ]; exact hprim)

end
end CCDN

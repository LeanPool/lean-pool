/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveFiltration
import LeanPool.CCDN.Algebra.CoordinatePowerGeneration
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The quotient by the infinity coordinate

The degree-`n+1` image in the quotient of the filtered homogeneous coordinate
algebra by its infinity coordinate has dimension `H(n+1)-H(n)`. Thus the
certified affine Hilbert degree is the eventual graded dimension of a
quotient ring.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- A homogeneous element with coefficient in the prescribed filtered space. -/
def projectiveMonomialMap {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    filteredCoordinateSpace I n →ₗ[K] projectiveCoordinateAlgebra I where
  toFun a := ⟨Polynomial.monomial n (a : MvPolynomial σ K ⧸ I),
    (projective_monomial_mem I n a).mpr a.property⟩
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c a := by apply Subtype.ext; simp

/-- `projectiveMonomialMap I n a` is the monomial `a · Tⁿ` in the homogeneous coordinate algebra. -/
@[simp] lemma projectiveMonomialMap_val {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (a : filteredCoordinateSpace I n) :
    (projectiveMonomialMap I n a : Polynomial (MvPolynomial σ K ⧸ I)) =
      Polynomial.monomial n (a : MvPolynomial σ K ⧸ I) := rfl

/-- The ideal cutting out the infinity section in the homogeneous coordinate ring. -/
def projectiveInfinityIdeal {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) : Ideal (projectiveCoordinateAlgebra I) :=
  Ideal.span {projectiveInfinityCoordinate I}

instance projectiveInfinityIdeal_twoSided {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) : (projectiveInfinityIdeal I).IsTwoSided := by
  constructor
  intro a b ha
  simpa only [smul_eq_mul, mul_comm a b] using (projectiveInfinityIdeal I).smul_mem b ha

/-- Divisibility by the new coordinate is exactly membership one step lower in
the affine degree filtration. -/
theorem projectiveMonomial_mem_infinityIdeal {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (a : filteredCoordinateSpace I (n + 1)) :
    projectiveMonomialMap I (n + 1) a ∈ projectiveInfinityIdeal I ↔
      (a : MvPolynomial σ K ⧸ I) ∈ filteredCoordinateSpace I n := by
  rw [projectiveInfinityIdeal,
    Ideal.mem_span_singleton (α := projectiveCoordinateAlgebra I)]
  constructor
  · rintro ⟨g, hg⟩
    have hc := congrArg (fun p : projectiveCoordinateAlgebra I =>
      (p : Polynomial (MvPolynomial σ K ⧸ I)).coeff (n + 1)) hg
    change (Polynomial.monomial (n + 1) (a : MvPolynomial σ K ⧸ I)).coeff (n + 1) =
      (Polynomial.X * (g : Polynomial (MvPolynomial σ K ⧸ I))).coeff (n + 1) at hc
    simp only [Polynomial.coeff_monomial_same, Polynomial.coeff_X_mul] at hc
    rw [hc]
    exact g.property n
  · intro ha
    refine ⟨projectiveMonomialMap I n ⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact (Polynomial.X_mul_monomial n (a : MvPolynomial σ K ⧸ I)).symm

/-- Map a homogeneous piece to the quotient by the infinity coordinate. -/
def projectivePieceToInfinity {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    filteredCoordinateSpace I (n + 1) →ₗ[K]
      projectiveCoordinateAlgebra I ⧸ projectiveInfinityIdeal I :=
  (Ideal.Quotient.mkₐ K (projectiveInfinityIdeal I)).toLinearMap.comp
    (projectiveMonomialMap I (n + 1))

private lemma projectivePieceToInfinity_ker {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    (projectivePieceToInfinity I n).ker =
      (filteredCoordinateSpace I n).comap (filteredCoordinateSpace I (n + 1)).subtype := by
  ext a
  change Ideal.Quotient.mk (projectiveInfinityIdeal I)
    (projectiveMonomialMap I (n + 1) a) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, projectiveMonomial_mem_infinityIdeal]
  rfl

/-- Degree-`n+1` elements of the infinity quotient ring. -/
def infinityGradedSpace {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Submodule K (projectiveCoordinateAlgebra I ⧸ projectiveInfinityIdeal I) :=
  (projectivePieceToInfinity I n).range

instance infinityGradedSpace_finite {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) : Module.Finite K (infinityGradedSpace I n) := by
  unfold infinityGradedSpace
  infer_instance

/-- The exact Hilbert difference for the homogeneous infinity quotient. -/
private theorem infinityGradedSpace_finrank {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Module.finrank K (infinityGradedSpace I n) +
      Module.finrank K (filteredCoordinateSpace I n) =
      Module.finrank K (filteredCoordinateSpace I (n + 1)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (projectivePieceToInfinity I n)
  rw [projectivePieceToInfinity_ker] at h
  have hk := Submodule.finrank_map_subtype_eq (filteredCoordinateSpace I (n + 1))
    ((filteredCoordinateSpace I n).comap (filteredCoordinateSpace I (n + 1)).subtype)
  rw [Submodule.map_comap_subtype,
    inf_eq_right.mpr (filteredCoordinateSpace_mono I (by omega))] at hk
  rw [← hk] at h
  exact h

/-- Every certified affine Hilbert degree is the eventual graded dimension of the
quotient by the infinity coordinate. -/
theorem infinityGradedSpace_eventually_degree {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) {d N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b) :
    ∀ n ≥ N, Module.finrank K (infinityGradedSpace I n) = d := by
  intro n hn
  have h0 := hdegree n hn
  have h1 := hdegree (n + 1) (by omega)
  have hs := infinityGradedSpace_finrank I n
  push_cast at h1
  nlinarith

end
end CCDN

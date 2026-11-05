/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import LeanPool.CCDN.Algebra.RadialHomogeneousMap
import LeanPool.CCDN.Algebra.IdealScalarDescent
import LeanPool.CCDN.Algebra.ProjectiveChartScalarExtension
import LeanPool.CCDN.Hilbert.HomogeneousPrimeComponents

/-! The projective closure ideal of an affine coordinate ideal. The
homogenizing parameter is a polynomial variable over the affine quotient,
so primeness and homogeneous components are proved directly. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Send the homogenizing coordinate to t and every affine coordinate to
its quotient class times t. -/
def projectiveClosureMap {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] Polynomial (MvPolynomial (Fin n) K ⧸ I) where
  toRingHom := (Polynomial.mapRingHom (Ideal.Quotient.mk I)).comp
    ((Polynomial.mapRingHom (affineChart n)).comp radialMap)
  commutes' c := by
    change Polynomial.map (Ideal.Quotient.mk I)
      (Polynomial.map (affineChart n) (radialMap (MvPolynomial.C c))) = _
    simp only [radialMap_C, Polynomial.map_C]
    rw [show affineChart n (C c) = C c by simp [affineChart], Polynomial.algebraMap_apply]
    congr 1

/-- The coefficient of `t ^ M` in `projectiveClosureMap I f` is the class modulo `I` of the
dehomogenization of the degree-`M` homogeneous component of `f`. -/
lemma projectiveClosureMap_coeff {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K) (M : ℕ) :
    (projectiveClosureMap I f).coeff M =
      Ideal.Quotient.mk I (affineChart n (homogeneousComponent M f)) := by
  change ((Polynomial.map (Ideal.Quotient.mk I))
    (Polynomial.map (affineChart n) (radialMap f))).coeff M = _
  simp only [Polynomial.coeff_map, radialMap_coeff]

/-- The projective closure of the affine coordinate ideal `I`: the homogeneous ideal of
polynomials in `n + 1` variables all of whose homogeneous components dehomogenize (by setting
`X 0 = 1`) into `I`, defined as the kernel of `projectiveClosureMap I`. -/
def projectiveClosureIdeal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) : Ideal (MvPolynomial (Fin (n + 1)) K) :=
  RingHom.ker (projectiveClosureMap I)

instance projectiveClosureIdeal_isPrime {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    (projectiveClosureIdeal I).IsPrime := RingHom.ker_isPrime _

/-- A polynomial lies in the projective closure ideal of `I` if and only if the dehomogenization
of each of its homogeneous components lies in `I`. -/
lemma mem_projectiveClosureIdeal_iff {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K) :
    f ∈ projectiveClosureIdeal I ↔
      ∀ M, affineChart n (homogeneousComponent M f) ∈ I := by
  change projectiveClosureMap I f = 0 ↔ _
  rw [Polynomial.ext_iff]
  simp only [projectiveClosureMap_coeff, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]

/-- A homogeneous polynomial lies in the projective closure ideal of `I` if and only if its
dehomogenization lies in `I`. -/
lemma homogeneous_mem_projectiveClosureIdeal_iff {K : Type*} [Field K] {n M : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f.IsHomogeneous M) :
    f ∈ projectiveClosureIdeal I ↔ affineChart n f ∈ I := by
  rw [mem_projectiveClosureIdeal_iff]
  constructor
  · intro h
    simpa only [homogeneousComponent_of_mem hf, ite_true] using h M
  · intro h N
    rw [homogeneousComponent_of_mem hf]
    split_ifs <;> simp_all only [map_zero, Ideal.zero_mem]

/-- The projective closure ideal is homogeneous: every homogeneous component of a member is a
member. -/
lemma projectiveClosureIdeal_homogeneous {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f ∈ projectiveClosureIdeal I) (M : ℕ) :
    homogeneousComponent M f ∈ projectiveClosureIdeal I := by
  rw [homogeneous_mem_projectiveClosureIdeal_iff I _ (homogeneousComponent_isHomogeneous _ _)]
  exact (mem_projectiveClosureIdeal_iff I f).mp hf M

/-- Closure commutes with arbitrary coefficient-field extension. -/
theorem projectiveClosureIdeal_scalar_extension {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    (projectiveClosureIdeal I).map (map (algebraMap K L)) =
      projectiveClosureIdeal (I.map (map (algebraMap K L))) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, mem_projectiveClosureIdeal_iff]
    intro M
    have he : homogeneousComponent M (map (algebraMap K L) f) =
        map (algebraMap K L) (homogeneousComponent M f) := by
      ext a
      simp only [coeff_homogeneousComponent, coeff_map]
      split_ifs <;> simp only [map_zero]
    rw [he, affineChart_map]
    exact Ideal.mem_map_of_mem _ ((mem_projectiveClosureIdeal_iff I f).mp hf M)
  · intro f hf
    by_contra hnot
    obtain ⟨φ,hφ⟩ :=
      exists_polynomialCoefficientLinear_not_mem (projectiveClosureIdeal I) f hnot
    apply hφ
    rw [mem_projectiveClosureIdeal_iff]
    intro M
    rw [← polynomialCoefficientLinear_homogeneousComponent,
      ← polynomialCoefficientLinear_affineChart]
    exact polynomialCoefficientLinear_mem_scalar_extension I _
      ((mem_projectiveClosureIdeal_iff _ f).mp hf M) φ

/-- If the extension of `I` to a field extension `L` of `K` is prime, then so is the extension of
the projective closure ideal of `I` to `L`. -/
theorem projectiveClosureIdeal_geometrically_prime {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [(I.map (map (algebraMap K L))).IsPrime] :
    ((projectiveClosureIdeal I).map (map (algebraMap K L))).IsPrime := by
  rw [projectiveClosureIdeal_scalar_extension]
  infer_instance

end
end CCDN

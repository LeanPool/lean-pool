/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Projection.InfinityParameterReduction

/-! The infinity ideal is homogeneous, so its geometric zero locus is closed
under scalar multiplication. This allows normalization into finite charts. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma leadingInfinityIdeal_homogeneousComponent_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K)
    (hf : f ∈ leadingInfinityIdeal I) (m : ℕ) :
    homogeneousComponent m f ∈ leadingInfinityIdeal I := by
  have hhom := homogeneousComponent_isHomogeneous m f
  change Ideal.Quotient.mk (projectiveInfinityIdeal I)
    (quotientRadialMap I (homogeneousComponent m f)) = 0
  rw [quotientRadialMap_homogeneous I _ m hhom, Ideal.Quotient.eq_zero_iff_mem]
  cases m with
  | succ n =>
    exact (projectiveMonomial_mem_infinityIdeal I n _).mpr
      (leadingInfinityIdeal_component_mem I f hf n)
  | zero =>
    have hm : quotientRadialMap I f ∈ projectiveInfinityIdeal I :=
      Ideal.Quotient.eq_zero_iff_mem.mp hf
    rw [projectiveInfinityIdeal,
      Ideal.mem_span_singleton (α := projectiveCoordinateAlgebra I)] at hm
    obtain ⟨g, hg⟩ := hm
    have he := congrArg (fun h : projectiveCoordinateAlgebra I =>
      (h : Polynomial (MvPolynomial σ K ⧸ I)).coeff 0) hg
    change ((quotientRadialMap I f : projectiveCoordinateAlgebra I) :
        Polynomial (MvPolynomial σ K ⧸ I)).coeff 0 =
        (Polynomial.X * (g : Polynomial (MvPolynomial σ K ⧸ I))).coeff 0 at he
    rw [quotientRadialMap_coeff, Polynomial.coeff_X_mul_zero] at he
    have hz : projectiveMonomialMap I 0
        ⟨(Ideal.Quotient.mk I) (homogeneousComponent 0 f),
          ⟨_, (mem_restrictTotalDegree _ _ _).mpr hhom.totalDegree_le, rfl⟩⟩ = 0 := by
      apply Subtype.ext
      simp only [projectiveMonomialMap_val, he, map_zero, ZeroMemClass.coe_zero]
    rw [hz]
    exact (projectiveInfinityIdeal I).zero_mem

/-- A homogeneous polynomial of degree `m` satisfies `f (c • z) = c ^ m * f z`. -/
lemma homogeneous_aeval_scale {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [Finite σ] (f : MvPolynomial σ K) {m : ℕ} (hf : f.IsHomogeneous m)
    (z : σ → L) (c : L) : aeval (fun j => c * z j) f = c ^ m * aeval z f := by
  classical
  let := Fintype.ofFinite σ
  conv_lhs => rw [f.as_sum, map_sum]
  conv_rhs => rw [f.as_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hedeg : e.degree = m := by
    rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
    exact hf (mem_support_iff.mp he)
  simp only [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hesum : ∑ j : σ, e j = m := by
    have hh := Finsupp.sum_fintype e (fun _ k => k) (by simp)
    exact hh.symm.trans hedeg
  rw [hesum]
  ring

/-- The zero locus of the ideal at infinity is a cone: it is stable under scaling by any `c`. -/
lemma infinity_zeroLocus_scale {K L σ : Type*} [Field K] [Field L]
    [Algebra K L] [Finite σ] (I : Ideal (MvPolynomial σ K)) (z : σ → L)
    (hz : z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I)) (c : L) :
    (fun j => c * z j) ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I) := by
  classical
  let := Fintype.ofFinite σ
  intro f hf
  rw [← sum_homogeneousComponent (φ := f), map_sum]
  apply Finset.sum_eq_zero
  intro m _
  rw [homogeneous_aeval_scale _ (homogeneousComponent_isHomogeneous m f)]
  rw [hz _ (leadingInfinityIdeal_homogeneousComponent_mem I f hf m), mul_zero]

end
end CCDN

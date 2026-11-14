/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.Algebra.MvPolynomial.Monad

/-! A linear homogeneous projection of a homogeneous quotient is strict
for the total-degree filtration: any image element of bounded degree has a
preimage of the same bounded degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def degreeTruncation {K σ : Type*} [Field K] (N : ℕ) :
    MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  ∑ i ∈ Finset.range (N + 1), homogeneousComponent i

private lemma degreeTruncation_apply {K σ : Type*} [Field K] (N : ℕ)
    (p : MvPolynomial σ K) :
    degreeTruncation N p = ∑ i ∈ Finset.range (N + 1), homogeneousComponent i p := by
  simp [degreeTruncation]

private lemma degreeTruncation_degree {K σ : Type*} [Field K] (N : ℕ)
    (p : MvPolynomial σ K) : (degreeTruncation N p).totalDegree ≤ N := by
  rw [degreeTruncation_apply]
  apply totalDegree_finsetSum_le
  intro i hi
  exact (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

private lemma degreeTruncation_eq_self {K σ : Type*} [Field K] (N : ℕ)
    (p : MvPolynomial σ K) (hp : p.totalDegree ≤ N) : degreeTruncation N p = p := by
  rw [degreeTruncation_apply]
  conv_rhs => rw [← sum_homogeneousComponent (φ := p)]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hp 1))
  intro i hi hnot
  apply homogeneousComponent_eq_zero
  have hh : ¬ i < p.totalDegree + 1 := by simpa only [Finset.mem_range] using hnot
  omega

/-- Substituting homogeneous linear forms commutes with taking homogeneous components: the
degree-`N` component of `aeval a p` is `aeval a` of the degree-`N` component of `p`. -/
lemma homogeneousComponent_aeval_linear {K σ τ : Type*} [Field K]
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (N : ℕ) (p : MvPolynomial σ K) :
    homogeneousComponent N (aeval a p) = aeval a (homogeneousComponent N p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial e c =>
    have hm := isHomogeneous_monomial c (rfl : e.degree = e.degree)
    have hm' : (aeval a (monomial e c)).IsHomogeneous e.degree := by
      simpa only [one_mul] using hm.aeval a ha
    rw [homogeneousComponent_of_mem hm, homogeneousComponent_of_mem hm']
    split_ifs <;> simp

private lemma degreeTruncation_aeval_linear {K σ τ : Type*} [Field K]
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (N : ℕ) (p : MvPolynomial σ K) :
    degreeTruncation N (aeval a p) = aeval a (degreeTruncation N p) := by
  simp only [degreeTruncation_apply, map_sum, homogeneousComponent_aeval_linear a ha]

/-- The projection of a homogeneous quotient by homogeneous linear forms `a` is strict for the
total-degree filtration: if the image of `p` has degree at most `N` in the quotient by `I`, then it
is the image of some `q` of total degree at most `N`. -/
theorem homogeneous_projection_filtered_lift
    {K σ τ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial τ K))
    (hI : IsHomogeneousIdeal I)
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (p : MvPolynomial σ K) (N : ℕ)
    (hp : projectionCoordinateMap I a p ∈ filteredCoordinateSpace I N) :
    ∃ q : MvPolynomial σ K, q.totalDegree ≤ N ∧
      projectionCoordinateMap I a q = projectionCoordinateMap I a p := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨f, hf, he⟩ := Submodule.mem_map.mp hp
  have hfd : f.totalDegree ≤ N := (mem_restrictTotalDegree _ _ _).mp hf
  have hmem : aeval a p - f ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    change projectionCoordinateMap I a p - (Ideal.Quotient.mk I) f = 0
    change projectionCoordinateMap I a p -
      (Ideal.Quotient.mkₐ K I).toLinearMap f = 0
    rw [he, sub_self]
  have htmem : degreeTruncation N (aeval a p - f) ∈ I := by
    rw [degreeTruncation_apply]
    exact I.sum_mem (fun i _ => hI _ hmem i)
  rw [map_sub, degreeTruncation_aeval_linear a ha, degreeTruncation_eq_self N f hfd] at htmem
  refine ⟨degreeTruncation N p, degreeTruncation_degree N p, ?_⟩
  have ht := Ideal.Quotient.eq_zero_iff_mem.mpr htmem
  rw [map_sub, sub_eq_zero] at ht
  exact ht.trans he

end
end CCDN

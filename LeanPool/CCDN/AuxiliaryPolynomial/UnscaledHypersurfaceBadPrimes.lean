/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ScaledHomogenization
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import LeanPool.CCDN.Algebra.HomogeneousChartIrreducible
import LeanPool.CCDN.Algebra.ScaledHypersurfaceModel
import LeanPool.CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Comparison with the affine bad-prime factor. For degree at least two the
homogeneous and affine bad-reduction predicates agree. In degree one, the
homogeneous bad-prime set can be smaller because affine degree loss can
produce a nonzero multiple of the homogenizing variable. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma affineChart_not_variable_dvd_of_full_degree {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0)
    (hd : (affineChart n f).totalDegree = f.totalDegree) : ¬ X 0 ∣ f := by
  rintro ⟨g, he⟩
  have hg : g ≠ 0 := by intro hz; exact hf (by rw [he, hz, mul_zero])
  have hdeg := totalDegree_mul_of_isDomain (X_ne_zero (0 : Fin (n + 1))) hg
  rw [← he, totalDegree_X] at hdeg
  have hchart : affineChart n f = affineChart n g := by
    rw [he, map_mul, show affineChart n (X 0) = 1 by simp [affineChart], one_mul]
  have hle := affineChart_totalDegree_le g
  rw [← hchart, hd, hdeg] at hle
  omega

/-- A nonzero integer polynomial is absolutely irreducible if and only if its ordinary
homogenization is. -/
lemma unscaledHomogenize_absolute_irreducible_iff {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    AbsolutelyIrreducible (scaledHomogenize f.totalDegree 1 f) ↔ AbsolutelyIrreducible f := by
  let φ := Int.castRingHom (AlgebraicClosure ℚ)
  have hd : (map φ f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective (RingHom.injective_int _) f
  have hfmap : map φ f ≠ 0 := by
    exact fun h => hf ((map_injective φ Int.cast_injective) (by simpa using h))
  dsimp only [AbsolutelyIrreducible]
  rw [scaledHomogenize_map, map_one]
  change Irreducible (scaledHomogenize f.totalDegree 1 (map φ f)) ↔ Irreducible (map φ f)
  constructor
  · intro hir
    have hhom := scaledHomogenize_homogeneous (1 : AlgebraicClosure ℚ) (map φ f) hd.le
    have hchart : affineChart n (scaledHomogenize f.totalDegree 1 (map φ f)) = map φ f := by
      rw [affineChart_scaledHomogenize_one]
    rw [← hchart]
    apply affineChart_irreducible_of_not_variable_dvd _ hhom hir
    apply affineChart_not_variable_dvd_of_full_degree _ hir.ne_zero
    rw [hchart, hhom.totalDegree hir.ne_zero, hd]
  · intro hir
    rw [← hd]
    exact scaledHomogenize_irreducible _ hir one_ne_zero

private lemma hypersurfaceBadReduction_unscaledHomogenize_imp {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) (p : ℕ) :
    HypersurfaceBadReduction (scaledHomogenize f.totalDegree 1 f) p →
      HypersurfaceBadReduction f p := by
  intro hbad
  let : Fact p.Prime := ⟨hbad.1⟩
  have hnot := (homogeneous_hypersurfaceBadReduction_iff _
    (scaledHomogenize_homogeneous 1 f le_rfl)
    (scaledHomogenize_ne_zero _ one_ne_zero hf) p).mp hbad
  refine ⟨hbad.1, ?_⟩
  by_cases hd : (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree = f.totalDegree
  · right
    intro hir
    apply hnot
    rw [scaledHomogenize_map, map_one, ← hd]
    exact scaledHomogenize_irreducible _ hir one_ne_zero
  · exact Or.inl hd

/-- Inclusion of the geometric bad-prime sets gives monotonicity of
 the corresponding factors, even across different numbers of variables. -/
theorem hypersurfaceBadPrimeFactor_mono_of_badReduction_imp {n m : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (g : MvPolynomial (Fin (m + 1)) ℤ)
    (hd : f.totalDegree = g.totalDegree)
    (habs : AbsolutelyIrreducible f → AbsolutelyIrreducible g)
    (hbad : ∀ q, HypersurfaceBadReduction f q → HypersurfaceBadReduction g q) :
    hypersurfaceBadPrimeFactor f ≤ hypersurfaceBadPrimeFactor g := by
  classical
  by_cases hf : AbsolutelyIrreducible f
  · have hg := habs hf
    let S := (finite_fin_hypersurface_bad_primes f hf
      (absolute_integer_polynomial_totalDegree_pos f hf)).toFinset
    let T := (finite_fin_hypersurface_bad_primes g hg
      (absolute_integer_polynomial_totalDegree_pos g hg)).toFinset
    have hS : ∀ q, q ∈ S ↔ stepanovThreshold f.totalDegree < q ∧ HypersurfaceBadReduction f q := by
      intro q
      exact Set.Finite.mem_toFinset _
    have hT : ∀ q, q ∈ T ↔ stepanovThreshold g.totalDegree < q ∧ HypersurfaceBadReduction g q := by
      intro q
      exact Set.Finite.mem_toFinset _
    have hsub : S ⊆ T := by
      intro q hq
      exact (hT q).mpr ⟨hd ▸ ((hS q).mp hq).1, hbad q ((hS q).mp hq).2⟩
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl S hS,
      hypersurfaceBadPrimeFactor_eq_exp g hg rfl T hT]
    apply Real.exp_le_exp.mpr
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro q hq _
    have hprime := ((hT q).mp hq).2.1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg q)
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf]
    exact hypersurfaceBadPrimeFactor_nonneg g

/-- Homogenization never enlarges the affine factor based on the repository's
 degree-loss-inclusive bad-reduction predicate. This holds also in degree one. -/
theorem hypersurfaceBadPrimeFactor_unscaledHomogenize_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f ≠ 0) :
    hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f) ≤
      hypersurfaceBadPrimeFactor f := by
  apply hypersurfaceBadPrimeFactor_mono_of_badReduction_imp
  · exact (scaledHomogenize_homogeneous 1 f le_rfl).totalDegree
      (scaledHomogenize_ne_zero _ one_ne_zero hf)
  · exact (unscaledHomogenize_absolute_irreducible_iff f hf).mp
  · exact hypersurfaceBadReduction_unscaledHomogenize_imp f hf

end
end CCDN

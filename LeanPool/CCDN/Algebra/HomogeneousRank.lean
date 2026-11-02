/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousMonomials
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import LeanPool.CCDN.Algebra.HomogeneousEvaluation
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hilbert.FilteredIntersection
import LeanPool.CCDN.Hilbert.HomogeneousHilbert

/-! The homogeneous Hilbert count bounds evaluation-matrix ranks.
The deficit includes every degree-allowed multiple of the defining equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- The `K`-linear map sending a polynomial in `n + 1` variables to its vector of coefficients
at the degree-`M` monomials, enumerated by `homogeneousMonomials n M`. -/
def homogeneousCoefficientMap (K : Type*) [Field K] (n M : ℕ) :
    MvPolynomial (Fin (n + 1)) K →ₗ[K] (Fin ((n + M).choose M) → K) :=
  LinearMap.pi fun j => lcoeff K (homogeneousMonomials n M j)

/-- The matrix of values of the degree-`M` monomials in `n + 1` variables at the points
`points i`: its `(i, j)` entry is the `j`-th monomial of `homogeneousMonomials n M` evaluated
at `points i`. -/
def homogeneousEvaluationMatrix (K : Type*) [Field K] (n M : ℕ) {t : ℕ}
    (points : Fin t → (Fin (n + 1) → K)) : Matrix (Fin t) (Fin ((n + M).choose M)) K :=
  fun i j => (homogeneousMonomials n M j).prod fun k e => points i k ^ e

/-- For a homogeneous polynomial `f` of degree `M`, multiplying the homogeneous evaluation matrix
by the coefficient vector of `f` gives the vector of values of `f` at the points. -/
lemma homogeneous_evaluation_mulVec {K : Type*} [Field K] {n M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M)
    (points : Fin t → (Fin (n + 1) → K)) (i : Fin t) :
    (homogeneousEvaluationMatrix K n M points *ᵥ homogeneousCoefficientMap K n M f) i =
      eval (points i) f := by
  symm
  calc
    eval (points i) f = eval (points i)
        (∑ j, monomial (homogeneousMonomials n M j) (f.coeff (homogeneousMonomials n M j))) :=
        congrArg (eval (points i)) (homogeneous_eq_sum_coeff f hf)
    _ = _ := by
      simp [homogeneousEvaluationMatrix, homogeneousCoefficientMap, mulVec, dotProduct,
        eval_monomial, mul_comm]

/-- For finitely many zeros of a nonzero homogeneous polynomial `f` of degree `d ≤ M`, the rank
of their degree-`M` evaluation matrix plus the dimension of the degree-`M` multiples of `f` is at
most the number of degree-`M` monomials. -/
private theorem homogeneous_evaluation_rank_bound {K : Type*} [Field K] {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → K)) (hzero : ∀ i, eval (points i) f = 0) :
    (homogeneousEvaluationMatrix K n M points).rank + (n + (M - d)).choose (M - d) ≤
      (n + M).choose M := by
  let A := homogeneousEvaluationMatrix K n M points
  let φ := homogeneousCoefficientMap K n M
  let U := homogeneousMultiples f d M
  let _ : Module.Finite K (homogeneousSubmodule (Fin (n + 1)) K (M - d)) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  let _ : Module.Finite K U := Module.Finite.of_fg
    ((homogeneousSubmodule_fg _ _ _).map (LinearMap.mulLeft K f))
  have hhom : ∀ u ∈ U, u.IsHomogeneous M := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    change (f * v).IsHomogeneous M
    simpa only [Nat.add_sub_of_le hdM] using hf.mul hv
  have hinj : Function.Injective (φ.domRestrict U) := by
    intro u v huv
    apply Subtype.ext
    have he : ∀ j, u.val.coeff (homogeneousMonomials n M j) =
        v.val.coeff (homogeneousMonomials n M j) := fun j => congrFun huv j
    rw [homogeneous_eq_sum_coeff u.val (hhom _ u.property),
      homogeneous_eq_sum_coeff v.val (hhom _ v.property)]
    simp only [he]
  have hdim := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_domRestrict] at hdim
  have hker : U.map φ ≤ A.mulVecLin.ker := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    change A *ᵥ φ u = 0
    ext i
    rw [homogeneous_evaluation_mulVec u (hhom _ hu)]
    obtain ⟨w, _, rfl⟩ := Submodule.mem_map.mp hu
    simp only [LinearMap.mulLeft_apply, eval_mul, hzero i, zero_mul, Pi.zero_apply]
  have hbound := finrank_map_add_kernel_subspace_le A.mulVecLin ⊤ (U.map φ) le_top hker
  rw [Submodule.map_top, hdim] at hbound
  change A.rank + Module.finrank K U ≤ Module.finrank K ↥(⊤ : Submodule K _) at hbound
  simpa only [U, homogeneousMultiples_finrank f hf0, finrank_homogeneousSubmodule_fin,
    finrank_top, Module.finrank_pi, Module.finrank_self, mul_one, Fintype.card_fin] using hbound

/-- For finitely many zeros of a nonzero homogeneous polynomial `f` of degree `d ≤ M` with
linearly independent degree-`M` evaluation rows, the number of points plus the dimension of the
degree-`M` multiples of `f` is at most the number of degree-`M` monomials. -/
private theorem homogeneous_independent_rows_hilbert_bound {K : Type*} [Field K] {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → K)) (hzero : ∀ i, eval (points i) f = 0)
    (hli : LinearIndependent K (homogeneousEvaluationMatrix K n M points).row) :
    t + (n + (M - d)).choose (M - d) ≤ (n + M).choose M := by
  have h := homogeneous_evaluation_rank_bound f hf hf0 hdM points hzero
  simpa only [hli.rank_matrix, Fintype.card_fin] using h

/-- The homogeneous evaluation matrix of integer points, computed over `ℚ`, is the cast of the
integer evaluation matrix of the degree-`M` monomials. -/
lemma homogeneousEvaluationMatrix_intCast {n M t : ℕ}
    (points : Fin t → (Fin (n + 1) → ℤ)) :
    homogeneousEvaluationMatrix ℚ n M (fun i j => (points i j : ℚ)) =
      (evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ) := by
  ext i j
  simp [homogeneousEvaluationMatrix, evaluationMatrix]

/-- For `t` integer zeros of a nonzero homogeneous integer polynomial `f` of degree `d ≤ M`
whose degree-`M` evaluation rows are linearly independent over `ℚ`, the count `t` plus the
dimension `(n + (M - d)).choose (M - d)` of the degree-`M` multiples of `f` is at most the
number `(n + M).choose M` of degree-`M` monomials in `n + 1` variables. -/
theorem integer_homogeneous_rows_hilbert_bound {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0)
    (hli : LinearIndependent ℚ
      ((evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ)).row) :
    t + (n + (M - d)).choose (M - d) ≤ (n + M).choose M := by
  have hfQ : map (Int.castRingHom ℚ) f ≠ 0 := by
    intro h
    apply hf0
    exact (map_injective (Int.castRingHom ℚ) Int.cast_injective) (h.trans (map_zero _).symm)
  have hzQ : ∀ i, eval (fun j => (points i j : ℚ)) (map (Int.castRingHom ℚ) f) = 0 := by
    intro i
    rw [eval_map]
    simpa only [Function.comp_def, Int.coe_castRingHom, hzero i, map_zero] using
      (eval₂_comp (Int.castRingHom ℚ) (points i) f).symm
  apply homogeneous_independent_rows_hilbert_bound _ (hf.map (Int.castRingHom ℚ)) hfQ hdM
    (fun i j => (points i j : ℚ)) hzQ
  simpa only [homogeneousEvaluationMatrix_intCast] using hli

end
end CCDN

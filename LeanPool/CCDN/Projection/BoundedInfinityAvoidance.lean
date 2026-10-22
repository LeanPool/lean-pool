/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Projection.CurvePrimitivePair
public import LeanPool.CCDN.Projection.InfinityParameterReduction
import LeanPool.CCDN.Algebra.BoundedLinearSeparation
import LeanPool.CCDN.Algebra.CoordinatePowerGeneration
import Mathlib.Algebra.Polynomial.OfFn

/-! An explicit bounded integer moment form avoids any prescribed finite set
of nonzero directions. No separation of pairs is needed for this step. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The moment coordinate `∑ j, k ^ j * X j` is homogeneous of degree one. -/
lemma momentCoordinate_homogeneous (K : Type*) [Field K] (n k : ℕ) :
    (momentCoordinate K n k).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- A moment form with parameter at most n times the number of directions
is nonzero on all those directions. -/
theorem exists_bounded_moment_nonvanishing {K ι : Type*} [Field K] [CharZero K]
    [Fintype ι] {n : ℕ} (v : ι → Fin n → K) (hv : ∀ i, v i ≠ 0) :
    ∃ k : ℕ, k ≤ n * Fintype.card ι ∧
      ∀ i, ∑ j : Fin n, v i j * (k : K) ^ j.val ≠ 0 := by
  classical
  let P (i : ι) : Polynomial K := Polynomial.ofFn n (v i)
  have hPn (i : ι) : P i ≠ 0 := by
    intro he
    apply hv i
    funext j
    have hc := congrArg (fun q : Polynomial K => q.coeff j.val) he
    simpa only [P, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
      Pi.zero_apply] using hc
  have hPd (i : ι) : (P i).natDegree ≤ n := by
    cases n with
    | zero => simp [P]
    | succ n => exact Nat.le_of_lt (Polynomial.ofFn_natDegree_lt (by omega) _)
  let Q := ∏ i, P i
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hPn i)
  have hd : Q.natDegree ≤ n * Fintype.card ι := by
    calc
      _ ≤ ∑ _i : ι, n := (Polynomial.natDegree_prod_le _ _).trans
        (Finset.sum_le_sum (fun i _ => hPd i))
      _ = _ := by simp [Nat.mul_comm]
  obtain ⟨k, hk, hval⟩ := polynomial_exists_small_nat_eval_ne_zero Q hQ
  refine ⟨k, hk.trans hd, ?_⟩
  intro i
  have hp : (∏ i, (P i).eval (k : K)) ≠ 0 := by
    simpa only [Q, Polynomial.eval_prod] using hval
  have hi := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  simpa only [P, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial] using hi

/-- Avoiding infinity gives the eventual recurrence of the original
coordinate filtration. -/
theorem filtration_recurrence_of_infinity_avoidance {K L σ : Type*}
    [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (l : MvPolynomial σ K) (hl : l.IsHomogeneous 1)
    (hzero : ∀ z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I ⊔ Ideal.span {l}), z = 0) :
    ∃ N : ℕ, ∀ m ≥ N, filteredCoordinateSpace I (m + 1) =
      filteredCoordinateSpace I m ⊔ (filteredCoordinateSpace I m).map
        (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨N, hN, hred⟩ := exists_power_reductions_of_infinity_avoidance I l hl hzero
  exact ⟨Fintype.card σ * N,
    eventual_generation_of_power_reductions I l hl.totalDegree_le N hN hred⟩

end
end CCDN

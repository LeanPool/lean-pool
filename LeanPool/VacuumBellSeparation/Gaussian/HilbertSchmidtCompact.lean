/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SquareSummableFamily

/-!
# Compactness from the actual Hilbert--Schmidt sum

Finite sums of actual rank-one operators converge in operator norm when
the squared norms of the basis images are summable. Consequently every
bounded operator with finite Hilbert--Schmidt sum is compact. In particular
the square root, and hence the operator itself, of a positive trace-class
operator is compact. No eigenbasis or finite-rank hypothesis is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap InnerProductSpace Filter
open scoped ENNReal lp Topology

variable {ι E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem norm_le_sqrt_basis_image_sum (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (hT : Summable fun i => ‖T (b i)‖ ^ 2) :
    ‖T‖ ≤ Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) := by
  have hrepr (x : F) :
      b.repr (T.adjoint x) = familyAnalysisVector (fun i => T (b i)) hT x := by
    ext i
    rw [b.repr_apply_apply, adjoint_inner_right, familyAnalysisVector_apply]
  calc
    ‖T‖ = ‖T.adjoint‖ := (adjoint.norm_map T).symm
    _ ≤ Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) := by
      apply T.adjoint.opNorm_le_bound (Real.sqrt_nonneg _)
      intro x
      rw [← b.repr.norm_map (T.adjoint x), hrepr]
      exact norm_familyAnalysisVector_le (fun i => T (b i)) hT x

/-- Basis finite rank given by `∑ i ∈ s, rankOne ℂ (T (b i)) (b i)`. -/
def basisFiniteRank (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F) (s : Finset ι) :
    E →L[ℂ] F := ∑ i ∈ s, rankOne ℂ (T (b i)) (b i)

omit [CompleteSpace E] [CompleteSpace F] in
theorem basisFiniteRank_apply_basis [DecidableEq ι] (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (s : Finset ι) (i : ι) : basisFiniteRank b T s (b i) = if i ∈ s then T (b i) else 0 := by
  classical
  have hb := orthonormal_iff_ite.mp b.orthonormal
  simp [basisFiniteRank, sum_apply, rankOne_apply, hb]

omit [CompleteSpace E] [CompleteSpace F] in
theorem isCompactOperator_rankOne (x : F) (y : E) :
    IsCompactOperator (rankOne ℂ x y) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
    (toSpanSingleton ℂ x)

omit [CompleteSpace E] [CompleteSpace F] in
theorem basisFiniteRank_isCompactOperator (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) (s : Finset ι) : IsCompactOperator (basisFiniteRank b T s) := by
  exact (compactOperator (RingHom.id ℂ) E F).sum_mem fun i _ =>
    isCompactOperator_rankOne (T (b i)) (b i)

theorem norm_sub_basisFiniteRank_le (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (hT : Summable fun i => ‖T (b i)‖ ^ 2) (s : Finset ι) :
    ‖T - basisFiniteRank b T s‖ ≤ Real.sqrt (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2) := by
  classical
  have hterm (i : ι) : ‖(T - basisFiniteRank b T s) (b i)‖ ^ 2 =
      if i ∉ s then ‖T (b i)‖ ^ 2 else 0 := by
    rw [sub_apply, basisFiniteRank_apply_basis]
    split_ifs <;> simp_all
  have hs : Summable fun i => ‖(T - basisFiniteRank b T s) (b i)‖ ^ 2 := by
    apply Summable.of_nonneg_of_le
      (f := fun i => ‖T (b i)‖ ^ 2)
      (g := fun i => ‖(T - basisFiniteRank b T s) (b i)‖ ^ 2)
      (fun i => sq_nonneg _) _ hT
    intro i
    by_cases hi : i ∉ s
    · simp only [hterm, ite_eq_left hi, le_refl]
    · simpa only [hterm, ite_eq_right hi] using (sq_nonneg ‖T (b i)‖)
  have hsum : (∑' i, ‖(T - basisFiniteRank b T s) (b i)‖ ^ 2) =
      ∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2 := by
    calc
      _ = ∑' i, Set.indicator {i | i ∉ s} (fun i => ‖T (b i)‖ ^ 2) i := by
        apply tsum_congr
        intro i
        simp only [hterm, Set.indicator_apply, Set.mem_ofPred_eq]
      _ = _ := (tsum_subtype {i | i ∉ s} (fun i => ‖T (b i)‖ ^ 2)).symm
  simpa only [hsum] using norm_le_sqrt_basis_image_sum b (T - basisFiniteRank b T s) hs

theorem basisFiniteRank_tendsto (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (hT : Summable fun i => ‖T (b i)‖ ^ 2) :
    Tendsto (basisFiniteRank b T) atTop (𝓝 T) := by
  have htail : Tendsto (fun s : Finset ι =>
      Real.sqrt (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp
        (tendsto_tsum_compl_atTop_zero fun i => ‖T (b i)‖ ^ 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ htail
  intro s
  rw [norm_sub_rev]
  exact norm_sub_basisFiniteRank_le b T hT s

theorem isCompactOperator_of_summable_basis_image (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) (hT : Summable fun i => ‖T (b i)‖ ^ 2) :
    IsCompactOperator T :=
  isCompactOperator_of_tendsto (basisFiniteRank_tendsto b T hT)
    (Eventually.of_forall fun s => basisFiniteRank_isCompactOperator b T s)

theorem isCompactOperator_of_hilbertSchmidt (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) (hT : basisHilbertSchmidtSquare b T < ∞) :
    IsCompactOperator T := by
  apply isCompactOperator_of_summable_basis_image b T
  have hs := ENNReal.summable_toReal hT.ne
  simpa only [basisHilbertSchmidtSquare, ENNReal.toReal_ofReal (sq_nonneg _)] using hs

theorem positiveTraceClass_sqrt_isCompactOperator {A : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) : IsCompactOperator (CFC.sqrt A : E →L[ℂ] E) := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  apply isCompactOperator_of_hilbertSchmidt b
  simpa only [positiveTrace_eq_basisSquareTrace b, basisSquareTrace,
    basisHilbertSchmidtSquare] using hA.2

theorem positiveTraceClass_isCompactOperator {A : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) : IsCompactOperator A := by
  have h := (positiveTraceClass_sqrt_isCompactOperator hA).clm_comp (CFC.sqrt A)
  have heq : (CFC.sqrt A).comp (CFC.sqrt A) = A := by
    change CFC.sqrt A * CFC.sqrt A = A
    rw [← pow_two, CFC.sq_sqrt A hA.1]
  simpa only [← ContinuousLinearMap.coe_comp, heq] using h

end VacuumBellSeparation.Gaussian

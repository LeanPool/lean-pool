/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.MomentBound
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Isotropic

/-!
# A-priori cumulant bounds for isotropic log-concave laws
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Analysis
namespace FunctionalInequalities.KLS.BKL

open FunctionalInequalities.Analysis.BakryEmery

variable {n : ℕ}

/-- A-priori cumulant bound in a fixed dimension. -/
theorem exists_norm_cumulant_le_isotropic (m : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
          KLS.LogConcave ν →
            KLS.Isotropic ν →
              IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
                ‖cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m‖ ≤ C := by
  classical
  let R : ℝ := 2 * Real.sqrt ((n : ℝ) + 1)
  let M : ℕ → ℝ := fun i =>
    (i.factorial : ℝ) / (Real.log 3 / (4 * R)) ^ i *
      ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))))
  let D : ℝ := 1 + ∑ i ∈ Finset.range (m + 1), |M i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (m + 1), |M i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (M i))
  have hD : 1 ≤ D := by dsimp [D]; linarith
  refine
    ⟨(m.factorial : ℝ) ^ 2 * D ^ m, mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _), ?_⟩
  intro ν hlc hiso hc
  apply
    norm_cumulant_le_of_moment_bounds (ν : Measure (EuclideanSpace ℝ (Fin n))) (r := 1)
      zero_lt_one (compact_support_integrable_exp _ hc 1)
  intro i hi him
  have hmoment : (∫ x, ‖x‖ ^ i ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ≤ M i :=
    (KLS.LogConcave.integral_norm_pow_le_of_isotropic hlc hiso i).2
  have hterm : |M i| ≤ ∑ j ∈ Finset.range (m + 1), |M j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (M j)) (Finset.mem_range.mpr (by omega))
  calc
    (∫ x, ‖x‖ ^ i ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ≤ M i := hmoment
    _ ≤ |M i| := le_abs_self _
    _ ≤ D := by dsimp [D]; linarith
    _ = D ^ 1 := (pow_one D).symm
    _ ≤ D ^ i := pow_le_pow_right₀ hD hi

/-- A-priori energy bound in a fixed dimension. -/
theorem exists_sum_sq_cumulant_le_isotropic (d : ℕ) :
    ∃ b : ℝ,
      0 ≤ b ∧
        ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
          KLS.LogConcave ν →
            KLS.Isotropic ν →
              IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
                ∀ u : EuclideanSpace ℝ (Fin n),
                  ∑ J : Fin d → Fin n,
                      cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
                          (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^
                        2 ≤
                    b * ‖u‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_norm_cumulant_le_isotropic (n := n) (d + 1)
  refine ⟨(n : ℝ) ^ d * C ^ 2, by positivity, ?_⟩
  intro ν hlc hiso hc u
  have hbasis (j : Fin n) : ‖EuclideanSpace.basisFun (Fin n) ℝ j‖ = 1 :=
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one j
  have hterm (J : Fin d → Fin n) :
    cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
          (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^
        2 ≤
      C ^ 2 * ‖u‖ ^ 2 := by
    have hop :=
      (cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)).le_opNorm
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))
    have habs :
      |cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))| ≤
        C * ‖u‖ := by
      calc
        _ ≤ ‖cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)‖ * ‖u‖ := by
          simpa only [Real.norm_eq_abs, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
            hbasis, Finset.prod_const_one, mul_one] using hop
        _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right (hbound ν hlc hiso hc) (norm_nonneg u)
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (norm_nonneg u))).2 habs
    simpa only [sq_abs, mul_pow] using hsq
  calc
    _ ≤ ∑ _J : Fin d → Fin n, C ^ 2 * ‖u‖ ^ 2 := Finset.sum_le_sum (fun J _ => hterm J)
    _ = ((n : ℝ) ^ d * C ^ 2) * ‖u‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ring


end FunctionalInequalities.KLS.BKL

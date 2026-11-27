/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialKernelMoments
public import LeanPool.VacuumBellSeparation.Polynomial.JointMidpointPolynomial

/-!
# Physical midpoint polynomials as actual finite-rank source forms

The affine substitution is performed on the polynomial itself. Its true
total degree does not increase, so the previously constructed moment
operator represents the literal physical kernel with cubic rank.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MvPolynomial MeasureTheory
open scoped InnerProductSpace

/-- Actual substitution of x/s minus the midpoint shift in every variable. -/
def jointPhysicalPolynomial (s : ℝ) (P : MvPolynomial (Fin 6) ℂ) :
    MvPolynomial (Fin 6) ℂ :=
  ∑ d ∈ P.support, C (P.coeff d) *
    ∏ j : Fin 6, (C ((s : ℂ)⁻¹) * X j - C (jointPhysicalMidpointShift j)) ^ d j

theorem eval_jointPhysicalPolynomial (s : ℝ) (P : MvPolynomial (Fin 6) ℂ)
    (z : Fin 6 → ℂ) :
    eval z (jointPhysicalPolynomial s P) = eval (jointPhysicalMidpoint s z) P := by
  rw [eval_eq' (jointPhysicalMidpoint s z) P]
  simp only [jointPhysicalPolynomial, eval_sum, eval_mul, eval_C, eval_prod,
    eval_pow, eval_sub, eval_X, jointPhysicalMidpoint, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [mul_comm ((s : ℂ)⁻¹)]

theorem totalDegree_jointPhysicalPolynomial_le (s : ℝ) (P : MvPolynomial (Fin 6) ℂ) :
    (jointPhysicalPolynomial s P).totalDegree ≤ P.totalDegree := by
  classical
  have hlin (j : Fin 6) :
      (C ((s : ℂ)⁻¹) * X j - C (jointPhysicalMidpointShift j) :
        MvPolynomial (Fin 6) ℂ).totalDegree ≤ 1 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by simp)
    · simp
  apply totalDegree_finsetSum_le
  intro d hd
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply (Finset.sum_le_sum (fun j _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hlin j)))).trans
  have hdegree := le_totalDegree hd
  rw [Finsupp.sum_fintype d (fun _ e => e) (fun _ => rfl)] at hdegree
  simpa only [mul_one] using hdegree

theorem jointPhysicalPolynomial_field_pairing {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (v : JointSourceMomentFamily hμ U)
    (s : ℝ) (P : MvPolynomial (Fin 6) ℂ) (x y : SourceTestSpace hμ U) :
    inner ℝ (x : SourceHilbert hμ U)
      (jointPolynomialMomentOperator (𝕜 := ℝ) v.field (jointPhysicalPolynomial s P)
        (y : SourceHilbert hμ U)) =
      (∫ z : JointKernelSpace, (x.1.1.1 z.fst : ℂ) * (y.1.1.1 z.snd : ℂ) *
        eval (jointPhysicalMidpoint s (jointComplexCoordinates z)) P).re := by
  simpa only [eval_jointPhysicalPolynomial] using
    jointPolynomial_field_pairing hμ U v (jointPhysicalPolynomial s P) x y

theorem jointPhysicalPolynomial_momentum_pairing {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (v : JointSourceMomentFamily hμ U)
    (s : ℝ) (P : MvPolynomial (Fin 6) ℂ) (x y : SourceTestSpace hμ U) :
    inner ℝ (x : SourceHilbert hμ U)
      (jointPolynomialMomentOperator (𝕜 := ℝ) v.momentum (jointPhysicalPolynomial s P)
        (y : SourceHilbert hμ U)) =
      (∫ z : JointKernelSpace, (x.1.2.1 z.fst : ℂ) * (y.1.2.1 z.snd : ℂ) *
        eval (jointPhysicalMidpoint s (jointComplexCoordinates z)) P).re := by
  simpa only [eval_jointPhysicalPolynomial] using
    jointPolynomial_momentum_pairing hμ U v (jointPhysicalPolynomial s P) x y

theorem jointMidpointMomentOperator_rank_le
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v : (Fin 3 → ℕ) → E) (s : ℝ) (F : (Fin 6 → ℂ) → ℂ) (n : ℕ) :
    Module.finrank 𝕜 (jointPolynomialMomentOperator (𝕜 := 𝕜) v
      (jointPhysicalPolynomial s (jointMidpointPolynomial F n))).toLinearMap.range ≤
        (9 * n + 1) ^ 3 := by
  exact finrank_jointPolynomialMomentOperator_le v _
    ((totalDegree_jointPhysicalPolynomial_le s _).trans (jointMidpointPolynomial_degree F n))

end VacuumBellSeparation

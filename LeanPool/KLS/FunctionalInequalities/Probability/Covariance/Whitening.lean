/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Whitening of a positive definite operator and of the covariance

Source: Blueprint `thm:affine-isotropic-reduction`, the sentence "whiten the centered intrinsic law
by `Cov_{μ,V}^{-1/2}`, which exists by `lem:ambient-intrinsic-covariance`". Read
`exists_whitening_of_isSymmetric` and `Covariance.exists_whitening`.

On a finite-dimensional real inner product space every symmetric operator `T` with
`⟪T v, v⟫ > 0` for `v ≠ 0` has a self-adjoint continuous linear equivalence `W` with
`⟪T (W u), W v⟫ = ⟪u, v⟫` for all `u, v`: take the orthonormal eigenbasis of `T` and scale each
eigenvector by the inverse square root of its (positive) eigenvalue. The public conclusion is the
self-adjoint whitening identity `W ∘ T ∘ W = 1`. The covariance operator of a Borel law is such a
`T` when it
is positive definite; the intrinsic covariance of a law with finite second moment is positive
definite by `lem:ambient-intrinsic-covariance`.

Only existence of a self-adjoint whitening is claimed; the statement does not assert positivity
or uniqueness of `W`, so its returned conditions do not characterize the positive inverse square
root `T^{-1/2}`. For example, `T = 1` and `W = -1` satisfy them. The isotropic reduction needs only
the whitening identity. The zero-dimensional space is included: the positivity premise is vacuous
and the unique linear equivalence satisfies the conclusion.

`Covariance.variance_inner_eq_of_sandwich` records the variance of a whitened linear statistic: for
a
probability law with finite second moment and a self-adjoint `S` with the actual sandwich
`S ∘ Cov ∘ S = 1`, `Var⟪S h, ·⟫ = ‖h‖²`. It is a deterministic support of the BKL (68) posterior
noise
estimate; the sandwich is a hypothesis, not a
produced root.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

namespace FunctionalInequalities

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A symmetric operator with positive definite quadratic form has a self-adjoint continuous linear
equivalence `W` with `⟪T (W u), W v⟫ = ⟪u, v⟫`. Positivity of `W` is not part of this conclusion. -/
theorem exists_whitening_of_isSymmetric (T : V →L[ℝ] V)
    (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ (T v) v) :
    ∃ W : V ≃L[ℝ] V, (W : V →L[ℝ] V).adjoint = W ∧
      ∀ u v, inner ℝ (T (W u)) (W v) = inner ℝ u v := by
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  set e := hT.eigenvectorBasis rfl with he
  set lam := hT.eigenvalues rfl with hlam
  have hTe : ∀ i, T (e i) = lam i • e i := fun i ↦ hT.apply_eigenvectorBasis rfl i
  have hlam_pos : ∀ i, 0 < lam i := by
    intro i
    have hne : e i ≠ 0 := by
      intro h0
      have := e.orthonormal.1 i
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have h2 := hpos (e i) hne
    rw [hTe i, real_inner_smul_left, real_inner_self_eq_norm_sq, e.orthonormal.1 i] at h2
    simpa using h2
  have hsqrt_pos : ∀ i, 0 < Real.sqrt (lam i) := fun i ↦ Real.sqrt_pos.mpr (hlam_pos i)
  -- `W₀ v = ∑ i, (√(lam i))⁻¹ * ⟪e i, v⟫ • e i`
  let W₀ : V →L[ℝ] V := ∑ i, (Real.sqrt (lam i))⁻¹ • (innerSL ℝ (e i)).smulRight (e i)
  have hW₀ : ∀ v, W₀ v = ∑ i, ((Real.sqrt (lam i))⁻¹ * inner ℝ (e i) v) • e i := by
    intro v
    simp only [W₀, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul]
    rfl
  have hcoef : ∀ i v, inner ℝ (e i) (W₀ v) = (Real.sqrt (lam i))⁻¹ * inner ℝ (e i) v := by
    intro i v
    rw [hW₀, e.orthonormal.inner_right_fintype]
  have hinj : Function.Injective W₀ := by
    intro u v huv
    have h : ∀ i, inner ℝ (e i) u = inner ℝ (e i) v := by
      intro i
      have := congrArg (fun w ↦ inner ℝ (e i) w) huv
      simp only [hcoef] at this
      exact mul_left_cancel₀ (inv_ne_zero (hsqrt_pos i).ne') this
    rw [← e.sum_repr' u, ← e.sum_repr' v]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [h i]
  let W : V ≃L[ℝ] V := (LinearEquiv.ofInjectiveEndo W₀.toLinearMap hinj).toContinuousLinearEquiv
  have hW : ∀ v, W v = W₀ v := fun v ↦ rfl
  have hsymm : ∀ u v, inner ℝ (W₀ u) v = inner ℝ u (W₀ v) := by
    intro u v
    rw [hW₀, hW₀, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, real_inner_smul_right, ← real_inner_comm u (e i)]
    ring
  refine ⟨W, ?_, ?_⟩
  · symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    exact hsymm x y
  · intro u v
    rw [hW, hW, hW₀ u, map_sum, sum_inner]
    have hterm : ∀ i, inner ℝ (T (((Real.sqrt (lam i))⁻¹ * inner ℝ (e i) u) • e i)) (W₀ v) =
        inner ℝ (e i) u * inner ℝ (e i) v := by
      intro i
      rw [map_smul, hTe i, smul_smul, real_inner_smul_left, hcoef]
      have hs : (Real.sqrt (lam i))⁻¹ * (Real.sqrt (lam i))⁻¹ * lam i = 1 := by
        rw [← mul_inv, Real.mul_self_sqrt (hlam_pos i).le]
        exact inv_mul_cancel₀ (hlam_pos i).ne'
      calc _ = ((Real.sqrt (lam i))⁻¹ * (Real.sqrt (lam i))⁻¹ * lam i) *
            (inner ℝ (e i) u * inner ℝ (e i) v) := by ring
        _ = _ := by rw [hs, one_mul]
    simp_rw [hterm]
    rw [← e.sum_inner_mul_inner u v]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm u (e i)]

namespace Covariance

variable [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]

/-- A positive definite covariance operator has a self-adjoint whitening `W` with
`⟪Σ (W u), W v⟫ = ⟪u, v⟫`, so that `W ∘ Σ ∘ W = 1`. -/
theorem exists_whitening (μ : MeasureTheory.Measure V)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ (operator μ v) v) :
    ∃ W : V ≃L[ℝ] V, (W : V →L[ℝ] V).adjoint = W ∧
      ∀ u v, inner ℝ (operator μ (W u)) (W v) = inner ℝ u v := by
  refine exists_whitening_of_isSymmetric (operator μ) ?_ hpos
  intro x y
  calc inner ℝ (operator μ x) y = ProbabilityTheory.covarianceBilin μ x y := operator_inner μ x y
    _ = ProbabilityTheory.covarianceBilin μ y x := ProbabilityTheory.covarianceBilin_comm x y
    _ = inner ℝ (operator μ y) x := (operator_inner μ y x).symm
    _ = inner ℝ x (operator μ y) := real_inner_comm _ _

section WhitenedStatistic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

private theorem finiteDimensional_marker (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Nonempty (FiniteDimensional ℝ E) :=
  ⟨inferInstance⟩

/--
**Variance of a whitened linear statistic**: for a probability law `μ` with finite second moment and
a
self-adjoint `S` with `S ∘ Cov(μ) ∘ S = 1`, `Var[⟪S h, x⟫] = ‖h‖²`. -/
theorem variance_inner_eq_of_sandwich (μ : Measure V) [IsProbabilityMeasure μ]
    (h2 : MemLp (id : V → V) 2 μ) (S : V →L[ℝ] V) (hS : IsSelfAdjoint S)
    (hsand : S * operator μ * S = 1) (h : V) : variance (fun x => ⟪S h, x⟫) μ = ‖h‖ ^ 2 := by
  have hSad : S.adjoint = S := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hS
  have hcomp : S (operator μ (S h)) = h := by
    have hfd := finiteDimensional_marker V
    have hsand_h : (S * operator μ * S) h = (1 : V →L[ℝ] V) h :=
      hfd.elim (fun _ => congrArg (fun T : V →L[ℝ] V => T h) hsand)
    simpa [mul_apply_eq_comp, one_apply_eq_self] using hsand_h
  calc
    variance (fun x => ⟪S h, x⟫) μ = covarianceBilin μ (S h) (S h) :=
      (covarianceBilin_self h2 (S h)).symm
    _ = ⟪operator μ (S h), S h⟫ := (Covariance.operator_inner μ (S h) (S h)).symm
    _ = ⟪S (operator μ (S h)), h⟫ := by
      simpa only [hSad] using (ContinuousLinearMap.adjoint_inner_right S (operator μ (S h)) h)
    _ = ⟪h, h⟫ := by rw [hcomp]
    _ = ‖h‖ ^ 2 := real_inner_self_eq_norm_sq h

end WhitenedStatistic

end Covariance

end FunctionalInequalities

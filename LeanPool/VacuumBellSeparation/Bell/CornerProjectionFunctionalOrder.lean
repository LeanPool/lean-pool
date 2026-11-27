/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.ProjectionFunctionalOrder
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Projection tests inside an actual supported corner

The corner is expressed by p*a=a in the original concrete VNA. No invented
normal representation, unitized corner carrier or corner spectral theorem
is assumed. The spectral projections commute with p; multiplying them by p
gives actual subprojections of p and retains the operator-norm approximation.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite positive spectral averages supported by the original projection p. -/
theorem exists_subprojection_average_near (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (a : M.toStarSubalgebra) (ha : 0 ≤ a) (han : ‖a‖ ≤ 1) (hpa : p * a = a)
    (N : ℕ) (hN : 0 < N) :
    ∃ Q : Fin N → M.toStarSubalgebra,
      (∀ k, IsStarProjection (Q k) ∧ Q k ≤ p) ∧
      ‖a - (1 / (N : ℝ)) • ∑ k, Q k‖ ≤ 1 / (N : ℝ) := by
  classical
  obtain ⟨P, hP, hcomm, herror⟩ :=
    exists_projection_average_near_positive_contraction M a ha han N hN
  have hap : a * p = a := by
    simpa only [star_mul, ha.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq]
      using congrArg star hpa
  have hpaComm : Commute (p : H →L[ℂ] H) (a : H →L[ℂ] H) := by
    change ((p * a : M.toStarSubalgebra) : H →L[ℂ] H) =
      ((a * p : M.toStarSubalgebra) : H →L[ℂ] H)
    rw [hpa, hap]
  have hpcoe : IsSelfAdjoint (p : H →L[ℂ] H) := hp.isSelfAdjoint.map M.toStarSubalgebra.subtype
  have hc (k : Fin N) : Commute p (P k) := by
    apply Subtype.ext
    exact (hcomm p hpcoe hpaComm k).eq
  let Q : Fin N → M.toStarSubalgebra := fun k => p * P k
  have hQ (k : Fin N) : IsStarProjection (Q k) := hp.mul (hP k) (hc k)
  have hQle (k : Fin N) : Q k ≤ p := (hQ k).le_iff_mul_eq_right hp |>.mpr (by
    change p * (p * P k) = p * P k
    rw [← mul_assoc, hp.isIdempotentElem.eq])
  have he : a - (1 / (N : ℝ)) • ∑ k, Q k =
      p * (a - (1 / (N : ℝ)) • ∑ k, P k) := by
    simp only [Q, mul_sub, hpa, mul_smul_comm, Finset.mul_sum]
  refine ⟨Q, fun k => ⟨hQ k, hQle k⟩, ?_⟩
  rw [he]
  calc
    _ ≤ ‖p‖ * ‖a - (1 / (N : ℝ)) • ∑ k, P k‖ := norm_mul_le _ _
    _ ≤ 1 * ‖a - (1 / (N : ℝ)) • ∑ k, P k‖ :=
      mul_le_mul_of_nonneg_right (IsStarProjection.norm_le p hp) (norm_nonneg _)
    _ ≤ 1 / (N : ℝ) := by simpa only [one_mul] using herror

/-- The all-positive comparison in the supported corner follows from its
subprojections; neither normality nor an assumed comparison on effects is used. -/
theorem continuousRealFunctional_nonneg_on_corner_of_subprojections
    (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (f : M.toStarSubalgebra →L[ℝ] ℝ)
    (hf : ∀ q : M.toStarSubalgebra, IsStarProjection q → q ≤ p → 0 ≤ f q)
    (a : M.toStarSubalgebra) (ha : 0 ≤ a) (hpa : p * a = a) : 0 ≤ f a := by
  classical
  have hcontraction (b : M.toStarSubalgebra) (hb : 0 ≤ b) (hbn : ‖b‖ ≤ 1)
      (hpb : p * b = b) : 0 ≤ f b := by
    have hchoose (n : ℕ) := exists_subprojection_average_near M p hp b hb hbn hpb
      (n + 1) (Nat.succ_pos n)
    choose Q hQ herror using hchoose
    let q : ℕ → M.toStarSubalgebra := fun n => (1 / ((n + 1 : ℕ) : ℝ)) • ∑ k, Q n k
    have hq (n : ℕ) : 0 ≤ f (q n) := by
      dsimp only [q]
      rw [map_smul, map_sum, smul_eq_mul]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ =>
        hf _ (hQ n k).1 (hQ n k).2)
    have ht : Tendsto q atTop (𝓝 b) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero (fun n => norm_nonneg _)
        (fun n => by simpa only [q, norm_sub_rev] using herror n)
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact ge_of_tendsto (f.continuous.tendsto b |>.comp ht) (Eventually.of_forall hq)
  by_cases hz : a = 0
  · simp only [hz, map_zero, le_refl]
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hscaled := hcontraction ((‖a‖⁻¹ : ℝ) • a)
    (smul_nonneg (inv_nonneg.mpr (norm_nonneg a)) ha)
    (norm_smul_inv_norm (𝕜 := ℝ) hz).le (by rw [mul_smul_comm, hpa])
  have hr : a = (‖a‖ : ℝ) • ((‖a‖⁻¹ : ℝ) • a) := by
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [hr, map_smul, smul_eq_mul]
  exact mul_nonneg (norm_nonneg a) hscaled

/-- Exact positive-functional corner comparison used after the maximal
orthogonal-family argument. -/
theorem positiveFunctional_re_le_on_corner_of_subprojections
    (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hφψ : ∀ q : M.toStarSubalgebra, IsStarProjection q → q ≤ p → (φ q).re ≤ (ψ q).re)
    (a : M.toStarSubalgebra) (ha : 0 ≤ a) (hpa : p * a = a) : (φ a).re ≤ (ψ a).re := by
  let f : M.toStarSubalgebra →L[ℝ] ℝ := Complex.reCLM.comp
    (((PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap -
      (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap).restrictScalars ℝ)
  have h := continuousRealFunctional_nonneg_on_corner_of_subprojections M p hp f
    (fun q hq hqp => by
      change 0 ≤ (ψ q - φ q).re
      rw [Complex.sub_re]
      exact sub_nonneg.mpr (hφψ q hq hqp)) a ha hpa
  change 0 ≤ (ψ a - φ a).re at h
  rw [Complex.sub_re] at h
  exact sub_nonneg.mp h

end VacuumBellSeparation

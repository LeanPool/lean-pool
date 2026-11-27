/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.SpectralReflectionQuadraticIntegral
public import LeanPool.VacuumBellSeparation.Bell.KaplanskyContractions
public import LeanPool.VacuumBellSeparation.Bell.StateExtension
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Projection tests determine the order of continuous functionals

Every positive contraction in an actual concrete von Neumann algebra is a
norm limit of positive averages of its actual spectral projections. Hence a
continuous real functional nonnegative on every projection is nonnegative
on the entire positive cone. No normality, trace, countability, finite
dimension or spectral-gap hypothesis is used here.

This is the spectral step in the corner argument of Anantharaman--Popa,
Section 2.5, Lemma 2.5.6.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Filter ReflectionApprox
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance projectionOrder_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- Actual projections in M, with a uniform norm error. The number of summands
is positive; no assertion about a nonexistent average with zero terms is made. -/
theorem exists_projection_average_near_positive_contraction (M : VonNeumannAlgebra H)
    (a : M.toStarSubalgebra) (ha : 0 ≤ a) (han : ‖a‖ ≤ 1)
    (N : ℕ) (hN : 0 < N) :
    ∃ P : Fin N → M.toStarSubalgebra, (∀ k, IsStarProjection (P k)) ∧
      (∀ S : H →L[ℂ] H, IsSelfAdjoint S → Commute S (a : H →L[ℂ] H) →
        ∀ k, Commute S (P k : H →L[ℂ] H)) ∧
      ‖a - (1 / (N : ℝ)) • ∑ k, P k‖ ≤ 1 / (N : ℝ) := by
  classical
  let A : H →L[ℂ] H := a
  have hA : 0 ≤ A := ha
  have hA1 : A ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg A hA).mp han
  let T : H →L[ℂ] H := (2 : ℝ) • A - 1
  have hT := two_smul_effect_sub_one_contraction hA hA1
  have hTM : T ∈ M := sub_mem
    ((M.toStarSubalgebra.toSubalgebra.toSubmodule.restrictScalars ℝ).smul_mem 2 a.property)
    (one_mem M)
  let P : Fin N → M.toStarSubalgebra := fun k =>
    ⟨closedThresholdProjection T (threshold N k), closedThresholdProjection_mem M hTM _⟩
  have hP (k : Fin N) : IsStarProjection (P k) := by
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      exact closedThresholdProjection_idem T _
    · apply Subtype.ext
      exact (closedThresholdProjection_isSelfAdjoint T _).star_eq
  have hcomm (S : H →L[ℂ] H) (hS : IsSelfAdjoint S)
      (hSa : Commute S (a : H →L[ℂ] H)) (k : Fin N) :
      Commute S (P k : H →L[ℂ] H) := by
    have hST : S * T = T * S := by
      dsimp only [T, A]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hSa.eq]
    have hneg : S * (-T) = (-T) * S := by
      simpa only [mul_neg, neg_mul] using congrArg Neg.neg hST
    have hstar : star S * (-T) = (-T) * star S := by
      rw [hS.star_eq]
      exact hneg
    have hc := thresholdProjection_commute hneg hstar (-(threshold N k))
    change S * (1 - thresholdProjection (-T) (-(threshold N k))) =
      (1 - thresholdProjection (-T) (-(threshold N k))) * S
    simp only [mul_sub, sub_mul, mul_one, one_mul, hc]
  let S : H →L[ℂ] H := ∑ k : Fin N, (P k : H →L[ℂ] H)
  have hsum : S = ∑ k ∈ Finset.range N, closedThresholdProjection T (threshold N k) :=
    Fin.sum_univ_eq_sum_range (fun k => closedThresholdProjection T (threshold N k)) N
  have hn : ‖T - ((2 / (N : ℝ)) • S - 1)‖ ≤ 2 / (N : ℝ) := by
    rw [hsum]
    exact closedThreshold_chain_norm_le hT.1 hT.2 hN
  have he : A - (1 / (N : ℝ)) • S =
      (1 / 2 : ℝ) • (T - ((2 / (N : ℝ)) • S - 1)) := by
    dsimp only [T]
    module
  have hb : ‖A - (1 / (N : ℝ)) • S‖ ≤ 1 / (N : ℝ) := by
    rw [he, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc
      _ ≤ (1 / 2 : ℝ) * (2 / (N : ℝ)) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = 1 / (N : ℝ) := by ring
  have hcoe : ((∑ k, P k : M.toStarSubalgebra) : H →L[ℂ] H) = S :=
    map_sum M.toStarSubalgebra.subtype P Finset.univ
  refine ⟨P, hP, hcomm, ?_⟩
  change ‖(a : H →L[ℂ] H) - (1 / (N : ℝ)) •
    ((∑ k, P k : M.toStarSubalgebra) : H →L[ℂ] H)‖ ≤ _
  rw [hcoe]
  exact hb

/-- Positivity on projections is sufficient; continuity is in the actual
operator norm on M, not an assumed ultraweak topology. -/
theorem continuousRealFunctional_nonneg_of_projections (M : VonNeumannAlgebra H)
    (f : M.toStarSubalgebra →L[ℝ] ℝ)
    (hf : ∀ p : M.toStarSubalgebra, IsStarProjection p → 0 ≤ f p)
    (a : M.toStarSubalgebra) (ha : 0 ≤ a) : 0 ≤ f a := by
  classical
  have hcontraction (b : M.toStarSubalgebra) (hb : 0 ≤ b) (hbn : ‖b‖ ≤ 1) : 0 ≤ f b := by
    have hchoose (n : ℕ) := exists_projection_average_near_positive_contraction M b hb hbn
      (n + 1) (Nat.succ_pos n)
    choose P hP hcomm herror using hchoose
    let q : ℕ → M.toStarSubalgebra := fun n => (1 / ((n + 1 : ℕ) : ℝ)) • ∑ k, P n k
    have hq (n : ℕ) : 0 ≤ f (q n) := by
      dsimp only [q]
      rw [map_smul, map_sum, smul_eq_mul]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hf _ (hP n k))
    have ht : Tendsto q atTop (𝓝 b) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero (fun n => norm_nonneg _)
        (fun n => by simpa only [q, norm_sub_rev] using herror n)
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact ge_of_tendsto (f.continuous.tendsto b |>.comp ht)
      (Eventually.of_forall hq)
  by_cases hz : a = 0
  · simp only [hz, map_zero, le_refl]
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hscaled := hcontraction ((‖a‖⁻¹ : ℝ) • a)
    (smul_nonneg (inv_nonneg.mpr (norm_nonneg a)) ha)
    (norm_smul_inv_norm (𝕜 := ℝ) hz).le
  have hr : a = (‖a‖ : ℝ) • ((‖a‖⁻¹ : ℝ) • a) := by
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [hr, map_smul, smul_eq_mul]
  exact mul_nonneg (norm_nonneg a) hscaled

/-- A projection-only comparison extends to every positive observable. -/
theorem continuousRealFunctional_le_of_projections (M : VonNeumannAlgebra H)
    (f g : M.toStarSubalgebra →L[ℝ] ℝ)
    (hfg : ∀ p : M.toStarSubalgebra, IsStarProjection p → f p ≤ g p)
    (a : M.toStarSubalgebra) (ha : 0 ≤ a) : f a ≤ g a := by
  have h := continuousRealFunctional_nonneg_of_projections M (g - f)
    (fun p hp => sub_nonneg.mpr (hfg p hp)) a ha
  exact sub_nonneg.mp h

/-- The form needed for actual complex positive functionals. Their automatic
norm continuity is proved by the pinned C-star API, not added as a premise. -/
theorem positiveFunctional_re_le_of_projections (M : VonNeumannAlgebra H)
    (φ ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hφψ : ∀ p : M.toStarSubalgebra, IsStarProjection p → (φ p).re ≤ (ψ p).re)
    (a : M.toStarSubalgebra) (ha : 0 ≤ a) : (φ a).re ≤ (ψ a).re := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M
  let f : M.toStarSubalgebra →L[ℝ] ℝ := Complex.reCLM.comp
    ((PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap.restrictScalars ℝ)
  let g : M.toStarSubalgebra →L[ℝ] ℝ := Complex.reCLM.comp
    ((PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap.restrictScalars ℝ)
  exact continuousRealFunctional_le_of_projections M f g hφψ a ha

end VacuumBellSeparation

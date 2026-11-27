/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.MonotoneThresholdIntegral

/-! The scalar diagonal layer-cake identity for the actual closed spectral cuts. -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory ReflectionApprox
open scoped InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeProjection_zero_op : rangeProjection (0 : H →L[ℂ] H) = 0 := by
  have hr : rangeClosure (0 : H →L[ℂ] H) = ⊥ := by
    apply SetLike.ext
    intro x
    change x ∈ closure (LinearMap.range (0 : H →ₗ[ℂ] H) : Set H) ↔
      x ∈ (⊥ : Submodule ℂ H)
    simp
  apply ContinuousLinearMap.ext
  intro x
  have hx : rangeProjection (0 : H →L[ℂ] H) x ∈ rangeClosure (0 : H →L[ℂ] H) :=
    Submodule.starProjection_apply_mem _ x
  rw [hr, Submodule.mem_bot] at hx
  exact hx

theorem closedThresholdProjection_neg_one {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hAn : ‖A‖ ≤ 1) : closedThresholdProjection A (-1) = 1 := by
  have hp : 0 ≤ (1 : H →L[ℂ] H) + A :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_one_add_of_saContraction hA hAn)
  have he : -A - ((-(-1 : ℝ) : ℝ) : ℂ) • (1 : H →L[ℂ] H) = -(1 + A) := by
    norm_num; abel
  have hz : (-(1 + A))⁺ = 0 :=
    (CFC.posPart_eq_zero_iff _ (ReflectionApprox.isSelfAdjoint_one_op.add hA).neg).mpr
      (neg_nonpos.mpr hp)
  rw [closedThresholdProjection, thresholdProjection, he, hz, rangeProjection_zero_op, sub_zero]

theorem closedThreshold_chain_norm_le {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hAn : ‖A‖ ≤ 1) {N : ℕ} (hN : 0 < N) :
    ‖A - ((2 / (N : ℝ)) •
      (∑ k ∈ Finset.range N, closedThresholdProjection A (threshold N k)) - 1)‖ ≤
        2 / (N : ℝ) := by
  let E := closedThresholdProjection A
  have hposc : ∀ k, k < N →
      ((A - (threshold N k : ℂ) • (1 : H →L[ℂ] H)) * chainProj E N k).IsPositive := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      have e : A - ((-1 : ℝ) : ℂ) • (1 : H →L[ℂ] H) = 1 + A := by
        rw [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul]
        abel
      rw [chainProj_zero, threshold_zero, mul_one, e]
      exact isPositive_one_add_of_saContraction hA hAn
    · rw [chainProj_of_lt E hk0 hk]
      exact sub_mul_closedThresholdProjection_isPositive hA _
  have hnegc : ∀ k, k < N →
      (((threshold N (k + 1) : ℂ) • (1 : H →L[ℂ] H) - A) *
        (1 - chainProj E N (k + 1))).IsPositive := by
    intro k hk
    by_cases hk1 : k + 1 < N
    · rw [chainProj_of_lt E (show k + 1 ≠ 0 by omega) hk1]
      exact sub_mul_one_sub_closedThresholdProjection_isPositive hA _
    · have hkN : k + 1 = N := by omega
      have ht : threshold N (k + 1) = 1 := by rw [hkN, threshold_self hN]
      rw [chainProj_of_not_lt E (show k + 1 ≠ 0 by omega) hk1, ht, sub_zero, mul_one,
        Complex.ofReal_one, one_smul]
      exact isPositive_one_sub_of_saContraction hA hAn
  have h := norm_sub_chain_average_le (A := A) (chainProj E N) (threshold N)
    (2 / (N : ℝ)) N (by positivity) (threshold_succ N)
    (chainProj_isSelfAdjoint (closedThresholdProjection_isSelfAdjoint A) N)
    (chainProj_idem (closedThresholdProjection_idem A) N)
    (chainProj_comm (closedThresholdProjection_commute_self hA) N)
    (chainProj_mono (fun _ _ huv => closedThresholdProjection_mul_of_le hA huv) N)
    hposc hnegc (chainProj_zero E N)
    (chainProj_of_not_lt E hN.ne' (lt_irrefl N)) (threshold_zero N)
  have hs : (∑ k ∈ Finset.range N, chainProj E N k) =
      ∑ k ∈ Finset.range N, closedThresholdProjection A (threshold N k) := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      rw [chainProj_zero, threshold_zero, closedThresholdProjection_neg_one hA hAn]
    · exact chainProj_of_lt E hk0 (Finset.mem_range.mp hk)
  rwa [hs] at h

omit [CompleteSpace H] in
theorem abs_real_quadratic_le (T : H →L[ℂ] H) (x : H) :
    |(⟪x, T x⟫_ℂ).re| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖⟪x, T x⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

theorem closedThreshold_quadratic_integral_error {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hAn : ‖A‖ ≤ 1) (x : H) {N : ℕ} (hN : 0 < N) :
    |(⟪x, A x⟫_ℂ).re - ((∫ u in (-1 : ℝ)..1, closedThresholdQuadratic A x u) - ‖x‖ ^ 2)| ≤
      (4 / (N : ℝ)) * ‖x‖ ^ 2 := by
  let S : H →L[ℂ] H := (2 / (N : ℝ)) •
    (∑ k ∈ Finset.range N, closedThresholdProjection A (threshold N k)) - 1
  have hsumre (f : ℕ → ℂ) (s : Finset ℕ) :
      (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := by
    simpa only [Complex.reCLM_apply] using map_sum Complex.reCLM f s
  have hs : (⟪x, S x⟫_ℂ).re =
      (2 / (N : ℝ)) * (∑ k ∈ Finset.range N, closedThresholdQuadratic A x (threshold N k)) -
        ‖x‖ ^ 2 := by
    simp only [S, ReflectionApprox.real_smul_eq_complex_smul,
      sub_apply, smul_apply,
      sum_apply, one_apply_eq_self, inner_sub_right,
      inner_smul_right, inner_sum, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hsumre, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow, closedThresholdQuadratic]
  have hn := closedThreshold_chain_norm_le hA hAn hN
  have hb := (abs_real_quadratic_le (A - S) x).trans
    (mul_le_mul_of_nonneg_right hn (sq_nonneg ‖x‖))
  have he : (⟪x, (A - S) x⟫_ℂ).re = (⟪x, A x⟫_ℂ).re - (⟪x, S x⟫_ℂ).re := by
    rw [sub_apply, inner_sub_right, Complex.sub_re]
  rw [he, hs] at hb
  obtain ⟨hlo, hhi⟩ := antitone_threshold_integral_bounds
    (closedThresholdQuadratic_antitone hA x) hN
  have hwidth : closedThresholdQuadratic A x (-1) - closedThresholdQuadratic A x 1 ≤ ‖x‖ ^ 2 :=
    (sub_le_self _ (closedThresholdQuadratic_nonneg A x 1)).trans
      (closedThresholdQuadratic_le A x (-1))
  have hhi' := hhi.trans (mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ 2 / (N : ℝ)))
  have hc : 4 / (N : ℝ) = 2 / (N : ℝ) + 2 / (N : ℝ) := by ring
  rw [hc, add_mul]
  rw [abs_le] at hb ⊢
  constructor <;> linarith

theorem integral_closedThresholdQuadratic {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hAn : ‖A‖ ≤ 1) (x : H) :
    (∫ u in (-1 : ℝ)..1, closedThresholdQuadratic A x u) =
      (⟪x, A x⟫_ℂ).re + ‖x‖ ^ 2 := by
  let d := |(⟪x, A x⟫_ℂ).re -
    ((∫ u in (-1 : ℝ)..1, closedThresholdQuadratic A x u) - ‖x‖ ^ 2)|
  have hd : d = 0 := by
    by_contra hne
    have hp : 0 < d := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (4 * ‖x‖ ^ 2 / d))
    have hNr : 0 < (N : ℝ) := (le_max_left _ _).trans_lt hN
    have hNn : 0 < N := Nat.cast_pos.mp hNr
    have hb := closedThreshold_quadratic_integral_error hA hAn x hNn
    have hlarge : 4 * ‖x‖ ^ 2 / d < (N : ℝ) := (le_max_right _ _).trans_lt hN
    have hsmall : (4 / (N : ℝ)) * ‖x‖ ^ 2 < d := by
      have hm := (div_lt_iff₀ hp).mp hlarge
      have he : (4 / (N : ℝ)) * ‖x‖ ^ 2 = 4 * ‖x‖ ^ 2 / (N : ℝ) := by ring
      rw [he]
      exact (div_lt_iff₀ hNr).mpr (by nlinarith)
    exact (not_lt_of_ge hb) hsmall
  have hz := abs_eq_zero.mp hd
  linarith

end VacuumBellSeparation

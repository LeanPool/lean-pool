/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support

/-!
# Lipschitz norm-ball cutoffs and compact localization
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace FunctionalInequalities.Probability.Diffusion

section Cutoff
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']

/-- The norm-ball cutoff `γ_R = clamp₀¹(R + 1 − ‖p‖)`. -/
noncomputable def ballCutoff (R : ℝ) (p : V) : ℝ := max 0 (min 1 (R + 1 - ‖p‖))

theorem ballCutoff_mem_Icc (R : ℝ) (p : V) : ballCutoff R p ∈ Set.Icc (0 : ℝ) 1 := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem ballCutoff_eq_one {R : ℝ} {p : V} (hp : ‖p‖ ≤ R) : ballCutoff R p = 1 := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  have h : (1 : ℝ) ≤ R + 1 - ‖p‖ := by linarith
  simp only [ballCutoff, min_eq_left h, max_eq_right zero_le_one]

theorem lipschitzWith_ballCutoff (R : ℝ) : LipschitzWith 1 (ballCutoff (V := V) R) := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  have hn : LipschitzWith 1 (fun x : V => ‖x‖) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
        abs_norm_sub_norm_le x y
  change LipschitzWith 1 (fun p : V => max 0 (min 1 (R + 1 - ‖p‖)))
  simpa only [zero_add, max_eq_right (show (0 : ℝ≥0) ≤ 1 by positivity)] using
    (LipschitzWith.const (0 : ℝ)).max
      ((LipschitzWith.const (1 : ℝ)).min ((LipschitzWith.const (R + 1)).sub hn))

theorem hasCompactSupport_ballCutoff (R : ℝ) : HasCompactSupport (ballCutoff (V := V) R) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : V) (R + 1))
  intro x hx
  have hr : R + 1 ≤ ‖x‖ :=
    le_of_lt (lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx))
  exact max_eq_left (le_trans (min_le_right _ _) (sub_nonpos.mpr hr))

/-- A Lipschitz cutoff with compact support times a locally Lipschitz map is globally
Lipschitz and bounded. -/
theorem exists_lipschitzWith_smul_of_locallyLipschitz {γ : V → ℝ} {Kγ : ℝ≥0}
    (hγ : LipschitzWith Kγ γ) (hγs : HasCompactSupport γ) {f : V → V'}
    (hf : LocallyLipschitz f) :
    (∃ K : ℝ≥0, LipschitzWith K fun x => γ x • f x) ∧ ∃ B : ℝ, ∀ x, ‖γ x • f x‖ ≤ B := by
  classical
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  obtain ⟨Kf, hKf⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      hγs.isCompact hf.locallyLipschitzOn
  obtain ⟨C, hC⟩ :=
    hγs.isCompact.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨D, hD⟩ :=
    hγs.isCompact.exists_bound_of_continuousOn hγ.continuous.continuousOn
  let Cf : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  let Cγ : ℝ≥0 := ⟨max D 0, le_max_right _ _⟩
  have hCf : ∀ x ∈ tsupport γ, ‖f x‖ ≤ (Cf : ℝ) :=
    fun x hx => (hC x hx).trans (le_max_left _ _)
  have hCγ : ∀ x ∈ tsupport γ, ‖γ x‖ ≤ (Cγ : ℝ) :=
    fun x hx => (hD x hx).trans (le_max_left _ _)
  let L : ℝ≥0 := Kγ * Cf + Cγ * Kf
  have hL : (Kγ : ℝ) * Cf ≤ (L : ℝ) := by
    dsimp only [L]
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul]
    exact le_add_of_nonneg_right (mul_nonneg Cγ.coe_nonneg Kf.coe_nonneg)
  have hbound (x y : V) (hx : γ x ≠ 0) :
      ‖γ x • f x - γ y • f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    have hxS : x ∈ tsupport γ := subset_tsupport γ hx
    have hγxy : ‖γ x - γ y‖ ≤ (Kγ : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hγ.dist_le_mul x y
    by_cases hy : γ y = 0
    · calc
        ‖γ x • f x - γ y • f y‖ = ‖γ x - γ y‖ * ‖f x‖ := by
          simp only [hy, zero_smul, sub_zero, norm_smul]
        _ ≤ ((Kγ : ℝ) * ‖x - y‖) * Cf :=
          mul_le_mul hγxy (hCf x hxS) (norm_nonneg _) (by positivity)
        _ = ((Kγ : ℝ) * Cf) * ‖x - y‖ := by ring
        _ ≤ (L : ℝ) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    · have hyS : y ∈ tsupport γ := subset_tsupport γ hy
      have hfxy : ‖f x - f y‖ ≤ (Kf : ℝ) * ‖x - y‖ := by
        simpa only [dist_eq_norm] using hKf.dist_le_mul x hxS y hyS
      have he :
          γ x • f x - γ y • f y =
            (γ x - γ y) • f x + γ y • (f x - f y) := by
        simp only [sub_smul, smul_sub]
        abel
      calc
        ‖γ x • f x - γ y • f y‖
            ≤ ‖(γ x - γ y) • f x‖ + ‖γ y • (f x - f y)‖ := by
              rw [he]
              exact norm_add_le _ _
        _ = ‖γ x - γ y‖ * ‖f x‖ + ‖γ y‖ * ‖f x - f y‖ := by
          rw [norm_smul, norm_smul]
        _ ≤ ((Kγ : ℝ) * ‖x - y‖) * Cf +
            (Cγ : ℝ) * ((Kf : ℝ) * ‖x - y‖) := by
          exact add_le_add
            (mul_le_mul hγxy (hCf x hxS) (norm_nonneg _) (by positivity))
            (mul_le_mul (hCγ y hyS) hfxy (norm_nonneg _) Cγ.coe_nonneg)
        _ = (L : ℝ) * ‖x - y‖ := by
          simp only [L, NNReal.coe_add, NNReal.coe_mul]
          ring
  constructor
  · refine ⟨L, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simp only [dist_eq_norm]
    by_cases hx : γ x = 0
    · by_cases hy : γ y = 0
      · simp only [hx, hy, zero_smul, sub_self, norm_zero]
        exact mul_nonneg L.coe_nonneg (norm_nonneg _)
      · simpa only [norm_sub_rev] using hbound y x hy
    · exact hbound x y hx
  · refine ⟨(Cγ : ℝ) * Cf, ?_⟩
    intro x
    by_cases hx : γ x = 0
    · simp only [hx, zero_smul, norm_zero]
      exact mul_nonneg Cγ.coe_nonneg Cf.coe_nonneg
    · have hxS : x ∈ tsupport γ := subset_tsupport γ hx
      rw [norm_smul]
      exact mul_le_mul (hCγ x hxS) (hCf x hxS) (norm_nonneg _) Cγ.coe_nonneg

end Cutoff

end FunctionalInequalities.Probability.Diffusion

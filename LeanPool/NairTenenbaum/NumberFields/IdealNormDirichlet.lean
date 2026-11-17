/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.DedekindZeta

import Mathlib.Algebra.BigOperators.Ring.Nat

/-! # The real Dirichlet series of ideal norms

This module connects the nonnegative real series needed for comparisons with
Mathlib's Dedekind zeta function and its proved residue at one.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Filter NumberField Ideal Asymptotics
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- The number of integral ideals of a specified absolute norm. -/
noncomputable def idealNormCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- The Dirichlet series counting integral ideals by their absolute norm. -/
noncomputable def idealNormDirichlet (σ : ℝ) : ℝ :=
  ∑' n : ℕ, (idealNormCount K n : ℝ) * (n : ℝ) ^ (-σ)

theorem idealNormCount_partialSum_limit :
    Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, (idealNormCount K k : ℝ)) / n) atTop
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr 1
  apply congrArg (fun m : ℕ => (m : ℝ))
  unfold idealNormCount
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Icc 1 n = Ioc 0 n from Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem lSeriesSummable_idealNormCount {σ : ℝ} (hσ : 1 < σ) :
    LSeriesSummable (fun n => (idealNormCount K n : ℂ)) σ := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n => (idealNormCount K n : ℝ))
    _ (fun _ => Nat.cast_nonneg _) zero_le_one (by simpa using hσ)
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa using idealNormCount_partialSum_limit K)

theorem idealNormDirichlet_term_complex {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    LSeries.term (fun n => (idealNormCount K n : ℂ)) σ n =
      ((idealNormCount K n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast n,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_natCast (idealNormCount K n),
    ← Complex.ofReal_div]
  congr 1
  rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem summable_idealNormDirichlet {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (idealNormCount K n : ℝ) * (n : ℝ) ^ (-σ)) := by
  have H := lSeriesSummable_idealNormCount K hσ
  change Summable (fun n => LSeries.term (fun n => (idealNormCount K n : ℂ)) σ n) at H
  simp only [idealNormDirichlet_term_complex K hσ, Complex.summable_ofReal] at H
  exact H

theorem idealNormDirichlet_eq_dedekindZeta {σ : ℝ} (hσ : 1 < σ) :
    (idealNormDirichlet K σ : ℂ) = NumberField.dedekindZeta K σ := by
  unfold idealNormDirichlet NumberField.dedekindZeta LSeries
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  exact (idealNormDirichlet_term_complex K hσ n).symm

theorem idealNormDirichlet_residue :
    Tendsto (fun s : ℝ => (s - 1) * idealNormDirichlet K s) (𝓝[>] 1)
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
  have H := Complex.continuous_re.continuousAt.tendsto.comp
    (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  dsimp only [Function.comp_def]
  rw [← idealNormDirichlet_eq_dedekindZeta K hs]
  simp

theorem exists_idealNormDirichlet_pole_bound :
    ∃ C b : ℝ, 0 < C ∧ 1 < b ∧ ∀ s : ℝ, 1 < s → s < b →
      idealNormDirichlet K s ≤ C / (s - 1) := by
  have H := (idealNormDirichlet_residue K).eventually_lt_const
    (by linarith : NumberField.dedekindZeta_residue K < NumberField.dedekindZeta_residue K + 1)
  obtain ⟨b, hb, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp H
  refine ⟨NumberField.dedekindZeta_residue K + 1, b,
    by linarith [NumberField.dedekindZeta_residue_pos K], hb, fun s hs hsb => ?_⟩
  apply (le_div_iff₀ (by linarith : 0 < s - 1)).mpr
  simpa only [mul_comm] using (hbound ⟨hs, hsb⟩).le

/-- The positive Dedekind residue also gives the matching lower pole bound. -/
theorem exists_idealNormDirichlet_pole_lower_bound :
    ∃ c b : ℝ, 0 < c ∧ 1 < b ∧ ∀ s : ℝ, 1 < s → s < b →
      c / (s - 1) ≤ idealNormDirichlet K s := by
  have hc := NumberField.dedekindZeta_residue_pos K
  have H := (idealNormDirichlet_residue K).eventually
    (lt_mem_nhds (show NumberField.dedekindZeta_residue K / 2 < NumberField.dedekindZeta_residue K
        by
      linarith))
  obtain ⟨b, hb, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp H
  refine ⟨NumberField.dedekindZeta_residue K / 2, b, half_pos hc, hb, fun s hs hsb => ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < s - 1)).mpr
  simpa only [mul_comm] using (hbound ⟨hs, hsb⟩).le

end NairTenenbaum

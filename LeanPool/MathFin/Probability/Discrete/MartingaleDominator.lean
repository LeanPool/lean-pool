/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import TauCeti.Probability.Martingale.MaximalInequality.Lp
public import LeanPool.MathFin.Init

/-!
# An all-time integrable martingale envelope

A discrete martingale bounded in `Lᵖ`, for `p > 1`, is dominated by the real
supremum of its norms. The module uses Tau Ceti's finite-time maximal inequality
and monotone convergence to put this envelope in `Lᵖ`.
-/

@[expose] public section

noncomputable section

open Filter Finset Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

namespace LpDominator

variable {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p R : ℝ}

/-- `maxₖ≤ₙ ‖f k ω‖`, the running max of the norms. -/
private noncomputable def runMaxNorm (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k ↦ ‖f k ω‖)

omit [MeasurableSpace Ω] in
private lemma runMaxNorm_nonneg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ runMaxNorm f n ω :=
  (norm_nonneg _).trans <| Finset.le_sup' (f := fun k ↦ ‖f k ω‖)
    (Finset.mem_range.mpr (Nat.succ_pos n))

omit [MeasurableSpace Ω] in
private lemma runMaxNorm_mono (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone (fun n ↦ runMaxNorm f n ω) :=
  fun _ _ hmn ↦ Finset.sup'_le _ _ fun k hk ↦
    Finset.le_sup' (f := fun k ↦ ‖f k ω‖) <|
      Finset.mem_range.mpr <| (Finset.mem_range.mp hk).trans_le (by omega)

/-- The all-time envelope `⨆ₖ ‖f k ω‖ₑ`, in `ℝ≥0∞`. -/
noncomputable def enormSup (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ := ⨆ k : ℕ, ‖f k ω‖ₑ

lemma measurable_enormSup (hf : ∀ k, Measurable (f k)) : Measurable (enormSup f) :=
  Measurable.iSup fun k ↦ (hf k).eNorm

/-- A nonnegative real power commutes with the supremum of a monotone sequence in `ℝ≥0∞`. -/
lemma iSup_rpow_of_monotone {g : ℕ → ℝ≥0∞} (hg : Monotone g) (hp : 0 ≤ p) :
    (⨆ n, g n) ^ p = ⨆ n, (g n) ^ p :=
  tendsto_nhds_unique
    ((ENNReal.continuous_rpow_const.tendsto _).comp (tendsto_atTop_iSup hg))
    (tendsto_atTop_iSup fun _ _ hmn ↦ ENNReal.monotone_rpow_of_nonneg hp (hg hmn))

/-- `ENNReal.ofReal` commutes with the supremum over a nonempty finset. -/
lemma ofReal_finset_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (g : ι → ℝ) :
    ENNReal.ofReal (s.sup' hs g) = s.sup' hs (fun i ↦ ENNReal.ofReal (g i)) :=
  Finset.apply_sup'_eq_sup'_comp hs ENNReal.ofReal ENNReal.ofReal_max

omit [MeasurableSpace Ω] in
private lemma iSup_ofReal_runMaxNorm (f : ℕ → Ω → ℝ) (ω : Ω) :
    (⨆ n : ℕ, ENNReal.ofReal (runMaxNorm f n ω)) = enormSup f ω := by
  refine le_antisymm (iSup_le fun n ↦ ?_) (iSup_le fun k ↦ ?_)
  · rw [runMaxNorm, ofReal_finset_sup']
    refine Finset.sup'_le _ _ fun k _ ↦ ?_
    rw [ofReal_norm]
    exact le_iSup (fun j : ℕ ↦ ‖f j ω‖ₑ) k
  · refine le_iSup_of_le k ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal <|
      Finset.le_sup' (f := fun j ↦ ‖f j ω‖) (Finset.mem_range.mpr (Nat.lt_succ_self k))

private lemma measurable_runMaxNorm (hf : Martingale f 𝒢 μ) (n : ℕ) :
    Measurable (runMaxNorm f n) :=
  Finset.measurable_range_sup'' (n := n) fun k _ ↦
    ((hf.stronglyMeasurable k).mono (𝒢.le k)).measurable.norm

private lemma lintegral_ofReal_runMaxNorm_rpow_le [IsFiniteMeasure μ] (hp : 1 < p)
    (hf : Martingale f 𝒢 μ)
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (runMaxNorm f n ω ^ p) ∂μ
      ≤ (ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal R) ^ p := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hDoob : eLpNorm (fun ω ↦ runMaxNorm f n ω) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal R :=
    by
      have hp_enn : 1 < ENNReal.ofReal p := by
        rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff hp_pos]
      have h := hf.eLpNorm_partialSups_norm_le n hp_enn ENNReal.ofReal_ne_top
      rw [← ENNReal.ofReal_div_sub_one hp] at h
      have hr : partialSups (fun k ω ↦ ‖f k ω‖) n = fun ω ↦ runMaxNorm f n ω := by
        ext ω
        simp only [Pi.partialSups_apply, partialSups_apply, runMaxNorm, Nat.range_succ_eq_Iic]
      rw [hr] at h
      exact h.trans (by gcongr; exact hbound n)
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by simp [hp_pos]) ENNReal.ofReal_ne_top
      (measurable_runMaxNorm hf n).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp_pos.le] at hDoob
  have hpow := ENNReal.rpow_le_rpow hDoob hp_pos.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp_pos.ne', ENNReal.rpow_one] at hpow
  refine le_trans (le_of_eq <| lintegral_congr fun ω ↦ ?_) hpow
  rw [Real.eNorm_of_nonneg (runMaxNorm_nonneg f n ω),
      ENNReal.ofReal_rpow_of_nonneg (runMaxNorm_nonneg f n ω) hp_pos.le]

/-- Monotone-convergence bound on `∫⁻ (enormSup f ω)^p ∂μ`. -/
lemma lintegral_enormSup_rpow_le [IsFiniteMeasure μ] (hp : 1 < p) (hf : Martingale f 𝒢 μ)
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∫⁻ ω, enormSup f ω ^ p ∂μ ≤ (ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal R) ^ p := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  set g : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ENNReal.ofReal (runMaxNorm f n ω)
  have hg_mono : ∀ ω, Monotone (fun n ↦ g n ω) := fun ω _ _ hmn ↦
    ENNReal.ofReal_le_ofReal (runMaxNorm_mono f ω hmn)
  have h_meas : ∀ n, AEMeasurable (fun ω ↦ g n ω ^ p) μ := fun n ↦
    ((ENNReal.continuous_rpow_const.measurable.comp
      (measurable_runMaxNorm hf n).ennreal_ofReal)).aemeasurable
  rw [show (fun ω ↦ enormSup f ω ^ p) = fun ω ↦ ⨆ n, g n ω ^ p from
    funext fun ω ↦ by rw [← iSup_ofReal_runMaxNorm, iSup_rpow_of_monotone (hg_mono ω) hp_pos.le]]
  rw [lintegral_iSup' h_meas (Filter.Eventually.of_forall fun ω _ _ hmn ↦
      ENNReal.monotone_rpow_of_nonneg hp_pos.le (hg_mono ω hmn))]
  refine iSup_le fun n ↦ ?_
  simp_rw [show ∀ ω, g n ω ^ p = ENNReal.ofReal (runMaxNorm f n ω ^ p) from fun ω ↦
    ENNReal.ofReal_rpow_of_nonneg (runMaxNorm_nonneg f n ω) hp_pos.le]
  exact lintegral_ofReal_runMaxNorm_rpow_le hp hf hbound n

private lemma enormSup_rpow_lintegral_lt_top [IsFiniteMeasure μ] (hp : 1 < p)
    (hf : Martingale f 𝒢 μ)
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∫⁻ ω, enormSup f ω ^ p ∂μ < ⊤ :=
  (lintegral_enormSup_rpow_le hp hf hbound).trans_lt <|
    ENNReal.rpow_lt_top_of_nonneg (lt_trans zero_lt_one hp).le
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

lemma enormSup_lt_top_ae [IsFiniteMeasure μ] (hp : 1 < p) (hf : Martingale f 𝒢 μ)
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∀ᵐ ω ∂μ, enormSup f ω < ⊤ := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  filter_upwards [ae_lt_top ((measurable_enormSup fun k ↦
      ((hf.stronglyMeasurable k).mono (𝒢.le k)).measurable).pow_const p)
    (enormSup_rpow_lintegral_lt_top hp hf hbound).ne] with ω hω
  exact (ENNReal.rpow_lt_top_iff_of_pos hp_pos).mp hω

/-- The real-valued envelope `f*(ω) = (⨆ₖ ‖f k ω‖ₑ).toReal`. -/
noncomputable def dominator (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ := (enormSup f ω).toReal

lemma measurable_dominator (hf : ∀ k, Measurable (f k)) : Measurable (dominator f) :=
  (measurable_enormSup hf).ennreal_toReal

lemma dominator_memLp [IsFiniteMeasure μ] (hp : 1 < p) (hf : Martingale f 𝒢 μ)
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    MemLp (dominator f) (ENNReal.ofReal p) μ := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hmeas : AEStronglyMeasurable (dominator f) μ :=
    (measurable_dominator fun k ↦
      ((hf.stronglyMeasurable k).mono (𝒢.le k)).measurable).aestronglyMeasurable
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_eNorm_toReal (by simp [hp_pos]) ENNReal.ofReal_ne_top
    hmeas, ENNReal.toReal_ofReal hp_pos.le]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (lt_of_le_of_lt ?_
    (enormSup_rpow_lintegral_lt_top hp hf hbound)).ne
  refine lintegral_mono fun ω ↦ ENNReal.rpow_le_rpow ?_ hp_pos.le
  rw [dominator, Real.eNorm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

lemma norm_le_dominator [IsFiniteMeasure μ] (hp : 1 < p) (hf : Martingale f 𝒢 μ)
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) (n : ℕ) :
    ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ dominator f ω := by
  filter_upwards [enormSup_lt_top_ae hp hf hbound] with ω hlt
  rw [show ‖f n ω‖ = (‖f n ω‖ₑ).toReal by
    rw [Real.eNorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]]
  exact ENNReal.toReal_mono hlt.ne <| le_iSup (fun k : ℕ ↦ ‖f k ω‖ₑ) n

end LpDominator

end MeasureTheory

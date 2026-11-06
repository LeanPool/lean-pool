/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Extremes.MaxLeafHeight

import LeanPool.RareSubtreePatterns.Bridge.Microscopic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# First-order consequences of Theorem `thm:max_lh` (inventory U03)

Source lines 574–581: Theorem `thm:max_lh` implies
`λ(𝒯^n)/log n → 1/log(1/μ_1)` in probability if `μ_1 > 0`, and
`λ(𝒯^n)/log_κ log n → 1` in probability if `μ_1 = 0`, `κ = min{i ≥ 2 : μ_i > 0}`. "In probability"
is stated as `P(|λ(𝒯^n)/ℓ_n - ℓ| > ε) → 0` for every `ε > 0`, along admissible sizes.

* `tendsto_div_log_of_latticeGumbel`: any lattice-modulated Gumbel limit (`LatticeGumbel`) with
  centering `(log n + c)/log(1/q)`, `0 < q < 1`, gives `H(𝒯^n)/log n → 1/log(1/q)`;
* `tendsto_div_logb_of_twoPoint`: any two-point localization (`TwoPointLocalization`) with
  centering `log_κ log n - c`, `κ ≥ 2`, gives `H(𝒯^n)/log_κ log n → 1`;
* `leafHeight_div_log_tendsto`, `leafHeight_div_logb_log_tendsto`: the two consequences, derived
  from `MaxLeafHeightStatement` itself (so they hold as soon as Theorem `thm:max_lh` does, e.g.
  through `MaxLeafHeight.maxLeafHeight_of`).
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace PoissonDeclumping
namespace MaxLeafHeight

open PlaneTree

variable {μ : PMF ℕ}

/-- `log n → ∞` along admissible sizes. -/
theorem tendsto_log_natCast_admissible (μ : PMF ℕ) :
    Tendsto (fun n : ℕ => Real.log n) (admissibleSizes μ) atTop :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).mono_left inf_le_left

/-- First-order consequence of a lattice-modulated Gumbel limit with centering
`x_n = (log n + c)/log(1/q)`: `H(𝒯^n)/log n → 1/log(1/q)` in probability. -/
theorem tendsto_div_log_of_latticeGumbel {H : PlaneTree → ℕ} {q c : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (hG : LatticeGumbel μ H q (fun n : ℕ => (Real.log n + c) / Real.log (1 / q)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (conditioned μ n).real
      {T | ε < |(H T : ℝ) / Real.log n - 1 / Real.log (1 / q)|}) (admissibleSizes μ) (𝓝 0) := by
  set L := Real.log (1 / q) with hL
  have hLpos : 0 < L := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hq0, hq1⟩)
  set x : ℕ → ℝ := fun n => (Real.log n + c) / L with hx
  refine Bridge.tendsto_zero_of_forall_eventually_le (fun n => measureReal_nonneg) fun η hη => ?_
  obtain ⟨t, ht0, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ q ^ t ≤ q * η / 4 := by
    have h := tendsto_rpow_atTop_of_base_lt_one q (by linarith) hq1
    obtain ⟨t, ht⟩ := eventually_atTop.1 (h.eventually (ge_mem_nhds (by positivity :
      (0 : ℝ) < q * η / 4)))
    exact ⟨max t 0, le_max_right _ _, ht _ (le_max_left _ _)⟩
  have hqt : q ^ t ≤ η / 4 := ht.trans (by nlinarith)
  have hup := (Metric.tendsto_nhds.1 (hG t)) (η / 4) (by positivity)
  have hlo := (Metric.tendsto_nhds.1 (hG (-t))) (η / 4) (by positivity)
  have hlog := tendsto_log_natCast_admissible μ
  filter_upwards [hup, hlo, eventually_admissible_sizes μ,
    hlog.eventually_gt_atTop 0, hlog.eventually_ge_atTop ((t + |c| / L + 1) / ε)]
    with n hun hln hadm hlogpos hlogbig
  have := conditioned_isProbabilityMeasure hadm
  rw [Real.dist_eq, sub_zero, abs_lt] at hun hln
  set ℓ := Real.log n with hℓ
  -- the upper tail
  have hs1 : t ≤ t + 1 - Int.fract (x n + t) := by linarith [Int.fract_lt_one (x n + t)]
  have hqs1 : q ^ (t + 1 - Int.fract (x n + t)) ≤ q ^ t :=
    Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hs1
  have hexp1 : 1 - q ^ t ≤ Real.exp (-q ^ (t + 1 - Int.fract (x n + t))) := by
    have := Real.add_one_le_exp (-q ^ (t + 1 - Int.fract (x n + t)))
    linarith
  have hP1 : 1 - η / 2 ≤ (conditioned μ n).real {T | ((H T : ℕ) : ℤ) ≤ ⌊x n + t⌋} := by
    linarith
  -- the lower tail
  have hs2 : -t + 1 - Int.fract (x n + -t) ≤ 1 - t := by linarith [Int.fract_nonneg (x n + -t)]
  have hqpos : 0 < q ^ (-t + 1 - Int.fract (x n + -t)) := Real.rpow_pos_of_pos hq0 _
  have hqs2 : q ^ (1 - t) ≤ q ^ (-t + 1 - Int.fract (x n + -t)) :=
    Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hs2
  have hq1t : q ^ (1 - t) = q / q ^ t := by
    rw [Real.rpow_sub hq0, Real.rpow_one]
  have hexp2 : Real.exp (-q ^ (-t + 1 - Int.fract (x n + -t))) ≤ η / 4 := by
    have h1 := Real.add_one_le_exp (q ^ (-t + 1 - Int.fract (x n + -t)))
    have hpos' : 0 < Real.exp (q ^ (-t + 1 - Int.fract (x n + -t))) := Real.exp_pos _
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos']
    have hqtpos : 0 < q ^ t := Real.rpow_pos_of_pos hq0 _
    have : q / q ^ t ≥ 4 / η := by
      rw [ge_iff_le, div_le_div_iff₀ hη hqtpos]
      nlinarith
    have : 4 / η ≤ Real.exp (q ^ (-t + 1 - Int.fract (x n + -t))) := by
      linarith
    rw [div_le_iff₀ hη] at this
    nlinarith
  have hP2 : (conditioned μ n).real {T | ((H T : ℕ) : ℤ) ≤ ⌊x n + -t⌋} ≤ η / 2 := by
    linarith
  -- inclusion
  have hxn : x n = ℓ / L + c / L := by rw [hx]; ring
  have hcL : |c / L| = |c| / L := by rw [abs_div, abs_of_pos hLpos]
  have hεℓ : t + |c| / L + 1 ≤ ε * ℓ := by
    rw [div_le_iff₀ hε] at hlogbig
    linarith
  have hsub : {T | ε < |(H T : ℝ) / ℓ - 1 / L|} ⊆
      {T | ((H T : ℕ) : ℤ) ≤ ⌊x n + t⌋}ᶜ ∪ {T | ((H T : ℕ) : ℤ) ≤ ⌊x n + -t⌋} := by
    intro T hT
    simp only [Set.mem_ofPred_eq] at hT
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rcases lt_abs.1 hT with h | h
    · left
      intro hle
      have h1 : ((H T : ℕ) : ℝ) ≤ x n + t := by
        have := Int.floor_le (x n + t)
        have h' : (((H T : ℕ) : ℤ) : ℝ) ≤ (⌊x n + t⌋ : ℝ) := by exact_mod_cast hle
        push_cast at h'
        linarith
      have h2 : (1 / L + ε) * ℓ < (H T : ℝ) := by
        rw [lt_sub_iff_add_lt, lt_div_iff₀ hlogpos] at h
        linarith
      have h3 : x n + t ≤ (1 / L + ε) * ℓ := by
        rw [hxn]
        have : ℓ / L = 1 / L * ℓ := by ring
        nlinarith [abs_le.1 (le_of_eq hcL)]
      linarith
    · right
      have h2 : (H T : ℝ) < (1 / L - ε) * ℓ := by
        have h' : (H T : ℝ) / ℓ < 1 / L - ε := by linarith
        rwa [div_lt_iff₀ hlogpos] at h'
      have h3 : (1 / L - ε) * ℓ ≤ x n + -t - 1 := by
        rw [hxn]
        have : ℓ / L = 1 / L * ℓ := by ring
        nlinarith [abs_le.1 (le_of_eq hcL)]
      have h4 : x n + -t - 1 < (⌊x n + -t⌋ : ℝ) := Int.sub_one_lt_floor _
      have h5 : ((H T : ℕ) : ℝ) < (⌊x n + -t⌋ : ℝ) := by linarith
      have h6 : (((H T : ℕ) : ℤ) : ℝ) < (⌊x n + -t⌋ : ℝ) := by exact_mod_cast h5
      exact (Int.cast_lt.1 h6).le
  calc (conditioned μ n).real {T | ε < |(H T : ℝ) / ℓ - 1 / L|}
      ≤ (conditioned μ n).real ({T | ((H T : ℕ) : ℤ) ≤ ⌊x n + t⌋}ᶜ ∪
          {T | ((H T : ℕ) : ℤ) ≤ ⌊x n + -t⌋}) := measureReal_mono hsub
    _ ≤ (conditioned μ n).real {T | ((H T : ℕ) : ℤ) ≤ ⌊x n + t⌋}ᶜ +
          (conditioned μ n).real {T | ((H T : ℕ) : ℤ) ≤ ⌊x n + -t⌋} := measureReal_union_le _ _
    _ = 1 - (conditioned μ n).real {T | ((H T : ℕ) : ℤ) ≤ ⌊x n + t⌋} +
          (conditioned μ n).real {T | ((H T : ℕ) : ℤ) ≤ ⌊x n + -t⌋} := by
        rw [probReal_compl_eq_one_sub MeasurableSet.of_discrete]
    _ ≤ η := by linarith

/-- First-order consequence of the two-point localization with centering
`x_n = log_κ log n - c`, `κ ≥ 2`: `H(𝒯^n)/log_κ log n → 1` in probability. -/
theorem tendsto_div_logb_of_twoPoint {H : PlaneTree → ℕ} {κ : ℕ} (hκ : 2 ≤ κ) {c : ℝ}
    (hTP : TwoPointLocalization μ H (fun n : ℕ => Real.logb κ (Real.log n) - c))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (conditioned μ n).real
      {T | ε < |(H T : ℝ) / Real.logb κ (Real.log n) - 1|}) (admissibleSizes μ) (𝓝 0) := by
  have hκ1 : (1 : ℝ) < κ := by exact_mod_cast (show 1 < κ by omega)
  have hℓ : Tendsto (fun n : ℕ => Real.logb κ (Real.log n)) (admissibleSizes μ) atTop :=
    (Real.tendsto_logb_atTop hκ1).comp (tendsto_log_natCast_admissible μ)
  have hJ := hTP.1
  have hJc : Tendsto (fun n : ℕ => 1 - (conditioned μ n).real
      {T | ((H T : ℕ) : ℤ) ∈ twoPointSet (Real.logb κ (Real.log n) - c)})
      (admissibleSizes μ) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hJ
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hJc
  filter_upwards [eventually_admissible_sizes μ, hℓ.eventually_gt_atTop 0,
    hℓ.eventually_gt_atTop ((|c| + 3 / 2) / ε)] with n hadm hpos hbig
  have := conditioned_isProbabilityMeasure hadm
  set ℓ := Real.logb κ (Real.log n) with hℓdef
  rw [← probReal_compl_eq_one_sub MeasurableSet.of_discrete]
  refine measureReal_mono fun T hT => ?_
  simp only [Set.mem_ofPred_eq] at hT
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  intro hmem
  rw [ExtremesAnalysis.mem_twoPointSet_iff] at hmem
  have h1 := ExtremesAnalysis.sub_le_twoPointLow (ℓ - c)
  have h2 := ExtremesAnalysis.twoPointLow_add_two_le (ℓ - c)
  have hlo : ((ExtremesAnalysis.twoPointLow (ℓ - c) : ℤ) : ℝ) ≤ ((H T : ℕ) : ℝ) := by
    exact_mod_cast hmem.1
  have hhi : ((H T : ℕ) : ℝ) + 1 ≤ ((ExtremesAnalysis.twoPointLow (ℓ - c) + 2 : ℤ) : ℝ) := by
    exact_mod_cast hmem.2
  have hle : |(H T : ℝ) - ℓ| ≤ |c| + 3 / 2 := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self c, neg_abs_le c]
  have hbig' : |c| + 3 / 2 < ε * ℓ := by
    rwa [div_lt_iff₀ hε, mul_comm] at hbig
  have : |(H T : ℝ) / ℓ - 1| = |(H T : ℝ) - ℓ| / ℓ := by
    rw [← abs_of_pos hpos, ← abs_div, abs_of_pos hpos, sub_div, div_self hpos.ne']
  rw [this, lt_div_iff₀ hpos] at hT
  linarith

/-- **U03, first-order consequence of Theorem `thm:max_lh`(i)** (source lines 574–577): if
`μ_1 > 0`, then `λ(𝒯^n)/log n → 1/log(1/μ_1)` in probability (along admissible sizes). -/
theorem leafHeight_div_log_tendsto (h : MaxLeafHeightStatement) (hμ : InStableDomain μ)
    (hpos : 0 < μ 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (conditioned μ n).real
      {T | ε < |(leafHeight T : ℝ) / Real.log n - 1 / Real.log (1 / (μ 1).toReal)|})
      (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨α, a, hD⟩ := id hμ
  obtain ⟨C, -, -, hG⟩ := (h μ hμ).1 hpos
  exact tendsto_div_log_of_latticeGumbel ((LeafHeight.mass_pos_iff 1).mpr hpos)
    (LeafHeight.mass_one_lt_one hD.nondegenerate) hG hε

/-- **U03, first-order consequence of Theorem `thm:max_lh`(ii)** (source lines 574–578): if
`μ_1 = 0` and `κ = min{i ≥ 2 : μ_i > 0}`, then `λ(𝒯^n)/log_κ log n → 1` in probability (along
admissible sizes). -/
theorem leafHeight_div_logb_log_tendsto (h : MaxLeafHeightStatement) (hμ : InStableDomain μ)
    (h0 : μ 1 = 0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (conditioned μ n).real
      {T | ε < |(leafHeight T : ℝ) / Real.logb (sInf {i : ℕ | 2 ≤ i ∧ 0 < μ i} : ℕ)
        (Real.log n) - 1|})
      (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨α, a, hD⟩ := id hμ
  obtain ⟨D, -, -, -, hTP⟩ := (h μ hμ).2 h0
  obtain ⟨j, hj, hjpos⟩ := LeafHeight.exists_two_le_pos hD.critical hD.nondegenerate
  have hκ : 2 ≤ sInf {i : ℕ | 2 ≤ i ∧ 0 < μ i} :=
    (Nat.sInf_mem (s := {i : ℕ | 2 ≤ i ∧ 0 < μ i}) ⟨j, hj, hjpos⟩).1
  exact tendsto_div_logb_of_twoPoint hκ hTP hε


end MaxLeafHeight
end PoissonDeclumping

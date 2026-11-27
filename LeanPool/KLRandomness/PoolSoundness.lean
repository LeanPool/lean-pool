/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolAdviceMeasure
public import LeanPool.KLRandomness.PoolSearch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Soundness of the fixed-advice pool tests

Acceptance only controls a finite horizon. A global upper bound on the final
weighted mass bounds all later increases. The gap between this upper bound
and the accepted weighted mass gives the paper's `4δ` increment bound and
`8δ` L1 bound. Approximation of the high sets and Markov's inequality then
give the two measure estimates required of an output pool.

All analytic hypotheses are explicit: this file does not assume a computable
limit, and it does not claim that the search terminates without a separate
finite-existence argument.
-/

@[expose] public section

namespace Klr.PoolSoundness

open MeasureTheory Filter
open scoped BigOperators symmDiff

/-- A nonnegative weighted increment is controlled by the gap between a final
upper bound and a strict lower bound on the initial weighted mass. -/
theorem increment_lt_of_weighted_gap {D i : ℕ} {w v u : ℕ → ℝ}
    {B γ δ w₀ : ℝ} (hi : i < D)
    (hw : ∀ j < D, 0 ≤ w j) (hmon : ∀ j < D, u j ≤ v j)
    (hB : ∑ j ∈ Finset.range D, w j * v j ≤ B)
    (hγ : γ < ∑ j ∈ Finset.range D, w j * u j)
    (hgap : B - γ < 4 * w₀ * δ) (hw₀ : 0 < w₀) (hwi : w₀ ≤ w i) :
    v i - u i < 4 * δ := by
  have hsum : ∑ j ∈ Finset.range D, w j * (v j - u j) < B - γ := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    linarith
  have hterm : w i * (v i - u i) ≤
      ∑ j ∈ Finset.range D, w j * (v j - u j) :=
    Finset.single_le_sum (fun j hj => mul_nonneg (hw j (Finset.mem_range.mp hj))
      (sub_nonneg.mpr (hmon j (Finset.mem_range.mp hj)))) (Finset.mem_range.mpr hi)
  have hleft : w₀ * (v i - u i) ≤ w i * (v i - u i) :=
    mul_le_mul_of_nonneg_right hwi (sub_nonneg.mpr (hmon i hi))
  have hlt := lt_of_le_of_lt hleft (lt_of_le_of_lt hterm (hsum.trans hgap))
  nlinarith

/-- The L1 triangle inequality, stated directly for real integrals. -/
theorem integral_abs_sub_le_add {f g h : Cantor → ℝ}
    (hf : Integrable f fairCoin) (hg : Integrable g fairCoin)
    (hh : Integrable h fairCoin) :
    (∫ Z, |f Z - h Z| ∂fairCoin) ≤
      (∫ Z, |f Z - g Z| ∂fairCoin) + (∫ Z, |g Z - h Z| ∂fairCoin) := by
  calc
    (∫ Z, |f Z - h Z| ∂fairCoin) ≤ ∫ Z, |f Z - g Z| + |g Z - h Z| ∂fairCoin :=
      integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
        (fun Z => abs_sub_le (f Z) (g Z) (h Z))
    _ = _ := by simpa only [Pi.sub_apply] using
        integral_add (hf.sub hg).abs (hg.sub hh).abs

/-- For monotone real coverage functions, the L1 increment is the difference
of their expected coverage. -/
theorem integral_abs_sub_of_le {u v : Cantor → ℝ}
    (hu : Integrable u fairCoin) (hv : Integrable v fairCoin) (h : ∀ Z, u Z ≤ v Z) :
    (∫ Z, |v Z - u Z| ∂fairCoin) = (∫ Z, v Z ∂fairCoin) - ∫ Z, u Z ∂fairCoin := by
  rw [← integral_sub hv hu]
  apply integral_congr_ae
  exact Eventually.of_forall fun Z => abs_of_nonneg (sub_nonneg.mpr (h Z))

/-- Set approximation transfers a high-set failure bound from finite coverage
to eventual coverage, using only their pointwise monotonicity. -/
theorem high_failure_lt {H H' : Set Cantor} {u v : Cantor → ℝ} {δ : ℝ}
    (hmon : ∀ Z, u Z ≤ v Z) (hH : fairCoin.real (H ∆ H') < δ)
    (hu : fairCoin.real {Z | Z ∈ H' ∧ u Z < 1} < 3 * δ) :
    fairCoin.real {Z | Z ∈ H ∧ v Z < 1} < 4 * δ := by
  have hsub : {Z | Z ∈ H ∧ v Z < 1} ⊆
      (H ∆ H') ∪ {Z | Z ∈ H' ∧ u Z < 1} := by
    intro Z hZ
    by_cases hZ' : Z ∈ H'
    · exact Or.inr ⟨hZ', lt_of_le_of_lt (hmon Z) hZ.2⟩
    · exact Or.inl (Or.inl ⟨hZ.1, hZ'⟩)
  have hle := (measureReal_mono (μ := fairCoin) hsub).trans
    (measureReal_union_le (μ := fairCoin) (H ∆ H') {Z | Z ∈ H' ∧ u Z < 1})
  linarith

/-- An L1 error controls the low-set points on which coverage is nearly full.
The separate near-one margin is a property of the fixed limiting function. -/
theorem low_near_full_le {v g : Cantor → ℝ} {τ : ℝ}
    (hv : Integrable v fairCoin) (hg : Integrable g fairCoin) (hτ : 0 < τ) :
    fairCoin.real {Z | g Z < 1 ∧ 1 - τ < v Z} ≤
      fairCoin.real {Z | 1 - 2 * τ < g Z ∧ g Z < 1} +
        (∫ Z, |v Z - g Z| ∂fairCoin) / τ := by
  have hsub : {Z | g Z < 1 ∧ 1 - τ < v Z} ⊆
      {Z | 1 - 2 * τ < g Z ∧ g Z < 1} ∪ {Z | τ ≤ |v Z - g Z|} := by
    intro Z hZ
    by_cases hm : 1 - 2 * τ < g Z
    · exact Or.inl ⟨hm, hZ.1⟩
    · apply Or.inr
      have hg' : g Z ≤ 1 - 2 * τ := le_of_not_gt hm
      have hv' : 1 - τ < v Z := hZ.2
      have he : τ < v Z - g Z := by linarith
      exact he.le.trans (le_abs_self _)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := fairCoin) (f := fun Z => |v Z - g Z|)
    (Eventually.of_forall fun Z => abs_nonneg _) (hv.sub hg).abs τ
  have hdiv : fairCoin.real {Z | τ ≤ |v Z - g Z|} ≤
      (∫ Z, |v Z - g Z| ∂fairCoin) / τ := by
    apply (le_div_iff₀ hτ).mpr
    simpa only [mul_comm] using hm
  exact ((measureReal_mono (μ := fairCoin) hsub).trans
    (measureReal_union_le (μ := fairCoin) _ _)).trans (add_le_add le_rfl hdiv)

theorem low_near_full_lt {v g : Cantor → ℝ} {τ δ ε : ℝ}
    (hv : Integrable v fairCoin) (hg : Integrable g fairCoin) (hτ : 0 < τ)
    (herr : (∫ Z, |v Z - g Z| ∂fairCoin) < 8 * δ)
    (hmargin : fairCoin.real {Z | 1 - 2 * τ < g Z ∧ g Z < 1} < ε) :
    fairCoin.real {Z | g Z < 1 ∧ 1 - τ < v Z} < ε + 8 * δ / τ := by
  exact (low_near_full_le hv hg hτ).trans_lt
    (add_lt_add hmargin (div_lt_div_of_pos_right herr hτ))

end Klr.PoolSoundness

namespace Klr.PoolAdvice

open MeasureTheory Filter PoolQuery PoolSoundness
open scoped BigOperators symmDiff

/-- The minimum weight among the protected zero-based indices. -/
noncomputable def protectedWeight (A : Advice) : ℝ := (1 / 2 : ℝ) ^ A.protectedCount

theorem protectedWeight_pos (A : Advice) : 0 < protectedWeight A := by
  exact pow_pos (by norm_num) _

theorem protectedWeight_le_weight (A : Advice) {i : ℕ} (hi : i < A.protectedCount) :
    protectedWeight A ≤ (weight i : ℝ) := by
  simp only [protectedWeight, weight, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem weight_nonneg (i : ℕ) : (0 : ℝ) ≤ weight i := by
  simp only [weight, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  positivity

/-- The accepted weighted mass bounds every protected scan's later L1 increase. -/
theorem Accepted.later_increase_lt {rules : List ScanRule} {A : Advice} {M : ℕ}
    {C : Candidate} (h : Accepted rules A M C) (π : ℕ → ScanRule)
    (hπ : ∀ i < rules.length, rules[i]? = some (π i))
    (hℓ : A.protectedCount ≤ rules.length) {B : ℝ}
    (hB : ∑ i ∈ Finset.range rules.length,
      (weight i : ℝ) * ∫ Z, readFraction (π i) C.1.toFinset Z ∂fairCoin ≤ B)
    (hgap : B - (A.threshold : ℝ) < 4 * protectedWeight A * (A.error : ℝ))
    {i : ℕ} (hi : i < A.protectedCount) :
    (∫ Z, |readFraction (π i) C.1.toFinset Z -
      readFractionBy (π i) C.1.toFinset C.2 Z| ∂fairCoin) < 4 * (A.error : ℝ) := by
  rw [integral_abs_sub_of_le (integrable_readFractionBy _ _ _)
    (integrable_readFraction _ _) (readFractionBy_le_readFraction _ _ _)]
  exact increment_lt_of_weighted_gap (hi.trans_le hℓ)
    (fun j _ => weight_nonneg j)
    (fun j _ => integral_mono (integrable_readFractionBy _ _ _) (integrable_readFraction _ _)
      (readFractionBy_le_readFraction _ _ _))
    hB (h.measure_spec π hπ hℓ).2.2 hgap (protectedWeight_pos A)
    (protectedWeight_le_weight A hi)

/-- Finite acceptance, later-increase control, and fixed cylinder approximation
give the paper's strict `8δ` L1 bound for final coverage. -/
theorem Accepted.final_l1_lt {rules : List ScanRule} {A : Advice} {M : ℕ}
    {C : Candidate} (h : Accepted rules A M C) (π : ℕ → ScanRule)
    (hπ : ∀ i < rules.length, rules[i]? = some (π i))
    (hℓ : A.protectedCount ≤ rules.length) {B : ℝ}
    (hB : ∑ i ∈ Finset.range rules.length,
      (weight i : ℝ) * ∫ Z, readFraction (π i) C.1.toFinset Z ∂fairCoin ≤ B)
    (hgap : B - (A.threshold : ℝ) < 4 * protectedWeight A * (A.error : ℝ))
    {i : ℕ} (hi : i < A.protectedCount) {g : Cantor → ℝ}
    (hg : Integrable g fairCoin)
    (happrox : (∫ Z, |approx A i Z - g Z| ∂fairCoin) < (A.error : ℝ)) :
    (∫ Z, |readFraction (π i) C.1.toFinset Z - g Z| ∂fairCoin) < 8 * (A.error : ℝ) := by
  have h₁ := h.later_increase_lt π hπ hℓ hB hgap hi
  have h₂ := (h.measure_spec π hπ hℓ).2.1 i hi
  have htriangle₁ := integral_abs_sub_le_add (integrable_readFraction (π i) C.1.toFinset)
    (integrable_readFractionBy (π i) C.1.toFinset C.2) hg
  have htriangle₂ := integral_abs_sub_le_add
    (integrable_readFractionBy (π i) C.1.toFinset C.2) (integrable_approx A i) hg
  linarith

/-- The accepted finite high-set test controls eventual high-set failure. -/
theorem Accepted.high_failure_lt {rules : List ScanRule} {A : Advice} {M : ℕ}
    {C : Candidate} (h : Accepted rules A M C) (π : ℕ → ScanRule)
    (hπ : ∀ i < rules.length, rules[i]? = some (π i))
    (hℓ : A.protectedCount ≤ rules.length) {i : ℕ} (hi : i < A.protectedCount)
    {H : Set Cantor} (hH : fairCoin.real (H ∆ highSet A i) < (A.error : ℝ)) :
    fairCoin.real {Z | Z ∈ H ∧ readFraction (π i) C.1.toFinset Z < 1} <
      4 * (A.error : ℝ) :=
  PoolSoundness.high_failure_lt (readFractionBy_le_readFraction _ _ _) hH
    ((h.measure_spec π hπ hℓ).1 i hi)

/-- The accepted finite tests control nearly full eventual coverage on the
strict low set, provided the fixed limiting function has the stated margin. -/
theorem Accepted.low_near_full_lt {rules : List ScanRule} {A : Advice} {M : ℕ}
    {C : Candidate} (h : Accepted rules A M C) (π : ℕ → ScanRule)
    (hπ : ∀ i < rules.length, rules[i]? = some (π i))
    (hℓ : A.protectedCount ≤ rules.length) {B : ℝ}
    (hB : ∑ i ∈ Finset.range rules.length,
      (weight i : ℝ) * ∫ Z, readFraction (π i) C.1.toFinset Z ∂fairCoin ≤ B)
    (hgap : B - (A.threshold : ℝ) < 4 * protectedWeight A * (A.error : ℝ))
    {i : ℕ} (hi : i < A.protectedCount) {g : Cantor → ℝ}
    (hg : Integrable g fairCoin)
    (happrox : (∫ Z, |approx A i Z - g Z| ∂fairCoin) < (A.error : ℝ))
    {τ ε : ℝ} (hτ : 0 < τ)
    (hmargin : fairCoin.real {Z | 1 - 2 * τ < g Z ∧ g Z < 1} < ε) :
    fairCoin.real {Z | g Z < 1 ∧ 1 - τ < readFraction (π i) C.1.toFinset Z} <
      ε + 8 * (A.error : ℝ) / τ :=
  PoolSoundness.low_near_full_lt (integrable_readFraction _ _) hg hτ
    (h.final_l1_lt π hπ hℓ hB hgap hi hg happrox) hmargin

end Klr.PoolAdvice

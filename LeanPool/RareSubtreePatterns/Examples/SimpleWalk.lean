/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.ToolkitProof
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Non-vacuity of the stable-domain hypothesis

A witness for `StableDomain`: the offspring law `μ = (δ₀ + δ₂)/2` (simple random walk steps
`±1`; critical, variance one, periodic with span two, so the lattice case is exercised),
`α = 2`, `a_n = √(n/2)` and limit law `ν = N(0,2)`. It shows that `StableDomain μ α a` is
  satisfiable,
hence that `PoissonDeclumping.Stable.stableToolkit` is not a vacuous implication.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.Examples.SimpleWalk
open PoissonDeclumping PoissonDeclumping.Stable

noncomputable def f : ℕ → ℝ≥0∞ := fun j => if j = 0 ∨ j = 2 then 1 / 2 else 0

noncomputable def μ : PMF ℕ := PMF.ofFinset f {0, 2}
  (by
    simp only [f, one_div, Finset.mem_singleton, OfNat.zero_ne_ofNat, not_false_eq_true,
      Finset.sum_insert, or_false, ↓reduceIte, Finset.sum_singleton, OfNat.ofNat_ne_zero, or_true]
    exact ENNReal.inv_two_add_inv_two)
  (by intro j hj; simp at hj; simp [f, hj.1, hj.2])

lemma μ_apply (j : ℕ) : μ j = f j := rfl

lemma critical : IsCritical μ := by
  unfold IsCritical
  rw [tsum_eq_single 2]
  · simp only [Nat.cast_ofNat, μ_apply, f, OfNat.ofNat_ne_zero, or_true, ↓reduceIte, one_div]
    exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  · intro j hj
    by_cases h0 : j = 0
    · simp [h0]
    · simp [μ_apply, f, h0, hj]

lemma nondeg : μ 1 ≠ 1 := by simp [μ_apply, f]

noncomputable def a (n : ℕ) : ℝ := Real.sqrt (n / 2)

noncomputable def ℓ (x : ℝ) : ℝ := if x < 2 then 0 else 2

lemma toReal_μ (j : ℕ) : (μ j).toReal = if j = 0 ∨ j = 2 then 1 / 2 else 0 := by
  rw [μ_apply, f]; split_ifs <;> simp

lemma second : ∃ ℓ : ℝ → ℝ, SlowlyVarying ℓ ∧ ∀ n : ℕ, 1 ≤ n →
    ∑ j ∈ Finset.range (n + 1), (j : ℝ) ^ 2 * (μ j).toReal = ℓ n * (n : ℝ) ^ ((2 : ℝ) - 2) := by
  refine ⟨ℓ, ?_, ?_⟩
  · intro c hc
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max 2 (2 / c))] with x hx
    have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
    have hcx : 2 ≤ c * x := by
      have := le_trans (le_max_right _ _) hx
      rw [div_le_iff₀ hc] at this; linarith
    simp [ℓ, not_lt.2 hx2, not_lt.2 hcx]
  · intro n hn
    simp only [sub_self, Real.rpow_zero, mul_one, toReal_μ]
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      simp [Finset.sum_range_succ, ℓ]
    · have hn2 : ¬ ((n : ℝ) < 2) := by
        rw [not_lt]; exact_mod_cast h
      rw [Finset.sum_eq_single 2]
      · simp [ℓ, hn2]; norm_num
      · intro j _ hj; by_cases h0 : j = 0 <;> simp [h0, hj]
      · intro h2; simp at h2; omega

/-- the step law pushed to ℝ -/
noncomputable def P : Measure ℝ := (stepLaw μ).map (fun z : ℤ => (z : ℝ))

instance : IsProbabilityMeasure P := by
  unfold P
  constructor
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

lemma toMeasure_eq : μ.toMeasure = (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) •
  Measure.dirac 2 := by
  rw [Measure.ext_iff_singleton]
  intro j
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j), μ_apply, f]
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h0 : j = 0
  · subst h0; simp
  · by_cases h2 : j = 2
    · subst h2; simp
    · simp [h0, h2, Set.indicator, Ne.symm h0, Ne.symm h2]

lemma P_eq : P = (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ) + (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)
  := by
  unfold P stepLaw
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _), toMeasure_eq,
    Measure.map_add _ _ (measurable_of_countable _), Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' (measurable_of_countable _), Measure.map_dirac' (measurable_of_countable _)]
  · norm_num
  all_goals exact (measurable_of_countable _).aemeasurable

lemma P_mean : P[id] = 0 := by
  rw [P_eq, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · norm_num
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma P_var : P[id ^ 2] = 1 := by
  rw [P_eq, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · norm_num
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma charFun_P (s : ℝ) : charFun (P.map id) s = stepCF μ s := by
  rw [Measure.map_id, charFun_apply_real, P, integral_map (measurable_of_countable _).aemeasurable
    (by fun_prop), stepCF]
  congr 1

lemma laplace : ∀ lam : ℝ, 0 < lam →
    ∫ y, Real.exp (-lam * y) ∂(gaussianReal 0 2) = Real.exp (lam ^ (2 : ℝ)) := by
  intro lam _
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 2)) (-lam)
  simp only [mgf, id] at h
  rw [h, Real.rpow_two]
  congr 1; push_cast; ring

lemma conv : ∀ g : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun n : ℕ => ∫ x, g x ∂((walkLaw μ n).map (fun z : ℤ => (z : ℝ) / a n)))
      atTop (𝓝 (∫ x, g x ∂(gaussianReal 0 2))) := by
  set PL : ℕ → ProbabilityMeasure ℝ := fun n => ⟨scaledLaw μ a n, inferInstance⟩
  set Pν : ProbabilityMeasure ℝ := ⟨gaussianReal 0 2, inferInstance⟩
  have hw : Tendsto PL atTop (𝓝 Pν) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    have h := tendsto_charFun_inv_sqrt_mul_pow (P := P) (X := id) measurable_id.aemeasurable
      P_mean P_var (Real.sqrt 2 * t)
    simp only [charFun_P] at h
    have e1 : ∀ n : ℕ, charFun (PL n : Measure ℝ) t = stepCF μ ((√(n : ℝ))⁻¹ * (√2 * t)) ^ n := by
      intro n
      change charFun (scaledLaw μ a n) t = _
      rw [scaledLaw, charFun_walkLaw_map_div]
      congr 2
      rw [a, Real.sqrt_div' (n : ℝ) (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
      rw [inv_inv]
      ring
    have e2 : charFun (Pν : Measure ℝ) t = cexp (-(((√2 * t : ℝ)) : ℂ) ^ 2 / 2) := by
      change charFun (gaussianReal 0 2) t = _
      rw [charFun_gaussianReal]
      congr 1
      push_cast
      have : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
      linear_combination ((t : ℂ) ^ 2 / 2) * this
    simp_rw [e1, e2]
    exact h
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hw
  exact hw

theorem witness : StableDomain μ 2 a where
  critical := critical
  nondegenerate := nondeg
  alpha_mem := by norm_num
  monotone := fun m n hmn => Real.sqrt_le_sqrt (by
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith)
  pos := fun n hn => Real.sqrt_pos.2 (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  converges := ⟨gaussianReal 0 2, inferInstance, laplace, conv⟩

theorem toolkit : StableToolkit μ 2 a := stableToolkit witness

end PoissonDeclumping.Examples.SimpleWalk

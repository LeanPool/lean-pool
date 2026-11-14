/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.ToolkitProof
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Non-vacuity of the stable-domain hypothesis: an aperiodic witness with `μ_1 > 0`

A second witness for `StableDomain`, complementing `PoissonDeclumping.Examples.SimpleWalk`
(which is periodic with `μ_1 = 0`): the offspring law `μ = (1/4, 1/2, 1/4)` on `{0, 1, 2}`
(Binomial(2, 1/2)). It is critical, has `μ_1 = 1/2 > 0` (`mu_one_pos`, the branch of
Theorems 1.3(i) and 1.4(i)), and is aperiodic: its span is one (`latticeSpan_eq_one`). The
step `X = K - 1 ∈ {-1, 0, 1}` has mean zero and variance `1/2`, so `S_n` has variance `n/2`.
With `α = 2`, `a_n = √(n/4)` and the limit law `ν = N(0,2)` (whose Laplace transform is
`e^{λ²}`), `S_n / a_n → N(0,2)` by the central limit theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.Examples.BinomialWalk
open PoissonDeclumping PoissonDeclumping.Stable

/-- The weights `(1/4, 1/2, 1/4)` on `{0, 1, 2}`. -/
noncomputable def w (j : ℕ) : ℝ := if j = 1 then 1 / 2 else if j = 0 ∨ j = 2 then 1 / 4 else 0

lemma w_nonneg (j : ℕ) : 0 ≤ w j := by unfold w; split_ifs <;> norm_num

lemma w_eq_zero {j : ℕ} (hj : j ∉ ({0, 1, 2} : Finset ℕ)) : w j = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  simp [w, hj.1, hj.2.1, hj.2.2]

/-- The binomial offspring weights as extended nonnegative reals. -/
noncomputable def f (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal (w j)

/-- The offspring law Binomial(2, 1/2). -/
noncomputable def μ : PMF ℕ := PMF.ofFinset f {0, 1, 2}
  (by
    rw [show ∑ j ∈ ({0, 1, 2} : Finset ℕ), f j =
        ENNReal.ofReal (∑ j ∈ ({0, 1, 2} : Finset ℕ), w j)
      from (ENNReal.ofReal_sum_of_nonneg fun j _ => w_nonneg j).symm]
    simp [w]; norm_num)
  (by intro j hj; simp [f, w_eq_zero hj])

lemma μ_apply (j : ℕ) : μ j = ENNReal.ofReal (w j) := rfl

lemma toReal_μ (j : ℕ) : (μ j).toReal = w j := by
  rw [μ_apply, ENNReal.toReal_ofReal (w_nonneg j)]

lemma critical : IsCritical μ := by
  unfold IsCritical
  have h : ∀ j : ℕ, (j : ℝ≥0∞) * μ j = ENNReal.ofReal (j * w j) := by
    intro j
    rw [μ_apply, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  simp_rw [h]
  rw [tsum_eq_sum (s := {0, 1, 2}) (fun j hj => by simp [w_eq_zero hj]),
    ← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (w_nonneg j))]
  simp [w]; norm_num

/-- `μ_1 > 0`. -/
theorem mu_one_pos : 0 < μ 1 := by
  rw [μ_apply]; simp [w]

lemma mu_zero_pos : 0 < μ 0 := by
  rw [μ_apply]; simp [w]

lemma nondeg : μ 1 ≠ 1 := by
  rw [μ_apply]; simp [w]

/-- Aperiodicity: the span `gcd {i - j : μ_i μ_j > 0}` of `μ` is one. -/
theorem latticeSpan_eq_one : Stable.latticeSpan μ = 1 := by
  have h := latticeSpan_dvd μ mu_one_pos.ne' mu_zero_pos.ne'
  have h1 : (latticeSpan μ : ℤ) ∣ 1 := by simpa using h
  have h' : latticeSpan μ ∣ 1 := by exact_mod_cast h1
  exact Nat.dvd_one.1 h'

/-- The normalizing sequence `a_n = √(n/4)`. -/
noncomputable def a (n : ℕ) : ℝ := Real.sqrt (n / 4)

/-- The truncated second-moment function at positive integer arguments. -/
noncomputable def ℓ (x : ℝ) : ℝ := if x < 2 then 1 / 2 else 3 / 2

/-- `∑_{j ≤ n} j² μ_j` is `1/2` for `n = 1` and `3/2` for `n ≥ 2`. -/
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
      simp [Finset.sum_range_succ, ℓ, w]
    · have hn2 : ¬ ((n : ℝ) < 2) := by
        rw [not_lt]; exact_mod_cast h
      have hsub : ({0, 1, 2} : Finset ℕ) ⊆ Finset.range (n + 1) := by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [Finset.mem_range]; omega
      rw [← Finset.sum_subset hsub (fun j _ hj => by simp [w_eq_zero hj])]
      simp [w, ℓ, hn2]; norm_num

/-- The step law pushed to `ℝ` and rescaled by `√2` (mean zero, variance one). -/
noncomputable def P : Measure ℝ := (stepLaw μ).map (fun z : ℤ => Real.sqrt 2 * (z : ℝ))

instance : IsProbabilityMeasure P := by
  unfold P
  constructor
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

lemma toMeasure_eq : μ.toMeasure = ENNReal.ofReal (1 / 4) • Measure.dirac 0 +
    ENNReal.ofReal (1 / 2) • Measure.dirac 1 + ENNReal.ofReal (1 / 4) • Measure.dirac 2 := by
  rw [Measure.ext_iff_singleton]
  intro j
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j), μ_apply]
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h0 : j = 0
  · subst h0; simp [w]
  · by_cases h1 : j = 1
    · subst h1; simp [w]
    · by_cases h2 : j = 2
      · subst h2; simp [w]
      · simp [w, h0, h1, h2, Set.indicator, Ne.symm h0, Ne.symm h1, Ne.symm h2]

lemma P_eq : P = ENNReal.ofReal (1 / 4) • Measure.dirac (-Real.sqrt 2) +
    ENNReal.ofReal (1 / 2) • Measure.dirac 0 +
    ENNReal.ofReal (1 / 4) • Measure.dirac (Real.sqrt 2) := by
  unfold P stepLaw
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _), toMeasure_eq,
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_smul, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' (measurable_of_countable _), Measure.map_dirac' (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _)]
  · norm_num
  all_goals exact (measurable_of_countable _).aemeasurable

lemma integrable_smul_dirac (g : ℝ → ℝ) (r x : ℝ) :
    Integrable g (ENNReal.ofReal r • Measure.dirac x) :=
  (integrable_dirac (by simp)).smul_measure (by simp)

lemma P_mean : P[id] = 0 := by
  rw [P_eq, integral_add_measure, integral_add_measure, integral_smul_measure,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac, integral_dirac]
  · norm_num
  all_goals first
    | exact integrable_smul_dirac _ _ _
    | exact (integrable_smul_dirac _ _ _).add_measure (integrable_smul_dirac _ _ _)

lemma P_var : P[id ^ 2] = 1 := by
  rw [P_eq, integral_add_measure, integral_add_measure, integral_smul_measure,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac, integral_dirac]
  · norm_num
  all_goals first
    | exact integrable_smul_dirac _ _ _
    | exact (integrable_smul_dirac _ _ _).add_measure (integrable_smul_dirac _ _ _)

lemma charFun_P (s : ℝ) : charFun (P.map id) s = stepCF μ (Real.sqrt 2 * s) := by
  rw [Measure.map_id, charFun_apply_real, P, integral_map (measurable_of_countable _).aemeasurable
    (by fun_prop), stepCF]
  congr 1; funext z; congr 1; push_cast; ring

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
    have e1 : ∀ n : ℕ, charFun (PL n : Measure ℝ) t =
        stepCF μ (√2 * ((√(n : ℝ))⁻¹ * (√2 * t))) ^ n := by
      intro n
      change charFun (scaledLaw μ a n) t = _
      rw [scaledLaw, charFun_walkLaw_map_div]
      congr 2
      have h4 : √(4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have h2 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
      rw [a, Real.sqrt_div' (n : ℝ) (by norm_num : (0 : ℝ) ≤ 4), h4, div_div_eq_mul_div,
        div_eq_mul_inv]
      linear_combination (-(√(n : ℝ))⁻¹ * t) * h2
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

theorem toolkit : StableToolkit μ 2 a := Stable.stableToolkit witness

end PoissonDeclumping.Examples.BinomialWalk

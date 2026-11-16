/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: Lean/Mathlib v4.35.0 replacements
-- of deprecated names (identifier-only); see vendor/port.patch.
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Doob's Lᵖ maximal inequality

For a non-negative submartingale `f : ℕ → Ω → ℝ` and `p > 1`,
`‖max_{k ≤ n} f_k‖_{L^p} ≤ (p / (p - 1)) · ‖f_n‖_{L^p}`.

This is the strong-type companion to `MeasureTheory.maximal_ineq`
(the weak-type / level-set form of Doob's maximal inequality).

## Main results

* `MeasureTheory.maximal_ineq_Lp`: Doob's L^p maximal inequality for
  discrete-time non-negative submartingales.

## Proof outline

The proof follows the standard textbook argument:

1. Layer-cake decomposition:
   `∫⁻ f*^p = p · ∫⁻ t in (0, ∞), μ{f* ≥ t} · t^{p-1}`.
2. Weak-type bound. Apply `MeasureTheory.maximal_ineq` pointwise:
   `μ{f* ≥ t} · t^{p-1} ≤ t^{p-2} · ∫_{f* ≥ t} f_n`.
3. Fubini. Swap the order of integration to express the right-hand side as
   `∫⁻ ω, f_n(ω) · f*(ω)^{p-1} / (p-1)`.
4. Hölder. Bound that integral by
   `(∫⁻ f_n^p)^{1/p} · (∫⁻ f*^p)^{(p-1)/p}` using conjugate exponents.
5. Rpow inversion. From `A ≤ C · B^{1/p} · A^{(p-1)/p}`, conclude
   `A^{1/p} ≤ C · B^{1/p}`. A truncation argument (replacing `f*` by
   `min f* K` and letting `K → ∞` via monotone convergence) handles the
   case where `A = ∞` a priori.

-/

@[expose] public section

open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*}

/-- Internal abbreviation for the running maximum
`max {f 0 ω, f 1 ω, …, f n ω}`. Kept `private`: the public theorem
states the bound in terms of the explicit `Finset.sup'` form to match
`MeasureTheory.maximal_ineq`. -/
private def runMax (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k ↦ f k ω)

private lemma runMax_nonneg {f : ℕ → Ω → ℝ} (hnonneg : ∀ n ω, 0 ≤ f n ω) (n : ℕ) (ω : Ω) :
    0 ≤ runMax f n ω :=
  le_trans (hnonneg 0 ω)
    (Finset.le_sup' (f := fun k ↦ f k ω) (Finset.mem_range.mpr (Nat.succ_pos n)))

variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}

private lemma runMax_measurable {f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ m0}
    (hsub : Submartingale f 𝒢 μ) (n : ℕ) :
    Measurable (runMax f n) := by
  unfold runMax
  exact Finset.measurable_range_sup''
    (fun k _ ↦ ((hsub.stronglyMeasurable k).mono (𝒢.le k)).measurable)

/-- Pointwise (in `t > 0`) integrand bound. -/
private lemma layer_integrand_bound
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω) (n : ℕ) {p : ℝ}
    {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ runMax f n ω} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal (t ^ (p - 2)) *
          ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ) := by
  have ht_pow_pos : (0 : ℝ) ≤ t ^ (p - 2) := Real.rpow_nonneg ht.le _
  have h_decomp : t ^ (p - 1) = t ^ (p - 2) * t := by
    rw [show (p - 1) = (p - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
  rw [h_decomp, ENNReal.ofReal_mul ht_pow_pos]
  rw [show μ {ω | t ≤ runMax f n ω} * (ENNReal.ofReal (t^(p-2)) * ENNReal.ofReal t)
        = ENNReal.ofReal (t^(p-2)) * (ENNReal.ofReal t * μ {ω | t ≤ runMax f n ω})
        by ring]
  gcongr
  -- Apply Doob's weak-type maximal inequality at level `t`.
  have key := MeasureTheory.maximal_ineq (μ := μ) (𝒢 := 𝒢)
    (f := f) hsub (fun k ω ↦ hnonneg k ω) (ε := t.toNNReal) n
  rw [show ({ω | t ≤ runMax f n ω}) = ({ω | (↑t.toNNReal : ℝ) ≤ runMax f n ω}) by
    rw [Real.coe_toNNReal _ ht.le]]
  exact key

/-- Combining steps: A ≤ ofReal p · ∫⁻ t in Ioi 0, ofReal(t^(p-2)) · ofReal(∫_{fstar ≥ t} f_n). -/
private lemma A_le_layer_integral
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ
      ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal (t ^ (p - 2)) *
              ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul μ
        (ae_of_all _ (runMax_nonneg hnonneg n))
        (runMax_measurable hsub n).aemeasurable hp_pos]
  apply mul_le_mul_right _ (ENNReal.ofReal p)
  apply MeasureTheory.setLIntegral_mono_ae'
  · exact measurableSet_Ioi
  refine Filter.Eventually.of_forall (fun t ht ↦ ?_)
  exact layer_integrand_bound hsub hnonneg n ht

/-- Inner integral evaluation: `∫⁻ t in Ioc 0 f, ofReal(t^(p-2)) = ofReal(f^(p-1)/(p-1))`. -/
private lemma lintegral_rpow_Ioc
    {f p : ℝ} (hf : 0 < f) (hp : 1 < p) :
    ∫⁻ t in Set.Ioc (0:ℝ) f, ENNReal.ofReal (t^(p-2)) =
      ENNReal.ofReal (f^(p-1)/(p-1)) := by
  have hpm1 : -1 < p - 2 := by linarith
  rw [show (f^(p-1)/(p-1) : ℝ) = ∫ t in Set.Ioc (0:ℝ) f, t^(p-2) from ?_]
  · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · apply MeasureTheory.IntegrableOn.integrable
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hf.le).mp
        (intervalIntegral.intervalIntegrable_rpow' hpm1)
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all _ (fun t ht ↦ Real.rpow_nonneg ht.1.le _))
  rw [← intervalIntegral.integral_of_le hf.le]
  rw [integral_rpow (Or.inl hpm1)]
  have hzp : (0:ℝ)^(p - 2 + 1) = 0 := Real.zero_rpow (by linarith : p - 2 + 1 ≠ 0)
  rw [hzp, show p - 2 + 1 = p - 1 by ring]
  ring

/-- Pointwise inner integral: for `fstar ≥ 0`, integrating `t^(p-2)` against
    the indicator `𝟙{0 < t ≤ fstar}` evaluates to `fstar^(p-1)/(p-1)`. -/
private lemma inner_t_integral
    {fstar p : ℝ} (hfstar : 0 ≤ fstar) (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t
      = ENNReal.ofReal (fstar ^ (p - 1) / (p - 1)) := by
  rcases hfstar.lt_or_eq with hpos | hzero
  · -- fstar > 0: rewrite indicator-restricted integral as setLIntegral on Ioc.
    have h_eq : Set.EqOn
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) *
            {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t)
        ((Set.Ioc 0 fstar).indicator (fun t ↦ ENNReal.ofReal (t ^ (p - 2))))
        (Set.Ioi (0:ℝ)) := by
      intro t ht
      simp only
      by_cases hle : t ≤ fstar
      · have hmem1 : t ∈ {t : ℝ | t ≤ fstar} := hle
        have hmem2 : t ∈ Set.Ioc (0:ℝ) fstar := ⟨ht, hle⟩
        rw [Set.indicator_of_mem hmem1, mul_one, Set.indicator_of_mem hmem2]
      · have hnmem1 : t ∉ {t : ℝ | t ≤ fstar} := hle
        have hnmem2 : t ∉ Set.Ioc (0:ℝ) fstar := fun h ↦ hle h.2
        rw [Set.indicator_of_notMem hnmem1, mul_zero, Set.indicator_of_notMem hnmem2]
    rw [setLIntegral_congr_fun measurableSet_Ioi h_eq]
    have hsubset : Set.Ioc (0:ℝ) fstar ⊆ Set.Ioi 0 :=
      fun _ ht ↦ ht.1
    have : ∫⁻ t in Set.Ioi (0:ℝ), (Set.Ioc 0 fstar).indicator
              (fun t ↦ ENNReal.ofReal (t ^ (p - 2))) t
            = ∫⁻ t in Set.Ioc (0:ℝ) fstar, ENNReal.ofReal (t ^ (p - 2)) := by
      rw [setLIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_left.mpr hsubset]
    rw [this]
    exact lintegral_rpow_Ioc hpos hp
  · -- fstar = 0: both sides are 0.
    subst hzero
    have h_eq : Set.EqOn
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) *
            {t : ℝ | t ≤ (0:ℝ)}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t)
        (fun _ ↦ 0) (Set.Ioi (0:ℝ)) := by
      intro t ht
      simp only
      have hnot : t ∉ {t : ℝ | t ≤ (0:ℝ)} := by
        change ¬ t ≤ 0
        exact not_le.mpr ht
      rw [Set.indicator_of_notMem hnot, mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi h_eq, lintegral_zero]
    have hp10 : p - 1 ≠ 0 := by linarith
    simp [Real.zero_rpow hp10]

/-- Fubini swap stage (Tier A.2 Stage 1).

    For `p > 1`, a non-negative submartingale `f`, and a time `n`, the
    iterated integral
       `∫⁻ t in Ioi 0, ofReal(t^(p-2)) ⋅ ∫⁻_{fstar ≥ t} ofReal(f_n) dμ`
    equals
       `∫⁻ ω, ofReal(f_n ω) ⋅ ofReal((fstar ω)^(p-1) / (p-1)) dμ`.

    Proof: rewrite the inner set-integral as an indicator-weighted full
    integral; apply `MeasureTheory.lintegral_lintegral_swap` to swap the
    order of integration; then evaluate the inner `t`-integral pointwise
    via `inner_t_integral`. -/
private lemma fubini_swap
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((runMax f n ω) ^ (p - 1) / (p - 1)) ∂μ := by
  -- Measurability of runMax f n and f n.
  have hRunMaxMeas : Measurable (runMax f n) := runMax_measurable hsub n
  have hsubM : Measurable (f n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl
  -- Joint set {(t,ω) | t ≤ runMax f n ω} is product-measurable as the
  -- preimage of {(a,b) : ℝ×ℝ | a ≤ b} under (fst, runMax ∘ snd).
  have hJointSet : MeasurableSet {pr : ℝ × Ω | pr.1 ≤ runMax f n pr.2} := by
    have h1 : Measurable (fun pr : ℝ × Ω ↦ pr.1) := measurable_fst
    have h2 : Measurable (fun pr : ℝ × Ω ↦ runMax f n pr.2) :=
      hRunMaxMeas.comp measurable_snd
    exact measurableSet_le h1 h2
  -- Step 1: rewrite the inner setLIntegral as a full lintegral via indicator.
  have step1 : ∀ t,
      ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
        = ∫⁻ ω, {ω | t ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    rw [lintegral_indicator (measurableSet_le measurable_const hRunMaxMeas)]
  -- Step 2: pull the constant `ofReal(t^(p-2))` inside the inner lintegral.
  have step2 : ∀ t, ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ ω, {ω | t ≤ runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ
      = ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
              {ω | t ≤ runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    exact (lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hsubM).indicator
            (measurableSet_le measurable_const hRunMaxMeas))).symm
  simp_rw [step1, step2]
  -- Joint measurability of the bivariate integrand.
  have hF_meas : Measurable (fun pr : ℝ × Ω ↦
      ENNReal.ofReal (pr.1 ^ (p - 2)) *
        {q : ℝ × Ω | q.1 ≤ runMax f n q.2}.indicator
          (fun q ↦ ENNReal.ofReal (f n q.2)) pr) := by
    refine Measurable.mul ?_ ?_
    · refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_fst : Measurable (fun pr : ℝ × Ω ↦ pr.1)).pow_const (p - 2)
    · refine Measurable.indicator ?_ hJointSet
      exact ENNReal.measurable_ofReal.comp (hsubM.comp measurable_snd)
  -- Rewrite the LHS with indicator on Ioi 0 (so it becomes a full lintegral
  -- over ℝ) and apply lintegral_lintegral_swap on ℝ × Ω.
  rw [← lintegral_indicator measurableSet_Ioi]
  -- LHS now is ∫⁻ t, (Ioi 0).indicator (fun t ↦ ∫⁻ ω, F(t,ω) ∂μ) t ∂volume
  -- Massage to ∫⁻ t, ∫⁻ ω, (Ioi 0).indicator (fun _ ↦ F(t,ω)) t ∂μ
  have lhs_rewrite : ∫⁻ a, (Set.Ioi (0:ℝ)).indicator
        (fun t ↦ ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
                {ω | t ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ) a
      = ∫⁻ t, ∫⁻ ω, (Set.Ioi (0:ℝ)).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                {ω | s ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t ∂μ := by
    apply lintegral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem ht]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, ← lintegral_zero (μ := μ)]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_notMem ht]
  rw [lhs_rewrite]
  -- Now apply lintegral_lintegral_swap.
  have hSwap_meas : AEMeasurable
      (Function.uncurry (fun t ω ↦ (Set.Ioi (0:ℝ)).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω | s ≤ runMax f n ω}.indicator
              (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t))
      (volume.prod μ) := by
    refine (Measurable.indicator ?_ ?_).aemeasurable
    · exact hF_meas
    · exact measurable_fst measurableSet_Ioi
  rw [lintegral_lintegral_swap hSwap_meas]
  -- Now have ∫⁻ ω, ∫⁻ t, indicator(Ioi 0) F(t,ω) ∂volume ∂μ.
  -- For each ω, the inner is the integral over Ioi 0 of
  --   ofReal(t^(p-2)) * 𝟙{t ≤ runMax f n ω} * ofReal(f n ω)
  -- = ofReal(f n ω) * (∫⁻ t in Ioi 0, ofReal(t^(p-2)) * 𝟙{t ≤ fstar ω})
  -- = ofReal(f n ω) * ofReal((runMax f n ω)^(p-1) / (p-1))  [inner_t_integral]
  apply lintegral_congr_ae
  filter_upwards with ω
  -- Reduce the inner integral.
  have h_inner_simp :
      ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω' | s ≤ runMax f n ω'}.indicator
              (fun ω' ↦ ENNReal.ofReal (f n ω')) ω) t
        = ENNReal.ofReal (f n ω) *
            ENNReal.ofReal ((runMax f n ω) ^ (p - 1) / (p - 1)) := by
    -- Rewrite the inner indicator
    have h_pointwise : ∀ t,
        (Set.Ioi (0:ℝ)).indicator
            (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
              {ω' | s ≤ runMax f n ω'}.indicator
                (fun ω' ↦ ENNReal.ofReal (f n ω')) ω) t
          = ENNReal.ofReal (f n ω) *
              ((Set.Ioi (0:ℝ)).indicator
                (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                  {s : ℝ | s ≤ runMax f n ω}.indicator
                    (fun _ ↦ (1 : ℝ≥0∞)) s)) t := by
      intro t
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        by_cases hle : t ≤ runMax f n ω
        · have hmem1 : ω ∈ {ω' | t ≤ runMax f n ω'} := hle
          have hmem2 : t ∈ {s : ℝ | s ≤ runMax f n ω} := hle
          rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, mul_one]
          ring
        · have hnmem1 : ω ∉ {ω' | t ≤ runMax f n ω'} := hle
          have hnmem2 : t ∉ {s : ℝ | s ≤ runMax f n ω} := hle
          rw [Set.indicator_of_notMem hnmem1, Set.indicator_of_notMem hnmem2,
              mul_zero, mul_zero]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
    simp_rw [h_pointwise]
    rw [lintegral_const_mul']
    · -- The inner lintegral matches inner_t_integral.
      have h_eq :
          ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                {s : ℝ | s ≤ runMax f n ω}.indicator
                  (fun _ ↦ (1 : ℝ≥0∞)) s) t
            = ∫⁻ t in Set.Ioi (0:ℝ),
                ENNReal.ofReal (t ^ (p - 2)) *
                  {s : ℝ | s ≤ runMax f n ω}.indicator
                    (fun _ ↦ (1 : ℝ≥0∞)) t := by
        rw [← lintegral_indicator measurableSet_Ioi]
      rw [h_eq, inner_t_integral (runMax_nonneg hnonneg n ω) hp]
    · exact ENNReal.ofReal_ne_top
  rw [h_inner_simp]

/-- Stage 2a: apply Hölder to the post-Fubini integral.

    For non-negative f, g and Hölder conjugates p, q (so 1/p + 1/q = 1):
       `∫⁻ ω, ofReal(f_n) ⋅ ofReal(fstar^(p-1)) ≤ (∫⁻ f_n^p)^(1/p) ⋅ (∫⁻ fstar^p)^(1/q)`.
    Wraps `ENNReal.lintegral_mul_le_Lp_mul_Lq` plus the rpow algebra
    `(x^(p-1))^q = x^p` (using `(p-1)*q = p`). -/
private lemma holder_apply
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (f n ω) *
            ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) ∂μ)
      ≤ (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ) ^ ((p - 1) / p) := by
  set q := p / (p - 1) with hq_def
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hq_pos : 0 < q := by
    simp only [hq_def]
    positivity
  have hpm1_q_eq_p : (p - 1) * q = p := by
    simp only [hq_def]
    field_simp
  have hf_meas : AEMeasurable (fun ω ↦ ENNReal.ofReal (f n ω)) μ :=
    (ENNReal.measurable_ofReal.comp
      (((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl)).aemeasurable
  have hg_meas : AEMeasurable
      (fun ω ↦ ENNReal.ofReal ((runMax f n ω) ^ (p - 1))) μ :=
    (ENNReal.measurable_ofReal.comp
      ((runMax_measurable hsub n).pow_const (p - 1))).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf_meas hg_meas
  -- Rewrite (ofReal f_n)^p = ofReal(f_n^p) using nonneg.
  have h_f_pow : ∀ ω, (ENNReal.ofReal (f n ω)) ^ p = ENNReal.ofReal ((f n ω) ^ p) :=
    fun ω ↦ ENNReal.ofReal_rpow_of_nonneg (hnonneg n ω) hp_pos.le
  -- Rewrite (ofReal fstar^(p-1))^q = ofReal(fstar^p) using (p-1)*q = p.
  have h_g_pow : ∀ ω,
      (ENNReal.ofReal ((runMax f n ω) ^ (p - 1))) ^ q
        = ENNReal.ofReal ((runMax f n ω) ^ p) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg
          (Real.rpow_nonneg (runMax_nonneg hnonneg n ω) _) hq_pos.le,
        ← Real.rpow_mul (runMax_nonneg hnonneg n ω) (p - 1) q, hpm1_q_eq_p]
  simp_rw [h_f_pow, h_g_pow] at key
  -- The goal has 1/p and (p-1)/p; key has 1/q (= q⁻¹). Rewrite 1/q = (p-1)/p.
  have h_one_div_q : (1 / q : ℝ) = (p - 1) / p := by
    simp only [hq_def, one_div, inv_div]
  rw [h_one_div_q] at key
  exact key

/-- Truncated inner t-integral: for `fstar ≥ 0` and `K > 0`,
       `∫⁻ t in Ioi 0, t^(p-2) ⋅ 𝟙{0 < t ≤ K ∧ t ≤ fstar}
         = ofReal(min fstar K^(p-1) / (p-1))`.
    Identical to `inner_t_integral` but with an extra `t ≤ K` constraint,
    which makes the inner Ioc become `Ioc 0 (min fstar K)`. -/
private lemma inner_t_integral_truncated
    {fstar K p : ℝ} (hfstar : 0 ≤ fstar) (hK : 0 < K) (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) t *
         {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t)
      = ENNReal.ofReal ((min fstar K) ^ (p - 1) / (p - 1)) := by
  -- Reduce to the untruncated case via `t ≤ K ∧ t ≤ fstar ↔ t ≤ min fstar K`.
  have h_eq : ∀ t,
      (Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) t *
        {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t
      = {t : ℝ | t ≤ min fstar K}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t := fun t ↦ by
    by_cases hK' : t ≤ K
    · by_cases hfs : t ≤ fstar
      · rw [Set.indicator_of_mem (show t ∈ Set.Iic K from hK'),
            Set.indicator_of_mem (show t ∈ {t : ℝ | t ≤ fstar} from hfs),
            Set.indicator_of_mem (show t ∈ {t : ℝ | t ≤ min fstar K} from le_min hfs hK'),
            mul_one]
      · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | t ≤ fstar} from hfs),
            Set.indicator_of_notMem
              (show t ∉ {t : ℝ | t ≤ min fstar K} from
                fun h ↦ hfs (h.trans (min_le_left _ _))),
            mul_zero]
    · rw [Set.indicator_of_notMem (show t ∉ Set.Iic K from hK'),
          Set.indicator_of_notMem
            (show t ∉ {t : ℝ | t ≤ min fstar K} from
              fun h ↦ hK' (h.trans (min_le_right _ _))),
          zero_mul]
  simp_rw [h_eq]
  exact inner_t_integral (le_min hfstar hK.le) hp

/-- Truncated Fubini swap. Analog of `fubini_swap` but with the outer
    `t`-integral restricted to `Ioc 0 K`, producing
    `min (runMax f n) K` in the post-swap formula. -/
private lemma fubini_swap_truncated
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    ∫⁻ t in Set.Ioc (0:ℝ) K,
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1) / (p - 1)) ∂μ := by
  -- Rewrite the LHS via an Ioi 0 outer integral with an Iic K indicator,
  -- so we can reuse the bivariate Fubini machinery.
  have hRunMaxMeas : Measurable (runMax f n) := runMax_measurable hsub n
  have hsubM : Measurable (f n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl
  have hIocEqRestrict : Set.Ioc (0:ℝ) K = Set.Ioi 0 ∩ Set.Iic K := by
    ext t
    simp [Set.mem_Ioc, Set.mem_Ioi, Set.mem_Iic, and_comm]
  rw [hIocEqRestrict]
  rw [← MeasureTheory.lintegral_indicator (measurableSet_Ioi.inter measurableSet_Iic)]
  -- Step 1: rewrite the inner setLIntegral as a full lintegral via indicator.
  have step1 : ∀ t,
      ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
        = ∫⁻ ω, {ω | t ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    rw [lintegral_indicator (measurableSet_le measurable_const hRunMaxMeas)]
  -- Step 2: pull the constant ofReal(t^(p-2)) inside the inner lintegral.
  have step2 : ∀ t, ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ ω, {ω | t ≤ runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ
      = ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
              {ω | t ≤ runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    exact (lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hsubM).indicator
            (measurableSet_le measurable_const hRunMaxMeas))).symm
  -- Joint measurability of the bivariate integrand (Ioi 0 ∩ Iic K is product-measurable).
  have hJointSet : MeasurableSet {pr : ℝ × Ω | pr.1 ≤ runMax f n pr.2} := by
    have h1 : Measurable (fun pr : ℝ × Ω ↦ pr.1) := measurable_fst
    have h2 : Measurable (fun pr : ℝ × Ω ↦ runMax f n pr.2) :=
      hRunMaxMeas.comp measurable_snd
    exact measurableSet_le h1 h2
  have hF_meas : Measurable (fun pr : ℝ × Ω ↦
      ENNReal.ofReal (pr.1 ^ (p - 2)) *
        {q : ℝ × Ω | q.1 ≤ runMax f n q.2}.indicator
          (fun q ↦ ENNReal.ofReal (f n q.2)) pr) := by
    refine Measurable.mul ?_ ?_
    · refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_fst : Measurable (fun pr : ℝ × Ω ↦ pr.1)).pow_const (p - 2)
    · refine Measurable.indicator ?_ hJointSet
      exact ENNReal.measurable_ofReal.comp (hsubM.comp measurable_snd)
  -- Rewrite outer indicator + push into bivariate integrand.
  have h_outer_eq : ∫⁻ a, (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) *
                ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ) a
      = ∫⁻ t, ∫⁻ ω, (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                {ω | s ≤ runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t ∂μ := by
    apply lintegral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Ioi (0:ℝ) ∩ Set.Iic K
    · rw [Set.indicator_of_mem ht, step1, step2]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, ← lintegral_zero (μ := μ)]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_notMem ht]
  rw [h_outer_eq]
  -- Apply Fubini.
  have hSwap_meas : AEMeasurable
      (Function.uncurry (fun t ω ↦ (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω | s ≤ runMax f n ω}.indicator
              (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t))
      (volume.prod μ) := by
    refine (Measurable.indicator ?_ ?_).aemeasurable
    · exact hF_meas
    · exact measurable_fst (measurableSet_Ioi.inter measurableSet_Iic)
  rw [lintegral_lintegral_swap hSwap_meas]
  apply lintegral_congr_ae
  filter_upwards with ω
  -- Pointwise: rewrite indicator product, pull out ofReal(f_n ω), use inner_t_integral_truncated.
  have h_pointwise : ∀ t,
      (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω' | s ≤ runMax f n ω'}.indicator
              (fun ω' ↦ ENNReal.ofReal (f n ω')) ω) t
        = ENNReal.ofReal (f n ω) *
            ((Set.Ioi (0:ℝ)).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) s *
                 {s : ℝ | s ≤ runMax f n ω}.indicator
                  (fun _ ↦ (1 : ℝ≥0∞)) s)) t) := by
    intro t
    by_cases ht_pos : t ∈ Set.Ioi (0:ℝ)
    · by_cases ht_K : t ∈ Set.Iic K
      · have ht_both : t ∈ Set.Ioi (0:ℝ) ∩ Set.Iic K := ⟨ht_pos, ht_K⟩
        rw [Set.indicator_of_mem ht_both, Set.indicator_of_mem ht_pos,
            Set.indicator_of_mem ht_K, one_mul]
        by_cases h_le : t ≤ runMax f n ω
        · have hmem1 : ω ∈ {ω' | t ≤ runMax f n ω'} := h_le
          have hmem2 : t ∈ {s : ℝ | s ≤ runMax f n ω} := h_le
          rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, mul_one]
          ring
        · have hnmem1 : ω ∉ {ω' | t ≤ runMax f n ω'} := h_le
          have hnmem2 : t ∉ {s : ℝ | s ≤ runMax f n ω} := h_le
          rw [Set.indicator_of_notMem hnmem1, Set.indicator_of_notMem hnmem2]
          ring
      · have ht_not_both : t ∉ Set.Ioi (0:ℝ) ∩ Set.Iic K := fun h ↦ ht_K h.2
        rw [Set.indicator_of_notMem ht_not_both, Set.indicator_of_mem ht_pos,
            Set.indicator_of_notMem ht_K, zero_mul, mul_zero, mul_zero]
    · have ht_not_both : t ∉ Set.Ioi (0:ℝ) ∩ Set.Iic K := fun h ↦ ht_pos h.1
      rw [Set.indicator_of_notMem ht_not_both,
          Set.indicator_of_notMem ht_pos, mul_zero]
  simp_rw [h_pointwise]
  rw [lintegral_const_mul']
  · -- Convert to setLIntegral on Ioi 0, then apply inner_t_integral_truncated.
    have h_unfold :
        ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
            (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
              ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) s *
               {s : ℝ | s ≤ runMax f n ω}.indicator
                (fun _ ↦ (1 : ℝ≥0∞)) s)) t
          = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
              ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) t *
               {t : ℝ | t ≤ runMax f n ω}.indicator
                (fun _ ↦ (1 : ℝ≥0∞)) t) := by
      rw [← lintegral_indicator measurableSet_Ioi]
    rw [h_unfold]
    rw [inner_t_integral_truncated (runMax_nonneg hnonneg n ω) hK hp]
  · exact ENNReal.ofReal_ne_top

/-- Truncated layer-cake bound: for `Z_K = min (runMax f n) K`,
       `∫⁻ Z_K^p ≤ ofReal(p) * ∫⁻ t in Ioc 0 K, ofReal(t^(p-2)) * ofReal(∫_{fstar ≥ t} f_n)`. -/
private lemma A_K_le_layer_integral
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    ∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ
      ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioc (0:ℝ) K,
            ENNReal.ofReal (t ^ (p - 2)) *
              ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  -- Apply layer cake to Z_K = min (runMax f n) K.
  have hZK_nn : ∀ ω, 0 ≤ min (runMax f n ω) K :=
    fun ω ↦ le_min (runMax_nonneg hnonneg n ω) hK.le
  have hZK_meas : Measurable (fun ω ↦ min (runMax f n ω) K) :=
    (runMax_measurable hsub n).min measurable_const
  have h_layer :=
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul μ
      (ae_of_all _ hZK_nn) hZK_meas.aemeasurable hp_pos
  rw [h_layer]
  -- The integrand `μ{Z_K ≥ t} * ofReal(t^(p-1))` equals
  -- `μ{runMax ≥ t} * ofReal(t^(p-1))` for t ∈ Ioc 0 K and 0 for t > K.
  have h_ZK_set : ∀ t > (0:ℝ),
      μ {ω | t ≤ min (runMax f n ω) K} =
        if t ≤ K then μ {ω | t ≤ runMax f n ω} else 0 := by
    intro t ht
    by_cases hle : t ≤ K
    · simp only [hle, ite_true]
      congr 1
      ext ω
      simp [hle]
    · simp only [hle, ite_false]
      rw [show {ω | t ≤ min (runMax f n ω) K} = ∅ by
        ext ω
        simp [hle]]
      simp
  -- Restrict the outer integral to Ioc 0 K.
  have h_split : ∫⁻ t in Set.Ioi (0:ℝ), μ {ω | t ≤ min (runMax f n ω) K} *
                  ENNReal.ofReal (t ^ (p - 1))
              = ∫⁻ t in Set.Ioc (0:ℝ) K, μ {ω | t ≤ runMax f n ω} *
                  ENNReal.ofReal (t ^ (p - 1)) := by
    have hIoiSplit : Set.Ioi (0:ℝ) = Set.Ioc 0 K ∪ Set.Ioi K := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases hle : t ≤ K
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr (not_le.mp hle)
      · rintro (⟨h1, _⟩ | h)
        · exact h1
        · exact lt_trans hK h
    rw [hIoiSplit, lintegral_union measurableSet_Ioi
        (by rw [Set.disjoint_iff]
            intro t ⟨h1, h2⟩
            simp only [Set.mem_Ioc, Set.mem_Ioi] at h1 h2
            linarith [h2, h1.2])]
    have h_zero_right : ∫⁻ t in Set.Ioi K, μ {ω | t ≤ min (runMax f n ω) K} *
                          ENNReal.ofReal (t ^ (p - 1)) = 0 := by
      apply setLIntegral_eq_zero measurableSet_Ioi
      intro t ht
      have ht_pos : 0 < t := lt_trans hK ht
      have h_eq_zero : μ {ω | t ≤ min (runMax f n ω) K} = 0 := by
        rw [h_ZK_set t ht_pos]
        have ht_gt : ¬ t ≤ K := not_le.mpr ht
        simp [ht_gt]
      change μ {ω | t ≤ min (runMax f n ω) K} * _ = 0
      rw [h_eq_zero, zero_mul]
    have h_left : ∫⁻ t in Set.Ioc (0:ℝ) K, μ {ω | t ≤ min (runMax f n ω) K} *
                    ENNReal.ofReal (t ^ (p - 1))
                = ∫⁻ t in Set.Ioc (0:ℝ) K, μ {ω | t ≤ runMax f n ω} *
                    ENNReal.ofReal (t ^ (p - 1)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change μ {ω | t ≤ min (runMax f n ω) K} * _ =
            μ {ω | t ≤ runMax f n ω} * _
      rw [h_ZK_set t ht.1, ite_eq_left ht.2]
    rw [h_left, h_zero_right, add_zero]
  rw [h_split]
  -- Now apply layer_integrand_bound pointwise.
  apply mul_le_mul_right _ (ENNReal.ofReal p)
  apply setLIntegral_mono_ae'
  · exact measurableSet_Ioc
  refine Filter.Eventually.of_forall (fun t ht ↦ ?_)
  exact layer_integrand_bound hsub hnonneg n ht.1

/-- Truncated holder_step: master bound for `A_K = ∫⁻ (min fstar K)^p`. -/
private lemma holder_step_truncated
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    (∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ)
      ≤ ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ) ^ ((p - 1) / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  -- Step 1: bound A_K via A_K_le_layer_integral.
  have hA := A_K_le_layer_integral hsub hnonneg hp n K hK
  -- Step 2: rewrite the inner Bochner integral as a setLIntegral of ofReal.
  have h_inner_rewrite : ∀ t,
      ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ)
        = ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ := fun _ ↦
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsub.integrable n).restrict
      (ae_of_all _ (hnonneg n))
  simp_rw [h_inner_rewrite] at hA
  -- Step 3: apply truncated Fubini swap.
  rw [fubini_swap_truncated hsub hnonneg hp n K hK] at hA
  -- Step 4: factor `ofReal((Z_K)^(p-1)/(p-1))` into `ofReal((Z_K)^(p-1)) * ofReal(1/(p-1))`.
  have h_factor : ∀ ω,
      ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1) / (p - 1))
        = ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) *
            ENNReal.ofReal (1 / (p - 1)) := by
    intro ω
    have hZK_nn : 0 ≤ min (runMax f n ω) K := le_min (runMax_nonneg hnonneg n ω) hK.le
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg hZK_nn _),
        show (p - 1)⁻¹ = 1 / (p - 1) by rw [one_div]]
  simp_rw [h_factor] at hA
  -- Step 5: pull constant ofReal(1/(p-1)) outside.
  have hsubM : Measurable (f n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl
  have hZKmeas : Measurable (fun ω ↦ min (runMax f n ω) K) :=
    (runMax_measurable hsub n).min measurable_const
  have h_mul_const :
      ∫⁻ ω, ENNReal.ofReal (f n ω) *
        (ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) *
          ENNReal.ofReal (1 / (p - 1))) ∂μ
      = ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) ∂μ := by
    rw [← lintegral_const_mul]
    · congr 1
      funext ω
      ring
    · exact ((ENNReal.measurable_ofReal.comp hsubM).mul
        (ENNReal.measurable_ofReal.comp (hZKmeas.pow_const (p - 1))))
  rw [h_mul_const] at hA
  -- Step 6: combine ofReal(p) * ofReal(1/(p-1)) = ofReal(p/(p-1)).
  have h_const_combine :
      ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) = ENNReal.ofReal (p / (p - 1)) := by
    rw [← ENNReal.ofReal_mul hp_pos.le]
    congr 1
    field_simp
  rw [show ENNReal.ofReal p * (ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) ∂μ)
      = ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) ∂μ from by ring,
      h_const_combine] at hA
  -- Step 7: apply Hölder to bound the inner integral.
  refine hA.trans ?_
  rw [mul_assoc]
  gcongr
  -- Hölder: ∫⁻ ofReal(f n) * ofReal(Z_K^(p-1))
  --   ≤ (∫⁻ ofReal(f n^p))^(1/p) * (∫⁻ ofReal(Z_K^p))^((p-1)/p)
  set q := p / (p - 1) with hq_def
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq_pos : 0 < q := by
    simp only [hq_def]
    positivity
  have hpm1_q_eq_p : (p - 1) * q = p := by
    simp only [hq_def]
    field_simp
  have hf_meas : AEMeasurable (fun ω ↦ ENNReal.ofReal (f n ω)) μ :=
    (ENNReal.measurable_ofReal.comp hsubM).aemeasurable
  have hg_meas : AEMeasurable
      (fun ω ↦ ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1))) μ :=
    (ENNReal.measurable_ofReal.comp (hZKmeas.pow_const (p - 1))).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf_meas hg_meas
  have h_f_pow : ∀ ω, (ENNReal.ofReal (f n ω)) ^ p = ENNReal.ofReal ((f n ω) ^ p) :=
    fun ω ↦ ENNReal.ofReal_rpow_of_nonneg (hnonneg n ω) hp_pos.le
  have h_g_pow : ∀ ω,
      (ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1))) ^ q
        = ENNReal.ofReal ((min (runMax f n ω) K) ^ p) := by
    intro ω
    have hZK_nn : 0 ≤ min (runMax f n ω) K := le_min (runMax_nonneg hnonneg n ω) hK.le
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hZK_nn _) hq_pos.le,
        ← Real.rpow_mul hZK_nn (p - 1) q, hpm1_q_eq_p]
  simp_rw [h_f_pow, h_g_pow] at key
  have h_one_div_q : (1 / q : ℝ) = (p - 1) / p := by
    simp only [hq_def, one_div, inv_div]
  rw [h_one_div_q] at key
  have hlhs : ∫⁻ a : Ω, ((fun ω ↦ ENNReal.ofReal (f n ω)) *
              fun ω ↦ ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1))) a ∂μ
            = ∫⁻ ω, ENNReal.ofReal (f n ω) *
                    ENNReal.ofReal ((min (runMax f n ω) K) ^ (p - 1)) ∂μ := by rfl
  rw [hlhs] at key
  exact key

/-- Stage 2 (Hölder + algebra): combining Fubini's output with Hölder
    yields the master bound on `∫⁻ fstar^p`. -/
private lemma holder_step
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ)
      ≤ ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ) ^ ((p - 1) / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hpm1_inv_pos : 0 < 1 / (p - 1) := by positivity
  -- Step 1: bound A := ∫⁻ fstar^p via A_le_layer_integral.
  have hA := A_le_layer_integral hsub hnonneg hp n
  -- Step 2: rewrite the inner Bochner setIntegral as a setLIntegral.
  have h_inner_rewrite : ∀ t,
      ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ)
        = ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ := fun _ ↦
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsub.integrable n).restrict
      (ae_of_all _ (hnonneg n))
  simp_rw [h_inner_rewrite] at hA
  -- Step 3: apply Fubini swap.
  rw [fubini_swap hsub hnonneg hp n] at hA
  -- Step 4: factor `ofReal(fstar^(p-1)/(p-1))` as `ofReal(fstar^(p-1)) * ofReal(1/(p-1))`.
  have h_factor : ∀ ω,
      ENNReal.ofReal ((runMax f n ω) ^ (p - 1) / (p - 1))
        = ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) * ENNReal.ofReal (1 / (p - 1)) := by
    intro ω
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg (runMax_nonneg hnonneg n ω) _),
        show (p - 1)⁻¹ = 1 / (p - 1) by rw [one_div]]
  simp_rw [h_factor] at hA
  -- Step 5: pull constant ofReal(1/(p-1)) outside the inner integral.
  have h_mul_const :
      ∫⁻ ω, ENNReal.ofReal (f n ω) *
        (ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) * ENNReal.ofReal (1 / (p - 1))) ∂μ
      = ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) ∂μ := by
    rw [← lintegral_const_mul]
    · congr 1
      funext ω
      ring
    · exact ((ENNReal.measurable_ofReal.comp
          (((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl)).mul
        (ENNReal.measurable_ofReal.comp
          ((runMax_measurable hsub n).pow_const (p - 1))))
  rw [h_mul_const] at hA
  -- Step 6: combine ofReal(p) * ofReal(1/(p-1)) = ofReal(p/(p-1)).
  have h_const_combine :
      ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) = ENNReal.ofReal (p / (p - 1)) := by
    rw [← ENNReal.ofReal_mul hp_pos.le]
    congr 1
    field_simp
  rw [show ENNReal.ofReal p * (ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) ∂μ)
      = ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((runMax f n ω) ^ (p - 1)) ∂μ from by ring,
      h_const_combine] at hA
  -- Step 7: apply holder_apply to bound the post-Fubini integral.
  refine hA.trans ?_
  rw [mul_assoc]
  gcongr
  exact holder_apply hsub hnonneg hp n

/-- Conversion lemma: for a non-negative `f : Ω → ℝ` and `1 < p`,
    `eLpNorm f (ofReal p) μ = (∫⁻ ω, ofReal(f ω ^ p) ∂μ)^(1/p)`. -/
private lemma eLpNorm_eq_lintegral_ofReal_pow
    {f : Ω → ℝ} (hf_meas : AEStronglyMeasurable f μ) (hf_nn : ∀ ω, 0 ≤ f ω) {p : ℝ} (hp : 1 < p) :
    eLpNorm f (ENNReal.ofReal p) μ
      = (∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) ^ (1 / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_ne_zero : (ENNReal.ofReal p) ≠ 0 := by
    simp [hp_pos]
  have hp_ne_top : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top hf_meas]
  rw [ENNReal.toReal_ofReal hp_pos.le]
  congr 1
  apply lintegral_congr_ae
  filter_upwards with ω
  have : ‖f ω‖ₑ = ENNReal.ofReal (f ω) := by
    rw [Real.enorm_eq_ofReal (hf_nn ω)]
  rw [this, ENNReal.ofReal_rpow_of_nonneg (hf_nn ω) hp_pos.le]

/-- Auxiliary finiteness lemma: if `∫⁻ (f n)^p ∂μ < ∞` for a non-negative submartingale
`f`, then `∫⁻ (max_{k ≤ n} f_k)^p ∂μ < ∞` as well. Derived from the truncated Hölder
bound by taking the monotone supremum over the truncation level. -/
private lemma runMax_pow_lintegral_lt_top
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω) (hp : 1 < p) (n : ℕ)
    (hB_lt_top : ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ < ⊤) :
    ∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ < ⊤ := by
  set A : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ with hA_def
  set B : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ
  set C : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hC_def
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hp_inv_pos : 0 < 1 / p := by positivity
  have hpm1_p_pos : 0 < (p - 1) / p := div_pos hpm1_pos hp_pos
  have hp_ne_zero : p ≠ 0 := hp_pos.ne'
  have h_sum_inv : (1 : ℝ) / p + (p - 1) / p = 1 := by
    rw [← add_div, show (1 : ℝ) + (p - 1) = p by ring, div_self hp_ne_zero]
  have h_prod_p : (1 : ℝ) / p * p = 1 := by field_simp
  have hC_lt_top : C < ⊤ := by
    rw [hC_def]
    exact ENNReal.ofReal_lt_top
  have hRHS_lt_top : C * B ^ (1 / p) < ⊤ :=
    ENNReal.mul_lt_top hC_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hp_inv_pos.le hB_lt_top.ne)
  have hRHS_p_lt_top : (C * B ^ (1 / p)) ^ p < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hp_pos.le hRHS_lt_top.ne
  -- For each K > 0: ∫ (min M* K)^p ≤ (C · B^{1/p})^p, finite and independent of K.
  have h_AK_bounded : ∀ (K : ℝ), 0 < K →
      (∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ)
        ≤ (C * B ^ (1 / p)) ^ p := by
    intro K hK
    have hAK_bound := holder_step_truncated hsub hnonneg hp n K hK
    set A_K : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ
        with hAK_def
    have hA_K_lt_top : A_K < ⊤ := by
      rw [hAK_def]
      calc ∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ
          ≤ ∫⁻ _ : Ω, ENNReal.ofReal (K ^ p) ∂μ :=
            lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal
              (Real.rpow_le_rpow (le_min (runMax_nonneg hnonneg n ω) hK.le)
                (min_le_right _ _) hp_pos.le)
        _ = ENNReal.ofReal (K ^ p) * μ Set.univ := lintegral_const _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)
    have h_inv_bound : A_K ^ (1 / p) ≤ C * B ^ (1 / p) := by
      by_cases hA_K_zero : A_K = 0
      · rw [hA_K_zero, ENNReal.zero_rpow_of_pos hp_inv_pos]
        exact bot_le
      have hAKpm1_ne_zero : A_K ^ ((p - 1) / p) ≠ 0 :=
        fun h ↦ hA_K_zero (ENNReal.rpow_eq_zero_iff_of_pos hpm1_p_pos |>.mp h)
      have hAKpm1_ne_top : A_K ^ ((p - 1) / p) ≠ ⊤ := fun h ↦
        hA_K_lt_top.ne ((ENNReal.rpow_eq_top_iff_of_pos hpm1_p_pos).mp h)
      have h_split : A_K ^ (1 / p) = A_K / A_K ^ ((p - 1) / p) := by
        rw [eq_div_iff hAKpm1_ne_zero hAKpm1_ne_top, mul_comm,
            ← ENNReal.rpow_add_of_nonneg (1/p) ((p-1)/p) hp_inv_pos.le hpm1_p_pos.le,
            h_sum_inv, ENNReal.rpow_one]
      rw [h_split, ENNReal.div_le_iff hAKpm1_ne_zero hAKpm1_ne_top]
      exact hAK_bound
    calc A_K = A_K ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ = (A_K ^ (1 / p)) ^ p := by rw [← ENNReal.rpow_mul, h_prod_p]
      _ ≤ (C * B ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow h_inv_bound hp_pos.le
  -- A = ⨆_K A_K (monotone convergence; min(M*, K+1) ↑ M* as K → ∞).
  have h_iSup : (⨆ K : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) ((K : ℝ) + 1)) ^ p) ∂μ) = A := by
    rw [hA_def, ← lintegral_iSup]
    · refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω ↦ le_antisymm ?_ ?_)
      · refine iSup_le fun K ↦ ENNReal.ofReal_le_ofReal ?_
        exact Real.rpow_le_rpow (le_min (runMax_nonneg hnonneg n ω) (by positivity))
          (min_le_left _ _) hp_pos.le
      · obtain ⟨K₀, hK₀⟩ := exists_nat_gt (runMax f n ω)
        refine le_iSup_of_le K₀ (ENNReal.ofReal_le_ofReal ?_)
        refine Real.rpow_le_rpow (runMax_nonneg hnonneg n ω) ?_ hp_pos.le
        exact le_min le_rfl (by linarith)
    · intro K
      exact (((runMax_measurable hsub n).min measurable_const).pow_const p).ennreal_ofReal
    · intro a b hab ω
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
        (le_min (runMax_nonneg hnonneg n ω) (by positivity)) ?_ hp_pos.le)
      refine min_le_min le_rfl ?_
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
  -- A ≤ (C · B^{1/p})^p < ⊤.
  have h_A_le : A ≤ (C * B ^ (1 / p)) ^ p :=
    h_iSup ▸ iSup_le fun K ↦ h_AK_bounded ((K : ℝ) + 1) (by positivity)
  exact lt_of_le_of_lt h_A_le hRHS_p_lt_top

/-- Doob's L^p maximal inequality for discrete-time non-negative submartingales.

For a non-negative submartingale `f : ℕ → Ω → ℝ` and `1 < p`, the L^p norm
of the running maximum `f*_n(ω) = max_{k ≤ n} f_k(ω)` is bounded by
`(p / (p - 1))` times the L^p norm of `f_n`:

  `‖f*_n‖_{L^p} ≤ (p / (p - 1)) · ‖f_n‖_{L^p}`.

This is the strong-type companion to `MeasureTheory.maximal_ineq`. The proof
combines a layer-cake decomposition, the weak-type maximal inequality, Fubini,
Hölder's inequality, and a truncation argument to handle the case where the
left-hand side could a priori be infinite. -/
theorem maximal_ineq_Lp
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ f k ω)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) *
          eLpNorm (f n) (ENNReal.ofReal p) μ := by
  -- `Finset.sup'` is definitionally `runMax f n`.
  change eLpNorm (runMax f n) (ENNReal.ofReal p) μ ≤ _
  rw [eLpNorm_eq_lintegral_ofReal_pow (runMax_measurable hsub n).aestronglyMeasurable
        (runMax_nonneg hnonneg n) hp,
      eLpNorm_eq_lintegral_ofReal_pow (hsub.integrable n).aestronglyMeasurable (hnonneg n) hp]
  set A : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ
  set B : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ
  set C : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hC_def
  have hbound : A ≤ C * B ^ (1 / p) * A ^ ((p - 1) / p) := holder_step hsub hnonneg hp n
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_inv_pos : 0 < 1 / p := by positivity
  have hpm1_p_pos : 0 < (p - 1) / p := div_pos (by linarith) hp_pos
  -- Degenerate cases first.
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos hp_inv_pos]
    exact bot_le
  by_cases hAtop : A = ⊤
  · by_cases hBtop : B = ⊤
    · -- Both sides `⊤` since `C ≠ 0`.
      have hC_ne_zero : C ≠ 0 := by
        rw [hC_def]
        exact (ENNReal.ofReal_pos.mpr (div_pos hp_pos (by linarith))).ne'
      rw [hAtop, hBtop, ENNReal.top_rpow_of_pos hp_inv_pos, ENNReal.mul_top hC_ne_zero]
    · -- `A = ⊤` while `B < ⊤` contradicts the finiteness lemma.
      exact absurd hAtop (runMax_pow_lintegral_lt_top hsub hnonneg hp n
        (lt_of_le_of_ne le_top hBtop)).ne
  -- Main case `0 < A < ⊤`: divide `hbound` by `A^{(p-1)/p}`.
  have hApm1_ne_zero : A ^ ((p - 1) / p) ≠ 0 :=
    fun h ↦ hA0 (ENNReal.rpow_eq_zero_iff_of_pos hpm1_p_pos |>.mp h)
  have hApm1_ne_top : A ^ ((p - 1) / p) ≠ ⊤ :=
    fun h ↦ hAtop ((ENNReal.rpow_eq_top_iff_of_pos hpm1_p_pos).mp h)
  have h_sum : (1 : ℝ) / p + (p - 1) / p = 1 := by
    rw [← add_div, show (1 : ℝ) + (p - 1) = p by ring, div_self hp_pos.ne']
  have h_split : A ^ (1 / p) = A / A ^ ((p - 1) / p) := by
    rw [eq_div_iff hApm1_ne_zero hApm1_ne_top, mul_comm,
        ← ENNReal.rpow_add_of_nonneg (1/p) ((p-1)/p) hp_inv_pos.le hpm1_p_pos.le,
        h_sum, ENNReal.rpow_one]
  rw [h_split, ENNReal.div_le_iff hApm1_ne_zero hApm1_ne_top]
  exact hbound

/-- The norm process of a Banach-valued martingale is a non-negative submartingale.
Internal lemma used to derive the Banach version of Doob's L^p inequality from the
real-valued case via Jensen (`MeasureTheory.norm_condExp_le`). -/
private lemma martingale_norm_submartingale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → E} (hf : Martingale f 𝒢 μ) :
    Submartingale (fun n ω ↦ ‖f n ω‖) 𝒢 μ := by
  refine ⟨fun n ↦ continuous_norm.comp_stronglyMeasurable (hf.stronglyAdapted n),
          fun i j hij ↦ ?_, fun n ↦ (hf.integrable n).norm⟩
  have hcondExp : f i =ᵐ[μ] μ[f j | (𝒢 i : MeasurableSpace Ω)] := (hf.condExp_ae_eq hij).symm
  filter_upwards [hcondExp,
    norm_condExp_le (f := f j) (m := (𝒢 i : MeasurableSpace Ω)) (μ := μ)]
    with ω hω hjensen
  calc ‖f i ω‖ = ‖(μ[f j | (𝒢 i : MeasurableSpace Ω)]) ω‖ := by rw [hω]
    _ ≤ _ := hjensen

/-- Doob's L^p maximal inequality, Banach-valued martingale form.

For a Banach-valued martingale `f : ℕ → Ω → E` and `1 < p`,
`‖max_{k ≤ n} ‖f_k‖‖_{L^p} ≤ (p / (p - 1)) · ‖f_n‖_{L^p}`.

Derived from `MeasureTheory.maximal_ineq_Lp` by applying it to the non-negative
real-valued submartingale `‖f‖`. -/
theorem Martingale.eLpNorm_norm_runMax_le
    [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → E} {p : ℝ}
    (hf : Martingale f 𝒢 μ) (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ ‖f k ω‖)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) * eLpNorm (f n) (ENNReal.ofReal p) μ := by
  have hsub := martingale_norm_submartingale hf
  have hbound := maximal_ineq_Lp hsub (fun _ _ ↦ norm_nonneg _) hp n
  rwa [eLpNorm_norm _ (hf.integrable n).aestronglyMeasurable] at hbound

end MeasureTheory

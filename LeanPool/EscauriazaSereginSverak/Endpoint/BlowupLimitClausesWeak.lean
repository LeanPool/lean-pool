/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Weak `L²` limits from an exhausting family of subsets

An abstract passage used for clause (c) of `prop:blowup-limit`: a sequence
bounded in `L²(Q)` that converges weakly in `L²(S n)` for an increasing family
of subsets exhausting `Q` converges weakly in `L²(Q)`, and the norm bound
passes to the limit. The tails of a fixed square-integrable test on `Q \ S n`
tend to zero, which controls the remaining part of every pairing.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace ESS

variable {α : Type*} [MeasurableSpace α]

/-- The Cauchy–Schwarz bound for the pairing of two square-integrable real
functions. -/
theorem blowupLimitClauses_abs_integral_mul_le {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hH := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (μ := μ) (f := f) (g := g) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
    (r := (1 : ℝ≥0∞)) (b := fun a b : ℝ => a * b) (c := (1 : NNReal))
    (by exact continuous_mul) hf.aestronglyMeasurable hg.aestronglyMeasurable (by
      filter_upwards [] with x
      simp only [one_mul]
      simp [nnnorm_mul])
  have hH' : eLpNorm (fun x => f x * g x) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    simpa using hH
  rw [← Real.norm_eq_abs, ← ENNReal.toReal_mul]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) ?_
  refine le_trans (le_of_eq ?_) hH'
  rw [eLpNorm_one_eq_lintegral_enorm]
  simp_rw [ofReal_norm]
  exact hf.aestronglyMeasurable.mul hg.aestronglyMeasurable

/-- The square of the `L²` norm is the integral of the square. -/
theorem blowupLimitClauses_integral_mul_self_eq {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) :
    ∫ x, f x * f x ∂μ = (eLpNorm f 2 μ).toReal ^ 2 := by
  have hinner : inner ℝ (hf.toLp f) (hf.toLp f) = ∫ x, f x * f x ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, real_inner_eq_re_inner, RCLike.re_to_real, real_inner_comm]
    rfl
  rw [← hinner, real_inner_self_eq_norm_sq, Lp.norm_toLp]

/-- The `L²` norm on a set of a square-integrable function is controlled by
the `L²` bounds on an increasing exhausting family of subsets. -/
theorem blowupLimitClauses_eLpNorm_le_of_exhaustion {μ : Measure α} {Q : Set α}
    {S : ℕ → Set α} (hSmono : Monotone S) (hSQ : ⋃ n, S n = Q)
    {G : α → ℝ} {M : ℝ} (hGm : AEStronglyMeasurable G (μ.restrict Q))
    (hG : ∀ n, eLpNorm G 2 (μ.restrict (S n)) ≤ ENNReal.ofReal M) :
    eLpNorm G 2 (μ.restrict Q) ≤ ENNReal.ofReal M := by
  have htwo : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have htwo' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hSQsub : ∀ n, S n ⊆ Q := fun n => hSQ ▸ subset_iUnion S n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal htwo htwo' hGm]
  rw [← hSQ, setLIntegral_iUnion_of_directed _ hSmono.directed_le]
  simp only [ENNReal.toReal_ofNat]
  have hbound : ∀ n, ∫⁻ x in S n, ‖G x‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal M ^ (2 : ℝ) := by
    intro n
    have h := hG n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal htwo htwo'
      (hGm.mono_measure (Measure.restrict_mono (hSQsub n) le_rfl))] at h
    simp only [ENNReal.toReal_ofNat] at h
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2
    exact h2
  have hsup : (⨆ n, ∫⁻ x in S n, ‖G x‖ₑ ^ (2 : ℝ) ∂μ) ≤ ENNReal.ofReal M ^ (2 : ℝ) :=
    iSup_le hbound
  have h3 := ENNReal.rpow_le_rpow hsup (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at h3
  exact h3

/-- The tails of a square-integrable test on the complements of an increasing
exhausting family of measurable subsets tend to zero. -/
theorem blowupLimitClauses_tail_tendsto_zero {μ : Measure α} {Q : Set α}
    {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n)) (hSmono : Monotone S)
    (hSQ : ⋃ n, S n = Q) {w : α → ℝ} (hw : MemLp w 2 (μ.restrict Q)) :
    Tendsto (fun n => (eLpNorm ((S n)ᶜ.indicator w) 2 (μ.restrict Q)).toReal)
      atTop (𝓝 0) := by
  set ν : Measure α := (μ.restrict Q).withDensity (fun x => ‖w x‖ₑ ^ (2 : ℝ))
  have htwo : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have htwo' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hfin : ν univ ≠ ⊤ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have h := hw.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal htwo htwo' hw.aestronglyMeasurable] at h
    simp only [ENNReal.toReal_ofNat] at h
    have h' := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 h
    exact h'.ne
  have hν : ∀ n, eLpNorm ((S n)ᶜ.indicator w) 2 (μ.restrict Q) =
      ν ((S n)ᶜ) ^ (1 / 2 : ℝ) := by
    intro n
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hS n).compl,
      eLpNorm_eq_lintegral_rpow_enorm_toReal htwo htwo'
        (hw.aestronglyMeasurable.mono_measure Measure.restrict_le_self),
      withDensity_apply _ (hS n).compl]
    simp only [ENNReal.toReal_ofNat]
  have hlim : Tendsto (fun n => ν ((S n)ᶜ)) atTop (𝓝 (ν (⋂ n, (S n)ᶜ))) :=
    tendsto_measure_iInter_atTop (fun n => (hS n).compl.nullMeasurableSet)
      (fun m n hmn => compl_subset_compl.mpr (hSmono hmn))
      ⟨0, ne_top_of_le_ne_top hfin (measure_mono (subset_univ _))⟩
  have hzero : ν (⋂ n, (S n)ᶜ) = 0 := by
    rw [← compl_iUnion, hSQ]
    have hQm : MeasurableSet Q := by
      rw [← hSQ]
      exact MeasurableSet.iUnion hS
    rw [withDensity_apply _ hQm.compl, Measure.restrict_restrict hQm.compl,
      compl_inter_self, Measure.restrict_empty, lintegral_zero_measure]
  rw [hzero] at hlim
  have hpow : Tendsto (fun n => ν ((S n)ᶜ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h.comp hlim
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hpow
  simp only [ENNReal.toReal_zero] at hreal
  refine hreal.congr fun n => ?_
  simp only [Function.comp_apply, hν n]

/-- Weak `L²` convergence from an increasing exhausting family of subsets: a
sequence bounded in `L²(Q)` that converges weakly in `L²(S n)` for every `n`
to a limit that is square integrable on each `S n` converges weakly in
`L²(Q)`, and the limit keeps the bound (`prop:blowup-limit`, clause (c)). -/
theorem blowupLimitClauses_weak_L2_of_exhaustion
    {μ : Measure α} {Q : Set α} {S : ℕ → Set α}
    (hS : ∀ n, MeasurableSet (S n)) (hSmono : Monotone S) (hSQ : ⋃ n, S n = Q)
    {g : ℕ → α → ℝ} {G : α → ℝ} {M : ℝ}
    (hg : ∀ᶠ k in atTop, MemLp (g k) 2 (μ.restrict Q) ∧
      (eLpNorm (g k) 2 (μ.restrict Q)).toReal ≤ M)
    (hGm : AEStronglyMeasurable G (μ.restrict Q))
    (hG : ∀ n, MemLp G 2 (μ.restrict (S n)))
    (hweak : ∀ n (w : α → ℝ), MemLp w 2 (μ.restrict (S n)) →
      Tendsto (fun k => ∫ x in S n, g k x * w x ∂μ) atTop
        (𝓝 (∫ x in S n, G x * w x ∂μ))) :
    MemLp G 2 (μ.restrict Q) ∧ (eLpNorm G 2 (μ.restrict Q)).toReal ≤ M ∧
      ∀ w : α → ℝ, MemLp w 2 (μ.restrict Q) →
        Tendsto (fun k => ∫ x in Q, g k x * w x ∂μ) atTop
          (𝓝 (∫ x in Q, G x * w x ∂μ)) := by
  have hSQsub : ∀ n, S n ⊆ Q := fun n => hSQ ▸ subset_iUnion S n
  have hQm : MeasurableSet Q := by
    rw [← hSQ]
    exact MeasurableSet.iUnion hS
  obtain ⟨k₀, hk₀⟩ := hg.exists
  have hM : 0 ≤ M := ENNReal.toReal_nonneg.trans hk₀.2
  -- the bound on each exhausting set
  have hGn : ∀ n, (eLpNorm G 2 (μ.restrict (S n))).toReal ≤ M := by
    intro n
    set N : ℝ := (eLpNorm G 2 (μ.restrict (S n))).toReal with hNdef
    have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
    have hself := blowupLimitClauses_integral_mul_self_eq (hG n)
    have hlim := hweak n G (hG n)
    have hle : ∫ x in S n, G x * G x ∂μ ≤ M * N := by
      apply le_of_tendsto hlim
      filter_upwards [hg] with k hk
      have hgk : MemLp (g k) 2 (μ.restrict (S n)) :=
        hk.1.mono_measure (Measure.restrict_mono (hSQsub n) le_rfl)
      have hmono : (eLpNorm (g k) 2 (μ.restrict (S n))).toReal ≤ M :=
        (ENNReal.toReal_mono hk.1.eLpNorm_ne_top
          (eLpNorm_mono_measure _ (Measure.restrict_mono (hSQsub n) le_rfl))).trans hk.2
      calc
        ∫ x in S n, g k x * G x ∂μ ≤ |∫ x in S n, g k x * G x ∂μ| := le_abs_self _
        _ ≤ (eLpNorm (g k) 2 (μ.restrict (S n))).toReal * N :=
          blowupLimitClauses_abs_integral_mul_le hgk (hG n)
        _ ≤ M * N := mul_le_mul_of_nonneg_right hmono hN0
    rw [hself] at hle
    rcases hN0.eq_or_lt with hN | hN
    · rw [← hN]
      exact hM
    · nlinarith only [hle, hN]
  have hGQ : eLpNorm G 2 (μ.restrict Q) ≤ ENNReal.ofReal M := by
    apply blowupLimitClauses_eLpNorm_le_of_exhaustion hSmono hSQ hGm
    intro n
    rw [← ENNReal.ofReal_toReal (hG n).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (hGn n)
  have hGmem : MemLp G 2 (μ.restrict Q) := memLp_iff.2 (hGQ.trans_lt ENNReal.ofReal_lt_top)
  have hGQreal : (eLpNorm G 2 (μ.restrict Q)).toReal ≤ M := by
    rw [← ENNReal.toReal_ofReal hM]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hGQ
  refine ⟨hGmem, hGQreal, fun w hw => ?_⟩
  -- the pairing splits into the exhausting set and its complement
  have hsplit : ∀ (f : α → ℝ), MemLp f 2 (μ.restrict Q) → ∀ n,
      ∫ x in Q, f x * w x ∂μ =
        (∫ x in S n, f x * w x ∂μ) +
          ∫ x in Q, f x * (S n)ᶜ.indicator w x ∂μ := by
    intro f hf n
    have hint : Integrable (fun x => f x * w x) (μ.restrict Q) := hf.integrable_mul hw
    have hindic : ∀ x, f x * w x =
        (S n).indicator (fun y => f y * w y) x + f x * (S n)ᶜ.indicator w x := by
      intro x
      by_cases hx : x ∈ S n
      · simp [hx]
      · simp [hx]
    have hint2 : Integrable (fun x => f x * (S n)ᶜ.indicator w x) (μ.restrict Q) :=
      hf.integrable_mul (hw.indicator (hS n).compl)
    have hint1 : Integrable ((S n).indicator (fun y => f y * w y)) (μ.restrict Q) :=
      hint.indicator (hS n)
    calc
      ∫ x in Q, f x * w x ∂μ =
          ∫ x in Q, ((S n).indicator (fun y => f y * w y) x +
            f x * (S n)ᶜ.indicator w x) ∂μ :=
        integral_congr_ae (Eventually.of_forall hindic)
      _ = (∫ x in Q, (S n).indicator (fun y => f y * w y) x ∂μ) +
            ∫ x in Q, f x * (S n)ᶜ.indicator w x ∂μ := integral_add hint1 hint2
      _ = (∫ x in S n, f x * w x ∂μ) + ∫ x in Q, f x * (S n)ᶜ.indicator w x ∂μ := by
        rw [integral_indicator (hS n), Measure.restrict_restrict (hS n),
          Set.inter_eq_left.mpr (hSQsub n)]
  have htail := blowupLimitClauses_tail_tendsto_zero hS hSmono hSQ hw
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (4 * (M + 1)) := by positivity
  obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.1 htail) _ hε'
  have hτ : (eLpNorm ((S n)ᶜ.indicator w) 2 (μ.restrict Q)).toReal <
      ε / (4 * (M + 1)) := by
    have h := hn n le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h
    exact h
  have hwn : MemLp w 2 (μ.restrict (S n)) :=
    hw.mono_measure (Measure.restrict_mono (hSQsub n) le_rfl)
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 (hweak n w hwn)) (ε / 2) (by positivity)
  obtain ⟨K', hK'⟩ := eventually_atTop.1 hg
  refine ⟨max K K', fun k hk => ?_⟩
  have hkK : K ≤ k := (le_max_left _ _).trans hk
  have hkK' : K' ≤ k := (le_max_right _ _).trans hk
  obtain ⟨hgk, hgkM⟩ := hK' k hkK'
  have hmain := hK k hkK
  rw [Real.dist_eq] at hmain ⊢
  have htailw : MemLp ((S n)ᶜ.indicator w) 2 (μ.restrict Q) := hw.indicator (hS n).compl
  have h1 := blowupLimitClauses_abs_integral_mul_le hgk htailw
  have h2 := blowupLimitClauses_abs_integral_mul_le hGmem htailw
  rw [hsplit (g k) hgk n, hsplit G hGmem n]
  set τ : ℝ := (eLpNorm ((S n)ᶜ.indicator w) 2 (μ.restrict Q)).toReal
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  have hA : |∫ x in Q, g k x * (S n)ᶜ.indicator w x ∂μ| ≤ M * τ :=
    h1.trans (mul_le_mul_of_nonneg_right hgkM hτ0)
  have hB : |∫ x in Q, G x * (S n)ᶜ.indicator w x ∂μ| ≤ M * τ :=
    h2.trans (mul_le_mul_of_nonneg_right hGQreal hτ0)
  have hMτ : M * τ ≤ ε / 4 := by
    have hlt : τ * (4 * (M + 1)) < ε := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (M + 1))).1 hτ
      linarith only [this]
    nlinarith only [hlt, hM, hτ0]
  calc
    |(∫ x in S n, g k x * w x ∂μ) + (∫ x in Q, g k x * (S n)ᶜ.indicator w x ∂μ) -
        ((∫ x in S n, G x * w x ∂μ) + ∫ x in Q, G x * (S n)ᶜ.indicator w x ∂μ)| ≤
        |(∫ x in S n, g k x * w x ∂μ) - ∫ x in S n, G x * w x ∂μ| +
          |∫ x in Q, g k x * (S n)ᶜ.indicator w x ∂μ| +
          |∫ x in Q, G x * (S n)ᶜ.indicator w x ∂μ| := by
      have := abs_add_three ((∫ x in S n, g k x * w x ∂μ) - ∫ x in S n, G x * w x ∂μ)
        (∫ x in Q, g k x * (S n)ᶜ.indicator w x ∂μ)
        (-∫ x in Q, G x * (S n)ᶜ.indicator w x ∂μ)
      rw [abs_neg] at this
      convert this using 2
      ring
    _ < ε / 2 + M * τ + M * τ := by linarith only [hmain, hA, hB]
    _ ≤ ε := by linarith only [hMτ]

end ESS

end

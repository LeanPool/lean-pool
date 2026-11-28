/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Dependence.HoeffdingCovariance

/-!
# The Marshall–Olkin common-shock model

Three independent exponential clocks `T₁, T₂, T₃` with rates `λ₁, λ₂, λ₃ > 0` drive two default
times. `T₁`, `T₂` are idiosyncratic shocks, and `T₃` is a common shock that kills both names.
Firm `j` defaults at `Xⱼ = min(Tⱼ, T₃)` (QRM Exercise Book Ex. 7.23; McNeil–Frey–Embrechts (2015)
Section 7.2.2; Marshall and Olkin 1967). In Lean the clocks are `T 0`, `T 1`, `T 2`, with rates
`rate 0`, `rate 1`, `rate 2`.

* **Joint survival** (`marshallOlkin_survival`): for `s, t ≥ 0`,
  `P(X₁ > s, X₂ > t) = exp(−λ₁ s − λ₂ t − λ₃ max(s, t))`.
* **Margins** (`hasLaw_marshallOlkin_fst`, `hasLaw_marshallOlkin_snd`): `Xⱼ ~ Exp(λⱼ + λ₃)`.
* **The survival copula** (`marshallOlkin_survival_eq_copula`): the joint survival function is
  the Marshall–Olkin copula `C(u₁, u₂) = min(u₁^{1−α₁} u₂, u₁ u₂^{1−α₂})`, with
  `αⱼ = λ₃ / (λⱼ + λ₃)`, evaluated at the marginal survival probabilities.
* **Dependence** (`marshallOlkin_survival_gt_mul`, `marshallOlkin_diagonal_pos`): the names
  survive together more often than independent names with the same margins would. With positive
  probability they default at the same instant, so the joint law has a singular component even
  though both margins are continuous.
* **Default covariance** (`covariance_indicator_marshallOlkin`): for horizons `s, t ≥ 0` the
  default indicators `𝟙{X₁ ≤ s}`, `𝟙{X₂ ≤ t}` have covariance
  `exp(−(λ₁ + λ₃)s − (λ₂ + λ₃)t) (exp(λ₃ min(s, t)) − 1)`, by the indicator covariance
  `covariance_indicator_one` of `Probability/Dependence/HoeffdingCovariance.lean`.
* **First to default** (`marshallOlkin_firstToDefault_survival`,
  `marshallOlkin_firstToDefault_spread_lt`): `min(X₁, X₂) = min(T₁, T₂, T₃)` survives to `t` with
  probability `exp(−(λ₁ + λ₂ + λ₃) t)`. So the first-to-default intensity is `λ₁ + λ₂ + λ₃`. That
  is strictly below the sum `(λ₁ + λ₃) + (λ₂ + λ₃)` of the single-name intensities whenever the
  common shock is active. For independent names `Models/Credit/FirstToDefault.lean`
  (`firstToDefault_spread_eq_sum_hazards`) shows the first-to-default spread equals the sum of
  the single-name hazards, and its docstring asserts that default correlation only lowers the
  spread below this sum. The common shock is a machine-checked instance of that assertion: it
  correlates the two defaults and lowers the basket intensity by exactly `λ₃`.

## Main definitions

* `marshallOlkinCopula`: the bivariate copula `C(u₁, u₂) = min(u₁^{1−α₁} u₂, u₁ u₂^{1−α₂})`
  with parameters `α₁`, `α₂`.

## Main results

For independent exponential clocks `T i` of positive rates `rate i`:

* `marshallOlkin_survival`: for `s, t ≥ 0`,
  `P(X₁ > s, X₂ > t) = exp(−λ₁ s − λ₂ t − λ₃ max(s, t))`.
* `hasLaw_marshallOlkin_fst`, `hasLaw_marshallOlkin_snd`: `X₁ ~ Exp(λ₁ + λ₃)` and
  `X₂ ~ Exp(λ₂ + λ₃)`.
* `marshallOlkin_survival_eq_copula`: for `s, t ≥ 0`, the joint survival probability equals
  `marshallOlkinCopula` (with `αⱼ = λ₃/(λⱼ + λ₃)`) at the two marginal survival probabilities.
* `marshallOlkin_survival_gt_mul`: for `s, t > 0`, the joint survival probability is strictly
  larger than the product of the marginal ones.
* `marshallOlkin_diagonal_pos`: `P(X₁ = X₂) > 0`.
* `covariance_indicator_marshallOlkin`: for `s, t ≥ 0`, `Cov(𝟙{X₁ ≤ s}, 𝟙{X₂ ≤ t})` is
  `exp(−(λ₁+λ₃)s − (λ₂+λ₃)t)·(exp(λ₃ min(s, t)) − 1)`.
* `marshallOlkin_firstToDefault_survival`: for `t ≥ 0`, `P(min(X₁, X₂) > t) = exp(−(λ₁+λ₂+λ₃)t)`.
* `marshallOlkin_firstToDefault_spread`, `marshallOlkin_single_name_spread_fst`,
  `marshallOlkin_single_name_spread_snd`: for `t > 0`, `−log P(·)/t` equals `λ₁+λ₂+λ₃` for the
  first-to-default time and `λ₁+λ₃`, `λ₂+λ₃` for the single names.
* `marshallOlkin_firstToDefault_spread_lt`: for `t > 0`, the first-to-default spread is strictly
  below the sum of the two single-name spreads.

## References

* [Marshall and Olkin (1967)][MarshallOlkin1967]
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 7.23

## Tags

Marshall–Olkin copula, common shock, joint default, default correlation, first-to-default,
exponential clocks, survival copula, MSC 91G40, MSC 62H05, JEL G33
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

/-- The exponential survival function: `Exp(r)` puts mass `exp(−r · max(t, 0))` on `(t, ∞)`. -/
lemma expMeasure_real_Ioi {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (expMeasure r).real (Ioi t) = Real.exp (-(r * max t 0)) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_expMeasure_eq hr]
  rcases le_total 0 t with ht | ht
  · rw [ite_eq_left ht, max_eq_left ht]
    ring
  · rcases ht.lt_or_eq with ht | rfl
    · rw [ite_eq_right (not_le.2 ht), max_eq_right ht.le]
      simp
    · simp

/-- An exponential clock outlasts any horizon with positive probability. -/
lemma expMeasure_Ioi_ne_zero {r : ℝ} (hr : 0 < r) (t : ℝ) : expMeasure r (Ioi t) ≠ 0 := by
  intro h
  have h' := expMeasure_real_Ioi hr t
  rw [measureReal_def, h, ENNReal.toReal_zero] at h'
  exact (Real.exp_pos _).ne h'

/-- An exponential clock rings before a positive horizon with positive probability. -/
lemma expMeasure_Iic_ne_zero {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    expMeasure r (Iic t) ≠ 0 := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr, ite_eq_left ht.le, ne_eq, ENNReal.ofReal_eq_zero, not_le,
    sub_pos]
  exact (Real.exp_lt_exp.2 (neg_lt_zero.2 (mul_pos hr ht))).trans_eq Real.exp_zero

/-- Two laws on `ℝ` with the same survival function coincide. -/
lemma ext_of_measureReal_Ioi {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ u, μ.real (Ioi u) = ν.real (Ioi u)) : μ = ν := by
  refine Measure.ext_of_Iic _ _ fun a ↦ ?_
  have h1 : μ.real (Iic a) = ν.real (Iic a) := by
    rw [← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi,
      probReal_compl_eq_one_sub measurableSet_Ioi, h]
  rwa [measureReal_def, measureReal_def,
    ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)] at h1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {T : Fin 3 → Ω → ℝ} {rate : Fin 3 → ℝ}

omit [IsProbabilityMeasure P] in
/-- Survival of all three clocks past their own thresholds: independence factorizes it. -/
lemma measureReal_iInter_Ioi_of_hasLaw_expMeasure (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) (c : Fin 3 → ℝ) :
    P.real (⋂ i, T i ⁻¹' Ioi (c i)) = ∏ i, Real.exp (-(rate i * max (c i) 0)) := by
  rw [measureReal_def, hind.meas_iInter fun i ↦ ⟨Ioi (c i), measurableSet_Ioi, rfl⟩,
    ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← measureReal_def, ← map_measureReal_apply_of_aemeasurable (hT i).aemeasurable
    measurableSet_Ioi, (hT i).map_eq]
  exact expMeasure_real_Ioi (hrate i) (c i)

omit [IsProbabilityMeasure P] in
/-- The survival function of a minimum of two of the independent clocks. -/
lemma measureReal_lt_min_of_hasLaw_expMeasure (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {i j : Fin 3}
    (hij : i ≠ j) (u : ℝ) :
    P.real {ω | u < min (T i ω) (T j ω)}
      = (expMeasure (rate i + rate j)).real (Ioi u) := by
  rw [expMeasure_real_Ioi (add_pos (hrate i) (hrate j)),
    show {ω | u < min (T i ω) (T j ω)} = T i ⁻¹' Ioi u ∩ T j ⁻¹' Ioi u by ext; simp,
    measureReal_def, (hind.indepFun hij).measure_inter_preimage_eq_mul _ _ measurableSet_Ioi
      measurableSet_Ioi, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
    ← map_measureReal_apply_of_aemeasurable (hT i).aemeasurable measurableSet_Ioi, (hT i).map_eq,
    ← map_measureReal_apply_of_aemeasurable (hT j).aemeasurable measurableSet_Ioi, (hT j).map_eq,
    expMeasure_real_Ioi (hrate i), expMeasure_real_Ioi (hrate j), ← Real.exp_add]
  congr 1
  ring

/-- A minimum of two independent exponential clocks is exponential at the summed rate. -/
lemma hasLaw_min_expMeasure (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {i j : Fin 3}
    (hij : i ≠ j) :
    HasLaw (fun ω ↦ min (T i ω) (T j ω)) (expMeasure (rate i + rate j)) P := by
  have hmeas : AEMeasurable (fun ω ↦ min (T i ω) (T j ω)) P :=
    (hT i).aemeasurable.min (hT j).aemeasurable
  have := isProbabilityMeasure_expMeasure (add_pos (hrate i) (hrate j))
  refine ⟨hmeas, ext_of_measureReal_Ioi fun u ↦ ?_⟩
  rw [map_measureReal_apply_of_aemeasurable hmeas measurableSet_Ioi]
  exact measureReal_lt_min_of_hasLaw_expMeasure hrate hT hind hij u

/-- **Margins of the Marshall–Olkin model**: `X₁ = min(T₁, T₃) ~ Exp(λ₁ + λ₃)`. -/
theorem hasLaw_marshallOlkin_fst (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) :
    HasLaw (fun ω ↦ min (T 0 ω) (T 2 ω)) (expMeasure (rate 0 + rate 2)) P :=
  hasLaw_min_expMeasure hrate hT hind (by decide)

/-- **Margins of the Marshall–Olkin model**: `X₂ = min(T₂, T₃) ~ Exp(λ₂ + λ₃)`. -/
theorem hasLaw_marshallOlkin_snd (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) :
    HasLaw (fun ω ↦ min (T 1 ω) (T 2 ω)) (expMeasure (rate 1 + rate 2)) P :=
  hasLaw_min_expMeasure hrate hT hind (by decide)

omit [IsProbabilityMeasure P] in
/-- **Joint survival of the Marshall–Olkin model** (QRM Exercise Book Ex. 7.23): for `s, t ≥ 0`,
`P(X₁ > s, X₂ > t) = exp(−λ₁ s − λ₂ t − λ₃ max(s, t))`. Both names survive exactly when the
idiosyncratic clocks pass their own horizons and the common shock passes the later one. -/
theorem marshallOlkin_survival (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    P.real {ω | s < min (T 0 ω) (T 2 ω) ∧ t < min (T 1 ω) (T 2 ω)}
      = Real.exp (-(rate 0 * s) - rate 1 * t - rate 2 * max s t) := by
  have hset : {ω | s < min (T 0 ω) (T 2 ω) ∧ t < min (T 1 ω) (T 2 ω)}
      = ⋂ i, T i ⁻¹' Ioi (![s, t, max s t] i) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_Ioi, lt_min_iff]
    constructor
    · rintro ⟨⟨h0, h2⟩, h1, h2'⟩ i
      fin_cases i
      exacts [h0, h1, max_lt h2 h2']
    · intro h
      have h2 : max s t < T 2 ω := h 2
      exact ⟨⟨h 0, (le_max_left s t).trans_lt h2⟩, h 1, (le_max_right s t).trans_lt h2⟩
  rw [hset, measureReal_iInter_Ioi_of_hasLaw_expMeasure hrate hT hind ![s, t, max s t],
    Fin.prod_univ_three, ← Real.exp_add, ← Real.exp_add]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [max_eq_left hs, max_eq_left ht, max_eq_left (le_max_of_le_left hs)]
  congr 1

/-- The bivariate **Marshall–Olkin copula** `C(u₁, u₂) = min(u₁^{1−α₁} u₂, u₁ u₂^{1−α₂})`. -/
noncomputable def marshallOlkinCopula (α₁ α₂ u₁ u₂ : ℝ) : ℝ :=
  min (u₁ ^ (1 - α₁) * u₂) (u₁ * u₂ ^ (1 - α₂))

omit [IsProbabilityMeasure P] in
/-- **The Marshall–Olkin survival copula** (QRM Exercise Book Ex. 7.23(a)): for `s, t ≥ 0` the
joint survival probability of `(X₁, X₂)` is the Marshall–Olkin copula with
`αⱼ = λ₃ / (λⱼ + λ₃)` evaluated at the marginal survival probabilities:
`P(X₁ > s, X₂ > t) = C(P(X₁ > s), P(X₂ > t))`. -/
theorem marshallOlkin_survival_eq_copula (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    P.real {ω | s < min (T 0 ω) (T 2 ω) ∧ t < min (T 1 ω) (T 2 ω)}
      = marshallOlkinCopula (rate 2 / (rate 0 + rate 2)) (rate 2 / (rate 1 + rate 2))
          (P.real {ω | s < min (T 0 ω) (T 2 ω)}) (P.real {ω | t < min (T 1 ω) (T 2 ω)}) := by
  have h02 : rate 0 + rate 2 ≠ 0 := (add_pos (hrate 0) (hrate 2)).ne'
  have h12 : rate 1 + rate 2 ≠ 0 := (add_pos (hrate 1) (hrate 2)).ne'
  rw [marshallOlkin_survival hrate hT hind hs ht,
    measureReal_lt_min_of_hasLaw_expMeasure hrate hT hind (i := 0) (j := 2) (by decide),
    measureReal_lt_min_of_hasLaw_expMeasure hrate hT hind (i := 1) (j := 2) (by decide),
    expMeasure_real_Ioi (add_pos (hrate 0) (hrate 2)),
    expMeasure_real_Ioi (add_pos (hrate 1) (hrate 2)), max_eq_left hs, max_eq_left ht,
    marshallOlkinCopula, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_monotone.map_min]
  congr 1
  have e1 : -((rate 0 + rate 2) * s) * (1 - rate 2 / (rate 0 + rate 2)) = -(rate 0 * s) := by
    field_simp
    ring
  have e2 : -((rate 1 + rate 2) * t) * (1 - rate 2 / (rate 1 + rate 2)) = -(rate 1 * t) := by
    field_simp
    ring
  rw [e1, e2]
  rcases le_total s t with hst | hst
  · rw [max_eq_right hst, min_eq_left (by nlinarith [hrate 2])]
    ring
  · rw [max_eq_left hst, min_eq_right (by nlinarith [hrate 2])]
    ring

omit [IsProbabilityMeasure P] in
/-- **Positive quadrant dependence**: for `s, t > 0` the two names survive together more often
than independent names with the same margins would,
`P(X₁ > s, X₂ > t) > P(X₁ > s) P(X₂ > t)`. The excess factor is `exp(λ₃ min(s, t))`. -/
theorem marshallOlkin_survival_gt_mul (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    P.real {ω | s < min (T 0 ω) (T 2 ω)} * P.real {ω | t < min (T 1 ω) (T 2 ω)}
      < P.real {ω | s < min (T 0 ω) (T 2 ω) ∧ t < min (T 1 ω) (T 2 ω)} := by
  rw [marshallOlkin_survival hrate hT hind hs.le ht.le,
    measureReal_lt_min_of_hasLaw_expMeasure hrate hT hind (i := 0) (j := 2) (by decide),
    measureReal_lt_min_of_hasLaw_expMeasure hrate hT hind (i := 1) (j := 2) (by decide),
    expMeasure_real_Ioi (add_pos (hrate 0) (hrate 2)),
    expMeasure_real_Ioi (add_pos (hrate 1) (hrate 2)), max_eq_left hs.le, max_eq_left ht.le,
    ← Real.exp_add, Real.exp_lt_exp]
  rcases le_total s t with hst | hst
  · rw [max_eq_right hst]
    nlinarith [hrate 2]
  · rw [max_eq_left hst]
    nlinarith [hrate 2]

/-- **The Marshall–Olkin law charges the diagonal**: `P(X₁ = X₂) > 0`, although both margins are
exponential and hence atomless. The common shock makes the two defaults simultaneous with
positive probability, so the joint law has a singular component on `{x₁ = x₂}`. -/
theorem marshallOlkin_diagonal_pos (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) :
    0 < P.real {ω | min (T 0 ω) (T 2 ω) = min (T 1 ω) (T 2 ω)} := by
  have hmeas (i : Fin 3) : MeasurableSet (![Ioi (1 : ℝ), Ioi 1, Iic 1] i) := by
    fin_cases i
    exacts [measurableSet_Ioi, measurableSet_Ioi, measurableSet_Iic]
  have hsub : ⋂ i, T i ⁻¹' ![Ioi (1 : ℝ), Ioi 1, Iic 1] i
      ⊆ {ω | min (T 0 ω) (T 2 ω) = min (T 1 ω) (T 2 ω)} := by
    intro ω hω
    simp only [mem_iInter, mem_preimage] at hω
    have h0 : 1 < T 0 ω := hω 0
    have h1 : 1 < T 1 ω := hω 1
    have h2 : T 2 ω ≤ 1 := hω 2
    change min (T 0 ω) (T 2 ω) = min (T 1 ω) (T 2 ω)
    rw [min_eq_right (h2.trans h0.le), min_eq_right (h2.trans h1.le)]
  have hpos (i : Fin 3) : P (T i ⁻¹' ![Ioi (1 : ℝ), Ioi 1, Iic 1] i) ≠ 0 := by
    rw [← Measure.map_apply_of_aemeasurable (hT i).aemeasurable (hmeas i), (hT i).map_eq]
    fin_cases i
    exacts [expMeasure_Ioi_ne_zero (hrate 0) 1, expMeasure_Ioi_ne_zero (hrate 1) 1,
      expMeasure_Iic_ne_zero (hrate 2) one_pos]
  have hS : 0 < P.real (⋂ i, T i ⁻¹' ![Ioi (1 : ℝ), Ioi 1, Iic 1] i) := by
    rw [measureReal_def, hind.meas_iInter fun i ↦ ⟨_, hmeas i, rfl⟩]
    exact ENNReal.toReal_pos (Finset.prod_ne_zero_iff.2 fun i _ ↦ hpos i)
      (ENNReal.prod_ne_top fun i _ ↦ measure_ne_top _ _)
  exact hS.trans_le (measureReal_mono hsub)

/-- **Default covariance under a common shock**: for horizons `s, t ≥ 0`, the default indicators
`𝟙{X₁ ≤ s}` and `𝟙{X₂ ≤ t}` have covariance
`exp(−(λ₁ + λ₃)s − (λ₂ + λ₃)t) · (exp(λ₃ min(s, t)) − 1)`, positive when `λ₃ min(s, t) > 0`. The
covariance of two indicators is `P(A ∩ B) − P(A)P(B)` (`covariance_indicator_one`,
`Probability/Dependence/HoeffdingCovariance.lean`), unchanged under complementing both events
(`measureReal_inter_sub_mul_compl`), so it is read off the joint survival function
(`marshallOlkin_survival`) and the margins. -/
theorem covariance_indicator_marshallOlkin (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    cov[{ω | min (T 0 ω) (T 2 ω) ≤ s}.indicator 1, {ω | min (T 1 ω) (T 2 ω) ≤ t}.indicator 1; P] =
      Real.exp (-((rate 0 + rate 2) * s) - (rate 1 + rate 2) * t) *
        (Real.exp (rate 2 * min s t) - 1) := by
  set Z : Ω → ℝ × ℝ := fun ω ↦ (min (T 0 ω) (T 2 ω), min (T 1 ω) (T 2 ω))
  have hZ : AEMeasurable Z P := ((hT 0).aemeasurable.min (hT 2).aemeasurable).prodMk
    ((hT 1).aemeasurable.min (hT 2).aemeasurable)
  have hA : MeasurableSet (Prod.fst ⁻¹' Iic s : Set (ℝ × ℝ)) :=
    measurableSet_Iic.preimage measurable_fst
  have hB : MeasurableSet (Prod.snd ⁻¹' Iic t : Set (ℝ × ℝ)) :=
    measurableSet_Iic.preimage measurable_snd
  -- the covariance is computed on the joint law of `(X₁, X₂)`
  have hcov : cov[{ω | min (T 0 ω) (T 2 ω) ≤ s}.indicator 1,
      {ω | min (T 1 ω) (T 2 ω) ≤ t}.indicator 1; P] =
      cov[(Prod.fst ⁻¹' Iic s).indicator 1, (Prod.snd ⁻¹' Iic t).indicator 1; P.map Z] :=
    (covariance_map_fun (measurable_one.indicator hA).aestronglyMeasurable
      (measurable_one.indicator hB).aestronglyMeasurable hZ).symm
  have e₁ : Z ⁻¹' ((Prod.fst ⁻¹' Iic s)ᶜ ∩ (Prod.snd ⁻¹' Iic t)ᶜ) =
      {ω | s < min (T 0 ω) (T 2 ω) ∧ t < min (T 1 ω) (T 2 ω)} := by
    ext ω
    simp [Z]
  have e₂ : Z ⁻¹' (Prod.fst ⁻¹' Iic s)ᶜ = {ω | s < min (T 0 ω) (T 2 ω)} := by
    ext ω
    simp [Z]
  have e₃ : Z ⁻¹' (Prod.snd ⁻¹' Iic t)ᶜ = {ω | t < min (T 1 ω) (T 2 ω)} := by
    ext ω
    simp [Z]
  rw [hcov, covariance_indicator_one hA hB, ← measureReal_inter_sub_mul_compl hA hB,
    map_measureReal_apply_of_aemeasurable hZ (hA.compl.inter hB.compl),
    map_measureReal_apply_of_aemeasurable hZ hA.compl,
    map_measureReal_apply_of_aemeasurable hZ hB.compl, e₁, e₂, e₃,
    marshallOlkin_survival hrate hT hind hs ht,
    measureReal_lt_min_of_hasLaw_expMeasure hrate hT hind (i := 0) (j := 2) (by decide),
    measureReal_lt_min_of_hasLaw_expMeasure hrate hT hind (i := 1) (j := 2) (by decide),
    expMeasure_real_Ioi (add_pos (hrate 0) (hrate 2)),
    expMeasure_real_Ioi (add_pos (hrate 1) (hrate 2)), max_eq_left hs, max_eq_left ht]
  have hmax : max s t = s + t - min s t := by linarith [min_add_max s t]
  have h₁ : Real.exp (-(rate 0 * s) - rate 1 * t - rate 2 * max s t) =
      Real.exp (-((rate 0 + rate 2) * s) - (rate 1 + rate 2) * t) *
        Real.exp (rate 2 * min s t) := by
    rw [← Real.exp_add, hmax]
    congr 1
    ring
  have h₂ : Real.exp (-((rate 0 + rate 2) * s)) * Real.exp (-((rate 1 + rate 2) * t)) =
      Real.exp (-((rate 0 + rate 2) * s) - (rate 1 + rate 2) * t) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  rw [h₁, h₂]
  ring

/-! ### First to default under a common shock -/

omit [IsProbabilityMeasure P] in
/-- **First-to-default survival under a common shock**: for `t ≥ 0`,
`P(min(X₁, X₂) > t) = exp(−(λ₁ + λ₂ + λ₃) t)`, since `min(X₁, X₂) = min(T₁, T₂, T₃)`. -/
theorem marshallOlkin_firstToDefault_survival (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {t : ℝ}
    (ht : 0 ≤ t) :
    P.real {ω | t < min (min (T 0 ω) (T 2 ω)) (min (T 1 ω) (T 2 ω))}
      = Real.exp (-((rate 0 + rate 1 + rate 2) * t)) := by
  have hset : {ω | t < min (min (T 0 ω) (T 2 ω)) (min (T 1 ω) (T 2 ω))}
      = ⋂ i, T i ⁻¹' Ioi t := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_Ioi, lt_min_iff]
    constructor
    · rintro ⟨⟨h0, h2⟩, h1, -⟩ i
      fin_cases i
      exacts [h0, h1, h2]
    · intro h
      exact ⟨⟨h 0, h 2⟩, h 1, h 2⟩
  rw [hset, measureReal_iInter_Ioi_of_hasLaw_expMeasure hrate hT hind (fun _ ↦ t),
    Fin.prod_univ_three, ← Real.exp_add, ← Real.exp_add, max_eq_left ht]
  congr 1
  ring

omit [IsProbabilityMeasure P] in
/-- The first-to-default credit spread under a common shock, `−log P(min(X₁, X₂) > t) / t`, is the
basket intensity `λ₁ + λ₂ + λ₃`. -/
theorem marshallOlkin_firstToDefault_spread (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {t : ℝ}
    (ht : 0 < t) :
    -Real.log (P.real {ω | t < min (min (T 0 ω) (T 2 ω)) (min (T 1 ω) (T 2 ω))}) / t
      = rate 0 + rate 1 + rate 2 := by
  rw [marshallOlkin_firstToDefault_survival hrate hT hind ht.le, Real.log_exp, neg_neg,
    mul_div_assoc, div_self ht.ne', mul_one]

omit [IsProbabilityMeasure P] in
/-- The single-name credit spread of the first name is its intensity `λ₁ + λ₃`. -/
theorem marshallOlkin_single_name_spread_fst (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {t : ℝ}
    (ht : 0 < t) :
    -Real.log (P.real {ω | t < min (T 0 ω) (T 2 ω)}) / t = rate 0 + rate 2 := by
  rw [measureReal_lt_min_of_hasLaw_expMeasure hrate hT hind (i := 0) (j := 2) (by decide),
    expMeasure_real_Ioi (add_pos (hrate 0) (hrate 2)), max_eq_left ht.le, Real.log_exp, neg_neg,
    mul_div_assoc, div_self ht.ne', mul_one]

omit [IsProbabilityMeasure P] in
/-- The single-name credit spread of the second name is its intensity `λ₂ + λ₃`. -/
theorem marshallOlkin_single_name_spread_snd (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {t : ℝ}
    (ht : 0 < t) :
    -Real.log (P.real {ω | t < min (T 1 ω) (T 2 ω)}) / t = rate 1 + rate 2 := by
  rw [measureReal_lt_min_of_hasLaw_expMeasure hrate hT hind (i := 1) (j := 2) (by decide),
    expMeasure_real_Ioi (add_pos (hrate 1) (hrate 2)), max_eq_left ht.le, Real.log_exp, neg_neg,
    mul_div_assoc, div_self ht.ne', mul_one]

omit [IsProbabilityMeasure P] in
/-- **Default correlation lowers the first-to-default spread**: under an active common shock
(`λ₃ > 0`), the first-to-default spread `λ₁ + λ₂ + λ₃` is strictly below the sum of the
single-name spreads `(λ₁ + λ₃) + (λ₂ + λ₃)`. The sum is what independent names with the same
single-name spreads would pay (`firstToDefault_spread_eq_sum_hazards`). -/
theorem marshallOlkin_firstToDefault_spread_lt (hrate : ∀ i, 0 < rate i)
    (hT : ∀ i, HasLaw (T i) (expMeasure (rate i)) P) (hind : iIndepFun T P) {t : ℝ}
    (ht : 0 < t) :
    -Real.log (P.real {ω | t < min (min (T 0 ω) (T 2 ω)) (min (T 1 ω) (T 2 ω))}) / t
      < -Real.log (P.real {ω | t < min (T 0 ω) (T 2 ω)}) / t
        + -Real.log (P.real {ω | t < min (T 1 ω) (T 2 ω)}) / t := by
  rw [marshallOlkin_firstToDefault_spread hrate hT hind ht,
    marshallOlkin_single_name_spread_fst hrate hT hind ht,
    marshallOlkin_single_name_spread_snd hrate hT hind ht]
  linarith [hrate 2]

end MathFin

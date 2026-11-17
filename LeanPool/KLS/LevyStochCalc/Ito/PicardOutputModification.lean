/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardOutputMoments

/-!
# Càdlàg modifications of the Picard step

The `L²` stochastic integral is defined separately at each time, so the Picard step as first
written has no path regularity. Replacing each Brownian component by a càdlàg adapted
modification, and the drift by its almost surely continuous version, produces a process
indistinguishable from the step at every fixed time and càdlàg along almost every path; the
Bielecki norm is unchanged, and the result is a genuine self-map of the space of bounded
adapted càdlàg processes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

omit [MeasurableSpace E] in
/-- **A càdlàg adapted modification of the Brownian Itô integral.** The `L²` integral is defined
separately at each time, so this is what supplies a path-regular representative. -/
theorem exists_cadlag_modification_itoIntegral
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Y : ℝ → Ω → ℝ, MeasureTheory.Adapted ℱ.rightCont Y ∧
      (∀ t, Y t =ᵐ[P]
        LevyStochCalc.Brownian.Ito.stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq t) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω)) ∧
          ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L) :=
  LevyStochCalc.Martingale.exists_adapted_ae_cadlag_of_eLpNorm
    (LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H
      h_meas h_progMeas h_sq)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eLpNorm_two_right_tendsto W ℱ hℱ H
      h_meas h_progMeas h_sq)
    (fun _ ht => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H
      h_meas h_progMeas h_sq ht)

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **The primitive of a locally integrable function is continuous.** The window `[0, t]` is
empty for `t < 0`, so the primitive is the constant `0` there and continuity at `0` glues. -/
theorem continuous_setIntegral_Icc_of_integrableOn {f : ℝ → ℝ}
    (h_int : ∀ b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) b) volume) :
    Continuous fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
  classical
  set g : ℝ → ℝ := Set.indicator (Set.Ici (0 : ℝ)) f with hgdef
  have hgint : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    have hsub : Set.Ici (0 : ℝ) ∩ Set.uIoc a b ⊆ Set.Icc (0 : ℝ) (max a b) := by
      rintro x ⟨hx0, hx⟩
      exact ⟨hx0, hx.2⟩
    rw [intervalIntegrable_iff, MeasureTheory.IntegrableOn,
      MeasureTheory.integrable_indicator_iff measurableSet_Ici,
      MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_restrict measurableSet_Ici]
    exact (h_int (max a b)).mono_set hsub
  have heq : (fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume)
      = fun t => ∫ s in (0 : ℝ)..(max t 0), g s ∂volume := by
    funext t
    rcases le_or_gt 0 t with ht | ht
    · rw [max_eq_left ht, intervalIntegral.integral_of_le ht,
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
      exact (Set.indicator_of_mem (Set.mem_Ici.mpr hx.1) f).symm
    · rw [max_eq_right ht.le, intervalIntegral.integral_same,
        Set.Icc_eq_empty (not_le.mpr ht), MeasureTheory.setIntegral_empty]
  rw [heq]
  exact (intervalIntegral.continuous_primitive hgint 0).comp
    (continuous_id.max continuous_const)

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- Almost every path of a process with locally finite energy is locally `L²`. -/
theorem ae_memLp_two_of_lintegral_sq {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hfin : ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ b : ℝ,
      MeasureTheory.MemLp (f ω) 2 (volume.restrict (Set.Icc (0 : ℝ) b)) := by
  have hstep : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∫⁻ s in Set.Icc (0 : ℝ) ((n : ℝ) + 1), (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ := by
    intro n
    refine MeasureTheory.ae_lt_top ?_ (hfin ((n : ℝ) + 1) (by positivity)).ne
    exact (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  filter_upwards [MeasureTheory.ae_all_iff.mpr hstep] with ω hω b
  obtain ⟨n, hn⟩ := exists_nat_ge b
  have hsub : Set.Icc (0 : ℝ) b ⊆ Set.Icc (0 : ℝ) ((n : ℝ) + 1) :=
    Set.Icc_subset_Icc le_rfl (by linarith)
  have hslice : Measurable (f ω) := hf.comp (measurable_const.prodMk measurable_id)
  exact (memLp_two_of_lintegral_sq_lt_top hslice (hω n)).mono_measure
    (MeasureTheory.Measure.restrict_mono hsub le_rfl)

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- Almost every path of a process with locally finite energy is locally integrable. -/
theorem ae_integrableOn_of_lintegral_sq {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hfin : ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ b : ℝ, MeasureTheory.IntegrableOn (f ω) (Set.Icc (0 : ℝ) b) volume := by
  filter_upwards [ae_memLp_two_of_lintegral_sq hf hfin] with ω hω b
  have : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) b)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (hω b).integrable (by norm_num)

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Almost every drift path of the Picard step is continuous.** -/
theorem ae_continuous_picardStep_drift
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_sq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, Continuous fun t => picardStepDrift coeffs X x₀ t ω i := by
  filter_upwards [ae_integrableOn_of_lintegral_sq h_μ_meas h_μ_sq] with ω hω
  have : (fun t => picardStepDrift coeffs X x₀ t ω i)
      = fun t => x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := rfl
  rw [this]
  exact continuous_const.add (continuous_setIntegral_Icc_of_integrableOn hω)

omit [MeasurableSpace E] in
omit [IsProbabilityMeasure P] in
/-- The Bielecki norm depends on the process only through its almost-everywhere class at each
time, so a modification has the same norm. -/
theorem bieleckiNorm_congr_ae (β T : ℝ) {Y Z : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ t : ℝ, Y t =ᵐ[P] Z t) :
    bieleckiNorm (P := P) β T Y = bieleckiNorm (P := P) β T Z := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun _ => ?_
  have hinner : (∫⁻ ω, ∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [h t] with ω hω
    rw [hω]
  rw [hinner]

section Modification

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X : ℝ → Ω → (Fin n → ℝ))
variable (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
  Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
variable (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
  Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
variable (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- A càdlàg representative of the `(i, j)` Brownian integral along `X`. -/
noncomputable def sigmaMod (i : Fin n) (j : Fin d) : ℝ → Ω → ℝ :=
  Classical.choose (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j))

omit [MeasurableSpace E] in
theorem sigmaMod_adapted (i : Fin n) (j : Fin d) :
    MeasureTheory.Adapted ℱ.rightCont
      (sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j) :=
  (Classical.choose_spec (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j))).1

omit [MeasurableSpace E] in
theorem sigmaMod_ae_eq (i : Fin n) (j : Fin d) (t : ℝ) :
    sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t
      =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
        (fun ω s => coeffs.σ s (X s ω) i j)
        (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j) t :=
  (Classical.choose_spec (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j)
      (h_σ_sq i j))).2.1 t

omit [MeasurableSpace E] in
theorem sigmaMod_cadlag (i : Fin n) (j : Fin d) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Ioi t))
          (nhds (sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)) ∧
        ∃ L : ℝ, Filter.Tendsto
          (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Iio t)) (nhds L) :=
  (Classical.choose_spec (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j)
      (h_σ_sq i j))).2.2

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (x₀ : Fin n → ℝ)
variable (h_γ_meas : ∀ i : Fin n,
  Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
variable (h_γ_progMeas : ∀ i : Fin n,
  Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
variable (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- **The Picard step with a càdlàg representative of its Brownian component.**

`picardStep` is an `L²` limit taken separately at each time, so it is not jointly measurable as
it stands; this replaces its Brownian component by the càdlàg modification of C0d-2, which
changes it only on a null set at each time. -/
noncomputable def picardStepMod : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω i => picardStepDrift coeffs X x₀ t ω i
    + (∑ j : Fin d, sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)
    + picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i

/-- The modified step is a modification of the Picard step. -/
theorem picardStepMod_ae_eq (t : ℝ) :
    picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t
      =ᵐ[P] picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t := by
  have hall : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin d,
      sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq p.1 p.2 t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
            (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
            (h_σ_meas p.1 p.2) (h_σ_progMeas p.1 p.2) (h_σ_sq p.1 p.2) t ω :=
    MeasureTheory.ae_all_iff.mpr fun p => sigmaMod_ae_eq W ℱ hℱW coeffs X h_σ_meas
      h_σ_progMeas h_σ_sq p.1 p.2 t
  filter_upwards [hall] with ω hω
  funext i
  change picardStepDrift coeffs X x₀ t ω i
      + (∑ j : Fin d, sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)
      + picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i
    = _
  simp only [picardStep, Pi.add_apply, picardStepDiffusion,
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => hω (i, j))) rfl

/-- The modified step has the same Bielecki norm as the Picard step. -/
theorem bieleckiNorm_picardStepMod (β T : ℝ) :
    bieleckiNorm (P := P) β T
        (picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
          h_γ_meas h_γ_progMeas h_γ_sq)
      = bieleckiNorm (P := P) β T
        (fun t ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
          h_γ_meas h_γ_progMeas h_γ_sq t ω) :=
  bieleckiNorm_congr_ae β T fun t => picardStepMod_ae_eq W ℱ hℱW coeffs X h_σ_meas
    h_σ_progMeas h_σ_sq N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq t

/-- The modified step is adapted to the right-continuous filtration. -/
theorem picardStepMod_adapted
    (h_μ_progMeas : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.μ s (X s ω) i))
    (i : Fin n) (t : ℝ) :
    Measurable[ℱ.rightCont t] fun ω =>
      picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t ω i := by
  have hdrift : Measurable[ℱ.rightCont t] fun ω => picardStepDrift coeffs X x₀ t ω i :=
    ((LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc
      (h_μ_progMeas i) t).mono (ℱ.le_rightCont t) le_rfl).const_add _
  have hσ : ∀ j : Fin d, Measurable[ℱ.rightCont t] fun ω =>
      sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω :=
    fun j => sigmaMod_adapted W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t
  have hγ : Measurable[ℱ.rightCont t] fun ω =>
      picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i :=
    (LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN
      (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i)
        (h_γ_sq i) t).stronglyMeasurable.measurable
  exact (hdrift.add (Finset.measurable_sum _ fun j _ => hσ j)).add hγ

/-- Almost every path of the modified step is càdlàg. -/
theorem picardStepMod_cadlag
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_sq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq s ω i)
          (nhdsWithin t (Set.Ioi t))
          (nhds (picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq t ω i)) ∧
        ∃ L : ℝ, Filter.Tendsto
          (fun s => picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq s ω i)
          (nhdsWithin t (Set.Iio t)) (nhds L) := by
  have hσall : ∀ᵐ ω ∂P, ∀ j : Fin d, ∀ t : ℝ,
      Filter.Tendsto (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Ioi t))
          (nhds (sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)) ∧
        ∃ L : ℝ, Filter.Tendsto
          (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Iio t)) (nhds L) :=
    MeasureTheory.ae_all_iff.mpr fun j =>
      sigmaMod_cadlag W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j
  filter_upwards [ae_continuous_picardStep_drift coeffs X x₀ i (h_μ_meas i) (h_μ_sq i),
    hσall,
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱN
      (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i)]
    with ω hdr hσ hγ t
  have hright := ((hdr.continuousAt (x := t)).continuousWithinAt (s := Set.Ioi t)).tendsto
  refine ⟨((hright.add (tendsto_finsetSum _ fun j _ => (hσ j t).1)).add (hγ t).1), ?_⟩
  choose L hL using fun j : Fin d => (hσ j t).2
  obtain ⟨Lγ, hLγ⟩ := (hγ t).2
  refine ⟨picardStepDrift coeffs X x₀ t ω i + (∑ j : Fin d, L j) + Lγ, ?_⟩
  exact ((((hdr.continuousAt (x := t)).continuousWithinAt (s := Set.Iio t)).tendsto.add
    (tendsto_finsetSum _ fun j _ => hL j)).add hLγ)

/-- **The Picard step lands in the process space.**

Under the usual conditions — a right-continuous filtration whose `ℱ 0` contains the `P`-null
sets — the Picard step has a modification that is a member of the Bielecki process space, which
is what makes `picardStepOnS2` a self-map. -/
theorem exists_sBoundedProcess_picardStep [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_progMeas : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_sq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ}
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hσT : ∀ i : Fin n, ∀ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ Y : SBoundedProcess (n := n) P ℱ T, ∀ t : ℝ,
      Y.X t =ᵐ[P] picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t := by
  classical
  have hrc : ℱ.rightCont = ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
  have hadapt : ∀ (i : Fin n) (t : ℝ), Measurable[ℱ t] fun ω =>
      picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t ω i := by
    intro i t
    have h := picardStepMod_adapted W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
      h_γ_meas h_γ_progMeas h_γ_sq h_μ_progMeas i t
    rwa [hrc] at h
  have hex : ∀ i : Fin n, ∃ Z : ℝ → Ω → ℝ, (∀ t : ℝ, Measurable[ℱ t] (Z t)) ∧
      (∀ t : ℝ, Z t =ᵐ[P] fun ω =>
        picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
          h_γ_meas h_γ_progMeas h_γ_sq t ω i) ∧
      (∀ (ω : Ω) (t : ℝ),
        Filter.Tendsto (fun s => Z s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Z t ω))) ∧
      ∀ (ω : Ω) (t : ℝ), ∃ L : ℝ,
        Filter.Tendsto (fun s => Z s ω) (nhdsWithin t (Set.Iio t)) (nhds L) := fun i =>
    LevyStochCalc.Probability.exists_everywhere_cadlag_modification hℱ0 hnull (hadapt i)
      (picardStepMod_cadlag W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas h_μ_sq i)
  choose Z hZmeas hZae hZright hZleft using hex
  have hstepae : ∀ t : ℝ, (fun ω i => Z i t ω) =ᵐ[P]
      picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t := by
    intro t
    filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin n => hZae i t] with ω hω
    exact funext fun i => hω i
  refine ⟨{
    X := fun t ω i => Z i t ω
    measurable_path := Measurable.of_eval fun i =>
      LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous (hZmeas i)
        (hZright i)
    adapted := fun i =>
      LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous (hZmeas i)
        (hZright i)
    cadlag_paths := Filter.Eventually.of_forall fun ω t =>
      ⟨tendsto_pi_nhds.mpr fun i => hZright i ω t, fun i => hZleft i ω t⟩
    sup_L2 := ?_ }, ?_⟩
  · rw [bieleckiNorm_congr_ae 0 T hstepae,
      bieleckiNorm_picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq 0 T]
    exact bieleckiNorm_picardStep_lt_top W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas
      h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas hμT hσT hγT
  · intro t
    exact (hstepae t).trans (picardStepMod_ae_eq W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas
      h_σ_sq N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq t)

end Modification

section SelfMap

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

/-- **The Picard self-map on the process space.**

Every hypothesis `picardStep` and `SBoundedProcess` ask for is supplied from `IsRegular` and
`IsLipschitz` along the frozen process, so this is a genuine map from the space to itself under
the usual conditions. -/
noncomputable def picardSelfMap
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    (Y : SBoundedProcess (n := n) P ℱ T) : SBoundedProcess (n := n) P ℱ T :=
  Classical.choose (exists_sBoundedProcess_picardStep W ℱ hℱW coeffs Y.stop.X
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT')
    N hℱN x₀
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT')
    hℱ0 hnull
    (fun i => measurable_mu_stop coeffs hReg Y i)
    (fun i => progressivelyMeasurable_mu_stop coeffs hReg Y i)
    (fun i _ hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hb)
    (fun i => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hT)
    (fun i j => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT)
    (fun i => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT))

/-- **The Picard self-map along a raw state process.** A process of the space whose path is a
modification of `picardStepOnRawStop`. -/
noncomputable def picardSelfMapRaw
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) : SBoundedProcess (n := n) P ℱ T :=
  Classical.choose (exists_sBoundedProcess_picardStep W ℱ hℱW coeffs
    (fun s ω => Z (min s T) ω)
    (measurable_sigma_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i j hT')
    N hℱN x₀
    (measurable_gamma_rawStop coeffs hReg hZm T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT')
    hℱ0 hnull
    (measurable_mu_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_mu_rawStop coeffs hReg hZa T)
    (fun i _ hb => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hb)
    (fun i => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT)
    (fun i j => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i j hT)
    (fun i => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT))

/-- The raw self-map's path is a modification of the Picard step along the raw process. -/
theorem picardSelfMapRaw_ae_eq
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) (t : ℝ) :
    (picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X t
      =ᵐ[P] picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t :=
  Classical.choose_spec (exists_sBoundedProcess_picardStep W ℱ hℱW coeffs
    (fun s ω => Z (min s T) ω)
    (measurable_sigma_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i j hT')
    N hℱN x₀
    (measurable_gamma_rawStop coeffs hReg hZm T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT')
    hℱ0 hnull
    (measurable_mu_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_mu_rawStop coeffs hReg hZa T)
    (fun i _ hb => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hb)
    (fun i => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT)
    (fun i j => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i j hT)
    (fun i => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT)) t

/-- The self-map's path is a modification of the Picard step along the frozen process. -/
theorem picardSelfMap_ae_eq
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    (Y : SBoundedProcess (n := n) P ℱ T) (t : ℝ) :
    (picardSelfMap W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t
      =ᵐ[P] picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t :=
  Classical.choose_spec (exists_sBoundedProcess_picardStep W ℱ hℱW coeffs Y.stop.X
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT')
    N hℱN x₀
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT')
    hℱ0 hnull
    (fun i => measurable_mu_stop coeffs hReg Y i)
    (fun i => progressivelyMeasurable_mu_stop coeffs hReg Y i)
    (fun i _ hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hb)
    (fun i => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hT)
    (fun i j => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT)
    (fun i => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT)) t

end SelfMap

end LevyStochCalc.Ito.Picard

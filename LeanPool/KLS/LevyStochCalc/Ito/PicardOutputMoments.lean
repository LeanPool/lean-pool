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

public import LeanPool.KLS.LevyStochCalc.Ito.PicardIntegrand
public import LeanPool.KLS.LevyStochCalc.Probability.ProgressiveCadlag
public import LeanPool.KLS.LevyStochCalc.Ito.PicardSpace

/-!
# Second moments of the Picard step

Each of the three components of the Picard step — the Lebesgue drift integral, the Brownian
stochastic integral and the compensated jump integral — is bounded in `L²` uniformly over
`[0, T]` by the energies of its integrand, through Cauchy–Schwarz for the drift and the Itô
and Itô–Lévy isometries for the two stochastic components; summing the three bounds gives a
finite Bielecki norm for the step.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Cauchy–Schwarz for a finite sum of reals, transported to `ℝ≥0∞`. -/
theorem sq_nnnorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (‖∑ j ∈ s, f j‖₊ : ℝ≥0∞) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ j ∈ s, (‖f j‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : (∑ j ∈ s, f j) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, (f j) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc (‖∑ j ∈ s, f j‖₊ : ℝ≥0∞) ^ 2
      = ENNReal.ofReal ((∑ j ∈ s, f j) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal ((s.card : ℝ) * ∑ j ∈ s, (f j) ^ 2) := ENNReal.ofReal_le_ofReal h1
    _ = (s.card : ℝ≥0∞) * ∑ j ∈ s, (‖f j‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (sq_coe_nnnorm_real (f j)).symm)

variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

omit [MeasurableSpace E] in
/-- The Itô isometry at every nonnegative horizon, including `0`. -/
theorem itoIsometry_of_nonneg
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
  LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_lintegral_sq W ℱ hℱ H h_meas h_progMeas
    h_sq hT

/-- The Itô–Lévy isometry at every nonnegative horizon, including `0`. -/
theorem compensatedIsometry_of_nonneg {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas
      h_sq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← LevyStochCalc.Poisson.Compensated.process_lintegral_sq' N ℱ hℱ φ h_meas h_progMeas
    h_sq hT]
  refine lintegral_congr_ae ?_
  filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ
    h_meas h_progMeas h_sq T] with ω hω
  rw [hω]

omit [MeasurableSpace E] in
/-- **Second moment of the diffusion component**, by the Itô isometry applied to each of the
`d` component integrals. -/
theorem lintegral_sq_picardStep_diffusion_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖picardStepDiffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set M : Fin d → Ω → ℝ := fun j ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j) t ω with hM
  have hM_meas : ∀ j : Fin d, Measurable (M j) := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j)
    exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl
  have hunfold : ∀ ω : Ω,
      picardStepDiffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i
        = ∑ j : Fin d, M j ω := by
    intro ω
    simp only [picardStepDiffusion,
      LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral, M]
  calc ∫⁻ ω, (‖picardStepDiffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_congr fun ω => by rw [hunfold ω]
    _ ≤ ∫⁻ ω, (d : ℝ≥0∞) * ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        refine lintegral_mono fun ω => ?_
        simpa using sq_nnnorm_sum_le (Finset.univ : Finset (Fin d)) (fun j => M j ω)
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : (d : ℝ≥0∞) ≠ ⊤),
          MeasureTheory.lintegral_finsetSum]
        exact fun j _ => ((hM_meas j).nnnorm.coe_nnreal_ennreal).pow_const 2
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        exact itoIsometry_of_nonneg (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) ht

/-- **Second moment of the jump component**, by the Itô–Lévy isometry. -/
theorem lintegral_sq_picardStep_jump_eq {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖picardStepJump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
  compensatedIsometry_of_nonneg N ℱ hℱN
    (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i) ht

/-- The extended norm of a square. -/
theorem enorm_sq_eq (x : ℝ) : ‖x ^ 2‖ₑ = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [← ENNReal.coe_pow, ← nnnorm_pow]
  rfl

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A function with finite energy on a bounded window is `L²` there. -/
theorem memLp_two_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {b : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    MeasureTheory.MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) b)) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr ?_
  refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => enorm_sq_eq (f s))) hfin

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A function with finite energy on a bounded window is integrable there. -/
theorem integrableOn_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {b : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) b) volume := by
  have : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) b)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (memLp_two_of_lintegral_sq_lt_top hf hfin).integrable (by norm_num)

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Second moment of a time-integral**, by Cauchy–Schwarz on `[0, t]`. -/
theorem lintegral_sq_setIntegral_le {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) {t : ℝ} (ht : 0 ≤ t)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal t
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hinner_meas : Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  have hae : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
    MeasureTheory.ae_lt_top hinner_meas hfin.ne
  have hpt : ∀ᵐ ω ∂P, (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal t * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    filter_upwards [hae] with ω hω
    have hslice : Measurable (f ω) := hf.comp (measurable_const.prodMk measurable_id)
    -- `f ω` is `L²` on `[0, t]`
    have hL2 : MeasureTheory.MemLp (f ω) 2 (volume.restrict (Set.Icc (0 : ℝ) t)) :=
      memLp_two_of_lintegral_sq_lt_top hslice hω
    have hint : MeasureTheory.Integrable (f ω) (volume.restrict (Set.Icc (0 : ℝ) t)) :=
      hL2.integrable (by norm_num)
    -- Cauchy–Schwarz against the constant `1`
    have hCS := integral_sq_le_mul_integral_sq_on_Icc (fun s => ‖f ω s‖) t ht
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hL2.norm
    have habs : |∫ s in Set.Icc (0 : ℝ) t, f ω s| ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ :=
      MeasureTheory.abs_integral_le_integral_abs.trans_eq
        (MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun s => (Real.norm_eq_abs (f ω s)).symm))
    have hsq : ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ ^ 2
        = (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun s => by positivity)
        ((hslice.norm.pow_const 2).aestronglyMeasurable)]
      congr 1
      refine lintegral_congr fun s => ?_
      rw [← sq_coe_nnnorm_real ‖f ω s‖, nnnorm_norm]
    have hbound : (∫ s in Set.Icc (0 : ℝ) t, f ω s) ^ 2
        ≤ t * (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal := by
      have hnn : 0 ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ :=
        MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun s => norm_nonneg (f ω s))
      rw [← hsq]
      refine le_trans ?_ hCS
      nlinarith [habs, abs_nonneg (∫ s in Set.Icc (0 : ℝ) t, f ω s),
        sq_abs (∫ s in Set.Icc (0 : ℝ) t, f ω s), hnn]
    calc (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((∫ s in Set.Icc (0 : ℝ) t, f ω s) ^ 2) := sq_coe_nnnorm_real _
      _ ≤ ENNReal.ofReal
            (t * (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal t * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
          rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_toReal hω.ne]
  refine (lintegral_mono_ae hpt).trans ?_
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` for reals, in `ℝ≥0∞`. -/
theorem sq_nnnorm_add_le (a b : ℝ) :
    (‖a + b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc (‖a + b‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((a + b) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal (2 * a ^ 2 + 2 * b ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
          ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real]

omit [MeasurableSpace E] in
/-- **Second moment of the drift component**, by Cauchy–Schwarz on `[0, t]`. -/
theorem lintegral_sq_picardStep_drift_le
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {t : ℝ} (ht : 0 ≤ t)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖picardStepDrift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
        + 2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
  have hunfold : ∀ ω : Ω, picardStepDrift coeffs X x₀ t ω i
      = x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := fun _ => rfl
  calc ∫⁻ ω, (‖picardStepDrift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_congr fun ω => by rw [hunfold ω]
    _ ≤ ∫⁻ ω, (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2) ∂P :=
        lintegral_mono fun ω => sq_nnnorm_add_le _ _
    _ = 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const,
          measure_univ, mul_one,
          MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    _ ≤ 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :=
        add_le_add le_rfl
          (mul_le_mul' le_rfl (lintegral_sq_setIntegral_le h_μ_meas ht hfin))

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The time-integral of a jointly measurable process is measurable in the sample. -/
theorem measurable_setIntegral_slice {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (t : ℝ) :
    Measurable fun ω => ∫ s in Set.Icc (0 : ℝ) t, f ω s := by
  have : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (hf.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) t))).measurable

/-- `‖x + y + z‖² ≤ 3‖x‖² + 3‖y‖² + 3‖z‖²` for reals, in `ℝ≥0∞`. -/
theorem sq_nnnorm_add3_le (x y z : ℝ) :
    (‖x + y + z‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (x + y + z) ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  calc (‖x + y + z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((x + y + z) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal (3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat,
          ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real]

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- Enlarging the time window increases the doubly-integrated energy. -/
theorem lintegral_lintegral_Icc_mono {f : Ω → ℝ → ℝ≥0∞} {t T : ℝ} (h : t ≤ T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, f ω s ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume ∂P :=
  lintegral_mono fun _ =>
    lintegral_mono' (MeasureTheory.Measure.restrict_mono
      (Set.Icc_subset_Icc le_rfl h) le_rfl) le_rfl

omit [MeasurableSpace E] in
/-- Slice measurability of the drift component. -/
theorem measurable_picardStep_drift
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i)) (t : ℝ) :
    Measurable fun ω => picardStepDrift coeffs X x₀ t ω i :=
  (measurable_setIntegral_slice h_μ_meas t).const_add _

omit [MeasurableSpace E] in
/-- Slice measurability of the diffusion component. -/
theorem measurable_picardStep_diffusion
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (t : ℝ) :
    Measurable fun ω =>
      picardStepDiffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i := by
  have hcomp : ∀ j : Fin d, Measurable fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
        (fun ω' s => coeffs.σ s (X s ω') i j)
        (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j)
    exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl
  have hunfold : (fun ω => picardStepDiffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
      = fun ω => ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
        (fun ω' s => coeffs.σ s (X s ω') i j)
        (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := rfl
  rw [hunfold]
  exact Finset.measurable_sum _ fun j _ => hcomp j

/-- Slice measurability of the jump component. -/
theorem measurable_picardStep_jump {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (i : Fin n) (t : ℝ) :
    Measurable fun ω => picardStepJump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i :=
  ((LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN
    (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i)
      t).stronglyMeasurable).measurable.mono (ℱ.rightCont.le t) le_rfl

section Step

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
variable (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
  Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
variable (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
  Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
variable (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
variable (h_γ_meas : ∀ i : Fin n,
  Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
variable (h_γ_progMeas : ∀ i : Fin n,
  Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
variable (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- **Second moment of the Picard step at a time of `[0, T]`, bounded uniformly by data at the
horizon `T`.** -/
theorem lintegral_sq_picardStep_le
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∑ i, (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ i : Fin n,
          (3 * (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
              + 2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
                  (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
            + 3 * ((d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
                (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 3 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
                (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
  obtain ⟨ht0, htT⟩ := ht
  have hdr : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStepDrift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 := fun i =>
    (((measurable_picardStep_drift coeffs X x₀ i (h_μ_meas i)
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hdf : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    (((measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hjp : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    (((measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq i
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  -- pointwise three-term split
  have hpt : ∀ ω : Ω, ∑ i, (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas
        h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊ : ℝ≥0∞) ^ 2
      ≤ ∑ i : Fin n,
          (3 * (‖picardStepDrift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
            + 3 * (‖picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
                t ω i‖₊ : ℝ≥0∞) ^ 2
            + 3 * (‖picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq
                t ω i‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω
    refine Finset.sum_le_sum fun i _ => ?_
    exact sq_nnnorm_add3_le _ _ _
  have hmeas2 : ∀ i : Fin n, Measurable fun ω =>
      3 * (‖picardStepDrift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => ((hdr i).const_mul 3).add ((hdf i).const_mul 3)
  have hmeas3 : ∀ i : Fin n, Measurable fun ω =>
      3 * (‖picardStepDrift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => (hmeas2 i).add ((hjp i).const_mul 3)
  refine (lintegral_mono hpt).trans ?_
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => hmeas3 i)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [MeasureTheory.lintegral_add_left (hmeas2 i),
    MeasureTheory.lintegral_add_left ((hdr i).const_mul 3),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤)]
  have hμt : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lt_of_le_of_lt (lintegral_lintegral_Icc_mono htT) (hμT i)
  refine add_le_add (add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_))
    (mul_le_mul' le_rfl ?_)
  · refine (lintegral_sq_picardStep_drift_le coeffs X x₀ i (h_μ_meas i) ht0 hμt).trans ?_
    exact add_le_add le_rfl (mul_le_mul' le_rfl
      (mul_le_mul' (ENNReal.ofReal_le_ofReal htT) (lintegral_lintegral_Icc_mono htT)))
  · refine (lintegral_sq_picardStep_diffusion_le W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas
      h_σ_sq i ht0).trans ?_
    exact mul_le_mul' le_rfl
      (Finset.sum_le_sum fun j _ => lintegral_lintegral_Icc_mono htT)
  · refine le_of_eq_of_le (lintegral_sq_picardStep_jump_eq N ℱ hℱN coeffs X h_γ_meas
      h_γ_progMeas h_γ_sq i ht0) ?_
    exact lintegral_lintegral_Icc_mono htT

/-- **The Picard step has finite Bielecki norm on `[0, T]`** — the `L²` output field that
`picardStepOnS2` takes as a hypothesis. -/
theorem bieleckiNorm_picardStep_lt_top
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {T : ℝ}
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hσT : ∀ i : Fin n, ∀ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤ := by
  have hKfin : (∑ i : Fin n,
      (3 * (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        + 3 * ((d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 3 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)) < ⊤ := by
    refine ENNReal.sum_lt_top.mpr fun i _ => ?_
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩
    · refine ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
      · exact ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      · exact ENNReal.mul_lt_top (by simp)
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμT i))
    · exact ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top (by simp)
        (ENNReal.sum_lt_top.mpr fun j _ => hσT i j))
    · exact ENNReal.mul_lt_top (by simp) (hγT i)
  refine lt_of_le_of_lt (b := _ ^ ((1 : ℝ) / 2)) ?_
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKfin.ne)
  unfold bieleckiNorm
  refine iSup₂_le fun t ht => ?_
  rw [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  exact ENNReal.rpow_le_rpow
    (lintegral_sq_picardStep_le W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas ht hμT) (by norm_num)

end Step

end LevyStochCalc.Ito.Picard

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardSupL2

/-!
# Locality of the Picard step

The Picard step at time `t` reads its input only on `[0, t]`: the drift is a Bochner integral
over `Set.Icc 0 t`, and the two stochastic components are `L²` integrals whose difference
isometries turn an a.e. vanishing integrand into an a.e. vanishing integral. Consequently two
input paths agreeing `volume ⊗ P`-a.e. on `[0, t]` produce a.e. equal steps at `t`, which is
what identifies a window solution with the solution on any longer window.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Slice measurability of the two stochastic integrals -/

/-- The Itô integral against a Brownian motion is measurable at each time. -/
theorem measurable_itoIntegral_slice
    (Wj : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration Wj ℱ)
    (H : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) :
    Measurable fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H hm hp hs t ω := by
  obtain ⟨Filt, hMart⟩ :=
    LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral Wj ℱ hℱ H hm hp hs
  exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl

/-- The compensated-Poisson integral is measurable at each time. -/
theorem measurable_compensatedIntegral_slice {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) :
    Measurable fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ hm hp hs t ω :=
  ((LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN φ hm hp hs
    t).stronglyMeasurable).measurable.mono (ℱ.rightCont.le t) le_rfl

/-! ### An a.e. vanishing integrand has an a.e. vanishing energy -/

omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The `L²` energy of a difference vanishing a.e. on the window is zero. -/
theorem lintegral_sq_sub_eq_zero_of_ae {t : ℝ} (H₁ H₂ : Ω → ℝ → ℝ)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), H₁ ω s = H₂ ω s) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [h] with ω hω
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hω] with s hs
  simp [hs]

omit [IsProbabilityMeasure P] in
/-- The mark-indexed `L²` energy of a difference vanishing a.e. on the window is zero. -/
theorem lintegral_sq_sub_mark_eq_zero_of_ae {ν : Measure E} {t : ℝ} (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), φ₁ ω s = φ₂ ω s) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P = 0 := by
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [h] with ω hω
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hω] with s hs
  simp [hs]

/-! ### Locality of the two stochastic integrals -/

/-- Integrands agreeing a.e. on `[0, t]` have a.e. equal Itô integrals at `t`. -/
theorem itoIntegral_congr_ae
    (Wj : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration Wj ℱ)
    (H₁ H₂ : Ω → ℝ → ℝ)
    (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), H₁ ω s = H₂ ω s) :
    ∀ᵐ ω ∂P, LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω := by
  have hiso := LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian
    Wj ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hs₁ hs₂ ht
  rw [lintegral_sq_sub_eq_zero_of_ae H₁ H₂ h] at hiso
  have hmeas : Measurable fun ω =>
      (‖LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω‖₊
          : ℝ≥0∞) ^ 2 :=
    (((measurable_itoIntegral_slice Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t).sub
      (measurable_itoIntegral_slice Wj ℱ hℱ H₂ hm₂ hp₂ hs₂
        t)).nnnorm.coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hiso] with ω hω
  have : (‖LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  have hn : ‖LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω‖ = 0 := by
    simpa [← ENNReal.coe_eq_zero, ← coe_nnnorm] using this
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Integrands agreeing a.e. on `[0, t]` have a.e. equal compensated-Poisson integrals at `t`. -/
theorem compensatedIntegral_congr_ae {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), φ₁ ω s = φ₂ ω s) :
    ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω := by
  have hiso := LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated
    N ℱ hℱN φ₁ φ₂ hm₁ hm₂ hp₁ hp₂ hs₁ hs₂ t ht
  rw [lintegral_sq_sub_mark_eq_zero_of_ae (ν := ν) φ₁ φ₂ h] at hiso
  have hmeas : Measurable fun ω =>
      (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω‖₊
          : ℝ≥0∞) ^ 2 :=
    (((measurable_compensatedIntegral_slice N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t).sub
      (measurable_compensatedIntegral_slice N ℱ hℱN φ₂ hm₂ hp₂ hs₂
        t)).nnnorm.coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hiso] with ω hω
  have hz : (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω‖₊
        : ℝ≥0∞) = 0 := by
    simpa using hω
  have hn : ‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω‖ = 0 := by
    simpa [← ENNReal.coe_eq_zero, ← coe_nnnorm] using hz
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-! ### Locality of the Picard step -/

section Step

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)

omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The drift component at `t` only reads its input on `[0, t]`. -/
theorem picardStep_drift_congr_ae {t : ℝ}
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P, picardStep_drift coeffs X x₀ t ω = picardStep_drift coeffs Y x₀ t ω := by
  filter_upwards [hXY] with ω hω
  have hω' : ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) t → X s ω = Y s ω :=
    (ae_restrict_iff' measurableSet_Icc).mp hω
  have hint : (fun i : Fin n => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i)
      = fun i : Fin n => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Y s ω) i := by
    funext i
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hω'] with s hs hsmem
    rw [hs hsmem]
  simp only [picardStep_drift, hint]

omit [MeasurableSpace E] in
/-- The Brownian component at `t` only reads its input on `[0, t]`. -/
theorem picardStep_diffusion_congr_ae
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
        = picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω := by
  have hcomp : ∀ p : Fin n × Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
          (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
          (h_σ_meas_X p.1 p.2) (h_σ_progMeas_X p.1 p.2) (h_σ_sq_X p.1 p.2) t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
          (fun ω' s => coeffs.σ s (Y s ω') p.1 p.2)
          (h_σ_meas_Y p.1 p.2) (h_σ_progMeas_Y p.1 p.2) (h_σ_sq_Y p.1 p.2) t ω := by
    rintro ⟨i, j⟩
    refine itoIntegral_congr_ae (W.W j) ℱ (hℱW j) _ _ _ _ _ _ _ _ ht ?_
    filter_upwards [hXY] with ω hω
    filter_upwards [hω] with s hs
    rw [hs]
  filter_upwards [MeasureTheory.ae_all_iff.mpr hcomp] with ω hω
  funext i
  simp only [picardStep_diffusion]
  exact Finset.sum_congr rfl fun j _ => hω (i, j)

/-- The compensated-Poisson component at `t` only reads its input on `[0, t]`. -/
theorem picardStep_jump_congr_ae
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        = picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω := by
  have hcomp : ∀ i : Fin n, ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω' s e => coeffs.γ s (X s ω') e i)
          (h_γ_meas_X i) (h_γ_progMeas_X i) (h_γ_sq_X i) t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω' s e => coeffs.γ s (Y s ω') e i)
          (h_γ_meas_Y i) (h_γ_progMeas_Y i) (h_γ_sq_Y i) t ω := by
    intro i
    refine compensatedIntegral_congr_ae N ℱ hℱN _ _ _ _ _ _ _ _ ht ?_
    filter_upwards [hXY] with ω hω
    filter_upwards [hω] with s hs
    funext e
    rw [hs]
  filter_upwards [MeasureTheory.ae_all_iff.mpr hcomp] with ω hω
  funext i
  exact hω i

/-- **The Picard step is local.** Inputs agreeing a.e. on `[0, t]` give a.e. equal steps at `t`. -/
theorem picardStep_congr_ae
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
          h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        = picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω := by
  filter_upwards [picardStep_drift_congr_ae coeffs X Y x₀ hXY,
    picardStep_diffusion_congr_ae W ℱ hℱW coeffs X Y h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y ht hXY,
    picardStep_jump_congr_ae N ℱ hℱN coeffs X Y h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y ht hXY] with ω h1 h2 h3
  simp only [picardStep, h1, h2, h3]

end Step

end LevyStochCalc.Ito.Picard

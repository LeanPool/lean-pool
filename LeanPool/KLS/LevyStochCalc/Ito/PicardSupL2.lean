/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardContraction
public import LeanPool.KLS.LevyStochCalc.Probability.DoobContinuous

/-!
# The `S²` bound for the Picard step

`JumpDiffusion.sup_L2` asks for `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞`, the `S²` norm, which is stronger
than the weighted supremum of `L²` norms the Picard space carries. The Picard step splits into a
drift, `d` Brownian integrals and a compensated-Poisson integral; the drift is bounded pathwise
by its own total variation over the window, and each stochastic component is a martingale, so
Doob's `L²` inequality over the dyadic points applies. Only the dyadic form of Doob is available
here, because the stochastic integrals are càdlàg only up to modification.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### An elementary two-term bound -/

/-- A squared sum of two extended reals, up to the constant `4`. -/
theorem sq_add_le_four_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have h1 : a + b ≤ 2 * (a ⊔ b) := by
    calc a + b ≤ (a ⊔ b) + (a ⊔ b) := add_le_add le_sup_left le_sup_right
      _ = 2 * (a ⊔ b) := by ring
  have h2 : (a ⊔ b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases max_choice a b with h | h <;> rw [h]
    · exact le_add_right le_rfl
    · exact le_add_left le_rfl
  calc (a + b) ^ 2 ≤ (2 * (a ⊔ b)) ^ 2 := pow_le_pow_left' h1 2
    _ = 4 * (a ⊔ b) ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl h2

/-- A squared sum of three extended reals, up to the constant `16`. -/
theorem sq_add3_le_sixteen_mul (a b c : ℝ≥0∞) : (a + b + c) ^ 2 ≤ 16 * (a ^ 2 + b ^ 2 + c ^ 2) :=
  calc (a + b + c) ^ 2 ≤ 4 * ((a + b) ^ 2 + c ^ 2) := sq_add_le_four_mul _ _
    _ ≤ 4 * (4 * (a ^ 2 + b ^ 2) + c ^ 2) :=
        mul_le_mul' le_rfl (add_le_add (sq_add_le_four_mul a b) le_rfl)
    _ = 16 * (a ^ 2 + b ^ 2) + 4 * c ^ 2 := by ring
    _ ≤ 16 * (a ^ 2 + b ^ 2) + 16 * c ^ 2 :=
        add_le_add le_rfl (mul_le_mul' (by norm_num) le_rfl)
    _ = 16 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring

/-! ### The drift component -/

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The drift component is dominated over the window by its own total variation there. -/
theorem iSup_dyadicRunMax_drift_le
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T') {ω : Ω}
    (hint : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (X s ω) i)
      (Set.Icc (0 : ℝ) T') volume) :
    (⨆ m, (‖dyadicRunMax (fun t ω => picardStepDrift coeffs X x₀ t ω i) T' m ω‖₊ : ℝ≥0∞))
      ≤ (‖x₀ i‖₊ : ℝ≥0∞)
        + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) := by
  refine iSup_dyadicRunMax_le_of_bound hT' fun t ht => ?_
  have hval : picardStepDrift coeffs X x₀ t ω i
      = x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := rfl
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T' := Set.Icc_subset_Icc le_rfl ht.2
  have hnn' : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) T')]
      fun s => ‖coeffs.μ s (X s ω) i‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  have hmono : ∫ s in Set.Icc (0 : ℝ) t, ‖coeffs.μ s (X s ω) i‖
      ≤ ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ :=
    MeasureTheory.setIntegral_mono_set hint.norm hnn' hsub.eventuallySubset
  have hnorm : ‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖
      ≤ ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ :=
    le_trans (MeasureTheory.norm_integral_le_integral_norm _) hmono
  rw [hval]
  refine le_trans (by rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.mpr (nnNorm_add_le _ _))
    (add_le_add le_rfl ?_)
  have hnn : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ :=
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  refine ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp ?_)
  rw [coe_nnNorm, coe_nnNorm,
    show ‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖
        = ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ from
      by rw [Real.norm_eq_abs, abs_of_nonneg hnn]]
  exact hnorm

omit [MeasurableSpace E] in
/-- The drift dominator is square integrable. -/
theorem lintegral_sq_drift_bound_lt_top
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T')
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ((‖x₀ i‖₊ : ℝ≥0∞)
        + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  have hfin' : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    exact lintegral_congr fun ω => lintegral_congr fun s => by rw [nnNorm_norm]
  have hkey := lintegral_sq_setIntegral_le (P := P)
    (f := fun ω s => ‖coeffs.μ s (X s ω) i‖) hμm.norm hT' hfin'
  have hbfin : ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) ^ 2 ∂P
      < ⊤ := lt_of_le_of_lt hkey (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin')
  have hbm : Measurable fun ω : Ω =>
      (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) ^ 2 :=
    (ENNReal.continuous_coe.measurable.comp
      (measurable_setIntegral_slice hμm.norm T').nnNorm).pow_const 2
  refine lt_of_le_of_lt (lintegral_mono fun ω => sq_add_le_four_mul _ _) ?_
  rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr
    ⟨ENNReal.pow_lt_top ENNReal.coe_lt_top, hbfin⟩)

/-! ### The stochastic components -/

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

/-- Doob's inequality for the jump component of the Picard step. -/
theorem lintegral_sq_iSup_jump_le
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
    (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax
        (fun t ω => picardStepJump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i)
        T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hmart : MeasureTheory.Martingale
      (fun t ω => picardStepJump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i)
      ℱ.rightCont P :=
    LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱN
      (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i)
  refine le_trans (lintegral_iSup_dyadicRunMax_sq_le hmart hT') ?_
  rw [lintegral_sq_picardStep_jump_eq N ℱ hℱN coeffs X h_meas h_progMeas h_sq i hT']

omit [MeasurableSpace E] in
/-- Doob's inequality for one Brownian coordinate of the Picard step. -/
theorem lintegral_sq_iSup_brownian_coord_le
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
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 ≤ T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) T' ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral (W.W j) ℱ (hℱW j)
    (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j)
  exact lintegral_iSup_dyadicRunMax_sq_le hF hT'

/-! ### The whole step -/

omit [MeasurableSpace E] in
/-- Slice measurability of one Brownian coordinate's integral. -/
theorem measurable_brownianIntegral_slice
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
    (i : Fin n) (j : Fin d) (t : ℝ) :
    Measurable fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral (W.W j) ℱ (hℱW j)
    (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j)
  exact (hF.stronglyMeasurable t).measurable.mono (F.le t) le_rfl

omit [MeasurableSpace E] in
/-- The dyadic supremum of the Brownian component, summed over the driving coordinates. -/
theorem lintegral_sq_iSup_diffusion_lt_top
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
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        picardStepDiffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
        T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  set g : Fin d → ℝ → Ω → ℝ := fun j t ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j) t ω with hg
  have hunfold : (fun t (ω : Ω) =>
      picardStepDiffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
      = fun t ω => ∑ j : Fin d, g j t ω := rfl
  have hmeas : ∀ j : Fin d, ∀ t : ℝ, Measurable (g j t) := fun j t =>
    measurable_brownianIntegral_slice W ℱ hℱW coeffs X h_meas h_progMeas h_sq i j t
  have hsupm : ∀ j : Fin d, Measurable fun ω =>
      (⨆ m, (‖dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2 :=
    fun j => (Measurable.iSup fun m => measurable_enorm_dyadicRunMax (hmeas j) T' m).pow_const 2
  calc ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω => ∑ j : Fin d, g j t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ∫⁻ ω, ((Finset.univ.card : ℝ≥0∞) ^ 2
          * ∑ j : Fin d, (⨆ m, (‖dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        lintegral_mono fun ω => le_trans
          (pow_le_pow_left' (iSup_dyadicRunMax_sum_le Finset.univ g T' ω) 2)
          (sq_sum_le_card_sq_mul Finset.univ _)
    _ = (Finset.univ.card : ℝ≥0∞) ^ 2
          * ∑ j : Fin d, ∫⁻ ω, (⨆ m, (‖dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ fun j _ => hsupm j]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by simp) (ENNReal.sum_lt_top.mpr fun j _ => ?_)
        refine lt_of_le_of_lt (lintegral_sq_iSup_brownian_coord_le W ℱ hℱW coeffs X
          h_meas h_progMeas h_sq i j hT'.le) ?_
        refine ENNReal.mul_lt_top (by norm_num) ?_
        refine lt_of_le_of_lt ?_ (h_sq i j T' hT')
        exact le_of_eq (LevyStochCalc.Brownian.Ito.itoIsometry (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j) T' hT'
          (h_meas i j) (h_progMeas i j) (h_sq i j))

/-- **The Picard step has finite `S²` norm on every window.** -/
theorem lintegral_sq_iSup_picardStep_lt_top
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
          h_γ_meas h_γ_progMeas h_γ_sq t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  set A : ℝ → Ω → ℝ := fun t ω => picardStepDrift coeffs X x₀ t ω i with hA
  set B : ℝ → Ω → ℝ := fun t ω =>
    picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i with hB
  set C : ℝ → Ω → ℝ := fun t ω =>
    picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i with hC
  have hunfold : (fun t (ω : Ω) =>
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i)
      = fun t ω => A t ω + B t ω + C t ω := rfl
  have hAm : ∀ t : ℝ, Measurable (A t) := fun t =>
    measurable_picardStep_drift coeffs X x₀ i (hμm i) t
  have hBm : ∀ t : ℝ, Measurable (B t) := fun t =>
    measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i t
  have hCm : ∀ t : ℝ, Measurable (C t) := fun t =>
    measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq i t
  have hsupm : ∀ (D : ℝ → Ω → ℝ), (∀ t, Measurable (D t)) →
      Measurable fun ω => (⨆ m, (‖dyadicRunMax D T' m ω‖₊ : ℝ≥0∞)) ^ 2 :=
    fun D hD => (Measurable.iSup fun m => measurable_enorm_dyadicRunMax hD T' m).pow_const 2
  -- the drift is dominated pathwise
  have hAfin : ∫⁻ ω, (⨆ m, (‖dyadicRunMax A T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_)
      (lintegral_sq_drift_bound_lt_top coeffs X x₀ i hT'.le (hμm i) (hμsq i T' hT'))
    filter_upwards [ae_integrableOn_of_lintegral_sq (P := P) (hμm i) (hμsq i)] with ω hω
    exact pow_le_pow_left' (iSup_dyadicRunMax_drift_le coeffs X x₀ i hT'.le (hω T')) 2
  have hBfin : ∫⁻ ω, (⨆ m, (‖dyadicRunMax B T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ :=
    lintegral_sq_iSup_diffusion_lt_top W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i hT'
  have hCfin : ∫⁻ ω, (⨆ m, (‖dyadicRunMax C T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_sq_iSup_jump_le N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas
      h_γ_sq i hT'.le) ?_
    exact ENNReal.mul_lt_top (by norm_num) (h_γ_sq i T' hT')
  rw [hunfold]
  calc ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω => A t ω + B t ω + C t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ∫⁻ ω, (16 : ℝ≥0∞) * ((⨆ m, (‖dyadicRunMax A T' m ω‖₊ : ℝ≥0∞)) ^ 2
          + (⨆ m, (‖dyadicRunMax B T' m ω‖₊ : ℝ≥0∞)) ^ 2
          + (⨆ m, (‖dyadicRunMax C T' m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        lintegral_mono fun ω => le_trans (pow_le_pow_left' (le_trans
          (iSup_dyadicRunMax_add_le (fun t ω => A t ω + B t ω) C T' ω)
          (add_le_add (iSup_dyadicRunMax_add_le A B T' ω) le_rfl)) 2)
          (sq_add3_le_sixteen_mul _ _ _)
    _ < ⊤ := by
        have hAB : Measurable fun ω : Ω => (⨆ m, (‖dyadicRunMax A T' m ω‖₊ : ℝ≥0∞)) ^ 2
            + (⨆ m, (‖dyadicRunMax B T' m ω‖₊ : ℝ≥0∞)) ^ 2 := (hsupm A hAm).add (hsupm B hBm)
        rw [lintegral_const_mul' _ _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤),
          lintegral_add_left hAB, lintegral_add_left (hsupm A hAm)]
        exact ENNReal.mul_lt_top (by norm_num)
          (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hAfin, hBfin⟩, hCfin⟩)

/-! ### The `S²` bound for the raw self-map -/

/-- **The Picard self-map along a raw state process has finite `S²` norm on every window.** -/
theorem lintegral_sq_iSup_picardSelfMapRaw_lt_top
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
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
        (‖(picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X
          (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  set Y := picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb with hY
  set St := picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ with hSt
  have hZsm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have hZe := lintegral_sq_rawStop_lt_top hZm hZb hT.le
  -- the step at the frozen process has finite `S²` norm
  have hstep : ∀ i : Fin n, ∫⁻ ω,
      (⨆ m, (‖dyadicRunMax (fun t ω => St t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := fun i =>
    lintegral_sq_iSup_picardStep_lt_top W N ℱ hℱW hℱN coeffs
      (fun s ω => Z (min s T) ω) x₀
      (measurable_sigma_rawStop coeffs hReg hZm T)
      (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
      (fun i' j _ hb => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
        (Z := fun s ω => Z (min s T) ω) hZsm hZe i' j hb)
      (measurable_gamma_rawStop coeffs hReg hZm T)
      (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
      (fun i' _ hb => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
        (Z := fun s ω => Z (min s T) ω) hZsm hZe i' hb)
      (measurable_mu_rawStop coeffs hReg hZm T)
      (fun i' b hb => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
        (Z := fun s ω => Z (min s T) ω) hZe i' hb)
      i hT'
  -- the modification agrees at all dyadic points simultaneously
  have hae : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, Y.X (dyadicTime T' p.1 p.2) ω
      = St (dyadicTime T' p.1 p.2) ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun p => picardSelfMapRaw_ae_eq W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
      hZm hZa hZb (dyadicTime T' p.1 p.2)
  have hcad : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ),
      Filter.Tendsto (fun s => Y.X s ω i) (nhdsWithin t (Set.Ioi t)) (nhds (Y.X t ω i)) := by
    filter_upwards [Y.cadlag_paths] with ω hω i t
    exact ((continuous_apply i).tendsto _).comp (hω t).1
  have hStm : ∀ i : Fin n, ∀ t : ℝ, Measurable fun ω => St t ω i := fun i t =>
    measurable_picardStepOnRawStop_slice W N ℱ hℱW hℱN coeffs hReg hLip x₀
      hZm hZa hZb hT.le t i
  calc ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ∫⁻ ω, ∑ i, (⨆ m, (‖dyadicRunMax (fun t ω => St t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae, hcad] with ω hω hc
        refine le_trans (iSup_sum_sq_le (fun t ω => Y.X t ω) T' ω) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [iSup_enorm_eq_iSup_dyadicRunMax hT'.le (hc i)]
        congr 1
        refine iSup_congr fun m => ?_
        rw [enorm_dyadicRunMax, enorm_dyadicRunMax]
        exact iSup_congr fun k => by rw [congrFun (hω (m, (k : ℕ))) i]
    _ = ∑ i, ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω => St t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P :=
        lintegral_finsetSum _ fun i _ =>
          (Measurable.iSup fun m => measurable_enorm_dyadicRunMax (hStm i) T' m).pow_const 2
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun i _ => hstep i

end LevyStochCalc.Ito.Picard

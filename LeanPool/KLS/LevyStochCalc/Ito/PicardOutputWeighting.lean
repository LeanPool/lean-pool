/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardOutputModification

/-!
# Bielecki weighting and the per-component difference bounds

The Bielecki norm with rate `β` dominates the second moment at each time of `[0, T]` after
reweighting by `e^{2βs}`, and the doubly-integrated energy over `[0, t]` by
`e^{2βt}/(2β)`, the factor `1/(2β)` being what makes the Picard rate small for large `β`.
Combined with the Lipschitz bounds on the coefficients this bounds the drift, diffusion and
jump components of the difference of two Picard steps by the energy of the difference of the
two frozen paths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting

omit [MeasurableSpace E] in
/-- The second moment at a single time of `[0, T]`, weighted back up from the Bielecki norm. -/
theorem lintegral_sq_le_bieleckiNorm_sq_weighted (β T : ℝ) (Z : ℝ → Ω → (Fin n → ℝ))
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (Real.exp (2 * β * s)) * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
  set A : ℝ≥0∞ := ∫⁻ ω, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P with hA
  have hle : ENNReal.ofReal (Real.exp (-β * s)) * A ^ ((1 : ℝ) / 2)
      ≤ bieleckiNorm (P := P) β T Z := by
    unfold bieleckiNorm
    exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) s hs
  have hmul : A ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (β * s)) * bieleckiNorm (P := P) β T Z := by
    refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl hle)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  calc A = (A ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by
        rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (ENNReal.ofReal (Real.exp (β * s)) * bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) :=
        pow_le_pow_left' hmul 2
    _ = ENNReal.ofReal (Real.exp (2 * β * s)) * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
        rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
        ring_nf

omit [MeasurableSpace E] in
/-- **The Bielecki weighting step.** The doubly-integrated energy over `[0, t]` is bounded by
`e^{2βt}/(2β)` times the squared Bielecki norm; the factor `1/(2β)` is what makes the Picard
rate small for large `β`. -/
theorem lintegral_lintegral_sq_le_bieleckiNorm_sq {β : ℝ} (hβ : 0 < β) (T : ℝ)
    (Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
          * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  -- the exponential window integral
  have hexp : ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (2 * β * s)) ∂volume
      ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β)) := by
    have hcont : Continuous fun s : ℝ => Real.exp (2 * β * s) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hint : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (2 * β * s))
        (Set.Icc (0 : ℝ) t) volume :=
      (hcont.continuousOn).integrableOn_compact isCompact_Icc
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun s => Real.exp_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hIcc : (∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) ∂volume)
        = ∫ s in (0 : ℝ)..t, Real.exp (2 * β * s) := by
      rw [intervalIntegral.integral_of_le ht.1,
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
    rw [hIcc, intervalIntegral.integral_comp_mul_left Real.exp (ne_of_gt hβ2),
      integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
    rw [div_eq_inv_mul]
    have hexp_pos : (0 : ℝ) < Real.exp (2 * β * t) := Real.exp_pos _
    have hinv : (0 : ℝ) < (2 * β)⁻¹ := by positivity
    nlinarith [hinv, hexp_pos]
  by_cases hB : bieleckiNorm (P := P) β T Z = ⊤
  · rw [hB]
    have hpos : ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [ENNReal.top_pow (by norm_num), ENNReal.mul_top hpos]
    exact le_top
  · have hjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) :=
      Finset.measurable_sum _ fun i _ =>
        ((((measurable_pi_apply i).comp hZ)).nnnorm.coe_nnreal_ennreal).pow_const 2
    rw [MeasureTheory.lintegral_lintegral_swap (μ := P)
      (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      (f := fun (ω : Ω) (s : ℝ) => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) hjoint.aemeasurable]
    calc ∫⁻ s in Set.Icc (0 : ℝ) t, (∫⁻ ω, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (2 * β * s))
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) ∂volume :=
          MeasureTheory.setLIntegral_mono' measurableSet_Icc fun s hs =>
            lintegral_sq_le_bieleckiNorm_sq_weighted β T Z ⟨hs.1, hs.2.trans ht.2⟩
      _ = (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (2 * β * s)) ∂volume)
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) :=
          MeasureTheory.lintegral_mul_const' _ _ (by simp [hB, ENNReal.pow_eq_top_iff])
      _ ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := mul_le_mul' hexp le_rfl

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A Bochner integral of a nonnegative function is below the corresponding lower integral, with
no integrability hypothesis: when the integrand is not integrable the Bochner integral is `0`. -/
theorem ofReal_setIntegral_le_lintegral {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (s : Set ℝ) :
    ENNReal.ofReal (∫ x in s, f x ∂volume) ≤ ∫⁻ x in s, ENNReal.ofReal (f x) ∂volume := by
  have h1 : ENNReal.ofReal (∫ x in s, f x ∂volume) ≤ ‖∫ x in s, f x ∂volume‖ₑ := by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  refine h1.trans ((MeasureTheory.enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_))
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf x)]

omit [MeasurableSpace Ω] [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The window energy in the supremum norm is below the window energy in coordinates. -/
theorem lintegral_window_norm_le_sum {Z : ℝ → Ω → (Fin n → ℝ)} (t : ℝ) (ω : Ω) :
    ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖Z s ω‖ ^ 2 ∂volume)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume := by
  refine (ofReal_setIntegral_le_lintegral (fun x => by positivity) _).trans ?_
  exact lintegral_mono fun s => ofReal_sq_norm_le_sum (Z s ω)

omit [MeasurableSpace E] in
/-- **From a per-time Grönwall estimate to a Bielecki bound.** If the second moment of `U` at
each time of `[0, T]` is at most `C` times the window energy of `Z`, then the Bielecki norm of
`U` is at most `√(C / 2β)` times that of `Z`. The weight cancels exactly, which is why the
constant carries the `1/(2β)` that makes the Picard map a contraction for large `β`. -/
theorem bieleckiNorm_le_of_perTime {β : ℝ} (hβ : 0 < β) {T C : ℝ} (hC : 0 ≤ C)
    (U Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P
        ≤ ENNReal.ofReal C
            * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P) :
    bieleckiNorm (P := P) β T U
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * bieleckiNorm (P := P) β T Z := by
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  refine iSup₂_le fun t ht => ?_
  have hcongr : (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P := by
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => sq_coe_nnnorm_real (U t ω i)
  have hA : (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ ENNReal.ofReal (C / (2 * β)) * ENNReal.ofReal (Real.exp (2 * β * t))
          * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
    calc (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P := hcongr
      _ ≤ ENNReal.ofReal C
            * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P := hbd t ht
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ)) :=
          mul_le_mul' le_rfl (lintegral_lintegral_sq_le_bieleckiNorm_sq hβ T Z hZ ht)
      _ = ENNReal.ofReal (C / (2 * β)) * ENNReal.ofReal (Real.exp (2 * β * t))
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC,
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C / (2 * β))]
          congr 2
          field_simp
  have hsqrt : (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * ENNReal.ofReal (Real.exp (β * t))
          * bieleckiNorm (P := P) β T Z := by
    refine le_trans (ENNReal.rpow_le_rpow hA (by norm_num)) (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    · congr 1
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
        show 2 * β * t * ((1 : ℝ) / 2) = β * t by ring]
    · rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
      norm_num
  calc ENNReal.ofReal (Real.exp (-β * t))
        * (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (-β * t))
          * ((ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2)
            * ENNReal.ofReal (Real.exp (β * t)) * bieleckiNorm (P := P) β T Z) :=
        mul_le_mul' le_rfl hsqrt
    _ = (ENNReal.ofReal (Real.exp (-β * t)) * ENNReal.ofReal (Real.exp (β * t)))
          * ((ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2)
            * bieleckiNorm (P := P) β T Z) := by ring
    _ = (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2)
          * bieleckiNorm (P := P) β T Z := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        simp

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The supremum norm is dominated by the coordinate sum, in `ℝ≥0∞`. -/
theorem sq_coe_nnnorm_le_sum (v : Fin n → ℝ) :
    (‖v‖₊ : ℝ≥0∞) ^ 2 ≤ ∑ i, (‖v i‖₊ : ℝ≥0∞) ^ 2 :=
  (sq_coe_nnnorm v).le.trans (ofReal_sq_norm_le_sum v)

omit [MeasurableSpace E] in
/-- `bieleckiNorm_le_of_perTime` with the window energy measured in the supremum norm, which is
the form the per-component difference estimates of `Ito/Picard.lean` produce. -/
theorem bieleckiNorm_le_of_perTime_sup {β : ℝ} (hβ : 0 < β) {T C : ℝ} (hC : 0 ≤ C)
    (U Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P
        ≤ ENNReal.ofReal C
            * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (‖Z s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :
    bieleckiNorm (P := P) β T U
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * bieleckiNorm (P := P) β T Z :=
  bieleckiNorm_le_of_perTime hβ hC U Z hZ fun t ht =>
    (hbd t ht).trans (mul_le_mul' le_rfl
      (lintegral_mono fun ω => lintegral_mono fun s => sq_coe_nnnorm_le_sum (Z s ω)))

omit [MeasurableSpace E] in
/-- `bieleckiNorm_le_of_perTime` with the window energy as a Bochner integral. -/
theorem bieleckiNorm_le_of_perTime_bochner {β : ℝ} (hβ : 0 < β) {T C : ℝ} (hC : 0 ≤ C)
    (U Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P
        ≤ ENNReal.ofReal C
            * ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖Z s ω‖ ^ 2 ∂volume) ∂P) :
    bieleckiNorm (P := P) β T U
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * bieleckiNorm (P := P) β T Z :=
  bieleckiNorm_le_of_perTime hβ hC U Z hZ fun t ht =>
    (hbd t ht).trans (mul_le_mul' le_rfl
      (lintegral_mono fun ω => lintegral_window_norm_le_sum t ω))

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **The drift half of the per-time contraction estimate.** The per-component bound of
`picardStep_drift_diff_lipschitz_sq_componentwise` needs four integrability facts about the
path; local finiteness of the energies supplies all of them off one null set. -/
theorem ae_drift_diff_sq_bound
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∑ i : Fin n,
        ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ (n : ℝ) * L_μ ^ 2 * t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume := by
  have hXYsq' : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(‖X s ω - Y s ω‖ : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro b hb
    refine lt_of_le_of_lt (le_of_eq ?_) (hXYsq b hb)
    exact lintegral_congr fun ω => lintegral_congr fun s => by rw [nnnorm_norm]
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin n =>
      ae_integrableOn_of_lintegral_sq (hμX i) (hμXsq i),
    MeasureTheory.ae_all_iff.mpr fun i : Fin n =>
      ae_integrableOn_of_lintegral_sq (hμY i) (hμYsq i),
    ae_integrableOn_of_lintegral_sq hXYm hXYsq',
    ae_memLp_two_of_lintegral_sq hXYm hXYsq'] with ω hX hY hXY hXYL2
  calc ∑ i : Fin n,
        ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ ∑ _i : Fin n, L_μ ^ 2 * t
          * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume :=
        Finset.sum_le_sum fun i _ =>
          picardStep_drift_diff_lipschitz_sq_componentwise coeffs hL_μ_nn h_μ_lip X Y x₀ t ht
            ω i (hX i t) (hY i t) (hXY t) (hXYL2 t)
    _ = (n : ℝ) * L_μ ^ 2 * t
          * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

omit [MeasurableSpace E] in
/-- **The drift half of the per-time contraction estimate, in lower-integral form.**
`picardStep_drift_diff_lintegral_sq_bound` with both of its almost-everywhere hypotheses
discharged. -/
theorem drift_diff_lintegral_sq_bound
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_drift (E := E) coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t)
          * ∫⁻ ω, ENNReal.ofReal
              (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
  picardStep_drift_diff_lintegral_sq_bound P coeffs hL_μ_nn h_μ_lip X Y x₀ t ht
    (ae_drift_diff_sq_bound coeffs hL_μ_nn h_μ_lip X Y x₀ hμX hμY hXYm hμXsq hμYsq hXYsq ht)
    (Filter.Eventually.of_forall fun _ =>
      MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => by positivity))

omit [MeasurableSpace E] in
/-- **The diffusion third of the per-time contraction estimate.** The per-component bound of
`picardStep_diffusion_diff_lipschitz_sq_componentwise`, summed over the `n` coordinates. -/
theorem diffusion_diff_lintegral_sq_bound
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_σ : ℝ} (hL_σ_nn : 0 ≤ L_σ)
    (h_σ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin d, (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
        ≤ L_σ ^ 2 * ‖x₁ - x₂‖ ^ 2)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ∑ i : Fin n,
        (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L_σ ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hmeas : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
        - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    ((((measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X i
      t).sub (measurable_picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y
        h_σ_sq_Y i t)).nnnorm).coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_finsetSum _ fun i _ => hmeas i]
  calc ∑ i : Fin n, ∫⁻ ω,
        (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ _i : Fin n, ENNReal.ofReal ((d : ℝ) * L_σ ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        Finset.sum_le_sum fun i _ =>
          picardStep_diffusion_diff_lipschitz_sq_componentwise W ℱ hℱW coeffs hL_σ_nn h_σ_lip
            X Y i h_σ_meas_X h_σ_meas_Y h_σ_progMeas_X h_σ_progMeas_Y h_σ_sq_X h_σ_sq_Y t ht
    _ = ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L_σ ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ← mul_assoc]
        congr 2
        simp

omit [MeasurableSpace Ω] [MeasureTheory.IsProbabilityMeasure P] in
/-- The `γ` clause of `IsLipschitz`, read on a single coordinate along two processes. This is
where the `ℝ≥0∞` form of the clause is used: the `.toReal` form it replaced would give nothing
when the jump energy is infinite. -/
theorem gamma_lip_componentwise {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (i : Fin n) (s : ℝ) (ω : Ω) :
    ∫⁻ e, (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ENNReal.ofReal (L ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 := by
  calc ∫⁻ e, (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ∫⁻ e, (‖coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
        refine lintegral_mono fun e => ?_
        have hco : |coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i|
            ≤ ‖coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e‖ := by
          simpa [Real.norm_eq_abs, Pi.sub_apply] using
            norm_le_pi_norm (coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e) i
        rw [sq_coe_nnnorm_real, sq_coe_nnnorm]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [hco, abs_nonneg (coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i),
          sq_abs (coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i),
          norm_nonneg (coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e)]
    _ ≤ ENNReal.ofReal (L ^ 2 * ‖X s ω - Y s ω‖ ^ 2) := hLip.2.2.2 s (X s ω) (Y s ω)
    _ = ENNReal.ofReal (L ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul (sq_nonneg L), sq_coe_nnnorm]

/-- **The jump third of the per-time contraction estimate.** The per-component bound of
`picardStep_jump_diff_lipschitz_sq_componentwise`, summed over the `n` coordinates. -/
theorem jump_diff_lintegral_sq_bound {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (hX_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (hX_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hY_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (hY_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (hY_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ∑ i : Fin n,
        (‖picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq t ω i
          - picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hmeas : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq t ω i
        - picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i =>
      ((((measurable_picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq i t).sub
        (measurable_picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq i
          t)).nnnorm).coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_finsetSum _ fun i _ => hmeas i]
  calc ∑ i : Fin n, ∫⁻ ω,
        (‖picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq t ω i
          - picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ _i : Fin n, ENNReal.ofReal (L ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        Finset.sum_le_sum fun i _ =>
          picardStep_jump_diff_lipschitz_sq_componentwise N ℱ hℱN coeffs hLip.1 X Y i
            (gamma_lip_componentwise coeffs hLip X Y i)
            hX_meas hX_progMeas hX_sq hY_meas hY_progMeas hY_sq t ht
    _ = ENNReal.ofReal ((n : ℝ) * L ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ← mul_assoc]
        congr 2
        simp

end Weighting

end LevyStochCalc.Ito.Picard

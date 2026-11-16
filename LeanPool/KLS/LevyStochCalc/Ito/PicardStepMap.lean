/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardBieleckiNorm

/-!
# The Picard map for jump-diffusion SDEs

The vector-norm and `ω`-integrated forms of the drift Lipschitz estimate; the Bielecki
exponential-weight calculus `∫_0^t e^{2βs} ds = (e^{2βt} - 1) / (2β)` together with the
weighted-integral bound and the contraction-rate threshold it yields; the joint measurability of
the coefficients `σ` and `γ` composed with a process; and the Picard map `picardStep` itself, the
sum of the initial value, the drift integral, the Brownian component `picardStep_diffusion` and
the compensated-Poisson component `picardStep_jump`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Vector-norm L² Lipschitz bound on the drift step.**

Sum the per-component L² bound over `i : Fin n`:

  `∑ i, ((drift X - drift Y) i)² ≤ n · L_μ² · t · ∫_0^t ‖X-Y‖²`.

This is the squared-Euclidean-norm bound on the drift difference; the
factor `n` comes from summing the per-component bound. Together with
the `E[·]` step (next lemma) this gives the Bielecki-norm Lipschitz
constant for the drift step. -/
lemma picardStep_drift_diff_sum_sq_bound
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω)
    (h_X_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_sq_L2 : MeasureTheory.MemLp
      (fun s => ‖X s ω - Y s ω‖) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ (n : ℝ) * L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by
  -- Per-component bound, summed over Fin n.
  have h_each : ∀ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ L_μ ^ 2 * t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := fun i =>
    picardStep_drift_diff_lipschitz_sq_componentwise
      coeffs hL_μ_nn h_μ_lip X Y x₀ t ht ω i
      (h_X_int i) (h_Y_int i) h_XY_diff_int h_XY_diff_sq_L2
  -- Sum the bounds. Sum of n copies of B = n · B.
  calc (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ ∑ _i : Fin n, L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => h_each i)
    _ = (n : ℝ) * (L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ = (n : ℝ) * L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by ring

omit [MeasurableSpace E] in
/-- **Drift step L² Lipschitz: integrated form (lintegral over ω).**

Take the lintegral of the sum-of-squares pointwise bound from
`picardStep_drift_diff_sum_sq_bound`. Using monotonicity of `∫⁻`
(the lemma `MeasureTheory.lintegral_mono_ae` applied to the pointwise
bound that holds for a.e. ω), we get:

  `∫⁻ ω, (∑ i, ((drift X - drift Y) i)²)
    ≤ n · L_μ² · t · ∫⁻ ω, ∫ s in [0, t], ‖X-Y‖² ds`.

The conversion from the real-valued pointwise bound to the ℝ≥0∞-valued
lintegral form uses `ENNReal.ofReal_le_ofReal` and the nonnegativity
of all the integrands.

This is the operator-level (probability-measure-integrated) bound that
sits one step away from the Bielecki β-norm contraction. -/
lemma picardStep_drift_diff_lintegral_sq_bound
    {n d : ℕ} (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    (_h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    -- Almost-everywhere integrability hypotheses (the pointwise bound only
    -- holds for ω with all integrands well-defined):
    (h_bound_ae : ∀ᵐ ω ∂P,
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        ≤ (n : ℝ) * L_μ ^ 2 * t *
            ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    -- Nonnegativity of the per-ω inner integral (for ENNReal conversion):
    (h_inner_nn : ∀ᵐ ω ∂P, 0 ≤
      ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
        ∫⁻ ω, ENNReal.ofReal
          (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P := by
  -- Monotonicity of lintegral applied to the a.e. bound.
  have h_pointwise_ennreal : ∀ᵐ ω ∂P,
      ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_drift (E := E) coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
          ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := by
    filter_upwards [h_bound_ae, h_inner_nn] with ω h_bd h_inner_nn
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) * L_μ ^ 2 * t)]
    exact ENNReal.ofReal_le_ofReal h_bd
  calc ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
          ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
        MeasureTheory.lintegral_mono_ae h_pointwise_ennreal
    _ = ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki calculus identity.** For `β > 0` and `t ≥ 0`,

  `∫_0^t e^{2βs} ds = (e^{2βt} - 1) / (2β)`.

This is the standard calculus identity that, combined with the
`e^{-2βt}` weight, gives the `1/(2β)` factor in the Bielecki β-norm
contraction estimate. The derivation: antiderivative of `e^{2βs}` is
`e^{2βs}/(2β)`, evaluated between 0 and t. -/
lemma integral_exp_two_beta_Icc
    {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s)
      = (Real.exp (2 * β * t) - 1) / (2 * β) := by
  -- Standard integration via FTC: antiderivative of e^{2βs} is e^{2βs}/(2β).
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by positivity
  have h_two_beta_ne : (2 * β) ≠ 0 := h_two_beta_pos.ne'
  -- Reduce Icc to Ioc (Lebesgue-null endpoint), then Ioc to interval integral.
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [show ∫ s in Set.Ioc (0 : ℝ) t, Real.exp (2 * β * s)
        = ∫ s in (0 : ℝ)..t, Real.exp (2 * β * s) from
    (intervalIntegral.integral_of_le ht).symm]
  -- FTC: ∫_0^t f'(s) ds = f(t) - f(0) where f(s) = e^{2βs}/(2β), f'(s) = e^{2βs}.
  have h_FTC : ∫ s in (0 : ℝ)..t, Real.exp (2 * β * s)
      = Real.exp (2 * β * t) / (2 * β) - Real.exp (2 * β * 0) / (2 * β) := by
    have h_deriv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun u : ℝ => Real.exp (2 * β * u) / (2 * β))
          (Real.exp (2 * β * s)) s := by
      intro s _
      have h₁ : HasDerivAt (fun u : ℝ => 2 * β * u) (2 * β) s := by
        have := (hasDerivAt_id s).const_mul (2 * β)
        simpa using this
      have h₂ : HasDerivAt (fun u : ℝ => Real.exp (2 * β * u))
          (Real.exp (2 * β * s) * (2 * β)) s := h₁.exp
      have h₃ : HasDerivAt (fun u : ℝ => Real.exp (2 * β * u) / (2 * β))
          (Real.exp (2 * β * s) * (2 * β) / (2 * β)) s := h₂.div_const (2 * β)
      have h_simp : Real.exp (2 * β * s) * (2 * β) / (2 * β) = Real.exp (2 * β * s) := by
        field_simp
      rw [← h_simp]
      exact h₃
    -- Integrability of the integrand on [0, t].
    have h_int_cont : Continuous (fun s : ℝ => Real.exp (2 * β * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have h_int : IntervalIntegrable (fun s : ℝ => Real.exp (2 * β * s))
        MeasureTheory.volume 0 t := h_int_cont.intervalIntegrable 0 t
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
  rw [h_FTC]
  -- Simplify Real.exp (2 * β * 0) = 1.
  have h_zero : Real.exp (2 * β * 0) = 1 := by rw [mul_zero, Real.exp_zero]
  rw [h_zero]
  field_simp

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki weight bound.** For `β > 0` and `t ≥ 0`,

  `e^{-2βt} · (e^{2βt} - 1) / (2β) = (1 - e^{-2βt}) / (2β) ≤ 1 / (2β)`.

This is the key bound that makes the Bielecki β-norm a contraction:
the weighted integral `∫_0^t e^{-2βt+2βs} ds` is uniformly bounded
above by `1/(2β)` regardless of `t`. -/
lemma bielecki_weight_bound
    {β : ℝ} (hβ : 0 < β) {t : ℝ} (_ht : 0 ≤ t) :
    Real.exp (-(2 * β * t)) * ((Real.exp (2 * β * t) - 1) / (2 * β))
      ≤ 1 / (2 * β) := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by positivity
  have h_two_beta_ne : (2 * β) ≠ 0 := h_two_beta_pos.ne'
  -- Step 1: expand e^{-2βt} · (e^{2βt} - 1) = 1 - e^{-2βt}.
  have h_exp_mul_neg : Real.exp (-(2 * β * t)) * Real.exp (2 * β * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h_step1 : Real.exp (-(2 * β * t)) * ((Real.exp (2 * β * t) - 1) / (2 * β))
      = (1 - Real.exp (-(2 * β * t))) / (2 * β) := by
    rw [mul_div_assoc', mul_sub, h_exp_mul_neg, mul_one]
  rw [h_step1]
  -- Step 2: (1 - e^{-2βt}) ≤ 1 since e^{-2βt} ≥ 0.
  have h_exp_neg_nn : 0 ≤ Real.exp (-(2 * β * t)) := Real.exp_nonneg _
  have h_num_bound : 1 - Real.exp (-(2 * β * t)) ≤ 1 := by linarith
  -- Divide both sides by 2β > 0.
  exact div_le_div_of_nonneg_right h_num_bound h_two_beta_pos.le |>.trans_eq rfl

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki integration interchange.** For `β > 0`, `t ≥ 0`, and a
non-negative `L¹` function `g : ℝ → ℝ`,

  `e^{-2βt} · ∫_0^t e^{2βs} · g(s) ds ≤ (⨆_{s ≤ t} g(s)) · (1/(2β))`,

assuming `g` is bounded by a constant `M`. The bound `M · 1/(2β)`
follows from `∫_0^t e^{2βs} M ds = M · (e^{2βt}-1)/(2β)` times the
weight `e^{-2βt}`.

This is the key "sup pull-out + Bielecki contraction" lemma used in the
Picard argument. -/
lemma bielecki_weighted_integral_bound
    {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t)
    {M : ℝ} (hM_nn : 0 ≤ M)
    (g : ℝ → ℝ)
    (_hg_nn : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)), 0 ≤ g s)
    (hg_bound : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)), g s ≤ M)
    (hg_int : MeasureTheory.IntegrableOn
      (fun s => Real.exp (2 * β * s) * g s) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    Real.exp (-(2 * β * t)) *
        ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * g s
      ≤ M * (1 / (2 * β)) := by
  -- Bound the integrand: e^{2βs} · g(s) ≤ e^{2βs} · M.
  have h_exp_nn : ∀ s : ℝ, 0 ≤ Real.exp (2 * β * s) := fun s => Real.exp_nonneg _
  have h_pt_bound : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)),
      Real.exp (2 * β * s) * g s ≤ Real.exp (2 * β * s) * M := by
    filter_upwards [hg_bound] with s h_bd
    exact mul_le_mul_of_nonneg_left h_bd (h_exp_nn s)
  -- Integrate the bound.
  have h_int_bound : ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * g s
      ≤ ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * M := by
    refine MeasureTheory.integral_mono_ae hg_int ?_ h_pt_bound
    -- Integrability of e^{2βs} · M on [0, t].
    have h_exp_cont : Continuous (fun s : ℝ => Real.exp (2 * β * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have h_exp_int : MeasureTheory.IntegrableOn
        (fun s : ℝ => Real.exp (2 * β * s)) (Set.Icc (0 : ℝ) t) MeasureTheory.volume :=
      h_exp_cont.integrableOn_Icc
    exact h_exp_int.mul_const M
  -- Compute ∫_0^t e^{2βs} · M ds = M · (e^{2βt} - 1)/(2β).
  have h_const_int : ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * M
      = M * ((Real.exp (2 * β * t) - 1) / (2 * β)) := by
    rw [show (fun s => Real.exp (2 * β * s) * M) = (fun s => M * Real.exp (2 * β * s)) from
      funext fun s => by ring]
    rw [MeasureTheory.integral_const_mul, integral_exp_two_beta_Icc hβ ht]
  -- Multiply by e^{-2βt} on both sides (both nonneg).
  have h_exp_neg_nn : 0 ≤ Real.exp (-(2 * β * t)) := Real.exp_nonneg _
  have h_mul_LHS_RHS : Real.exp (-(2 * β * t)) *
        ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * g s
      ≤ Real.exp (-(2 * β * t)) * (M * ((Real.exp (2 * β * t) - 1) / (2 * β))) := by
    refine mul_le_mul_of_nonneg_left ?_ h_exp_neg_nn
    rw [h_const_int] at h_int_bound
    exact h_int_bound
  refine h_mul_LHS_RHS.trans ?_
  -- e^{-2βt} · (M · (e^{2βt}-1)/(2β)) = M · (e^{-2βt} · (e^{2βt}-1)/(2β))
  --                                 ≤ M · 1/(2β)   by bielecki_weight_bound.
  rw [show Real.exp (-(2 * β * t)) * (M * ((Real.exp (2 * β * t) - 1) / (2 * β)))
      = M * (Real.exp (-(2 * β * t)) * ((Real.exp (2 * β * t) - 1) / (2 * β))) by ring]
  exact mul_le_mul_of_nonneg_left (bielecki_weight_bound hβ ht) hM_nn

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki weight bound — variant with `n L² T` constant.**

For the drift step of the Picard map with Lipschitz constant `L_μ`,
state dimension `n`, and time horizon `T`, the Bielecki-norm
contraction constant is `n L_μ² T / (2β)`. This wraps the
`bielecki_weight_bound` lemma in the specific multiplicative form that
arises from the drift L²-Lipschitz analysis. -/
lemma bielecki_drift_contraction_factor
    (n : ℕ) {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    {β T : ℝ} (hβ : 0 < β) (_hT : 0 ≤ T) :
    (n : ℝ) * L_μ ^ 2 * T * (1 / (2 * β)) =
      (n : ℝ) * L_μ ^ 2 * T / (2 * β) := by
  -- Algebraic equality; the substance is the bound's USE in the contraction.
  -- This lemma exposes the canonical form for downstream Banach-fixed-point use.
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by positivity
  field_simp

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki contraction threshold.** The drift step is a Bielecki-norm
contraction iff `β > n L_μ² T / 2`, i.e., the Picard contraction
rate `n L_μ² T / (2β) < 1`.

This lemma asserts the threshold and rate explicitly so downstream
Picard-iteration callers can plug in `β = n L_μ² T` (giving rate `1/2`,
a strict contraction). -/
lemma bielecki_contraction_rate_lt_one
    (n : ℕ) {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    {β T : ℝ} (hT_pos : 0 < T)
    (h_β_threshold : (n : ℝ) * L_μ ^ 2 * T < 2 * β) :
    (n : ℝ) * L_μ ^ 2 * T / (2 * β) < 1 := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by
    have h_LHS_nn : 0 ≤ (n : ℝ) * L_μ ^ 2 * T :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg L_μ)) hT_pos.le
    linarith
  rw [div_lt_one h_two_beta_pos]
  exact h_β_threshold

omit [MeasurableSpace E] in
/-- **Joint measurability of σ-along-X.** If `X : ℝ → Ω → (Fin n → ℝ)`
is jointly measurable and `σ : ℝ → (Fin n → ℝ) → Fin n → Fin d → ℝ`
is jointly measurable in `(s, x)`, then the composite
`(s, ω) ↦ σ s (X s ω) i j` is jointly measurable on `ℝ × Ω`.

This is the structural lemma that lets the σ component of the Picard
step be passed to `MultidimBrownianMotion.stochasticIntegral` as a
valid integrand. -/
lemma sigma_along_X_measurable
    {n d : ℕ}
    (σ : ℝ → (Fin n → ℝ) → Fin n → Fin d → ℝ)
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X))
    (hσ_meas : Measurable (Function.uncurry σ))
    (i : Fin n) (j : Fin d) :
    Measurable (fun (p : Ω × ℝ) => σ p.2 (X p.2 p.1) i j) := by
  -- Decompose: (ω, s) ↦ σ s (X s ω) i j
  --          = (((s, X s ω) → σ s (X s ω)) → σ s (X s ω) i j) ∘ (p ↦ (p.2, X p.2 p.1))
  -- Each component is measurable.
  -- Step 1: (p : Ω × ℝ) ↦ X p.2 p.1 is measurable via hX_meas.
  have h_X_swap_meas : Measurable (fun p : Ω × ℝ => X p.2 p.1) := by
    have : (fun p : Ω × ℝ => X p.2 p.1)
        = (Function.uncurry X) ∘ (fun p : Ω × ℝ => (p.2, p.1)) := by
      funext p; rfl
    rw [this]
    exact hX_meas.comp (measurable_snd.prodMk measurable_fst)
  -- Step 2: (p : Ω × ℝ) ↦ (p.2, X p.2 p.1) is measurable (product of measurable).
  have h_prod_meas : Measurable (fun p : Ω × ℝ => (p.2, X p.2 p.1)) :=
    measurable_snd.prodMk h_X_swap_meas
  -- Step 3: (s, x) ↦ σ s x is measurable (hσ_meas via Function.uncurry).
  -- Then take component (i, j).
  have h_eval_ij : Measurable (fun (m : Fin n → Fin d → ℝ) => m i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  -- σ along the path:
  --   σ p.2 (X p.2 p.1) i j = (h_eval_ij ∘ Function.uncurry σ ∘ h_prod_meas).
  exact h_eval_ij.comp (hσ_meas.comp h_prod_meas)

/-- **Joint measurability of γ-along-X.** Analog of `sigma_along_X_measurable`
for the jump coefficient `γ : ℝ → (Fin n → ℝ) → E → Fin n → ℝ`.

The composite `(ω, s, e) ↦ γ s (X s ω) e i` is jointly measurable on
`Ω × ℝ × E`, given joint measurability of X and γ. This is what makes
the γ component of the Picard step well-typed for the
`Compensated.stochasticIntegral` integrand. -/
lemma gamma_along_X_measurable
    {n : ℕ}
    (γ : ℝ → (Fin n → ℝ) → E → Fin n → ℝ)
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X))
    (hγ_meas : Measurable
      (fun (p : ℝ × (Fin n → ℝ) × E) => γ p.1 p.2.1 p.2.2))
    (i : Fin n) :
    Measurable (fun (p : Ω × ℝ × E) => γ p.2.1 (X p.2.1 p.1) p.2.2 i) := by
  -- The composite extracts (ω, s, e), evaluates X at (ω, s), and feeds (s, X s ω, e) into γ.
  -- Step 1: (p : Ω × ℝ × E) ↦ X p.2.1 p.1 measurable.
  have h_X_along_meas : Measurable (fun p : Ω × ℝ × E => X p.2.1 p.1) := by
    have : (fun p : Ω × ℝ × E => X p.2.1 p.1)
        = (Function.uncurry X) ∘ (fun p : Ω × ℝ × E => (p.2.1, p.1)) := by
      funext p; rfl
    rw [this]
    exact hX_meas.comp ((measurable_snd.comp measurable_id).fst.prodMk measurable_fst)
  -- Step 2: (p : Ω × ℝ × E) ↦ (p.2.1, X p.2.1 p.1, p.2.2) measurable.
  have h_triple_meas : Measurable
      (fun p : Ω × ℝ × E => (p.2.1, X p.2.1 p.1, p.2.2)) := by
    exact ((measurable_snd.comp measurable_id).fst.prodMk
      (h_X_along_meas.prodMk (measurable_snd.comp measurable_id).snd))
  -- Step 3: γ evaluation gives Fin n → ℝ; take component i.
  have h_eval_i : Measurable (fun (v : Fin n → ℝ) => v i) := measurable_pi_apply i
  exact h_eval_i.comp (hγ_meas.comp h_triple_meas)

/-- **Picard map diffusion component (σ row i along X).**

For row `i : Fin n`, the diffusion component is
`∫_0^t (σ(s, X_s) i) · dW_s`, i.e., the multidim Brownian Itô integral
of `Z_i(s, ω) := fun j => σ(s, X(s,ω)) i j` against `W`.

Built using `MultidimBrownianMotion.stochasticIntegral`. The hypotheses
`h_meas`, `h_progMeas`, `h_sq_int_global` propagate from joint-measurability
+ progressive-measurability + L²-boundedness of σ along X, which in turn
follow from the corresponding hypotheses on X and σ. -/
noncomputable def picardStep_diffusion
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    -- Per-row joint measurability of σ along X.
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    -- Progressive measurability wrt W component j's natural filtration.
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i j))
    -- Per-row, per-component L² boundedness on every finite horizon.
    (h_sq_int_global : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
    W ℱ hℱW
    (fun s ω' => fun j => coeffs.σ s (X s ω') i j)
    (h_meas i) (h_progMeas i) (h_sq_int_global i) t ω

/-- **Picard map jump component (γ row i along X compensated-Poisson integral).**

For row `i : Fin n`, the jump component is
`∫_0^t ∫_E γ(s, X_s, e) i Ñ(ds, de)`, i.e., the compensated-Poisson
integral of `(s, e, ω) ↦ γ(s, X(s,ω), e) i` against `Ñ`.

Built using `Compensated.stochasticIntegral`. The hypotheses
`h_meas`, `h_progMeas`, `h_sq` propagate from joint Ω×ℝ×E-measurability
+ progressive-measurability + L²-boundedness of γ along X. -/
noncomputable def picardStep_jump
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    -- Per-row joint Ω×ℝ×E measurability.
    (h_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    -- Per-row progressive measurability wrt N's natural filtration.
    (h_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X s ω) e i))
    -- Per-row L² boundedness on every finite horizon.
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
    (fun ω' s e => coeffs.γ s (X s ω') e i)
    (h_meas i) (h_progMeas i) (h_sq i) t ω

/-- **The full Picard map.** Combines the drift, diffusion (Brownian),
and jump (compensated-Poisson) components:

  `Φ X t ω = x₀ + ∫_0^t μ(s, X_s) ds + ∫_0^t σ(s, X_s) dW_s
          + ∫_0^t ∫_E γ(s, X_s, e) Ñ(ds, de)`

The `x₀ +` is already in `picardStep_drift`; here we add the diffusion
and jump components.

This is the literature Picard map for the jump-diffusion SDE (Applebaum
6.2.9 / Ikeda-Watanabe IV). The hypotheses required to make all three
components well-typed are bundled as explicit parameters. -/
noncomputable def picardStep
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    -- σ-side hypotheses for the Brownian integral.
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- γ-side hypotheses for the compensated-Poisson integral.
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  picardStep_drift coeffs X x₀ t ω
    + picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω
    + picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω

/-! ## Map of the contraction argument

The Picard map `picardStep` and its three components are defined above,
together with the drift-component Lipschitz estimates. The rest of the
argument is:

1. `integral_sq_le_mul_integral_sq_on_Icc` (above) — the `L²`
   Cauchy–Schwarz bound `(∫_0^t f)² ≤ t · ∫_0^t f²` behind the
   Bielecki-norm contraction estimate.
2. `picardStep_diffusion_diff_lipschitz_sq_componentwise` — the Lipschitz
   bound of the Brownian component, via the `L²`-isometry of the integral
   difference (`itoIsometry_diff_brownian`) and the Lipschitz hypothesis on
   `σ`.
3. `picardStep_jump_diff_lipschitz_sq_componentwise` — the Lipschitz bound
   of the compensated-Poisson component, via `itoIsometry_diff_compensated`
   and the Lipschitz hypothesis on `γ`.
4. `picardStep_bielecki_contraction`, `picardStep_bielecki_contraction_tight`
   — the map is a Bielecki contraction once `β` is large relative to the
   Lipschitz constant; `bieleckiNorm_picardStep_diff_le`
   (`Ito/PicardOutput.lean`) is the form the well-posedness proof uses, and
   `bieleckiNorm_picardSelfMap_diff_le` (`Ito/PicardContraction.lean`) its
   transfer to the self-map of the process space.
5. `picardIter`, `picardLimit` (`Ito/PicardContraction.lean`, on
   `bieleckiLimit` of `Ito/PicardLimit.lean`) and
   `picardSelfMapRaw_isFixedPoint` — the iterates converge and the limit is
   a fixed point.
6. `exists_solvesOn`, `ae_eq_of_solvesOn` (`Ito/PicardWindow.lean`),
   `exists_globalSolution` (`Ito/PicardGlobal.lean`) and
   `exists_jumpDiffusion_unique_of_solvesOn` (`Ito/PicardWellPosed.lean`)
   — the fixed point solves the SDE on each window, is unique there, and
   the windows glue to a strong solution on `[0, ∞)`; `Ito/PicardFixedPoint.lean`
   restates the result as `JumpDiffusion.exists_unique`. -/

end LevyStochCalc.Ito.Picard

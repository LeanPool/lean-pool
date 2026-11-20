/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0; a proof
-- supplies the measurability witness that the Mathlib v4.35.0 `MemLp` finiteness lemma requires.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2CompletionExistence

/-!
# Brownian Itô integral: increment expansions and the intermediate-time isometry

Diagonal and off-diagonal expectations of products of Brownian increments against
adapted weights, the Bochner expansion of the square of a simple integral clamped
at an intermediate time, and the isometry
`∫⁻ ‖simpleIntegral W H t‖₊² = ∫⁻ ∫⁻_{[0, t]} ‖H.eval‖₊²` it gives for every
intermediate time `t`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **General two-time diagonal (`L²` second moment of a single increment).**
For `0 ≤ a < b` and an `F_a`-measurable `ξ`,
`∫⁻ ‖ξ·(W_b − W_a)‖² = (b − a)·∫⁻ ‖ξ‖²`. Generalizes `simpleIntegral_diagonal`
from partition points to arbitrary times — the foundational piece of the
intermediate-time isometry needed for the coherent `F` (cited result #5). Proof:
`ξ ⟂ (W_b − W_a)` (independence of an `F_a`-measurable r.v. from the future
increment, `joint_increment_independent`), then the Gaussian second moment
`∫⁻ ‖W_b − W_a‖² = b − a`. -/
lemma diagonal_increment_lint
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (ξ : Ω → ℝ)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) ξ) :
    ∫⁻ ω, (‖ξ ω * (W.W b ω - W.W a ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (b - a) * ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW_def
  have h_ξ_meas : Measurable ξ :=
    (h_adapt.mono (ℱ.le a)).measurable
  have h_ΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have h_nn_meas : Measurable (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) := by fun_prop
  have h_indep_F_ΔW := hℱ.indep ha hab
  have h_ξ_comap_le : MeasurableSpace.comap ξ inferInstance ≤ ℱ a :=
    h_adapt.measurable.comap_le
  have h_indep_ξ_ΔW : ProbabilityTheory.IndepFun ξ ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ a] u := h_ξ_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW
    exact h_indep_F_ΔW u v hu_F hv
  have h_indep_norm_sq :
      ProbabilityTheory.IndepFun
        (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2) (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2) P := by
    have := h_indep_ξ_ΔW.comp h_nn_meas h_nn_meas
    simpa [Function.comp_def] using this
  have h_norm_mul : ∀ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2
      = (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 * (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω
    rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
        = (‖ξ ω‖₊ : ℝ≥0∞) * (‖ΔW ω‖₊ : ℝ≥0∞) from by
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) = ((‖ξ ω * ΔW ω‖₊ : ℝ≥0) : ℝ≥0∞) from rfl]
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0) = ‖ξ ω‖₊ * ‖ΔW ω‖₊ from nnNorm_mul _ _]
      push_cast; rfl]
    ring
  rw [show (∫⁻ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 * (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P from
    MeasureTheory.lintegral_congr h_norm_mul]
  rw [show (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 * (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2)
      = (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2) * (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2) from rfl]
  have h_ξ_norm_sq_meas : Measurable (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2) := by fun_prop
  have h_ΔW_norm_sq_meas : Measurable (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2) := by fun_prop
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      h_ξ_norm_sq_meas h_ΔW_norm_sq_meas h_indep_norm_sq]
  have h_ΔW_sq_int : ∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (b - a) := by
    rw [show (∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 ∂(P.map ΔW) from
      (MeasureTheory.lintegral_map h_nn_meas h_ΔW_meas).symm]
    rw [W.increment_gaussian ha hab]
    have h_int_sq : MeasureTheory.Integrable (fun x : ℝ => x ^ 2)
        (ProbabilityTheory.gaussianReal 0 ⟨b - a, by linarith⟩) := by
      have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
          (ProbabilityTheory.gaussianReal 0 ⟨b - a, by linarith⟩) :=
        ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp)
      have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
      convert h using 1; ext x; change x ^ 2 = ‖x‖ ^ 2; rw [Real.norm_eq_abs, sq_abs]
    have h_nn_sq : 0 ≤ᵐ[ProbabilityTheory.gaussianReal 0 ⟨b - a, by linarith⟩]
        fun x : ℝ => x ^ 2 := by filter_upwards with x; positivity
    have h_norm_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := by
      intro x
      rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [show ‖x‖ ^ 2 = x ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show (∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 ∂(ProbabilityTheory.gaussianReal 0
              ⟨b - a, by linarith⟩))
        = ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(ProbabilityTheory.gaussianReal 0
              ⟨b - a, by linarith⟩) from
      MeasureTheory.lintegral_congr (fun x => h_norm_eq x)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sq h_nn_sq]
    rw [LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨b - a, by linarith⟩]
    rfl
  rw [h_ΔW_sq_int, mul_comm]

/-- **General off-diagonal vanishing.** For two increments with the second
strictly after the first (`a₁ < b₁ ≤ a₂ < b₂`) and `Fᵢ`-measurable coefficients,
`∫ (ξ₁·(W_{b₁}−W_{a₁}))·(ξ₂·(W_{b₂}−W_{a₂})) = 0`. Generalizes
`simpleIntegral_offDiagonal` from partition points to arbitrary times. Proof:
`f := ξ₁·ΔW₁·ξ₂` is `F_{a₂}`-measurable, `ΔW₂ ⟂ F_{a₂}` with `𝔼[ΔW₂] = 0`, so
`𝔼[f·ΔW₂] = 𝔼[f]·0 = 0`. -/
lemma offDiagonal_increment_integral_zero
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₂) :
    ∫ ω, (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω)) ∂P = 0 := by
  set ΔW₁ : Ω → ℝ := fun ω => W.W b₁ ω - W.W a₁ ω with hΔW₁_def
  set ΔW₂ : Ω → ℝ := fun ω => W.W b₂ ω - W.W a₂ ω with hΔW₂_def
  have ha₂_nn : 0 ≤ a₂ := le_trans ha₁ (le_trans (le_of_lt h₁) h₁₂)
  have ha₁a₂ : a₁ ≤ a₂ := le_trans (le_of_lt h₁) h₁₂
  have hξ₁meas : Measurable ξ₁ :=
    (hadapt₁.mono (ℱ.le a₁)).measurable
  have hξ₂meas : Measurable ξ₂ :=
    (hadapt₂.mono (ℱ.le a₂)).measurable
  set f : Ω → ℝ := fun ω => ξ₁ ω * ΔW₁ ω * ξ₂ ω with hf_def
  have h_factored : (fun ω => (ξ₁ ω * ΔW₁ ω) * (ξ₂ ω * ΔW₂ ω)) = fun ω => f ω * ΔW₂ ω := by
    funext ω; simp only [hf_def]; ring
  rw [show (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω)))
        = fun ω => f ω * ΔW₂ ω from h_factored]
  have h_Wb₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W b₁) :=
    ((hℱ.measurable b₁).stronglyMeasurable).mono
      (ℱ.mono h₁₂)
  have h_Wa₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W a₁) :=
    ((hℱ.measurable a₁).stronglyMeasurable).mono
      (ℱ.mono (le_trans (le_of_lt h₁) h₁₂))
  have h_ξ₁_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₁ :=
    hadapt₁.mono (ℱ.mono ha₁a₂)
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) f :=
    (h_ξ₁_F_meas.mul (h_Wb₁_meas.sub h_Wa₁_meas)).mul hadapt₂
  have h_indep_F_ΔW₂ := hℱ.indep ha₂_nn h₂
  have h_f_meas : Measurable f :=
    (hξ₁meas.mul ((W.measurable_eval b₁).sub (W.measurable_eval a₁))).mul hξ₂meas
  have h_ΔW₂_meas : Measurable ΔW₂ := (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have h_f_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ a₂ :=
    h_f_F_meas.measurable.comap_le
  have h_indep_f_ΔW₂ : ProbabilityTheory.IndepFun f ΔW₂ P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ a₂] u := h_f_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW₂
    exact h_indep_F_ΔW₂ u v hu_F hv
  have h_ΔW₂_mean : ∫ ω, ΔW₂ ω ∂P = 0 := by
    rw [show ∫ ω, ΔW₂ ω ∂P = ∫ x, x ∂(P.map ΔW₂) from
      (MeasureTheory.integral_map h_ΔW₂_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (id : ℝ → ℝ) _)).symm]
    rw [W.increment_gaussian ha₂_nn h₂]
    exact ProbabilityTheory.integral_id_gaussianReal
  rw [show (fun ω => f ω * ΔW₂ ω) = f * ΔW₂ from rfl]
  rw [h_indep_f_ΔW₂.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW₂_meas.aestronglyMeasurable]
  rw [h_ΔW₂_mean, mul_zero]

/-- **Square-integrability of a Brownian increment** over `[s,t]` (general `s<t`).
A non-`private` companion of `ItoSimple`'s helper, needed below. -/
lemma increment_sq_integrable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    MeasureTheory.Integrable (fun ω => (W.W t ω - W.W s ω) ^ 2) P := by
  have h_meas : Measurable (fun ω => W.W t ω - W.W s ω) :=
    (W.measurable_eval t).sub (W.measurable_eval s)
  rw [show (fun ω => (W.W t ω - W.W s ω) ^ 2)
        = (fun x : ℝ => x ^ 2) ∘ (fun ω => W.W t ω - W.W s ω) from rfl]
  rw [(MeasureTheory.integrable_map_measure (μ := P) (f := fun ω => W.W t ω - W.W s ω)
      (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        (P.map (fun ω => W.W t ω - W.W s ω))) h_meas.aemeasurable).symm]
  rw [W.increment_gaussian hs hst]
  have h := (ProbabilityTheory.memLp_id_gaussianReal' (μ := 0)
    (v := ⟨t - s, by linarith⟩) 2 (by simp)).integrable_norm_pow
    (p := 2) (by norm_num)
  convert h using 1; ext x; change x ^ 2 = ‖x‖ ^ 2; rw [Real.norm_eq_abs, sq_abs]

/-- **General two-time diagonal, Bochner form.** `∫ (ξ·(W_b−W_a))² = (b−a)·∫ ξ²`
for `0 ≤ a < b`, `ξ` `F_a`-measurable and bounded (`|ξ| ≤ M`). Bochner companion
of `diagonal_increment_lint`, for the Bochner sum-expansion in the isometry. -/
lemma diagonal_increment_bochner
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (ξ : Ω → ℝ)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) ξ)
    (M : ℝ) (h_bound : ∀ ω, |ξ ω| ≤ M) :
    ∫ ω, (ξ ω * (W.W b ω - W.W a ω)) ^ 2 ∂P = (b - a) * ∫ ω, (ξ ω) ^ 2 ∂P := by
  have hξ_meas : Measurable ξ :=
    (h_adapt.mono (ℱ.le a)).measurable
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖ ^ 2 = x ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  have h_lint := diagonal_increment_lint W ℱ hℱ ha hab ξ h_adapt
  rw [show (∫⁻ ω, (‖ξ ω * (W.W b ω - W.W a ω)‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((ξ ω * (W.W b ω - W.W a ω)) ^ 2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  rw [show (∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P) = ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  have h_xi_sq_bound : ∀ ω, (ξ ω) ^ 2 ≤ M ^ 2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (h_bound ω)) (le_of_abs_le (h_bound ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (ξ ω) ^ 2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M ^ 2)
      (MeasureTheory.integrable_const _) (hξ_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h_xi_sq_bound ω
  have h_int_ΔW_sq := increment_sq_integrable W ha hab
  have h_int_aN_sq : MeasureTheory.Integrable
      (fun ω => (ξ ω * (W.W b ω - W.W a ω)) ^ 2) P := by
    rw [show (fun ω => (ξ ω * (W.W b ω - W.W a ω)) ^ 2)
            = fun ω => (ξ ω) ^ 2 * (W.W b ω - W.W a ω) ^ 2 from by funext ω; ring]
    refine MeasureTheory.Integrable.bdd_mul (c := M ^ 2) h_int_ΔW_sq
      (hξ_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (ξ ω) ^ 2 := by filter_upwards with ω; positivity
  have h_nn_aN_sq : 0 ≤ᵐ[P] fun ω => (ξ ω * (W.W b ω - W.W a ω)) ^ 2 := by
    filter_upwards with ω; positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_aN_sq h_nn_aN_sq] at h_lint
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq] at h_lint
  have h_dt_nn : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt hab)
  rw [show ENNReal.ofReal (b - a) * ENNReal.ofReal (∫ ω, (ξ ω) ^ 2 ∂P)
          = ENNReal.ofReal ((b - a) * ∫ ω, (ξ ω) ^ 2 ∂P) from
    (ENNReal.ofReal_mul h_dt_nn).symm] at h_lint
  exact (ENNReal.ofReal_eq_ofReal_iff
    (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _))
    (mul_nonneg h_dt_nn (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)))).mp h_lint

/-- **Integrability of a cross product of two (possibly degenerate) increments.**
`(ξ₁·(W_{b₁}−W_{a₁}))·(ξ₂·(W_{b₂}−W_{a₂}))` is integrable for bounded `ξ`s and
`0 ≤ aₖ ≤ bₖ`. Degenerate (`aₖ = bₖ`) increments are `0`. Used (with clamped
endpoints) in the intermediate-time Bochner expansion. -/
lemma cross_increment_integrable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (hab₁ : a₁ ≤ b₁) (ha₂ : 0 ≤ a₂) (hab₂ : a₂ ≤ b₂)
    (ξ₁ ξ₂ : Ω → ℝ) (hξ₁meas : Measurable ξ₁) (hξ₂meas : Measurable ξ₂)
    (M₁ : ℝ) (hbd₁ : ∀ ω, |ξ₁ ω| ≤ M₁) (M₂ : ℝ) (hbd₂ : ∀ ω, |ξ₂ ω| ≤ M₂) :
    MeasureTheory.Integrable
      (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) P := by
  have h_meas₁ : Measurable (fun ω => W.W b₁ ω - W.W a₁ ω) :=
    (W.measurable_eval b₁).sub (W.measurable_eval a₁)
  have h_meas₂ : Measurable (fun ω => W.W b₂ ω - W.W a₂ ω) :=
    (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have sq_int : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      MeasureTheory.Integrable (fun ω => (W.W b ω - W.W a ω) ^ 2) P := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with h_eq | h_lt
    · rw [show (fun ω => (W.W b ω - W.W a ω) ^ 2) = fun _ => (0 : ℝ) from by
        funext ω; rw [← h_eq]; ring]
      exact MeasureTheory.integrable_const 0
    · exact increment_sq_integrable W ha h_lt
  have h_int_i_sq := sq_int ha₁ hab₁
  have h_int_j_sq := sq_int ha₂ hab₂
  have h_int_ΔW : MeasureTheory.Integrable
      (fun ω => (W.W b₁ ω - W.W a₁ ω) * (W.W b₂ ω - W.W a₂ ω)) P := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.add (h_int_i_sq.const_mul (1 / 2 : ℝ))
        (h_int_j_sq.const_mul (1 / 2 : ℝ))) (h_meas₁.mul h_meas₂).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    have h : |W.W b₁ ω - W.W a₁ ω| * |W.W b₂ ω - W.W a₂ ω|
        ≤ (1 / 2) * (W.W b₁ ω - W.W a₁ ω) ^ 2 + (1 / 2) * (W.W b₂ ω - W.W a₂ ω) ^ 2 := by
      nlinarith [sq_abs (W.W b₁ ω - W.W a₁ ω), sq_abs (W.W b₂ ω - W.W a₂ ω),
        sq_nonneg (|W.W b₁ ω - W.W a₁ ω| - |W.W b₂ ω - W.W a₂ ω|)]
    exact h
  rw [show (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω)))
        = fun ω => (ξ₁ ω * ξ₂ ω)
            * ((W.W b₁ ω - W.W a₁ ω) * (W.W b₂ ω - W.W a₂ ω)) from by funext ω; ring]
  refine MeasureTheory.Integrable.bdd_mul (c := |M₁| * |M₂|) h_int_ΔW
    (hξ₁meas.mul hξ₂meas).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hbd₁ ω) (le_abs_self _)) (le_trans (hbd₂ ω) (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

/-- **Clamped Bochner second moment of `simpleIntegral W H t`.** For `0 ≤ t`,
`∫ (simpleIntegral W H t)² = ∑ᵢ (pᵢ₊₁∧t − pᵢ∧t)·∫ ξᵢ²`. Cross terms vanish
(`offDiagonal_increment_integral_zero`), diagonal terms give the clamped lengths
(`diagonal_increment_bochner`); degenerate clamped increments are `0`. The core
of the intermediate-time isometry for the coherent L²-Itô integral (#5). -/
lemma simpleIntegral_sq_bochner_clamped
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫ ω, (simpleIntegral W H t ω) ^ 2 ∂P
      = ∑ i : Fin H.N,
        (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
          * ∫ ω, (H.ξ i ω) ^ 2 ∂P := by
  have h_part_nn : ∀ i : Fin H.N, 0 ≤ H.partition i.castSucc := fun i => by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  set term : Fin H.N → Ω → ℝ := fun i ω =>
    H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
      - W.W (min (H.partition i.castSucc) t) ω) with hterm
  have h_a_le_b : ∀ i : Fin H.N,
      min (H.partition i.castSucc) t ≤ min (H.partition i.succ) t :=
    fun i => min_le_min_right t
      (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  have h_a_nn : ∀ i : Fin H.N, 0 ≤ min (H.partition i.castSucc) t :=
    fun i => le_min (h_part_nn i) ht_nn
  -- In the genuine case, the lower clamp equals the partition point.
  have h_acs : ∀ i : Fin H.N,
      min (H.partition i.castSucc) t < min (H.partition i.succ) t →
        min (H.partition i.castSucc) t = H.partition i.castSucc := by
    intro i hlt
    refine min_eq_left ?_
    by_contra h
    rw [not_le] at h
    rw [min_eq_right h.le,
      min_eq_right (h.le.trans (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ)))] at hlt
    exact lt_irrefl t hlt
  -- integrability of every cross product
  have h_cross : ∀ i j : Fin H.N,
      MeasureTheory.Integrable (fun ω => term i ω * term j ω) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := H.ξ_bounded j
    exact cross_increment_integrable W (h_a_nn i) (h_a_le_b i) (h_a_nn j) (h_a_le_b j)
      (H.ξ i) (H.ξ j) (H.ξ_measurable i) (H.ξ_measurable j) Mi hMi Mj hMj
  -- off-diagonal vanishing for i < j
  have h_off : ∀ i j : Fin H.N, i < j → ∫ ω, term i ω * term j ω ∂P = 0 := by
    intro i j hij
    rcases eq_or_lt_of_le (h_a_le_b j) with hj_eq | hj_lt
    · -- j-increment degenerate
      rw [show (fun ω => term i ω * term j ω) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hj_eq]; ring]
      exact MeasureTheory.integral_zero _ _
    · rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
      · -- i-increment degenerate
        rw [show (fun ω => term i ω * term j ω) = fun _ => (0 : ℝ) from by
          funext ω; simp only [hterm]; rw [← hi_eq]; ring]
        exact MeasureTheory.integral_zero _ _
      · -- both genuine: apply the general off-diagonal
        have hbi_le_aj : min (H.partition i.succ) t ≤ H.partition j.castSucc := by
          refine le_trans (min_le_left _ _) ?_
          exact H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
        have h := offDiagonal_increment_integral_zero W ℱ hℱ (h_part_nn i)
          (by rw [← h_acs i hi_lt]; exact hi_lt)
          hbi_le_aj
          (by rw [← h_acs j hj_lt]; exact hj_lt)
          (H.ξ i) (H.ξ j) (h_adapt i) (h_adapt j)
        rw [show (fun ω => term i ω * term j ω)
              = fun ω => (H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
                  - W.W (H.partition i.castSucc) ω))
                * (H.ξ j ω * (W.W (min (H.partition j.succ) t) ω
                  - W.W (H.partition j.castSucc) ω)) from by
          funext ω; simp only [hterm]; rw [h_acs i hi_lt, h_acs j hj_lt]]
        exact h
  rw [show (fun ω => (simpleIntegral W H t ω) ^ 2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N, term i ω * term j ω from by
    funext ω
    rw [show simpleIntegral W H t ω = ∑ i : Fin H.N, term i ω from rfl, sq,
      Finset.sum_mul_sum]]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => h_cross i j),
    Finset.sum_eq_single i]
  · -- diagonal j = i
    rw [show (fun ω => term i ω * term i ω) = fun ω => (term i ω) ^ 2 from by
      funext ω; ring]
    rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
    · rw [show (fun ω => (term i ω) ^ 2) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hi_eq]; ring, MeasureTheory.integral_zero,
        ← hi_eq]; ring
    · obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
      rw [show (fun ω => (term i ω) ^ 2)
            = fun ω => (H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
                - W.W (H.partition i.castSucc) ω)) ^ 2 from by
        funext ω; simp only [hterm]; rw [h_acs i hi_lt]]
      rw [diagonal_increment_bochner W ℱ hℱ (h_part_nn i)
        (by rw [← h_acs i hi_lt]; exact hi_lt) (H.ξ i) (h_adapt i) Mi hMi]
      rw [h_acs i hi_lt]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => term i ω * term j ω) = fun ω => term j ω * term i ω from by
        funext ω; ring]
      exact h_off j i h_lt
    · exact h_off i j h_gt
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Clamped inner integral.** Per `ω`,
`∫⁻_{[0,t]} ‖H.eval s ω‖² ds = ∑ᵢ ofReal(pᵢ₊₁∧t − pᵢ∧t)·‖ξᵢ ω‖²` (`t ≥ 0`).
Clamped companion of `lintegral_eval_sq`: each level-set contributes the length
of `(pᵢ, pᵢ₊₁] ∩ [0,t]`. -/
lemma lintegral_eval_sq_clamped {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} :
    ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∑ i : Fin H.N,
        ENNReal.ofReal (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
          * (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 := by
  have h_part_nn : ∀ i : Fin H.N, 0 ≤ H.partition i.castSucc := fun i => by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  rw [show (fun s => (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2)
      = (fun s => ∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s) from
    funext (eval_sq_eq_sum_indicator H · ω)]
  rw [MeasureTheory.lintegral_finsetSum _
    (fun i _ => (Measurable.indicator (by fun_prop) measurableSet_Ioc))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.lintegral_indicator measurableSet_Ioc,
    MeasureTheory.setLIntegral_const,
    MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  -- volume ((pᵢ, pᵢ₊₁] ∩ [0,t]) = ofReal (pᵢ₊₁∧t − pᵢ∧t)
  have h_inter : Set.Ioc (H.partition i.castSucc) (H.partition i.succ) ∩ Set.Icc 0 t
      = Set.Ioc (H.partition i.castSucc) (min (H.partition i.succ) t) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, h4⟩; exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, le_of_lt (lt_of_le_of_lt (h_part_nn i) h1), h3⟩
  rw [h_inter, Real.volume_Ioc, mul_comm]
  congr 1
  rcases le_or_gt (H.partition i.castSucc) t with h | h
  · rw [min_eq_left h]
  · have hpsucc : min (H.partition i.succ) t = t :=
      min_eq_right (h.le.trans (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ)))
    rw [hpsucc, min_eq_right h.le,
      ENNReal.ofReal_of_nonpos (by linarith : t - H.partition i.castSucc ≤ 0)]
    simp

/-- **Intermediate-time L²-isometry for the simple Brownian integral.** For
`0 ≤ t`, `∫⁻ ‖simpleIntegral W H t‖² = ∫⁻ ∫⁻_{[0,t]} ‖H.eval‖²`. The general-`t`
companion of `simpleIntegral_isometry`; combines the clamped Bochner assembly
(LHS) with the clamped inner integral (RHS) through `ENNReal.ofReal`. This is the
hinge for the coherent L²-Itô integral (cited result #5). -/
lemma simpleIntegral_intermediate_isometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W H t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h_part_nn : ∀ i : Fin H.N, 0 ≤ H.partition i.castSucc := fun i => by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_a_le_b : ∀ i : Fin H.N,
      min (H.partition i.castSucc) t ≤ min (H.partition i.succ) t :=
    fun i => min_le_min_right t (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  have h_norm_sq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), show ‖x‖ ^ 2 = x ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
  have hξsqmeas : ∀ i : Fin H.N, Measurable (fun ω => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) :=
    fun i => (((H.ξ_measurable i).nnNorm).coe_nnreal_ennreal).pow_const 2
  have hξ_int : ∀ i : Fin H.N, MeasureTheory.Integrable (fun ω => (H.ξ i ω) ^ 2) P := by
    intro i; obtain ⟨M, hM⟩ := H.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M ^ 2)
      (MeasureTheory.integrable_const _) ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have hξ_lint : ∀ i : Fin H.N,
      ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (H.ξ i ω) ^ 2 ∂P) := by
    intro i
    rw [show (fun ω => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) = fun ω => ENNReal.ofReal ((H.ξ i ω) ^ 2) from
      funext (fun ω => h_norm_sq _)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hξ_int i)
      (by filter_upwards with ω; positivity)]
  set term : Fin H.N → Ω → ℝ := fun i ω =>
    H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
      - W.W (min (H.partition i.castSucc) t) ω) with hterm
  have h_cross : ∀ i j : Fin H.N,
      MeasureTheory.Integrable (fun ω => term i ω * term j ω) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := H.ξ_bounded j
    exact cross_increment_integrable W (le_min (h_part_nn i) ht_nn) (h_a_le_b i)
      (le_min (h_part_nn j) ht_nn) (h_a_le_b j)
      (H.ξ i) (H.ξ j) (H.ξ_measurable i) (H.ξ_measurable j) Mi hMi Mj hMj
  have h_si_int : MeasureTheory.Integrable (fun ω => (simpleIntegral W H t ω) ^ 2) P := by
    rw [show (fun ω => (simpleIntegral W H t ω) ^ 2)
          = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N, term i ω * term j ω from by
      funext ω
      rw [show simpleIntegral W H t ω = ∑ i : Fin H.N, term i ω from rfl, sq,
        Finset.sum_mul_sum]]
    exact MeasureTheory.integrable_finsetSum _
      (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))
  rw [show (∫⁻ ω, (‖simpleIntegral W H t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((simpleIntegral W H t ω) ^ 2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq _)]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_si_int
    (by filter_upwards with ω; positivity)]
  rw [simpleIntegral_sq_bochner_clamped W ℱ hℱ H h_adapt ht_nn]
  rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        = fun ω => ∑ i : Fin H.N,
            ENNReal.ofReal (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
              * (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 from
    funext (fun ω => lintegral_eval_sq_clamped H ω)]
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => (hξsqmeas i).const_mul _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg
    (sub_nonneg.mpr (h_a_le_b i)) (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.lintegral_const_mul _ (hξsqmeas i),
    ENNReal.ofReal_mul (sub_nonneg.mpr (h_a_le_b i)), hξ_lint i]

/-- **`simpleIntegral W H t` is in `L²(P)` at every intermediate time `t ≤ T`.**
The `AEStronglyMeasurable` part is the finite-sum argument of
`simpleIntegral_memLp_brownian`; the `eLpNorm < ⊤` part uses the intermediate-time
isometry `∫⁻‖I_t‖² = ∫⁻∫⁻_{[0,t]}‖H.eval‖²` bounded by the (finite) endpoint
`∫⁻∫⁻_{[0,T]}‖H.eval‖²` via `Set.Icc` monotonicity (`t ≤ T`). Needed to treat
`fun t => simpleIntegral W H t` as an `L²` martingale for the orthogonal-increment
Cauchy estimate. -/
lemma simpleIntegral_memLp_intermediate_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ T) :
    MeasureTheory.MemLp (fun ω => simpleIntegral W H t ω) 2 P := by
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun ω => simpleIntegral W H t ω) P := by
    refine Measurable.aestronglyMeasurable ?_
    unfold simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (H.ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  · rw [MeasureTheory.memLp_iff, MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤) hmeas]
    rw [show (2 : ℝ≥0∞).toReal = 2 from by simp]
    have h_rewrite : (fun ω => (‖simpleIntegral W H t ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = (fun ω => (‖simpleIntegral W H t ω‖₊ : ℝ≥0∞) ^ 2) := by
      funext ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
    rw [h_rewrite, simpleIntegral_intermediate_isometry W ℱ hℱ H h_adapt ht_nn]
    -- bound `∫⁻∫⁻_{[0,t]} ≤ ∫⁻∫⁻_{[0,T]} < ⊤`.
    have h_fin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      rw [← simpleIntegral_isometry W ℱ hℱ hT H h_adapt]
      exact simpleIntegral_lintegral_sq_finite_brownian W ℱ hℱ hT H h_adapt
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono (fun ω => ?_)) h_fin
    exact lintegral_mono_set (Set.Icc_subset_Icc_right htT)

/-- **General-time difference isometry.** For adapted `H₁, H₂` sharing the endpoint
`T`, the `L²(P)`-norm² of the integral difference at *any* `t ≥ 0` equals the
`L²(λ⊗P)`-norm² of their eval difference over `[0, t]`. The `min (·) t`-clamped
analogue of `diff_isometry_simple`: rewrite the integral difference as the integral
of `subOnCommonRefinement` (`simpleIntegral_sub_on_common_intermediate`), apply the
intermediate-time isometry, and unfold `eval` of `subOnCommonRefinement`. This is the exact
isometry underlying both `L²`-Cauchy-at-each-`t` and cross-horizon consistency. -/
lemma simpleIntegral_intermediate_diff_isometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hLHS : ∫⁻ ω, (‖simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (H₁.subOnCommonRefinement H₂ h_eq) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [SimplePredictable.simpleIntegral_sub_on_common_intermediate W H₁ H₂ h_eq t ω]
  rw [hLHS, simpleIntegral_intermediate_isometry W ℱ hℱ (H₁.subOnCommonRefinement H₂ h_eq)
      (SimplePredictable.sub_on_common_adapt ℱ H₁ H₂ h_eq h_adapt₁ h_adapt₂) ht_nn]
  refine lintegral_congr (fun ω => ?_)
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
  rw [SimplePredictable.eval_sub_on_common H₁ H₂ h_eq s ω]

end LevyStochCalc.Brownian.Ito

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Second moments of almost everywhere limits

Fatou's lemma transfers a uniform actual second-moment bound to the limit.
This is used to pass finite-grid maximal inequalities to continuous Brownian
paths. It requires no uniform-integrability or moment assumption on the limit.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω}

/-- Almost everywhere limits inherit a uniform L² bound by Fatou. -/
theorem memLp_two_and_second_moment_le_of_ae_tendsto
    {f : ℕ → Ω → E} {g : Ω → E} {C : ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : AEStronglyMeasurable g μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hbound : ∀ n, (∫ ω, ‖f n ω‖ ^ 2 ∂μ) ≤ C) :
    MemLp g 2 μ ∧ (∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ C := by
  have hfi (n : ℕ) : Integrable (fun ω => ‖f n ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hf n).aestronglyMeasurable).mp (hf n)
  let F (n : ℕ) (ω : Ω) := ENNReal.ofReal (‖f n ω‖ ^ 2)
  have hFmeas (n : ℕ) : AEMeasurable (F n) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hf n).aestronglyMeasurable.norm.aemeasurable.pow_const 2)
  have hFatou := lintegral_liminf_le' (μ := μ) (f := F) (u := atTop) hFmeas
  have hlimEq : (fun ω => liminf (fun n => F n ω) atTop) =ᵐ[μ]
      fun ω => ENNReal.ofReal (‖g ω‖ ^ 2) := by
    filter_upwards [hlim] with ω hω
    exact (ENNReal.continuous_ofReal.tendsto _ |>.comp (hω.norm.pow 2)).liminf_eq
  rw [lintegral_congr_ae hlimEq] at hFatou
  have hEach (n : ℕ) : (∫⁻ ω, F n ω ∂μ) ≤ ENNReal.ofReal C := by
    have heq := ofReal_integral_eq_lintegral_ofReal (hfi n)
      (Eventually.of_forall (fun ω => sq_nonneg ‖f n ω‖))
    change ENNReal.ofReal (∫ ω, ‖f n ω‖ ^ 2 ∂μ) = ∫⁻ ω, F n ω ∂μ at heq
    rw [← heq]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hlimBound : liminf (fun n => ∫⁻ ω, F n ω ∂μ) atTop ≤ ENNReal.ofReal C :=
    liminf_le_of_frequently_le (Eventually.of_forall hEach).frequently
  have hcost : (∫⁻ ω, ENNReal.ofReal (‖g ω‖ ^ 2) ∂μ) ≤ ENNReal.ofReal C :=
    hFatou.trans hlimBound
  have hgi : Integrable (fun ω => ‖g ω‖ ^ 2) μ := by
    refine ⟨hg.norm.pow 2, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun ω => sq_nonneg ‖g ω‖))).mpr
    exact lt_of_le_of_lt hcost ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm hg).mpr hgi, ?_⟩
  have hC : 0 ≤ C :=
    (integral_nonneg (μ := μ) (fun ω => sq_nonneg ‖f 0 ω‖)).trans (hbound 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hgi
    (Eventually.of_forall (fun ω => sq_nonneg ‖g ω‖))] at hcost
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hcost

end CutoffRigidity

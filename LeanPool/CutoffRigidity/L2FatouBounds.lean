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

Fatou's lemma transfers bounds on integrals to the almost-everywhere limit.
A uniform second-moment bound then gives L² membership of the limit.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω}

/-- Fatou's lemma with convergent upper bounds on the integrals. -/
theorem lintegral_le_of_ae_tendsto_bounds {f : ℕ → Ω → ℝ≥0∞} {g : Ω → ℝ≥0∞}
    {bound : ℕ → ℝ≥0∞} {limit : ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hbound : ∀ n, (∫⁻ x, f n x ∂μ) ≤ bound n)
    (hbound_lim : Tendsto bound atTop (𝓝 limit)) :
    (∫⁻ x, g x ∂μ) ≤ limit := by
  have hpoint : (fun x => liminf (fun n => f n x) atTop) =ᵐ[μ] g :=
    hlim.mono (fun _ hx => hx.liminf_eq)
  calc
    _ = ∫⁻ x, liminf (fun n => f n x) atTop ∂μ := (lintegral_congr_ae hpoint).symm
    _ ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := lintegral_liminf_le' hf
    _ ≤ liminf bound atTop := liminf_le_liminf (Eventually.of_forall hbound)
    _ = limit := hbound_lim.liminf_eq

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
  have hpoint : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (ENNReal.ofReal (‖g ω‖ ^ 2))) := by
    filter_upwards [hlim] with ω hω
    exact ENNReal.continuous_ofReal.tendsto _ |>.comp (hω.norm.pow 2)
  have hEach (n : ℕ) : (∫⁻ ω, F n ω ∂μ) ≤ ENNReal.ofReal C := by
    have heq := ofReal_integral_eq_lintegral_ofReal (hfi n)
      (Eventually.of_forall (fun ω => sq_nonneg ‖f n ω‖))
    change ENNReal.ofReal (∫ ω, ‖f n ω‖ ^ 2 ∂μ) = ∫⁻ ω, F n ω ∂μ at heq
    rw [← heq]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hcost := lintegral_le_of_ae_tendsto_bounds hFmeas hpoint hEach tendsto_const_nhds
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

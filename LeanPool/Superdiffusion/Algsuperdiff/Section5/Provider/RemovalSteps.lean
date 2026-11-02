/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PthMoment

/-!
# RemovalSteps

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Removing a stopping time on a rare event

These are the measure-theoretic Cauchy--Schwarz estimates used in ABK26
`e.remove.stop.mean` and in the second-moment removal step.  If two random
variables agree off a measurable event, their means differ by a square-root
moment term plus the deterministic bound for the stopped variable on that
event.
-/

namespace Algsuperdiff.Section5.Provider

open MeasureTheory

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

private theorem integral_mul_indicator_le_sqrt (mu : Measure Omega) [IsFiniteMeasure mu]
    {Z : Omega → ℝ} (hZ : AEStronglyMeasurable Z mu) (hZ0 : 0 ≤ᵐ[mu] Z)
    (hZsq : Integrable (fun omega => Z omega ^ (2 : ℕ)) mu)
    {A : Set Omega} (hA : MeasurableSet A) :
    ∫ omega, Z omega * A.indicator (fun _ => (1 : ℝ)) omega ∂mu ≤
      (∫ omega, Z omega ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
        mu.real A ^ (1 / 2 : ℝ) := by
  have hmemZ : MemLp Z (ENNReal.ofReal (2 : ℝ)) mu := by
    simpa only [ENNReal.ofReal_ofNat] using (memLp_two_iff_integrable_sq hZ).2 hZsq
  have hmemI : MemLp (A.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) mu :=
    memLp_indicator_const (ENNReal.ofReal (2 : ℝ)) hA 1 (Or.inr (measure_ne_top mu A))
  have hI0 : 0 ≤ᵐ[mu] A.indicator fun _ => (1 : ℝ) :=
    Filter.Eventually.of_forall fun omega => Set.indicator_nonneg (fun _ _ => zero_le_one) omega
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hZ0 hI0 hmemZ hmemI
  have hpow : ∀ omega : Omega,
      (A.indicator (fun _ => (1 : ℝ)) omega) ^ (2 : ℝ) =
        A.indicator (fun _ => (1 : ℝ)) omega := by
    intro omega
    by_cases homega : omega ∈ A
    · simp only [Set.indicator_of_mem homega, Real.one_rpow]
    · rw [Set.indicator_of_notMem homega, Real.zero_rpow (by norm_num)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpow),
    integral_indicator_const (1 : ℝ) hA] at h
  norm_num at h ⊢
  exact h

/-- **Mean removal on a rare event.** If `X = Y` off `A`, the difference of
their means is controlled by the second moment of `X` and a pointwise bound on
`Y` on `A`.  This is the abstract C4 estimate. -/
theorem norm_integral_sub_le_moment_on_event (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega → E} (hX : Integrable X mu) (hY : Integrable Y mu)
    (hXsq : Integrable (fun omega => ‖X omega‖ ^ (2 : ℕ)) mu)
    {A : Set Omega} (hA : MeasurableSet A)
    (heq : ∀ omega, omega ∉ A → X omega = Y omega)
    {B : ℝ} (hYbound : ∀ᵐ omega ∂mu, omega ∈ A → ‖Y omega‖ ≤ B) :
    ‖∫ omega, X omega ∂mu - ∫ omega, Y omega ∂mu‖ ≤
      (∫ omega, ‖X omega‖ ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
          mu.real A ^ (1 / 2 : ℝ) + B * mu.real A := by
  have hnormMeas : AEStronglyMeasurable (fun omega => ‖X omega‖) mu :=
    hX.norm.aestronglyMeasurable
  have hXevent := integral_mul_indicator_le_sqrt mu hnormMeas
    (Filter.Eventually.of_forall fun omega => norm_nonneg (X omega)) hXsq hA
  rw [← integral_sub hX hY]
  have hrestrict : ∫ omega, X omega - Y omega ∂mu =
      ∫ omega in A, X omega - Y omega ∂mu := by
    rw [← integral_indicator hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
    by_cases homega : omega ∈ A
    · simp only [Set.indicator_of_mem homega]
    · simp only [Set.indicator_of_notMem homega, heq omega homega, sub_self]
  rw [hrestrict, integral_sub (hX.integrableOn) (hY.integrableOn)]
  calc
    ‖∫ omega in A, X omega ∂mu - ∫ omega in A, Y omega ∂mu‖ ≤
        ‖∫ omega in A, X omega ∂mu‖ + ‖∫ omega in A, Y omega ∂mu‖ :=
      norm_sub_le _ _
    _ ≤ ∫ omega in A, ‖X omega‖ ∂mu + B * mu.real A := by
      refine add_le_add (norm_integral_le_integral_norm _) ?_
      have hbound : ∀ᵐ omega ∂(mu.restrict A), ‖Y omega‖ ≤ B := by
        filter_upwards [ae_restrict_mem hA,
          ae_mono Measure.restrict_le_self hYbound] with omega hmem hbound
        exact hbound hmem
      calc
        ‖∫ omega in A, Y omega ∂mu‖ ≤ B * (mu.restrict A).real Set.univ :=
          norm_integral_le_of_norm_le_const hbound
        _ = B * mu.real A := by
          congr 1
          simp only [measureReal_def, Measure.restrict_apply_univ]
    _ = ∫ omega, ‖X omega‖ * A.indicator (fun _ => (1 : ℝ)) omega ∂mu +
          B * mu.real A := by
      rw [← integral_indicator hA]
      refine congrArg (fun z : ℝ => z + B * mu.real A) ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
      by_cases homega : omega ∈ A
      · simp only [Set.indicator_of_mem homega, mul_one]
      · simp only [Set.indicator_of_notMem homega, mul_zero]
    _ ≤ (∫ omega, ‖X omega‖ ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
          mu.real A ^ (1 / 2 : ℝ) + B * mu.real A := by
      exact add_le_add hXevent le_rfl

end

end Algsuperdiff.Section5.Provider

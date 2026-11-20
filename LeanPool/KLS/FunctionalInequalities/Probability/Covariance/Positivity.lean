/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Intrinsic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Positive

/-!
# Positivity of the ambient covariance

For a probability law with finite second moment on a finite-dimensional inner product space: full
affine
support gives a strictly positive covariance operator, an injective covariance operator gives full
affine
support, and the covariance operator is self-adjoint.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A law with full affine support and finite second moment has strictly positive covariance. -/
theorem Covariance.inner_operator_self_pos_of_affineSupport_eq_top (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E)) (hfull : Probability.affineSupport μ = ⊤)
    {v : E} (hv : v ≠ 0) : 0 < ⟪Covariance.operator (μ : Measure E) v, v⟫ := by
  rw [Covariance.operator_inner, covarianceBilin_self h2]
  rcases (variance_nonneg (fun x => ⟪v, x⟫) (μ : Measure E)).lt_or_eq with h | h
  · exact h
  exfalso
  have hX : MemLp (fun x => ⟪v, x⟫) 2 (μ : Measure E) := by
    simpa only [Function.comp_def, id_eq, innerSL_apply_apply] using (innerSL ℝ v).comp_memLp' h2
  have hae := ae_eq_integral_of_variance_eq_zero hX h.symm
  let c : ℝ := ∫ x, ⟪v, x⟫ ∂(μ : Measure E)
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let H : AffineSubspace ℝ E := AffineSubspace.mk' ((c / ‖v‖ ^ 2) • v) (Submodule.span ℝ {v})ᗮ
  have hmem : ∀ᵐ x ∂(μ : Measure E), x ∈ H := by
    filter_upwards [hae] with x hx
    have hx' : ⟪v, x⟫ = c := hx
    rw [AffineSubspace.mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hx',
      div_mul_cancel₀ c (pow_ne_zero 2 hv'), sub_self]
  have hle := Probability.affineSupport_le_of_ae_mem μ H H.isClosed_of_finiteDimensional hmem
  rw [hfull] at hle
  have hH : H = ⊤ := top_le_iff.mp hle
  have hdir : (Submodule.span ℝ {v})ᗮ = ⊤ := by
    have hh := congrArg AffineSubspace.direction hH
    rwa [AffineSubspace.direction_mk', AffineSubspace.direction_top] at hh
  exact hv (Submodule.span_singleton_eq_bot.mp ((Submodule.orthogonal_eq_top_iff _).mp hdir))

/-- An injective covariance operator forces full affine support. -/
theorem Probability.affineSupport_eq_top_of_covariance_injective (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E))
    (hinj : Function.Injective (Covariance.operator (μ : Measure E))) :
    Probability.affineSupport μ = ⊤ := by
  have hperp : (Probability.affineSupport μ).directionᗮ = ⊥ := by
    apply bot_unique
    intro w hw
    have h := Covariance.operator_apply_eq_zero_of_mem_orthogonal μ h2 hw
    have hz : w = 0 := hinj (h.trans (map_zero _).symm)
    simpa only [Submodule.mem_bot] using hz
  have hdir : (Probability.affineSupport μ).direction = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hperp
  have hne : (Probability.affineSupport μ : Set E).Nonempty :=
    ⟨Probability.origin μ, (Probability.origin μ).property⟩
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir

/-- The covariance operator is self-adjoint. -/
theorem Covariance.operator_isSelfAdjoint (μ : Measure E) :
    IsSelfAdjoint (Covariance.operator μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪Covariance.operator μ x, y⟫ = ⟪x, Covariance.operator μ y⟫
  calc
    ⟪Covariance.operator μ x, y⟫ = covarianceBilin μ x y := Covariance.operator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = ⟪Covariance.operator μ y, x⟫ := (Covariance.operator_inner μ y x).symm
    _ = ⟪x, Covariance.operator μ y⟫ := real_inner_comm _ _

end FunctionalInequalities

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Conditional expectation of a bivariate Gaussian

For `(X, Y)` jointly Gaussian with means `μ_X, μ_Y`, `Var Y = σ_Y² > 0` and
`Cov(X, Y) = ρ σ_X σ_Y` with `σ_X > 0` (`BivariateGaussianHyp`):

    E[X | σ(Y)] = μ_X + (ρ σ_X / σ_Y) (Y − μ_Y)   a.s.

The hypotheses do not ask that `Var X = σ_X²` or `|ρ| < 1`: only the covariance of `X` with `Y`
enters. The standard bivariate normal law of `Probability/Gaussian/BivariateNormalCDF.lean`
satisfies them (`bivariateGaussianHyp_bivariateNormalLaw`), giving `E[X | Y] = r Y` there.

## Main definitions

* `BivariateGaussianHyp`: the hypotheses of the conditional-expectation formula for a pair
  `(X, Y)` with means `μ_X, μ_Y`, `Var Y = σ_Y² > 0` and `Cov(X, Y) = ρ σ_X σ_Y`.

## Main results

* `conditional_expectation_formula`: under `BivariateGaussianHyp`,
  `E[X | σ(Y)] = μ_X + (ρ σ_X / σ_Y) (Y − μ_Y)` almost surely.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem B.1.3(2)

## Tags

conditional expectation, jointly Gaussian, regression coefficient, correlation, bivariate normal,
MSC 60E05, MSC 60G15
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- Hypotheses for the bivariate Gaussian conditional-expectation formula. -/
structure BivariateGaussianHyp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (μ_X μ_Y σ_X σ_Y ρ : ℝ) : Prop where
  σ_X_pos : 0 < σ_X
  σ_Y_pos : 0 < σ_Y
  X_meas : Measurable X
  Y_meas : Measurable Y
  /-- (X, Y) is jointly Gaussian. -/
  joint_gaussian : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P
  /-- Marginal mean of X. -/
  mean_X : ∫ ω, X ω ∂P = μ_X
  /-- Marginal mean of Y. -/
  mean_Y : ∫ ω, Y ω ∂P = μ_Y
  /-- Variance of Y is σ_Y². -/
  var_Y : Var[Y; P] = σ_Y ^ 2
  /-- Cov(X, Y) = ρ σ_X σ_Y. -/
  cov_XY : cov[X, Y; P] = ρ * σ_X * σ_Y

namespace BivariateGaussianHyp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ} {μ_X μ_Y σ_X σ_Y ρ : ℝ}

/-- The continuous linear map `(x, y) ↦ (x - β y, y)`. -/
private noncomputable def linearShift (β : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Pointwise-evaluation lemma for `linearShift` to keep proofs readable. -/
@[simp] private lemma linearShift_apply (β : ℝ) (p : ℝ × ℝ) :
    linearShift β p = (p.1 - β * p.2, p.2) := by
  simp [linearShift]

/-- Conditional expectation formula for a bivariate Gaussian. -/
theorem conditional_expectation_formula
    (h : BivariateGaussianHyp P X Y μ_X μ_Y σ_X σ_Y ρ) :
    (P[X | MeasurableSpace.comap Y inferInstance])
      =ᵐ[P] fun ω ↦ μ_X + (ρ * σ_X / σ_Y) * (Y ω - μ_Y) := by
  set β : ℝ := ρ * σ_X / σ_Y with hβ_def
  set Xhat : Ω → ℝ := fun ω ↦ μ_X + β * (Y ω - μ_Y)
  have hY_le : MeasurableSpace.comap Y inferInstance ≤ mΩ := by
    rintro s ⟨t, ht, rfl⟩
    exact h.Y_meas ht
  have hY_smeas_comap : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] Y :=
    (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have hXhat_smeas : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] Xhat := by
    refine StronglyMeasurable.add stronglyMeasurable_const ?_
    refine StronglyMeasurable.const_mul ?_ β
    exact hY_smeas_comap.sub stronglyMeasurable_const
  have hX_int : Integrable X P := h.joint_gaussian.fst.integrable
  have hY_int : Integrable Y P := h.joint_gaussian.snd.integrable
  have hXhat_int : Integrable Xhat P := by
    refine Integrable.add (integrable_const _) ?_
    exact (hY_int.sub (integrable_const _)).const_mul β
  have h_condXhat : P[Xhat | MeasurableSpace.comap Y inferInstance] = Xhat :=
    condExp_of_stronglyMeasurable hY_le hXhat_smeas hXhat_int
  have hPair_eq :
      (fun ω ↦ (X ω - β * Y ω, Y ω))
        = (linearShift β) ∘ (fun ω ↦ (X ω, Y ω)) := by
    funext ω
    simp [Function.comp]
  have h_jointGaussian_diff : HasGaussianLaw (fun ω ↦ (X ω - β * Y ω, Y ω)) P := by
    rw [hPair_eq]
    exact h.joint_gaussian.map_of_measurable (linearShift β)
      (linearShift β).continuous.measurable
  have hcov_zero : cov[fun ω ↦ X ω - β * Y ω, Y; P] = 0 := by
    have h_memLp_X : MemLp X 2 P := h.joint_gaussian.fst.memLp_two
    have h_memLp_Y : MemLp Y 2 P := h.joint_gaussian.snd.memLp_two
    have h_memLp_betaY : MemLp (fun ω ↦ β * Y ω) 2 P := h_memLp_Y.const_mul β
    rw [show (fun ω ↦ X ω - β * Y ω) = (fun ω ↦ X ω) - (fun ω ↦ β * Y ω) from rfl]
    rw [covariance_sub_left h_memLp_X h_memLp_betaY h_memLp_Y]
    rw [show (fun ω ↦ β * Y ω) = β • Y from by
      funext ω
      simp [Pi.smul_apply, smul_eq_mul]]
    rw [covariance_smul_left, h.cov_XY,
        show cov[Y, Y; P] = Var[Y; P] from covariance_self h_memLp_Y.aemeasurable,
        h.var_Y]
    have hY_ne : σ_Y ≠ 0 := ne_of_gt h.σ_Y_pos
    rw [hβ_def]
    field_simp
    ring
  have hIndep : IndepFun (fun ω ↦ X ω - β * Y ω) Y P :=
    h_jointGaussian_diff.indepFun_of_covariance_eq_zero hcov_zero
  have h_diff_meas : Measurable (fun ω ↦ X ω - β * Y ω) :=
    h.X_meas.sub (h.Y_meas.const_mul β)
  have h_diff_smeas_comap :
      StronglyMeasurable[MeasurableSpace.comap (fun ω ↦ X ω - β * Y ω) (borel ℝ)]
        (fun ω ↦ X ω - β * Y ω) :=
    (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have h_diff_le_comap :
      MeasurableSpace.comap (fun ω ↦ X ω - β * Y ω) (borel ℝ) ≤ mΩ :=
    h_diff_meas.comap_le
  have h_indep_sigma :
      Indep (MeasurableSpace.comap (fun ω ↦ X ω - β * Y ω) (borel ℝ))
            (MeasurableSpace.comap Y inferInstance) P :=
    (IndepFun_iff_Indep _ _ _).mp hIndep
  have hE_diff : ∫ ω, X ω - β * Y ω ∂P = μ_X - β * μ_Y := by
    rw [integral_sub hX_int (hY_int.const_mul β), integral_const_mul, h.mean_X, h.mean_Y]
  have h_int_diff : Integrable (fun ω ↦ X ω - β * Y ω) P :=
    hX_int.sub (hY_int.const_mul β)
  have h_condDiff :
      P[fun ω ↦ X ω - β * Y ω | (MeasurableSpace.comap Y inferInstance)]
        =ᵐ[P] fun _ ↦ μ_X - β * μ_Y := by
    have := condExp_indep_eq h_diff_le_comap hY_le h_diff_smeas_comap h_indep_sigma
    rw [hE_diff] at this
    exact this
  have h_X_decomp : (X : Ω → ℝ) = Xhat + (fun ω ↦ X ω - β * Y ω - (μ_X - β * μ_Y)) := by
    funext ω
    change X ω = (μ_X + β * (Y ω - μ_Y)) + (X ω - β * Y ω - (μ_X - β * μ_Y))
    ring
  have h_cond_split :
      P[X | MeasurableSpace.comap Y inferInstance]
        =ᵐ[P] (P[Xhat | MeasurableSpace.comap Y inferInstance])
          + (P[fun ω ↦ X ω - β * Y ω - (μ_X - β * μ_Y)
              | MeasurableSpace.comap Y inferInstance]) := by
    conv_lhs => rw [h_X_decomp]
    exact condExp_add hXhat_int (h_int_diff.sub (integrable_const _)) _
  have h_cond_centered :
      P[fun ω ↦ X ω - β * Y ω - (μ_X - β * μ_Y)
        | MeasurableSpace.comap Y inferInstance]
        =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    have h1 : P[fun ω ↦ X ω - β * Y ω - (μ_X - β * μ_Y)
        | MeasurableSpace.comap Y inferInstance]
              =ᵐ[P]
              (P[fun ω ↦ X ω - β * Y ω | MeasurableSpace.comap Y inferInstance])
                - P[fun _ : Ω ↦ μ_X - β * μ_Y | MeasurableSpace.comap Y inferInstance] :=
      condExp_sub h_int_diff (integrable_const _) _
    have h2 : P[fun _ : Ω ↦ μ_X - β * μ_Y | MeasurableSpace.comap Y inferInstance]
            = fun _ ↦ μ_X - β * μ_Y :=
      condExp_const hY_le (μ_X - β * μ_Y)
    filter_upwards [h1, h_condDiff] with ω hω1 hω2
    show _ = (0 : ℝ)
    rw [hω1, Pi.sub_apply, hω2, h2]
    ring
  refine h_cond_split.trans ?_
  filter_upwards [h_cond_centered] with ω hω
  change ((P[Xhat | MeasurableSpace.comap Y inferInstance]) +
        (P[fun ω ↦ X ω - β * Y ω - (μ_X - β * μ_Y)
          | MeasurableSpace.comap Y inferInstance])) ω
      = μ_X + (ρ * σ_X / σ_Y) * (Y ω - μ_Y)
  simp only [Pi.add_apply]
  rw [hω, h_condXhat]
  change (μ_X + β * (Y ω - μ_Y)) + (0 : ℝ) = μ_X + (ρ * σ_X / σ_Y) * (Y ω - μ_Y)
  rw [hβ_def]
  ring

end BivariateGaussianHyp

end MathFin

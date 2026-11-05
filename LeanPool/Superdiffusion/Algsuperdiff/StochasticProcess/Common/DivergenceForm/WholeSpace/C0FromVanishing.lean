/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PositiveC0Resolvent

/-!
# C0FromVanishing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The analytic minimal resolvent on `C₀` from vanishing at infinity

This module separates the coefficient-dependent proof of vanishing at infinity
from the coefficient-free algebraic assembly.  The resulting operator is
definitionally the signed analytic minimal resolvent; in particular, later
kernel-identification arguments do not require an operator rewrite.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

omit [NeZero d] in
theorem abs_le_norm_c0_generic (f : C₀(Vec d, ℝ)) (x : Vec d) :
    |f x| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF x

/-- The coefficient-dependent input needed to realize the signed analytic
minimal resolvent as a map from `C₀` to `C₀`. -/
def HasVanishingAnalyticMinimalResolvent : Prop :=
  ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)),
    Tendsto (A.analyticMinimalResolventReal mu f f.continuous.measurable
      (D := ‖f‖) (abs_le_norm_c0_generic f))
      (cocompact (Vec d)) (nhds 0)

/-- The analytic minimal resolvent as a `C₀` map, given its
coefficient-dependent vanishing theorem. -/
def analyticMinimalC0ResolventOfVanishing
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) : C₀(Vec d, ℝ) where
  toFun := A.analyticMinimalResolventReal mu f f.continuous.measurable
    (D := ‖f‖) (abs_le_norm_c0_generic f)
  continuous_toFun := A.continuous_analyticMinimalResolventReal mu f
  zero_at_infty' := hVanish mu f

@[simp] theorem analyticMinimalC0ResolventOfVanishing_apply
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) (x : Vec d) :
    A.analyticMinimalC0ResolventOfVanishing hVanish mu f x =
      A.analyticMinimalResolventReal mu f f.continuous.measurable
        (D := ‖f‖) (abs_le_norm_c0_generic f) x := rfl

/-- Additivity of the analytic minimal `C₀` resolver constructed from a
vanishing theorem. -/
theorem analyticMinimalC0ResolventOfVanishing_add
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (mu : PositiveShift) (f g : C₀(Vec d, ℝ)) :
    A.analyticMinimalC0ResolventOfVanishing hVanish mu (f + g) =
      A.analyticMinimalC0ResolventOfVanishing hVanish mu f +
        A.analyticMinimalC0ResolventOfVanishing hVanish mu g := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  let hsum : ∀ y, |f y + g y| ≤ ‖f‖ + ‖g‖ := fun y ↦
    (abs_add_le (f y) (g y)).trans
      (add_le_add (abs_le_norm_c0_generic f y) (abs_le_norm_c0_generic g y))
  calc
    A.analyticMinimalC0ResolventOfVanishing hVanish mu (f + g) x =
        A.analyticMinimalResolventReal mu (fun y ↦ f y + g y)
          (f.continuous.measurable.add g.continuous.measurable) hsum x := by
            apply A.analyticMinimalResolventReal_bound_irrel mu
              (f + g).continuous.measurable
              (fun y ↦ abs_le_norm_c0_generic (f + g) y) hsum
    _ = A.analyticMinimalC0ResolventOfVanishing hVanish mu f x +
        A.analyticMinimalC0ResolventOfVanishing hVanish mu g x :=
      A.analyticMinimalResolventReal_add mu f.continuous.measurable
        g.continuous.measurable (abs_le_norm_c0_generic f)
        (abs_le_norm_c0_generic g) x
    _ = _ := rfl

/-- Homogeneity of the analytic minimal `C₀` resolver constructed from a
vanishing theorem. -/
theorem analyticMinimalC0ResolventOfVanishing_smul
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (mu : PositiveShift) (c : ℝ) (f : C₀(Vec d, ℝ)) :
    A.analyticMinimalC0ResolventOfVanishing hVanish mu (c • f) =
      c • A.analyticMinimalC0ResolventOfVanishing hVanish mu f := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  have hcf : ∀ y, |c * f y| ≤ |c| * ‖f‖ := fun y ↦ by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le_norm_c0_generic f y) (abs_nonneg c)
  calc
    A.analyticMinimalC0ResolventOfVanishing hVanish mu (c • f) x =
        A.analyticMinimalResolventReal mu (fun y ↦ c * f y)
          (measurable_const.mul f.continuous.measurable) hcf x := by
            apply A.analyticMinimalResolventReal_bound_irrel mu
              (c • f).continuous.measurable
              (fun y ↦ abs_le_norm_c0_generic (c • f) y) hcf
    _ = c * A.analyticMinimalC0ResolventOfVanishing hVanish mu f x :=
      A.analyticMinimalResolventReal_smul mu c f.continuous.measurable
        (abs_le_norm_c0_generic f) x
    _ = _ := rfl

/-- The analytic minimal `C₀` resolver constructed from a vanishing theorem
has the sharp pointwise operator bound. -/
theorem norm_analyticMinimalC0ResolventOfVanishing_le
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    ‖A.analyticMinimalC0ResolventOfVanishing hVanish mu f‖ ≤
      (mu : ℝ)⁻¹ * ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (inv_nonneg.mpr mu.property.le) (norm_nonneg f))).2
  intro x
  rw [Real.norm_eq_abs]
  calc
    |A.analyticMinimalC0ResolventOfVanishing hVanish mu f x| ≤
        ‖f‖ / (mu : ℝ) :=
      A.abs_analyticMinimalResolventReal_le mu f.continuous.measurable
        (abs_le_norm_c0_generic f) x
    _ = (mu : ℝ)⁻¹ * ‖f‖ := by rw [div_eq_inv_mul]

/-- The analytic minimal resolver constructed from a vanishing theorem as a
continuous linear map on `C₀`. -/
noncomputable def analyticMinimalC0ResolventCLMOfVanishing
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (mu : PositiveShift) : C₀(Vec d, ℝ) →L[ℝ] C₀(Vec d, ℝ) :=
  LinearMap.mkContinuous
    { toFun := A.analyticMinimalC0ResolventOfVanishing hVanish mu
      map_add' := A.analyticMinimalC0ResolventOfVanishing_add hVanish mu
      map_smul' := A.analyticMinimalC0ResolventOfVanishing_smul hVanish mu }
    (mu : ℝ)⁻¹ (A.norm_analyticMinimalC0ResolventOfVanishing_le hVanish mu)

@[simp] theorem analyticMinimalC0ResolventCLMOfVanishing_apply
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    A.analyticMinimalC0ResolventCLMOfVanishing hVanish mu f =
      A.analyticMinimalC0ResolventOfVanishing hVanish mu f := rfl

/-- The analytic minimal `C₀` operators constructed from a vanishing
theorem satisfy the resolvent identity. -/
theorem analyticMinimalC0ResolventCLMOfVanishing_resolvent_identity
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (lam mu : PositiveShift) :
    A.analyticMinimalC0ResolventCLMOfVanishing hVanish lam -
        A.analyticMinimalC0ResolventCLMOfVanishing hVanish mu =
      ((mu : ℝ) - (lam : ℝ)) •
        ((A.analyticMinimalC0ResolventCLMOfVanishing hVanish lam).comp
          (A.analyticMinimalC0ResolventCLMOfVanishing hVanish mu)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro x
  have hbound : ∀ y,
      |A.analyticMinimalC0ResolventOfVanishing hVanish mu f y| ≤
        ‖f‖ / (mu : ℝ) :=
    A.abs_analyticMinimalResolventReal_le mu f.continuous.measurable
      (abs_le_norm_c0_generic f)
  have hinner :
      A.analyticMinimalC0ResolventOfVanishing hVanish lam
          (A.analyticMinimalC0ResolventOfVanishing hVanish mu f) x =
        A.analyticMinimalResolventReal lam
          (A.analyticMinimalResolventReal mu f f.continuous.measurable
            (abs_le_norm_c0_generic f))
          (A.measurable_analyticMinimalResolventReal mu
            f.continuous.measurable (abs_le_norm_c0_generic f)) hbound x := by
    apply A.analyticMinimalResolventReal_bound_irrel lam
      (A.analyticMinimalC0ResolventOfVanishing hVanish mu f).continuous.measurable
      (abs_le_norm_c0_generic _) hbound
  have h := A.analyticMinimalResolventReal_resolventEquation lam mu
    f.continuous.measurable (abs_le_norm_c0_generic f) x
  change
    A.analyticMinimalC0ResolventOfVanishing hVanish lam f x -
        A.analyticMinimalC0ResolventOfVanishing hVanish mu f x =
      ((mu : ℝ) - (lam : ℝ)) *
        A.analyticMinimalC0ResolventOfVanishing hVanish lam
          (A.analyticMinimalC0ResolventOfVanishing hVanish mu f) x
  rw [hinner]
  exact sub_eq_iff_eq_add'.mpr h

/-- The constructed analytic minimal operator has the sharp Hille--Yosida
norm bound. -/
theorem norm_analyticMinimalC0ResolventCLMOfVanishing_le
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (mu : PositiveShift) :
    ‖A.analyticMinimalC0ResolventCLMOfVanishing hVanish mu‖ ≤ (mu : ℝ)⁻¹ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr mu.property.le)
    (A.norm_analyticMinimalC0ResolventOfVanishing_le hVanish mu)

/-- The constructed analytic minimal operator preserves pointwise
nonnegativity. -/
theorem analyticMinimalC0ResolventCLMOfVanishing_nonnegative
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ A.analyticMinimalC0ResolventCLMOfVanishing hVanish mu f x := by
  intro x
  exact A.analyticMinimalResolventReal_nonneg mu f.continuous.measurable hf
    (abs_le_norm_c0_generic f) x

/-- The dense-range input for the analytic minimal `C₀` resolver
constructed from a vanishing theorem. -/
def HasDenseRangeAnalyticMinimalC0OfVanishing
    (hVanish : A.HasVanishingAnalyticMinimalResolvent) : Prop :=
  ∀ mu : PositiveShift,
    DenseRange (A.analyticMinimalC0ResolventOfVanishing hVanish mu)

/-- The analytic minimal resolver assembled as a positive contractive `C₀`
resolvent from coefficient-dependent vanishing and dense-range proofs. -/
noncomputable def analyticMinimalPositiveC0ContractiveResolventOfVanishing
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (hDense : A.HasDenseRangeAnalyticMinimalC0OfVanishing hVanish) :
    PositiveC0ContractiveResolvent (Vec d) where
  operator := A.analyticMinimalC0ResolventCLMOfVanishing hVanish
  resolvent_identity :=
    A.analyticMinimalC0ResolventCLMOfVanishing_resolvent_identity hVanish
  opNorm_le_inv := A.norm_analyticMinimalC0ResolventCLMOfVanishing_le hVanish
  denseRange := by
    intro mu
    simpa only [analyticMinimalC0ResolventCLMOfVanishing_apply] using! hDense mu
  isPositive := A.analyticMinimalC0ResolventCLMOfVanishing_nonnegative hVanish

@[simp] theorem analyticMinimalPositiveC0ContractiveResolventOfVanishing_operator
    (hVanish : A.HasVanishingAnalyticMinimalResolvent)
    (hDense : A.HasDenseRangeAnalyticMinimalC0OfVanishing hVanish)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    (A.analyticMinimalPositiveC0ContractiveResolventOfVanishing hVanish
      hDense).toContractiveResolvent.operator mu f =
      A.analyticMinimalC0ResolventOfVanishing hVanish mu f := rfl

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LpMultiplication
public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioGraph
public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioResolvent
public import LeanPool.VacuumBellSeparation.FreeField.PositiveOperatorPowers

/-!
# Maximal exponential multiplication as an actual selfadjoint partial operator

The domain is proved to be exactly the L² functions whose pointwise
exponential product is another L² function. A bounded logistic resolvent
constructs the operator, so no boundedness of the exponential is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Exponential ratio coefficient given by `1 / (1 + Real.exp t)`. -/
noncomputable def exponentialRatioCoefficient (t : ℝ) : ℝ := 1 / (1 + Real.exp t)

theorem exponentialRatioCoefficient_bounds (t : ℝ) :
    0 < exponentialRatioCoefficient t ∧ exponentialRatioCoefficient t ≤ 1 := by
  constructor
  · unfold exponentialRatioCoefficient
    positivity
  · rw [exponentialRatioCoefficient, div_le_one (by positivity : 0 < 1 + Real.exp t)]
    linarith [Real.exp_pos t]

theorem exponentialRatioCoefficient_mul (t : ℝ) :
    (exponentialRatioCoefficient t : ℂ) * (1 + (Real.exp t : ℂ)) = 1 := by
  have h : exponentialRatioCoefficient t * (1 + Real.exp t) = 1 :=
    div_mul_cancel₀ 1 (by positivity : (1 + Real.exp t : ℝ) ≠ 0)
  exact_mod_cast h

theorem memLp_exponentialRatioCoefficient (w : α → ℝ) (hw : Measurable w) :
    MemLp (fun x => (exponentialRatioCoefficient (w x) : ℂ)) ⊤ μ := by
  have hm : Measurable (fun x => (exponentialRatioCoefficient (w x) : ℂ)) := by
    unfold exponentialRatioCoefficient
    fun_prop
  apply memLp_top_of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (exponentialRatioCoefficient_bounds (w x)).1]
    exact (exponentialRatioCoefficient_bounds (w x)).2

/-- Continuous linear map for the exponential resolvent, of type `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`. -/
noncomputable def exponentialResolvent (w : α → ℝ) (hw : Measurable w) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpMultiplication μ (fun x => (exponentialRatioCoefficient (w x) : ℂ))
    (memLp_exponentialRatioCoefficient μ w hw)

theorem exponentialResolvent_injective (w : α → ℝ) (hw : Measurable w) :
    Function.Injective (exponentialResolvent μ w hw) :=
  lpMultiplication_injective μ _ _ (Filter.Eventually.of_forall fun x =>
    Complex.ofReal_ne_zero.mpr (exponentialRatioCoefficient_bounds (w x)).1.ne')

theorem exponentialResolvent_isSelfAdjoint (w : α → ℝ) (hw : Measurable w) :
    IsSelfAdjoint (exponentialResolvent μ w hw) :=
  lpMultiplication_isSelfAdjoint μ _ _ (Filter.Eventually.of_forall fun _x =>
    Complex.conj_ofReal _)

/-- Linear map for the exponential multiplication, of type `Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ`. -/
noncomputable def exponentialMultiplication (w : α → ℝ) (hw : Measurable w) :
    Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ :=
  boundedRatio (exponentialResolvent μ w hw) (1 - exponentialResolvent μ w hw)
    (exponentialResolvent_injective μ w hw)

theorem exponentialMultiplication_isSelfAdjoint (w : α → ℝ) (hw : Measurable w) :
    IsSelfAdjoint (exponentialMultiplication μ w hw) := by
  let R := exponentialResolvent μ w hw
  have hR := exponentialResolvent_isSelfAdjoint μ w hw
  change IsSelfAdjoint (boundedRatio R (1 - R) (exponentialResolvent_injective μ w hw))
  apply boundedRatio_isSelfAdjoint_of_isUnit_add R (1 - R)
    (exponentialResolvent_injective μ w hw)
  · exact selfAdjoint_denseRange_of_injective R hR (exponentialResolvent_injective μ w hw)
  · exact hR
  · exact (show IsSelfAdjoint (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) by simp).sub hR
  · exact (Commute.one_right R).sub_right (Commute.refl R)
  · have he : R + (1 - R) = 1 := by abel
    rw [he]
    exact isUnit_one

/-- Exact maximal graph: both sides are actual vectors of the full L² space. -/
theorem exponentialMultiplication_mem_graph (w : α → ℝ) (hw : Measurable w)
    (f g : Lp ℂ 2 μ) :
    (f, g) ∈ (exponentialMultiplication μ w hw).graph ↔
      g =ᵐ[μ] fun x => (Real.exp (w x) : ℂ) * f x := by
  let R := exponentialResolvent μ w hw
  have hR (u : Lp ℂ 2 μ) : R u =ᵐ[μ]
      fun x => (exponentialRatioCoefficient (w x) : ℂ) * u x :=
    lpMultiplication_ae μ _ _ u
  change (f, g) ∈ (boundedRatio R (1 - R) _).graph ↔ _
  rw [boundedRatio_mem_graph]
  constructor
  · rintro ⟨u, rfl, rfl⟩
    change (u - R u : Lp ℂ 2 μ) =ᵐ[μ] fun x => (Real.exp (w x) : ℂ) * (R u) x
    filter_upwards [Lp.coeFn_sub u (R u), hR u] with x hsub hx
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hx]
    have hc := congrArg (fun z : ℂ => z * u x) (exponentialRatioCoefficient_mul (w x))
    linear_combination -hc
  · intro hfg
    have he : R (f + g) = f := by
      apply Lp.ext
      filter_upwards [hR (f + g), Lp.coeFn_add f g, hfg] with x hx hsum he
      simp only [Pi.add_apply] at hsum
      rw [hx, hsum, he]
      have hc := congrArg (fun z : ℂ => z * f x) (exponentialRatioCoefficient_mul (w x))
      linear_combination hc
    refine ⟨f + g, he, ?_⟩
    change f + g - R (f + g) = g
    rw [he]
    abel

end VacuumBellSeparation

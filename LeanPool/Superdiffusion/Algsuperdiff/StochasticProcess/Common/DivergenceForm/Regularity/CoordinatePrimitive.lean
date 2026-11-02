/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.ParametricIntegralC1
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# CoordinatePrimitive

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A one-coordinate primitive for scalar forcing

This file constructs a scalar primitive by integrating along one coordinate.
The fixed-interval formula makes its joint parameter regularity accessible to
the parametric-integral calculus API. A change of variables recovers the
ordinary oriented coordinate integral, from which the selected derivative and
the sharp segment bound follow.
-/

namespace DivergenceFormProcess

open Filter MeasureTheory Set
open HCPolySupport

variable {d : ℕ}

/-- The primitive of `f` along coordinate `i`, based at coordinate `z`,
written as a fixed integral over `[0, 1]`. -/
noncomputable def coordinatePrimitive (f : Vec d → ℝ) (i : Fin d) (z : ℝ)
    (x : Vec d) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1,
    (x i - z) * f (Function.update x i (z + t * (x i - z)))

/-- A globally `C¹` scalar field has a globally `C¹` one-coordinate
primitive. -/
theorem contDiff_one_coordinatePrimitive (f : Vec d → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin d) (z : ℝ) :
    ContDiff ℝ 1 (coordinatePrimitive f i z) := by
  let F : Vec d → ℝ → ℝ := fun x t ↦
    (x i - z) * f (Function.update x i (z + t * (x i - z)))
  let F' : Vec d → ℝ → Vec d →L[ℝ] ℝ := fun x t ↦
    fderiv ℝ (fun y ↦ F y t) x
  have hfamily : ContDiff ℝ 1 (Function.uncurry fun p : (Vec d × ℝ) ↦
      fun y : Vec d ↦ F y p.2) := by
    have ht : ContDiff ℝ 1 (fun q : (Vec d × ℝ) × Vec d ↦ q.1.2) :=
      contDiff_snd.comp contDiff_fst
    have hyi : ContDiff ℝ 1 (fun q : (Vec d × ℝ) × Vec d ↦ q.2 i) :=
      (contDiff_apply ℝ ℝ i).comp contDiff_snd
    have harg : ContDiff ℝ 1 (fun q : (Vec d × ℝ) × Vec d ↦
        Function.update q.2 i (z + q.1.2 * (q.2 i - z))) := by
      rw [contDiff_pi]
      intro j
      classical
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self]
        exact contDiff_const.add (ht.mul (hyi.sub contDiff_const))
      · simp only [Function.update_of_ne hji]
        exact (contDiff_apply ℝ ℝ j).comp contDiff_snd
    exact (hyi.sub contDiff_const).mul (hf.comp harg)
  have hF : Continuous (Function.uncurry F) := by
    exact hfamily.continuous.comp (continuous_id.prodMk continuous_fst)
  have hF' : Continuous (Function.uncurry F') := by
    dsimp [F']
    exact Continuous.fderiv_one hfamily continuous_fst
  have hdiff : ∀ x t, HasFDerivAt (fun y ↦ F y t) (F' x t) x := by
    intro x t
    dsimp [F']
    have hembed : ContDiff ℝ 1 (fun y : Vec d ↦ ((x, t), y)) :=
      contDiff_const.prodMk contDiff_id
    have hslice : ContDiff ℝ 1 (fun y : Vec d ↦ F y t) := by
      exact hfamily.comp hembed
    exact hslice.differentiable (by norm_num) |>.differentiableAt.hasFDerivAt
  simpa only [coordinatePrimitive, F] using!
    contDiff_one_setIntegral_of_continuous_hasFDerivAt
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)) hF hF' hdiff

/-- The fixed-interval definition equals the ordinary oriented coordinate
integral. -/
theorem coordinatePrimitive_eq_intervalIntegral (f : Vec d → ℝ)
    (hf : Continuous f) (i : Fin d) (z : ℝ) (x : Vec d) :
    coordinatePrimitive f i z x =
      ∫ s in z..x i, f (Function.update x i s) := by
  let φ : ℝ → ℝ := fun t ↦ z + t * (x i - z)
  let φ' : ℝ → ℝ := fun _ ↦ x i - z
  let g : ℝ → ℝ := fun s ↦ f (Function.update x i s)
  have hφ : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt φ (φ' t) t := by
    intro t _
    dsimp [φ, φ']
    convert (hasDerivAt_id t).mul_const (x i - z) |>.const_add z using 1
    all_goals first | rfl | ring
  have hφ' : ContinuousOn φ' (uIcc (0 : ℝ) 1) :=
    continuous_const.continuousOn
  have hg : Continuous g := by
    exact hf.comp (contDiff_update (𝕜 := ℝ) 1 x i).continuous
  have hchange := intervalIntegral.integral_comp_mul_deriv hφ hφ' hg
  rw [coordinatePrimitive, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  calc
    (∫ t in (0 : ℝ)..1,
        (x i - z) * f (Function.update x i (z + t * (x i - z)))) =
        ∫ t in (0 : ℝ)..1, (g ∘ φ) t * φ' t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [g, φ, φ', Function.comp_apply, mul_comm]
    _ = ∫ s in φ 0..φ 1, g s := hchange
    _ = ∫ s in z..x i, f (Function.update x i s) := by
      have hend : z + (x i - z) = x i := by ring
      simp only [φ, g, zero_mul, add_zero, one_mul, hend]

/-- Varying the selected coordinate differentiates the primitive back to the
original scalar field. -/
theorem coordinatePrimitive_hasDerivAt_update (f : Vec d → ℝ)
    (hf : Continuous f) (i : Fin d) (z : ℝ) (x : Vec d) :
    HasDerivAt (fun s ↦ coordinatePrimitive f i z (Function.update x i s))
      (f x) (x i) := by
  let g : ℝ → ℝ := fun s ↦ f (Function.update x i s)
  have hg : Continuous g :=
    hf.comp (contDiff_update (𝕜 := ℝ) 1 x i).continuous
  have hfun : (fun s ↦ coordinatePrimitive f i z (Function.update x i s)) =
      fun s ↦ ∫ r in z..s, g r := by
    funext s
    rw [coordinatePrimitive_eq_intervalIntegral f hf i z]
    have hcoordinate : Function.update x i s i = s := by
      simp [Function.update]
    rw [hcoordinate]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp [g]
    congr 1
    funext j
    classical
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]
  rw [hfun]
  have hderiv := intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable z (x i))
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hupdate : Function.update x i (x i) = x := by
    funext j
    classical
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]
  simpa only [g, hupdate] using hderiv

end DivergenceFormProcess

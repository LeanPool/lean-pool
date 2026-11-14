/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.CurryingProduct

/-! # The product L² currying linear isometry

The unique class characterization supplies both linearity and the Tonelli
norm identity. No choices of slice representatives enter the public API.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}
  [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]

/-- Currying is the unique outer class with the nested slice formula. -/
@[expose] noncomputable def l2Curry (f : Lp E 2 (μ.prod ν)) : Lp (Lp E 2 ν) 2 μ :=
  (existsUnique_l2_curry (fun z => f z) (Lp.stronglyMeasurable f) (Lp.memLp f)).choose

/-- The exact representative characterization of product currying. -/
theorem l2Curry_ae (f : Lp E 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, l2Curry f x y = f (x, y) :=
  (existsUnique_l2_curry (fun z => f z) (Lp.stronglyMeasurable f)
    (Lp.memLp f)).choose_spec.1

/-- The iterated L² norm of the curried class is the original L² norm. -/
theorem l2Curry_norm (f : Lp E 2 (μ.prod ν)) : ‖l2Curry f‖ = ‖f‖ := by
  have hsq : ‖l2Curry f‖ₑ ^ 2 = ‖f‖ₑ ^ 2 := by
    calc
      _ = ∫⁻ x, ‖l2Curry f x‖ₑ ^ 2 ∂μ := (lintegral_l2_enorm_sq _).symm
      _ = ∫⁻ x, ∫⁻ y, ‖l2Curry f x y‖ₑ ^ 2 ∂ν ∂μ := by
        apply lintegral_congr
        intro x
        exact (lintegral_l2_enorm_sq _).symm
      _ = ∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ^ 2 ∂ν ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [l2Curry_ae f] with x hx
        exact lintegral_congr_ae (hx.mono
          (fun _ hy => congrArg (fun u : E => ‖u‖ₑ ^ 2) hy))
      _ = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(μ.prod ν) :=
        (lintegral_prod _ ((Lp.stronglyMeasurable f).enorm.pow_const 2).aemeasurable).symm
      _ = _ := lintegral_l2_enorm_sq _
  have hnormsq : ‖l2Curry f‖ ^ 2 = ‖f‖ ^ 2 := by
    simpa only [ENNReal.toReal_pow, enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm]
      using congrArg ENNReal.toReal hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq

/-- Product currying commutes with addition. -/
theorem l2Curry_add (f h : Lp E 2 (μ.prod ν)) : l2Curry (f + h) = l2Curry f + l2Curry h := by
  apply Lp.ext
  have hj := Measure.ae_ae_of_ae_prod (Lp.coeFn_add f h)
  filter_upwards [l2Curry_ae (f + h), l2Curry_ae f, l2Curry_ae h,
    Lp.coeFn_add (l2Curry f) (l2Curry h), hj] with x hc hf hh hs hx
  simp only [Pi.add_apply] at hs hx
  rw [hs]
  apply Lp.ext
  filter_upwards [hc, hf, hh, Lp.coeFn_add (l2Curry f x) (l2Curry h x), hx]
    with y hcy hfy hhy hsy hxy
  simp only [Pi.add_apply] at hsy
  rw [hsy, hcy, hfy, hhy]
  exact hxy

variable [NormedSpace ℂ E]

/-- Product currying commutes with complex scalar multiplication. -/
theorem l2Curry_smul (a : ℂ) (f : Lp E 2 (μ.prod ν)) :
    l2Curry (a • f) = a • l2Curry f := by
  apply Lp.ext
  have hj := Measure.ae_ae_of_ae_prod (Lp.coeFn_smul a f)
  filter_upwards [l2Curry_ae (a • f), l2Curry_ae f,
    Lp.coeFn_smul a (l2Curry f), hj] with x hc hf hs hx
  simp only [Pi.smul_apply] at hs hx
  rw [hs]
  apply Lp.ext
  filter_upwards [hc, hf, Lp.coeFn_smul a (l2Curry f x), hx] with y hcy hfy hsy hxy
  simp only [Pi.smul_apply] at hsy
  rw [hsy, hcy, hfy]
  exact hxy

/-- The generic complex linear isometry from product L² to iterated L². -/
@[expose] noncomputable def l2CurryLinearIsometry :
    Lp E 2 (μ.prod ν) →ₗᵢ[ℂ] Lp (Lp E 2 ν) 2 μ where
  toFun := l2Curry
  map_add' := l2Curry_add
  map_smul' := l2Curry_smul
  norm_map' := l2Curry_norm

end LiebThirring

end

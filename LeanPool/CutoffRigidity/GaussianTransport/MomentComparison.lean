/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A quadratic coupling bound from two moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace CutoffRigidity.Riemann

section Aux

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

/-- An inner product of functions with integrable squared norms is integrable. -/
theorem integrable_inner_of_sq (π : Measure Ω)
    {u v : Ω → EuclideanSpace ℝ (Fin k)} (hu : Measurable u) (hv : Measurable v)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) π) (hv2 : Integrable (fun ω => ‖v ω‖ ^ 2) π) :
    Integrable (fun ω => ⟪u ω, v ω⟫) π := by
  refine ((hu2.add hv2).div_const 2).mono' (by fun_prop) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  calc |⟪u ω, v ω⟫| ≤ ‖u ω‖ * ‖v ω‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖u ω‖ ^ 2 + ‖v ω‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖u ω‖ - ‖v ω‖)]

private theorem integral_inner_le_sqrt (π : Measure Ω)
    {u v : Ω → EuclideanSpace ℝ (Fin k)} (hu : MemLp u 2 π) (hv : MemLp v 2 π) :
    (∫ ω, ⟪u ω, v ω⟫ ∂π) ≤
      Real.sqrt ((∫ ω, ‖u ω‖ ^ 2 ∂π) * ∫ ω, ‖v ω‖ ^ 2 ∂π) := by
  let U := hu.toLp u
  let V := hv.toLp v
  have pair_eq {f g : Ω → EuclideanSpace ℝ (Fin k)}
      (hf : MemLp f 2 π) (hg : MemLp g 2 π) :
      ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, ⟪f x, g x⟫ ∂π := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]
  have norm_eq {f : Ω → EuclideanSpace ℝ (Fin k)} (hf : MemLp f 2 π) :
      ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂π := by
    simp only [← real_inner_self_eq_norm_sq, pair_eq hf hf]
  rw [← pair_eq hu hv, ← norm_eq hu, ← norm_eq hv, ← mul_pow,
    Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact real_inner_le_norm U V

/-- Cauchy-Schwarz lower bound for a coupling of two `ℝ^k`-valued random variables. -/
theorem integral_norm_sub_sq_lower_bound (π : Measure Ω) [IsProbabilityMeasure π]
    (X Z : Ω → EuclideanSpace ℝ (Fin k)) (hX : Measurable X) (hZ : Measurable Z)
    (m : EuclideanSpace ℝ (Fin k)) (C B : ℝ)
    (hX1 : ∀ a, ∫ ω, ⟪a, X ω⟫ ∂π = ⟪a, m⟫)
    (hX2i : Integrable (fun ω => ‖X ω‖ ^ 2) π) (hX2 : ∫ ω, ‖X ω‖ ^ 2 ∂π = ‖m‖ ^ 2 + C)
    (hZ1 : ∀ a, ∫ ω, ⟪a, Z ω⟫ ∂π = 0)
    (hZ2i : Integrable (fun ω => ‖Z ω‖ ^ 2) π) (hZ2 : ∫ ω, ‖Z ω‖ ^ 2 ∂π = B) :
    ‖m‖ ^ 2 + C + B - 2 * Real.sqrt (C * B) ≤ ∫ ω, ‖X ω - Z ω‖ ^ 2 ∂π := by
  have hmc : Measurable (fun _ : Ω => m) := measurable_const
  have i2 : Integrable (fun ω => ⟪m, X ω⟫) π :=
    integrable_inner_of_sq π hmc hX (integrable_const _) hX2i
  have i3 : Integrable (fun ω => ⟪X ω, Z ω⟫) π := integrable_inner_of_sq π hX hZ hX2i hZ2i
  have i4 : Integrable (fun ω => ⟪m, Z ω⟫) π :=
    integrable_inner_of_sq π hmc hZ (integrable_const _) hZ2i
  have hI' : ∫ ω, ⟪m, X ω⟫ ∂π = ‖m‖ ^ 2 := by rw [hX1 m, real_inner_self_eq_norm_sq]
  have hJ : ∫ ω, ⟪m, Z ω⟫ ∂π = 0 := hZ1 m
  set I := ∫ ω, ⟪X ω, Z ω⟫ ∂π with hIdef
  -- expansion of the cost
  have hcost : ∫ ω, ‖X ω - Z ω‖ ^ 2 ∂π = ‖m‖ ^ 2 + C - 2 * I + B := by
    have e : ∀ ω, ‖X ω - Z ω‖ ^ 2 = ‖X ω‖ ^ 2 - 2 * ⟪X ω, Z ω⟫ + ‖Z ω‖ ^ 2 := fun ω => by
      rw [@norm_sub_sq_real]
    simp_rw [e]
    have h1 : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * ⟪X ω, Z ω⟫) π := hX2i.sub (i3.const_mul 2)
    rw [integral_add h1 hZ2i, integral_sub hX2i (i3.const_mul 2),
      integral_const_mul, hX2, hZ2]
  -- the variance of `X`
  have hvar : ∫ ω, ‖X ω - m‖ ^ 2 ∂π = C := by
    have e : ∀ ω, ‖X ω - m‖ ^ 2 = ‖X ω‖ ^ 2 - 2 * ⟪m, X ω⟫ + ‖m‖ ^ 2 := fun ω => by
      rw [@norm_sub_sq_real, real_inner_comm]
    simp_rw [e]
    have h1 : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * ⟪m, X ω⟫) π := hX2i.sub (i2.const_mul 2)
    rw [integral_add h1 (integrable_const _),
      integral_sub hX2i (i2.const_mul 2), integral_const_mul, hX2, hI']
    simp
    ring
  have hcross : ∫ ω, ⟪X ω - m, Z ω⟫ ∂π = I := by
    have e : ∀ ω, ⟪X ω - m, Z ω⟫ = ⟪X ω, Z ω⟫ - ⟪m, Z ω⟫ := fun ω => inner_sub_left _ _ _
    simp_rw [e]
    rw [integral_sub i3 i4, hJ, sub_zero]
  have hx : MemLp X 2 π := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).2 hX2i
  have centered : MemLp (fun ω => X ω - m) 2 π := hx.sub (memLp_const m)
  have hz : MemLp Z 2 π := (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).2 hZ2i
  have hbound := integral_inner_le_sqrt π centered hz
  rw [hcross, hvar, hZ2] at hbound
  rw [hcost]
  linarith

end Aux

end CutoffRigidity.Riemann

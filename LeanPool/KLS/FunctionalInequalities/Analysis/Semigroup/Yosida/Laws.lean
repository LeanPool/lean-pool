/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Resolvent.Limit
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.VonNeumann
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Yosida.Approximation
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Laws of the Yosida approximation
Nonnegativity, symmetry, commutation and convergence on the generator domain.
The counterexample for unrestricted operator families lives in Exponential/Counterexample.lean. -/

@[expose] public section

noncomputable section

open Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

/-! ## The Yosida approximation of `T†T` -/

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-- The Yosida approximation is a nonnegative operator.  Indeed
`⟪L_s f, f⟫ = s⁻¹ (⟪f, f⟫ - ⟪J_s f, f⟫)` and `⟪J_s f, f⟫ ≤ ‖J_s f‖ ‖f‖ ≤ ‖f‖ ^ 2 = ⟪f, f⟫` because
`J_s` is a contraction. -/
theorem yosida_nonneg (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀) :
    0 ≤ ⟪yosida T hT hs f, f⟫ := by
  have hle : ⟪resolventCLM T hT hs f, f⟫ ≤ ⟪f, f⟫ := by
    calc ⟪resolventCLM T hT hs f, f⟫ ≤ ‖resolventCLM T hT hs f‖ * ‖f‖ := real_inner_le_norm _ _
      _ ≤ ‖f‖ * ‖f‖ := by
          gcongr
          exact norm_resolventCLM_le T hT hs f
      _ = ⟪f, f⟫ := (real_inner_self_eq_norm_mul_norm f).symm
  rw [yosida_apply, real_inner_smul_left, inner_sub_left]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (by linarith)

/-- The Yosida approximation is symmetric, because `J_s` is. -/
theorem yosida_symm (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f g : H₀) :
    ⟪yosida T hT hs f, g⟫ = ⟪f, yosida T hT hs g⟫ := by
  rw [yosida_apply, yosida_apply, real_inner_smul_left, real_inner_smul_right, inner_sub_left,
    inner_sub_right, resolventCLM_symm]

/-- The Yosida family commutes, `L_s L_r = L_r L_s`.  Both sides expand to
`s⁻¹ r⁻¹ (1 - J_s - J_r + J_s J_r)`, and `J_s J_r = J_r J_s` is resolvent commutation
(`resolventCLM_comp_comm`). -/
theorem yosida_comp_comm (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) :
    (yosida T hT hs).comp (yosida T hT hr) = (yosida T hT hr).comp (yosida T hT hs) := by
  ext f
  have hcomm := ContinuousLinearMap.ext_iff.mp (resolventCLM_comp_comm T hT hs hr) f
  simp only [ContinuousLinearMap.comp_apply] at hcomm
  simp only [ContinuousLinearMap.comp_apply, yosida_apply, map_smul, map_sub, hcomm]
  module

/-- On `D(T†T)` the Yosida approximation is `L_s = J_s T†T`.  This is the resolvent defect identity
(`sub_resolvent_eq_smul`) divided by `s`. -/
theorem yosida_apply_eq_resolventCLM_adjointComp (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {s : ℝ} (hs : 0 < s) (f : (adjointComp T).domain) :
    yosida T hT hs f = resolventCLM T hT hs (adjointComp T f) := by
  rw [yosida_apply, sub_resolvent_eq_smul T hT hd hs f, smul_smul, inv_mul_cancel₀ hs.ne',
    one_smul]

/-- On `D(T†T)` the Yosida approximation converges strongly to `T†T` as `s ↓ 0`.  By
`yosida_apply_eq_resolventCLM_adjointComp`
the difference is `J_s (T†T f) - T†T f`, which strong resolvent convergence
(`exists_delta_norm_resolventCLM_sub_lt`) makes small. -/
theorem exists_delta_norm_yosida_sub_adjointComp_lt (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : (adjointComp T).domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
      ‖yosida T hT hs f - adjointComp T f‖ < ε := by
  obtain ⟨δ, hδ, hlt⟩ :=
    exists_delta_norm_resolventCLM_sub_lt T hT hd (adjointComp T f) hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ
  rw [yosida_apply_eq_resolventCLM_adjointComp T hT hd hs f]
  exact hlt hs hsδ

end FunctionalInequalities.Analysis.Semigroup

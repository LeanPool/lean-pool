/-
Copyright (c) 2026 BrownianMotion contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BrownianMotion contributors
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: Lean/Mathlib v4.35.0 replacements
-- of deprecated names (identifier-only); see vendor/port.patch.
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Analysis lemmas for Brownian motion -/


@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

attribute [simp] convex_empty
attribute [simp] convex_univ

@[nontriviality]
lemma convexOn_subsingleton {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [Subsingleton E] [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 E] [Module 𝕜 β] (s : Set E)
    (f : E → β) : ConvexOn 𝕜 s f := by
  constructor
  · exact Subsingleton.set_cases (by simp) (by simp) s
  · intro x hx y hy a b ha hb hab
    simp_rw [Subsingleton.eq_zero (α := E), ← add_smul, hab, one_smul]
    rfl

lemma convexOn_rpow_norm {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ p) := by
  nontriviality E
  refine ConvexOn.comp (g := fun x ↦ x ^ p) ?_ convexOn_univ_norm ?_
  · refine (convexOn_rpow hp).subset ?_ ?_
    · rintro - ⟨y, -, rfl⟩
      simp
    rintro - ⟨x, -, rfl⟩ - ⟨y, -, rfl⟩ a b ha hb hab
    obtain hx | hx := eq_or_ne ‖x‖ 0
    · refine ⟨b • y, by simp, ?_⟩
      simp [hx, norm_smul, hb]
    · refine ⟨((a * ‖x‖ + b * ‖y‖) / ‖x‖) • x, by simp, ?_⟩
      simp only [norm_smul, norm_div, Real.norm_eq_abs, abs_norm, isUnit_iff_ne_zero, ne_eq, hx,
        not_false_eq_true, IsUnit.div_mul_cancel, smul_eq_mul, abs_eq_self]
      positivity
  · apply (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by linarith)).mono
    rintro - ⟨x, -, rfl⟩
    simp

lemma lpNorm_congr {α ε : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
    [NormedAddCommGroup ε] {f g : α → ε} (hfg : f =ᵐ[μ] g) :
    lpNorm f p μ = lpNorm g p μ := by
  rw [lpNorm, lpNorm, eLpNorm_congr_ae hfg]

lemma lpNorm_rpow_nnreal_eq_integral {α ε : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup ε] {f : α → ε} {p : ℝ≥0} (hp : p ≠ 0)
    (hf : AEStronglyMeasurable f μ) :
    (lpNorm f p μ) ^ (p : ℝ) = ∫ a, ‖f a‖ ^ (p : ℝ) ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by simpa) (by simp) hf,
    show (p : ℝ≥0∞).toReal = p from rfl, Real.rpow_inv_rpow]
  · positivity
  simpa

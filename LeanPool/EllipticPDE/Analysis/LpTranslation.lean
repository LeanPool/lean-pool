/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import LeanPool.EllipticPDE.Analysis.PoincareInequality


/-!
# `L²` translation estimate

For a continuously differentiable, compactly supported `f : ℝⁿ → ℝ`, the `L²`
norm of the difference between `f` and its translate `f(· + h)` is controlled by
the displacement `‖h‖` and the `L²` norm of the gradient:
`∫ x, (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2`.

This is the gradient-to-`L²` translation estimate, the equicontinuity input to the
Fréchet-Kolmogorov precompactness criterion and hence to the Rellich-Kondrachov
compact embedding.

The argument writes `f (x + h) - f x = ∫ t in 0..1, (fderiv ℝ f (x + t • h)) h`
by the fundamental theorem of calculus along the segment `t ↦ x + t • h`, squares
through the one-variable Cauchy-Schwarz bound on `[0, 1]`
(`MeasureTheory.sq_intervalIntegral_le`), integrates over `x`, swaps the order of
integration (Tonelli, the integrand being a continuous function supported in a
bounded slab), and uses translation invariance of the Lebesgue integral to collapse
the inner translate back to the gradient integral.

## Main results

* `MeasureTheory.integral_sq_sub_translation_le`: the `L²` translation estimate.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral Metric
open scoped ENNReal

noncomputable section

namespace MeasureTheory

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- The segment path `t ↦ f (x + t • h)` has derivative `(fderiv ℝ f (x + t • h)) h`
at every `t`, for a differentiable `f`. -/
private theorem hasDerivAt_comp_segment (hf : ContDiff ℝ 1 f)
    (x h : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • h)) ((fderiv ℝ f (x + t • h)) h) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f (x + t • h)) (x + t • h) :=
    hf.differentiable_one.differentiableAt.hasFDerivAt
  exact hf'.comp_hasDerivAt t hline

/-- Continuity of the segment derivative `t ↦ (fderiv ℝ f (x + t • h)) h`. -/
private theorem continuous_segment_deriv (hf : ContDiff ℝ 1 f)
    (x h : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun t : ℝ => (fderiv ℝ f (x + t • h)) h) :=
  ((hf.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const

/-- Joint continuity of `(x, t) ↦ ((fderiv ℝ f (x + t • h)) h) ^ 2`. -/
private theorem continuous_uncurry_segment (hf : ContDiff ℝ 1 f)
    (h : EuclideanSpace ℝ (Fin n)) :
    Continuous (Function.uncurry fun (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) =>
        ((fderiv ℝ f (x + t • h)) h) ^ 2) :=
  (((hf.continuous_fderiv (by norm_num)).comp (by fun_prop : Continuous
    fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1 + p.2 • h)).clm_apply continuous_const).pow 2

/-- Fundamental theorem of calculus along the segment from `x` to `x + h`. -/
private theorem sub_translation_eq_integral (hf : ContDiff ℝ 1 f)
    (x h : EuclideanSpace ℝ (Fin n)) :
    f (x + h) - f x = ∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • h)) h := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_comp_segment hf x h t)
        (continuous_segment_deriv hf x h).continuousOn.intervalIntegrable]
  simp

/-- Pointwise square estimate: `(f (x + h) - f x) ^ 2` is at most the `[0, 1]`
integral of the squared segment derivative. -/
private theorem sq_sub_translation_le (hf : ContDiff ℝ 1 f)
    (x h : EuclideanSpace ℝ (Fin n)) :
    (f (x + h) - f x) ^ 2 ≤ ∫ t in (0 : ℝ)..1, ((fderiv ℝ f (x + t • h)) h) ^ 2 := by
  rw [sub_translation_eq_integral hf x h]
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have := MeasureTheory.sq_intervalIntegral_le h01
    (continuous_segment_deriv hf x h).continuousOn
  simpa using this

/-- The squared-gradient integrand `x ↦ (fderiv ℝ f x v) ^ 2` is integrable for a
`C¹` compactly supported `f`. -/
private theorem integrable_grad_apply_sq (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => ((fderiv ℝ f x) v) ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
  · exact (((hfc.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v)
      (by simp)).comp_left (g := fun r : ℝ => r ^ 2) (by simp))

/-- The squared gradient norm `x ↦ ‖fderiv ℝ f x‖ ^ 2` is integrable for a `C¹`
compactly supported `f`. -/
private theorem integrable_grad_norm_sq (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hf.continuous_fderiv (by norm_num)).norm.pow 2
  · exact ((hfc.fderiv ℝ).norm.comp_left (g := fun r : ℝ => r ^ 2) (by simp))

/-- The integrand `(x, t) ↦ ((fderiv ℝ f (x + t • h)) h) ^ 2` is integrable for the
product of Lebesgue measure with the unit-interval slice. -/
private theorem integrable_uncurry_segment (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (h : EuclideanSpace ℝ (Fin n)) :
    Integrable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) =>
        ((fderiv ℝ f (x + t • h)) h) ^ 2)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set g : EuclideanSpace ℝ (Fin n) × ℝ → ℝ :=
    Function.uncurry fun (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) =>
      ((fderiv ℝ f (x + t • h)) h) ^ 2 with hg
  set ρ : Measure (EuclideanSpace ℝ (Fin n) × ℝ) :=
    volume.prod (volume.restrict (Ioc (0 : ℝ) 1)) with hρ
  have hcont : Continuous g := continuous_uncurry_segment hf h
  obtain ⟨R, hR⟩ := (hfc.fderiv ℝ).isCompact.isBounded.subset_closedBall 0
  set C : Set (EuclideanSpace ℝ (Fin n) × ℝ) := closedBall 0 (R + ‖h‖) ×ˢ Icc 0 1 with hC
  have hCcomp : IsCompact C := (isCompact_closedBall _ _).prod isCompact_Icc
  -- Integrable on the compact slab `C`.
  have hIntOn : IntegrableOn g C ρ := hcont.locallyIntegrable.integrableOn_isCompact hCcomp
  -- `g` vanishes off `C` on the support of `ρ` (where `t ∈ Ioc 0 1`).
  have hzero : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, p.2 ∈ Ioc (0 : ℝ) 1 → p ∉ C → g p = 0 := by
    rintro ⟨x, t⟩ ht hpC
    have hxball : x ∉ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + ‖h‖) := by
      intro hx; exact hpC ⟨hx, ⟨le_of_lt ht.1, ht.2⟩⟩
    have hxt : x + t • h ∉ tsupport (fderiv ℝ f) := by
      intro hmem
      apply hxball
      have hxK : ‖x + t • h‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hR hmem
      have htnorm : ‖t • h‖ ≤ ‖h‖ := by
        rw [norm_smul]
        have htle : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2
        nlinarith [norm_nonneg h, htle]
      have hxle : ‖x‖ ≤ R + ‖h‖ := by
        calc ‖x‖ = ‖(x + t • h) - t • h‖ := by congr 1; abel
          _ ≤ ‖x + t • h‖ + ‖t • h‖ := norm_sub_le _ _
          _ ≤ R + ‖h‖ := by linarith
      simpa [mem_closedBall, dist_eq_norm] using hxle
    simp only [hg, Function.uncurry_apply_pair,
      image_eq_zero_of_notMem_tsupport hxt, _root_.zero_apply]
    norm_num
  -- Almost everywhere `t ∈ Ioc 0 1`, so `g =ᵐ[ρ] C.indicator g`.
  have htioc : ∀ᵐ p ∂ρ, p.2 ∈ Ioc (0 : ℝ) 1 := by
    have hnull : ρ {p : EuclideanSpace ℝ (Fin n) × ℝ | p.2 ∉ Ioc (0 : ℝ) 1} = 0 := by
      have hset : {p : EuclideanSpace ℝ (Fin n) × ℝ | p.2 ∉ Ioc (0 : ℝ) 1}
          = univ ×ˢ (Ioc (0 : ℝ) 1)ᶜ := by ext p; simp
      rw [hset, hρ, Measure.prod_prod, Measure.restrict_apply' measurableSet_Ioc,
        compl_inter_self, measure_empty, mul_zero]
    rw [ae_iff]; exact hnull
  have hae : g =ᵐ[ρ] C.indicator g := by
    filter_upwards [htioc] with p hp
    by_cases hpC : p ∈ C
    · rw [indicator_of_mem hpC]
    · rw [indicator_of_notMem hpC, hzero p hp hpC]
  rw [integrable_congr hae]
  exact (integrable_indicator_iff hCcomp.measurableSet).mpr hIntOn

/-- **`L²` translation estimate.** For a continuously differentiable, compactly
supported `f : ℝⁿ → ℝ`,
`∫ x, (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2`. -/
theorem integral_sq_sub_translation_le (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (h : EuclideanSpace ℝ (Fin n)) :
    ∫ x, (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  set F : EuclideanSpace ℝ (Fin n) → ℝ → ℝ :=
    fun x t => ((fderiv ℝ f (x + t • h)) h) ^ 2 with hF
  have hInt := integrable_uncurry_segment hf hfc h
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- LHS is integrable (continuous, compact support).
  have hLHS_int : Integrable (fun x => (f (x + h) - f x) ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hf.continuous.comp (by fun_prop)).sub hf.continuous).pow 2
    · exact (((hfc.comp_homeomorph (Homeomorph.addRight h)).sub hfc).comp_left
        (g := fun r : ℝ => r ^ 2) (by simp))
  -- The inner translate integral is integrable in `x`.
  have hRHS_int : Integrable (fun x => ∫ t in (0 : ℝ)..1, F x t) := by
    simp_rw [intervalIntegral.integral_of_le h01]
    exact hInt.integral_prod_left
  -- Step A: integrate the pointwise square bound.
  have stepA : ∫ x, (f (x + h) - f x) ^ 2 ≤ ∫ x, ∫ t in (0 : ℝ)..1, F x t :=
    integral_mono hLHS_int hRHS_int (fun x => sq_sub_translation_le hf x h)
  -- Step B: swap the order of integration.
  have stepB : ∫ x, ∫ t in (0 : ℝ)..1, F x t = ∫ t in (0 : ℝ)..1, ∫ x, F x t := by
    simp_rw [intervalIntegral.integral_of_le h01]
    exact integral_integral_swap hInt
  -- Step C: translation invariance collapses the inner integral, constant in `t`.
  have stepC : (∫ t in (0 : ℝ)..1, ∫ x, F x t) = ∫ x, ((fderiv ℝ f x) h) ^ 2 := by
    have hI0 : ∀ t : ℝ, (∫ x, F x t) = ∫ x, ((fderiv ℝ f x) h) ^ 2 := fun t =>
      integral_add_right_eq_self (fun x => ((fderiv ℝ f x) h) ^ 2) (t • h)
    rw [intervalIntegral.integral_congr (g := fun _ => ∫ x, ((fderiv ℝ f x) h) ^ 2)
        (fun t _ => hI0 t)]
    simp
  -- Step D: bound the segment derivative by the operator norm of the gradient.
  have stepD : (∫ x, ((fderiv ℝ f x) h) ^ 2) ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
    have hpt : ∀ x, ((fderiv ℝ f x) h) ^ 2 ≤ ‖h‖ ^ 2 * ‖fderiv ℝ f x‖ ^ 2 := by
      intro x
      have hle : ‖(fderiv ℝ f x) h‖ ≤ ‖fderiv ℝ f x‖ * ‖h‖ := (fderiv ℝ f x).le_opNorm h
      calc ((fderiv ℝ f x) h) ^ 2 = ‖(fderiv ℝ f x) h‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        _ ≤ (‖fderiv ℝ f x‖ * ‖h‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = ‖h‖ ^ 2 * ‖fderiv ℝ f x‖ ^ 2 := by ring
    calc ∫ x, ((fderiv ℝ f x) h) ^ 2
        ≤ ∫ x, ‖h‖ ^ 2 * ‖fderiv ℝ f x‖ ^ 2 :=
          integral_mono (integrable_grad_apply_sq hf hfc h)
            ((integrable_grad_norm_sq hf hfc).const_mul _) hpt
      _ = ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := integral_const_mul _ _
  calc ∫ x, (f (x + h) - f x) ^ 2
      ≤ ∫ x, ∫ t in (0 : ℝ)..1, F x t := stepA
    _ = ∫ t in (0 : ℝ)..1, ∫ x, F x t := stepB
    _ = ∫ x, ((fderiv ℝ f x) h) ^ 2 := stepC
    _ ≤ ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := stepD

end MeasureTheory

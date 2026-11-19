/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The global Lipschitz cut-off

Let `g` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood of `0` in a finite-dimensional real normed space
`E`, with `g 0 = 0` and derivative `A` at `0`. For every `η > 0` there are `δ > 0` and a `Cⁿ` map
`φ : E → E`, globally `η`-Lipschitz, with `φ 0 = 0` and `Dφ(0) = 0`, such that `g = A + φ` on the
ball of radius `δ` (`StableManifold.exists_contDiff_lipschitzWith_eqOn_ball`). Thus near `0`, `g`
is a globally small Lipschitz perturbation of its linear part, to which the global theory
(`StableManifold.Perturbation`) applies.

* `StableManifold.exists_cutoff`: a smooth function `ρ : E → ℝ` with values in `[0, 1]`, equal to
  `1` on the closed unit ball and to `0` off the open ball of radius `2`, with bounded derivative;
* `StableManifold.exists_norm_fderiv_le_of_hasFDerivAt_zero`: a `C¹` map with `ψ 0 = 0` and
  `Dψ(0) = 0` satisfies `‖Dψ x‖ ≤ η` and `‖ψ x‖ ≤ η ‖x‖` on a small closed ball;
* `StableManifold.exists_contDiff_lipschitzWith_eqOn_ball`: the cut-off.

## Proofs

* `exists_cutoff`: the bump function `ContDiffBump (0 : E)` with radii `1` and `2` (finite
  dimension provides `HasContDiffBump E`), with `ContDiffBump.contDiff`, `one_of_mem_closedBall`,
  `zero_of_le_dist`, `nonneg` and `le_one`. Its derivative is continuous
  (`ContDiff.continuous_fderiv`) with compact support (`ContDiffBump.hasCompactSupport`,
  `HasCompactSupport.fderiv`), hence bounded (`Continuous.bounded_above_of_compact_support`).
* `exists_norm_fderiv_le_of_hasFDerivAt_zero`: `fderiv ℝ ψ` is continuous at `0`
  (`ContDiffAt.continuousAt_fderiv`) with value `0`, so some ball `ball 0 ε` lies in
  `{x | ‖Dψ x‖ < η} ∩ interior W`; take `r = ε / 2`. On `closedBall 0 r`, `ψ` is differentiable
  (`ContDiffOn.contDiffAt` on `interior W`), and the mean value inequality between `0` and `x`
  (`Convex.norm_image_sub_le_of_norm_fderiv_le`) gives `‖ψ x‖ ≤ η ‖x‖`.
* `exists_contDiff_lipschitzWith_eqOn_ball`: let `ψ = g - A` (derivative `0` at `0`), `M` a bound
  of `‖Dρ‖`, `η' = η / (2 M + 1)`, `r` as in the previous lemma for `η'`, `δ = r / 2`, and
  `φ x = ρ (δ⁻¹ • x) • ψ x`.
  - `φ = ψ` on `ball 0 δ`, where `ρ (δ⁻¹ • x) = 1`, so `g = A + φ` there; `φ 0 = 0`; and
    `Dφ(0) = Dψ(0) = 0` (`HasFDerivAt.congr_of_eventuallyEq`).
  - `Cⁿ` (`contDiff_iff_contDiffAt`): at a point with `‖x‖ ≤ r`, `φ` is a product of maps that are
    `Cⁿ` there (`ContDiffAt.smul`, as `closedBall 0 r ⊆ interior W`); on the open set
    `{x | r < ‖x‖}` it is `0` (`ContDiffAt.congr_of_eventuallyEq`, `contDiffAt_const`).
  - Lipschitz: for `‖x‖ ≤ r`, `Dφ x = ρ (δ⁻¹ • x) • Dψ x + c'.smulRight (ψ x)` with
    `c' = Dρ (δ⁻¹ • x) ∘ (δ⁻¹ • id)` (`HasFDerivAt.smul`, `HasFDerivAt.comp`), so
    `‖Dφ x‖ ≤ η' + (M / δ) (η' · 2 δ) = η' (2 M + 1) = η`; for `‖x‖ > r`, `Dφ x = 0`. Then
    `lipschitzWith_of_nnnorm_fderiv_le`.
-/

@[expose] public section

open Filter Topology Metric Set
open scoped NNReal

namespace StableManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A **smooth cut-off**: `ρ : E → ℝ`, `C^∞`, with values in `[0, 1]`, equal to `1` on the closed
unit ball and to `0` off the open ball of radius `2`, with bounded derivative.

Proof: a `ContDiffBump (0 : E)` with radii `1` and `2`; its derivative is continuous with compact
support. -/
theorem exists_cutoff :
    ∃ ρ : E → ℝ, (∀ m : ℕ∞, ContDiff ℝ m ρ) ∧ (∀ x, ‖x‖ ≤ 1 → ρ x = 1) ∧
      (∀ x, 2 ≤ ‖x‖ → ρ x = 0) ∧ (∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1) ∧
      ∃ M, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ ρ x‖ ≤ M := by
  let f : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hf : ContDiff ℝ 1 f := f.contDiff
  obtain ⟨C, hC⟩ := (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (f.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨f, fun m ↦ f.contDiff, fun x hx ↦ f.one_of_mem_closedBall ?_,
    fun x hx ↦ f.zero_of_le_dist ?_, fun x ↦ ⟨f.nonneg, f.le_one⟩,
    max C 0, le_max_right _ _, fun x ↦ (hC x).trans (le_max_left _ _)⟩
  · simpa [f] using hx
  · simpa [f] using hx

omit [FiniteDimensional ℝ E] in
/-- A `C¹` map near `0` with `ψ 0 = 0` and `Dψ(0) = 0` has, on a small closed ball inside the
interior of its domain, derivative of norm `≤ η` and values of norm `≤ η ‖x‖`.

Proof: continuity of `fderiv ℝ ψ` at `0`, and the mean value inequality on the ball. -/
theorem exists_norm_fderiv_le_of_hasFDerivAt_zero {ψ : E → E} {W : Set E} {n : ℕ∞} (hn : 1 ≤ n)
    (hW : W ∈ 𝓝 0) (hψ : ContDiffOn ℝ n ψ W) (hψ0 : ψ 0 = 0)
    (hdψ : HasFDerivAt ψ (0 : E →L[ℝ] E) 0) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, closedBall (0 : E) r ⊆ interior W ∧
      ∀ x ∈ closedBall (0 : E) r, ‖fderiv ℝ ψ x‖ ≤ η ∧ ‖ψ x‖ ≤ η * ‖x‖ := by
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le hn).ne'
  have hcont : Tendsto (fun x ↦ ‖fderiv ℝ ψ x‖) (𝓝 0) (𝓝 0) := by
    have := ((hψ.contDiffAt hW).continuousAt_fderiv hn0).norm
    rwa [ContinuousAt, hdψ.fderiv, norm_zero] at this
  have hS : {x | ‖fderiv ℝ ψ x‖ < η} ∩ interior W ∈ 𝓝 (0 : E) :=
    inter_mem (hcont.eventually_lt_const hη) (interior_mem_nhds.2 hW)
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.1 hS
  have hsub : closedBall (0 : E) (ε / 2) ⊆ ball 0 ε := closedBall_subset_ball (half_lt_self hε)
  have hdiff : ∀ x ∈ closedBall (0 : E) (ε / 2), DifferentiableAt ℝ ψ x := fun x hx ↦
    ((hψ.mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds (hεS (hsub hx)).2)).differentiableAt hn0
  refine ⟨ε / 2, half_pos hε, fun x hx ↦ (hεS (hsub hx)).2,
    fun x hx ↦ ⟨(hεS (hsub hx)).1.le, ?_⟩⟩
  have := (convex_closedBall (0 : E) (ε / 2)).norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun y hy ↦ (hεS (hsub hy)).1.le) (mem_closedBall_self (half_pos hε).le) hx
  simpa [hψ0] using this

/-- **The global Lipschitz cut-off.** Let `g` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood `W` of `0`,
with `g 0 = 0` and derivative `A` at `0`. For every `η > 0` there are `δ > 0` and a `Cⁿ` map
`φ : E → E`, globally `η`-Lipschitz, with `φ 0 = 0` and derivative `0` at `0`, such that
`g x = A x + φ x` on the ball of radius `δ`.

Proof: `φ x = ρ (δ⁻¹ • x) • (g x - A x)` with the cut-off `ρ` of `exists_cutoff` and `δ` small
(`exists_norm_fderiv_le_of_hasFDerivAt_zero`); its derivative has norm `≤ η` everywhere, so it is
`η`-Lipschitz (`lipschitzWith_of_nnnorm_fderiv_le`). -/
theorem exists_contDiff_lipschitzWith_eqOn_ball {g : E → E} {A : E →L[ℝ] E} {W : Set E}
    {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 0) (hg : ContDiffOn ℝ n g W) (hg0 : g 0 = 0)
    (hA : HasFDerivAt g A 0) {η : ℝ≥0} (hη : 0 < η) :
    ∃ δ > 0, ∃ φ : E → E, ContDiff ℝ n φ ∧ LipschitzWith η φ ∧ φ 0 = 0 ∧
      HasFDerivAt φ (0 : E →L[ℝ] E) 0 ∧ EqOn g (fun x ↦ A x + φ x) (ball 0 δ) := by
  -- the remainder `ψ = g - A`, and the cut-off `ρ`
  let ψ : E → E := fun x ↦ g x - A x
  have hψ : ContDiffOn ℝ n ψ W := hg.sub A.contDiff.contDiffOn
  have hψ0 : ψ 0 = 0 := by simp [ψ, hg0]
  have hdψ : HasFDerivAt ψ (0 : E →L[ℝ] E) 0 := by
    have := hA.sub A.hasFDerivAt
    rwa [sub_self] at this
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le hn).ne'
  obtain ⟨ρ, hρ, hρ1, hρ0, hρI, M, hM, hρM⟩ := exists_cutoff (E := E)
  have hM1 : 0 < 2 * M + 1 := by linarith
  set η' : ℝ := η / (2 * M + 1) with hη'
  have hη'0 : 0 < η' := div_pos (by exact_mod_cast hη) hM1
  obtain ⟨r, hr, hrW, hrψ⟩ := exists_norm_fderiv_le_of_hasFDerivAt_zero hn hW hψ hψ0 hdψ hη'0
  set δ := r / 2 with hδdef
  have hδ : 0 < δ := half_pos hr
  let φ : E → E := fun x ↦ ρ (δ⁻¹ • x) • ψ x
  have hnorm : ∀ x : E, ‖δ⁻¹ • x‖ = δ⁻¹ * ‖x‖ := fun x ↦ by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
  -- `φ = ψ` on the ball of radius `δ`, and `φ = 0` off the closed ball of radius `r = 2 δ`
  have hφψ : ∀ x ∈ ball (0 : E) δ, φ x = ψ x := fun x hx ↦ by
    have : ‖δ⁻¹ • x‖ ≤ 1 := by
      rw [hnorm, inv_mul_le_iff₀ hδ, mul_one]
      exact (mem_ball_zero_iff.1 hx).le
    simp [φ, hρ1 _ this]
  have hφ0 : ∀ x : E, r < ‖x‖ → φ =ᶠ[𝓝 x] fun _ ↦ 0 := fun x hx ↦ by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    have : 2 ≤ ‖δ⁻¹ • y‖ := by
      rw [hnorm, le_inv_mul_iff₀ hδ]
      have hy' : r < ‖y‖ := hy
      linarith
    simp [φ, hρ0 _ this]
  have hxW : ∀ x : E, ‖x‖ ≤ r → interior W ∈ 𝓝 x := fun x hx ↦
    isOpen_interior.mem_nhds (hrW (mem_closedBall_zero_iff.2 hx))
  -- smoothness
  have hρδ : ContDiff ℝ n fun x : E ↦ ρ (δ⁻¹ • x) := (hρ n).comp (contDiff_const_smul δ⁻¹)
  have hφC : ContDiff ℝ n φ := by
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    rcases le_or_gt ‖x‖ r with hx | hx
    · exact hρδ.contDiffAt.smul ((hψ.mono interior_subset).contDiffAt (hxW x hx))
    · exact contDiffAt_const.congr_of_eventuallyEq (hφ0 x hx)
  refine ⟨δ, hδ, φ, hφC, ?_, by simp [φ, hψ0],
    hdψ.congr_of_eventuallyEq (eventually_of_mem (ball_mem_nhds 0 hδ) hφψ), fun x hx ↦ ?_⟩
  · -- the derivative of `φ` has norm `≤ η` everywhere
    refine lipschitzWith_of_nnnorm_fderiv_le (hφC.differentiable hn0) fun x ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    rcases le_or_gt ‖x‖ r with hx | hx
    · have hψx : HasFDerivAt ψ (fderiv ℝ ψ x) x :=
        (((hψ.mono interior_subset).contDiffAt (hxW x hx)).differentiableAt hn0).hasFDerivAt
      set c' : E →L[ℝ] ℝ := (fderiv ℝ ρ (δ⁻¹ • x)).comp (δ⁻¹ • ContinuousLinearMap.id ℝ E)
      have hρx : HasFDerivAt (fun y : E ↦ ρ (δ⁻¹ • y)) c' x :=
        ((hρ 1).differentiable one_ne_zero _).hasFDerivAt.comp x
          ((hasFDerivAt_id x).const_smul δ⁻¹)
      have hD : fderiv ℝ φ x = ρ (δ⁻¹ • x) • fderiv ℝ ψ x + c'.smulRight (ψ x) :=
        (hρx.smul hψx).fderiv
      have h1 : ‖ρ (δ⁻¹ • x) • fderiv ℝ ψ x‖ ≤ η' := by
        rw [norm_smul, Real.norm_of_nonneg (hρI _).1]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hρI _).2).trans
          (hrψ x (mem_closedBall_zero_iff.2 hx)).1
      have hc' : ‖c'‖ ≤ M * δ⁻¹ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hρM _) ?_ (norm_nonneg _) hM)
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
        exact mul_le_of_le_one_right (inv_nonneg.2 hδ.le) ContinuousLinearMap.norm_id_le
      have hψx' : ‖ψ x‖ ≤ η' * (2 * δ) :=
        (hrψ x (mem_closedBall_zero_iff.2 hx)).2.trans
          (mul_le_mul_of_nonneg_left (by linarith) hη'0.le)
      have h2 : ‖c'.smulRight (ψ x)‖ ≤ 2 * M * η' := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        calc ‖c'‖ * ‖ψ x‖ ≤ (M * δ⁻¹) * (η' * (2 * δ)) :=
              mul_le_mul hc' hψx' (norm_nonneg _) (by positivity)
          _ = 2 * M * η' := by field_simp
      calc ‖fderiv ℝ φ x‖ ≤ η' + 2 * M * η' := hD ▸ (norm_add_le _ _).trans (add_le_add h1 h2)
        _ = η := by rw [hη']; field_simp; ring
    · rw [(hφ0 x hx).fderiv_eq, fderiv_const_apply, norm_zero]
      exact η.coe_nonneg
  · simp only [hφψ x hx, ψ, add_sub_cancel]

end StableManifold

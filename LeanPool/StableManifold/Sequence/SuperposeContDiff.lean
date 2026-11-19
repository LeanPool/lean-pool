/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Sequence.Superpose
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Smoothness of the superposition operator

Let `E` be a finite-dimensional real normed space and `φ : E → G` a `Cⁿ` map. Then the
superposition operator `x ↦ φ ∘ x` on the Banach space `ℕ →ᵇ E` of bounded sequences is `Cⁿ`
(`StableManifold.contDiff_superpose`, `n ≤ ∞`), with derivative
`D(superpose φ)(x) y = (n ↦ Dφ(x n) (y n))` (`StableManifold.hasFDerivAt_superpose`).

A bounded sequence takes its values in a compact ball of `E` (finite dimension), on which the
derivatives of `φ` are uniformly continuous; this is what makes the superposition operator
differentiable in the sup norm. No compact support or global bound on `φ` is needed.

* `StableManifold.exists_norm_sub_sub_fderiv_le`: the first-order Taylor remainder of a `C¹` map
  is `o(‖b‖)` uniformly for base points in a ball;
* `StableManifold.hasFDerivAt_superpose`, `StableManifold.fderiv_superpose`: the derivative;
* `StableManifold.contDiff_superpose`: `Cⁿ` regularity.

`E` and `G` live in the same universe, so that the induction on `n` can pass from `φ : E → G` to
`fderiv ℝ φ : E → (E →L[ℝ] G)` (`StableManifold.Perron.Smooth` uses it with `G = E`).

## Proofs

* `exists_norm_sub_sub_fderiv_le`: `fderiv ℝ φ` is continuous (`ContDiff.continuous_fderiv`),
  hence uniformly continuous on the compact ball `closedBall 0 (R + 1)`
  (`IsCompact.uniformContinuousOn_of_continuous`): take `δ` with `‖Dφ z - Dφ a‖ ≤ ε` when
  `‖z - a‖ < δ` in that ball, and use `min δ 1`, so that `ball a (min δ 1)` lies in the ball. The
  mean value inequality on `ball a (min δ 1)`, for `φ` and the linear map `Dφ(a)`
  (`Convex.norm_image_sub_le_of_norm_fderiv_le'`), gives `‖φ (a + b) - φ a - Dφ(a) b‖ ≤ ε ‖b‖`.
* `hasFDerivAt_superpose`: given `c > 0`, take `δ` from the previous lemma with `R = ‖x‖`. For
  `‖y‖ < δ`, evaluating at each `n` (`superpose_apply`, `applyCLM_apply`) and taking the sup
  (`BoundedContinuousFunction.norm_le`) gives
  `‖superpose φ (x + y) - superpose φ x - applyCLM (superpose (fderiv ℝ φ) x) y‖ ≤ c ‖y‖`, which
  is `HasFDerivAt` (`hasFDerivAt_iff_isLittleO_nhds_zero`, `Asymptotics.isLittleO_iff`).
  `fderiv_superpose`: `HasFDerivAt.fderiv`.
* `contDiff_superpose`: for `m : ℕ`, induction on `m`, generalizing `G` (in the universe `u`).
  `m = 0` is `continuous_superpose` (`contDiff_zero`). For `m + 1`, by `contDiff_succ_iff_fderiv`
  it suffices that `superpose φ` is differentiable (`hasFDerivAt_superpose`) and that
  `fderiv ℝ (superpose φ) = applyCLM ∘ superpose (fderiv ℝ φ)` (`fderiv_superpose`) is `Cᵐ`: the
  continuous linear map `applyCLM` is smooth, and `superpose (fderiv ℝ φ)` is `Cᵐ` by the
  induction hypothesis for `fderiv ℝ φ : E → (E →L[ℝ] G)`, which is `Cᵐ`
  (`contDiff_succ_iff_fderiv` again). For `n = ∞`, `contDiff_infty` reduces to the finite orders
  (`ENat.recTopCoe`).
-/

@[expose] public section

open Filter Topology Metric
open scoped NNReal BoundedContinuousFunction

universe u

namespace StableManifold

open BoundedContinuousFunction

variable {E G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Uniform first-order Taylor estimate** for a `C¹` map: for base points `a` in the ball of
radius `R`, `‖φ (a + b) - φ a - Dφ(a) b‖ ≤ ε ‖b‖` as soon as `‖b‖ < δ`.

Proof: `Dφ` is uniformly continuous on `closedBall 0 (R + 1)`; mean value inequality for
`z ↦ φ z - Dφ(a) z` on the segment `[a, a + b]`. -/
theorem exists_norm_sub_sub_fderiv_le {φ : E → G} (hφ : ContDiff ℝ 1 φ) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : E, ‖a‖ ≤ R → ‖b‖ < δ →
      ‖φ (a + b) - φ a - fderiv ℝ φ a b‖ ≤ ε * ‖b‖ := by
  obtain ⟨δ, hδ, hφδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : E) (R + 1)).uniformContinuousOn_of_continuous
      (hφ.continuous_fderiv one_ne_zero).continuousOn) ε hε
  have hδ₁ : 0 < min δ 1 := lt_min hδ one_pos
  refine ⟨min δ 1, hδ₁, fun a b ha hb ↦ ?_⟩
  have hsub : ball a (min δ 1) ⊆ closedBall 0 (R + 1) := fun z hz ↦ by
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall_zero_iff]
    calc ‖z‖ ≤ ‖a‖ + ‖z - a‖ := norm_le_insert' _ _
      _ ≤ R + 1 := add_le_add ha (hz.le.trans (min_le_right _ _))
  have ha' : a ∈ closedBall (0 : E) (R + 1) := hsub (mem_ball_self hδ₁)
  have hab : a + b ∈ ball a (min δ 1) := by simpa [mem_ball, dist_eq_norm] using hb
  have bound : ∀ z ∈ ball a (min δ 1), ‖fderiv ℝ φ z - fderiv ℝ φ a‖ ≤ ε := fun z hz ↦ by
    rw [← dist_eq_norm]
    exact (hφδ z (hsub hz) a ha' ((mem_ball.1 hz).trans_le (min_le_left _ _))).le
  simpa using (convex_ball a (min δ 1)).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ ↦ hφ.differentiable one_ne_zero z) bound (mem_ball_self hδ₁) hab

/-- **The derivative of the superposition operator**: for a `C¹` map `φ`, the superposition
operator has at `x` the derivative `y ↦ (n ↦ Dφ(x n) (y n))`.

Proof: `exists_norm_sub_sub_fderiv_le` with `R = ‖x‖`, evaluated at each `n`. -/
theorem hasFDerivAt_superpose {φ : E → G} (hφ : ContDiff ℝ 1 φ) (x : ℕ →ᵇ E) :
    HasFDerivAt (superpose φ) (applyCLM (superpose (fderiv ℝ φ) x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hTaylor⟩ := exists_norm_sub_sub_fderiv_le hφ ‖x‖ hc
  filter_upwards [ball_mem_nhds (0 : ℕ →ᵇ E) hδ] with y hy
  rw [mem_ball_zero_iff] at hy
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun n ↦ ?_
  change ‖superpose φ (x + y) n - superpose φ x n -
    applyCLM (superpose (fderiv ℝ φ) x) y n‖ ≤ c * ‖y‖
  rw [applyCLM_apply, superpose_apply hφ.continuous, superpose_apply hφ.continuous,
    superpose_apply (hφ.continuous_fderiv one_ne_zero)]
  change ‖φ (x n + y n) - φ (x n) - fderiv ℝ φ (x n) (y n)‖ ≤ c * ‖y‖
  exact (hTaylor (x n) (y n) (x.norm_coe_le_norm n) ((y.norm_coe_le_norm n).trans_lt hy)).trans
    (by gcongr; exact y.norm_coe_le_norm n)

theorem fderiv_superpose {φ : E → G} (hφ : ContDiff ℝ 1 φ) :
    fderiv ℝ (superpose φ) = fun x ↦ applyCLM (superpose (fderiv ℝ φ) x) :=
  funext fun x ↦ (hasFDerivAt_superpose hφ x).fderiv

/-- **The superposition operator of a `Cⁿ` map is `Cⁿ`** on bounded sequences (`n ≤ ∞`).

Proof: induction on `n`, through `fderiv ℝ (superpose φ) = applyCLM ∘ superpose (fderiv ℝ φ)`
and the induction hypothesis for `fderiv ℝ φ`; `contDiff_infty` for `n = ∞`. -/
theorem contDiff_superpose {φ : E → G} {n : ℕ∞} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (superpose φ) := by
  suffices h : ∀ (m : ℕ) {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] {φ : E → G},
      ContDiff ℝ m φ → ContDiff ℝ m (superpose φ) by
    induction n using ENat.recTopCoe with
    | top => exact contDiff_infty.2 fun m ↦ h m (hφ.of_le (by exact_mod_cast le_top))
    | coe m => exact_mod_cast h m (by exact_mod_cast hφ)
  intro m
  induction m with
  | zero =>
    intro G _ _ φ hφ
    exact contDiff_zero.2 (continuous_superpose (contDiff_zero.1 hφ))
  | succ m ih =>
    intro G _ _ φ hφ
    have h1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast Nat.le_add_left 1 m)
    rw [Nat.cast_succ] at hφ ⊢
    refine contDiff_succ_iff_fderiv.2 ⟨fun x ↦ (hasFDerivAt_superpose h1 x).differentiableAt,
      by simp, ?_⟩
    rw [fderiv_superpose h1]
    exact applyCLM.contDiff.comp (ih (contDiff_succ_iff_fderiv.1 hφ).2.2)

end StableManifold

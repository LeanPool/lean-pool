/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicContDiff
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Weierstrass division from abstract Taylor division operators

Let `E` be a complex normed space and write points of `E × ℂ` as `(z, t)`. Suppose we are
given operators `Q h ρ d` and `Cf h ρ k` realising a *parametric Taylor division by `t ^ d`*
on polydiscs `ball 0 δ ×ˢ ball 0 R`:
`h = Q h ρ d · t ^ d + ∑_{k < d} Cf h ρ k (z) · t ^ k`, where `Q h ρ d` and `Cf h ρ k` are
holomorphic, `‖Cf h ρ k‖ ≤ M / ρ ^ k` and `‖Q h ρ d‖ ≤ C M` whenever `‖h‖ ≤ M`.

We deduce the Weierstrass division theorem: if `G` is holomorphic near `0` with
`G (0, t) = t ^ d u(t)`, `u(0) ≠ 0`, then every germ `h` can be written as
`h = q G + ∑_{k < d} r_k(z) t ^ k` with `q` and `r_k` holomorphic near `0`.

## Proof (Neumann series)

Choose `R` small so that `|u| ≥ m > 0` on `closedBall 0 R`, put `ρ = R / 2`, and write
`G = u(t) t ^ d + H` with `H (0, t) = 0`. By the tube lemma there is `δ > 0` such that on
`U = ball 0 δ ×ˢ ball 0 R` we have `2 C |H| ≤ m` and `|h| ≤ M`.
Put `h₀ = h`, `h_{k+1} = -H · Q(h_k) / u(t)`. Then `|h_k| ≤ M 2^{-k}` on `U`, and
`h_k = (Q(h_k) / u) G + ∑_j Cf(h_k)_j t ^ j + h_{k+1}`. Summing and letting `k → ∞` gives the
division with `q = ∑_k Q(h_k) / u` and `r_j = ∑_k Cf(h_k)_j`; both series converge uniformly
by the Weierstrass M-test and are holomorphic by the several-variable Weierstrass theorem
`SGPT.Foundations.Analysis.FirstPass.differentiableAt_of_tendstoUniformlyOn_ball`.

## Main statements

* `differentiableAt_tsum_of_forall_norm_le`: a normally convergent series of holomorphic
  functions on an open set is holomorphic.
* `neumannIter`: the Neumann iterates `h_k`.
* `neumannIter_differentiableOn_and_norm_le`: holomorphy and geometric bounds of `h_k`.
* `neumannIter_telescope`: the telescoped division identity.
* `exists_division_of_neumann`: the division on a fixed open set, from abstract operators.
* `exists_weierstrass_division_of_taylorDivision`: the Weierstrass division theorem for germs.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.Pending

open Metric Set Filter
open scoped Topology

section Series

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A series of complex differentiable functions on an open set, dominated by a summable
sequence, has a complex differentiable sum. -/
theorem differentiableAt_tsum_of_forall_norm_le {S : Set X} (hS : IsOpen S)
    {f : ℕ → X → ℂ} {a : ℕ → ℝ} (ha : Summable a)
    (hfd : ∀ k, DifferentiableOn ℂ (f k) S) (hfa : ∀ k, ∀ x ∈ S, ‖f k x‖ ≤ a k)
    {x : X} (hx : x ∈ S) : DifferentiableAt ℂ (fun y => ∑' k, f k y) x := by
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 hS x hx
  have hu := tendstoUniformlyOn_tsum_nat ha (s := S) fun n y hy => hfa n y hy
  exact FirstPass.differentiableAt_of_tendstoUniformlyOn_ball hε
    (Eventually.of_forall fun N =>
      (DifferentiableOn.fun_sum fun k _ => hfd k).mono hεS) (hu.mono hεS)

end Series

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Neumann iterates `h₀ = h`, `h_{k+1} = -(H · Q h_k) / v`. -/
noncomputable def neumannIter (Q : (E × ℂ → ℂ) → E × ℂ → ℂ) (H v h : E × ℂ → ℂ) :
    ℕ → E × ℂ → ℂ
  | 0 => h
  | k + 1 => fun x => -(H x * Q (neumannIter Q H v h k) x) / v x

/-- The Neumann iterates are complex differentiable and decay geometrically. -/
theorem neumannIter_differentiableOn_and_norm_le
    {U : Set (E × ℂ)} {Q : (E × ℂ → ℂ) → E × ℂ → ℂ} {C m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hQd : ∀ f, DifferentiableOn ℂ f U → DifferentiableOn ℂ (Q f) U)
    (hQb : ∀ (f : E × ℂ → ℂ) (M : ℝ), DifferentiableOn ℂ f U → (∀ x ∈ U, ‖f x‖ ≤ M) →
      ∀ x ∈ U, ‖Q f x‖ ≤ C * M)
    {H v h : E × ℂ → ℂ} (hHd : DifferentiableOn ℂ H U) (hvd : DifferentiableOn ℂ v U)
    (hvm : ∀ x ∈ U, m ≤ ‖v x‖) (hHC : ∀ x ∈ U, 2 * C * ‖H x‖ ≤ m)
    (hhd : DifferentiableOn ℂ h U) (hhM : ∀ x ∈ U, ‖h x‖ ≤ M) (k : ℕ) :
    DifferentiableOn ℂ (neumannIter Q H v h k) U ∧
      ∀ x ∈ U, ‖neumannIter Q H v h k x‖ ≤ M * (1 / 2) ^ k := by
  induction k with
  | zero => exact ⟨hhd, fun x hx => by simpa [neumannIter] using hhM x hx⟩
  | succ k ih =>
    obtain ⟨hd, hb⟩ := ih
    have hv0 : ∀ x ∈ U, v x ≠ 0 := fun x hx => norm_pos_iff.1 (hm.trans_le (hvm x hx))
    refine ⟨?_, fun x hx => ?_⟩
    · change DifferentiableOn ℂ (fun x => -(H x * Q (neumannIter Q H v h k) x) / v x) U
      simpa only [div_eq_mul_inv] using
        ((hHd.fun_mul (hQd _ hd)).fun_neg).fun_mul (hvd.fun_inv hv0)
    have hQ := hQb _ _ hd hb x hx
    simp only [neumannIter]
    rw [norm_div, norm_neg, norm_mul, div_le_iff₀ (hm.trans_le (hvm x hx)), pow_succ]
    have h1 : ‖H x‖ * ‖Q (neumannIter Q H v h k) x‖ ≤ ‖H x‖ * (C * (M * (1 / 2) ^ k)) :=
      mul_le_mul_of_nonneg_left hQ (norm_nonneg _)
    have h2 : 0 ≤ M * (1 / 2 : ℝ) ^ k := by positivity
    have h3 := mul_le_mul_of_nonneg_right ((hHC x hx).trans (hvm x hx)) h2
    nlinarith

/-- One step of the Neumann scheme: `h_k = (Q h_k / v) G + ∑ Cf h_k t ^ j + h_{k+1}`. -/
theorem neumannIter_eq_step {U : Set (E × ℂ)} {Q : (E × ℂ → ℂ) → E × ℂ → ℂ}
    {Cf : (E × ℂ → ℂ) → ℕ → E → ℂ} {d : ℕ}
    (heq : ∀ f, DifferentiableOn ℂ f U → ∀ x ∈ U,
      f x = Q f x * x.2 ^ d + ∑ k ∈ Finset.range d, Cf f k x.1 * x.2 ^ k)
    {G H v h : E × ℂ → ℂ} (hv0 : ∀ x ∈ U, v x ≠ 0)
    (hGHv : ∀ x ∈ U, G x = v x * x.2 ^ d + H x) (k : ℕ)
    (hd : DifferentiableOn ℂ (neumannIter Q H v h k) U) {x : E × ℂ} (hx : x ∈ U) :
    neumannIter Q H v h k x = Q (neumannIter Q H v h k) x / v x * G x +
      ∑ j ∈ Finset.range d, Cf (neumannIter Q H v h k) j x.1 * x.2 ^ j +
        neumannIter Q H v h (k + 1) x := by
  conv_lhs => rw [heq _ hd x hx]
  simp only [neumannIter]
  rw [hGHv x hx]
  have := hv0 x hx
  field_simp
  ring

/-- The telescoped Neumann identity after `N` steps. -/
theorem neumannIter_telescope {U : Set (E × ℂ)} {Q : (E × ℂ → ℂ) → E × ℂ → ℂ}
    {Cf : (E × ℂ → ℂ) → ℕ → E → ℂ} {d : ℕ}
    (heq : ∀ f, DifferentiableOn ℂ f U → ∀ x ∈ U,
      f x = Q f x * x.2 ^ d + ∑ k ∈ Finset.range d, Cf f k x.1 * x.2 ^ k)
    {G H v h : E × ℂ → ℂ} (hv0 : ∀ x ∈ U, v x ≠ 0)
    (hGHv : ∀ x ∈ U, G x = v x * x.2 ^ d + H x)
    (hd : ∀ k, DifferentiableOn ℂ (neumannIter Q H v h k) U) (N : ℕ) {x : E × ℂ}
    (hx : x ∈ U) :
    h x = (∑ k ∈ Finset.range N, Q (neumannIter Q H v h k) x / v x) * G x +
      ∑ j ∈ Finset.range d,
        (∑ k ∈ Finset.range N, Cf (neumannIter Q H v h k) j x.1) * x.2 ^ j +
        neumannIter Q H v h N x := by
  induction N with
  | zero => simp [neumannIter]
  | succ N ih =>
    rw [ih, neumannIter_eq_step heq hv0 hGHv N (hd N) hx]
    simp only [Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
    ring

/-- Division on a fixed open set `U ⊆ E × ℂ` from abstract Taylor division operators, by
summing the Neumann series. -/
theorem exists_division_of_neumann {U : Set (E × ℂ)} {V : Set E} (hU : IsOpen U)
    (hV : IsOpen V) (hUV : ∀ x ∈ U, x.1 ∈ V)
    {Q : (E × ℂ → ℂ) → E × ℂ → ℂ} {Cf : (E × ℂ → ℂ) → ℕ → E → ℂ} {d : ℕ} {C m M ρ : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M)
    (hQd : ∀ f, DifferentiableOn ℂ f U → DifferentiableOn ℂ (Q f) U)
    (hCd : ∀ f, DifferentiableOn ℂ f U → ∀ k, DifferentiableOn ℂ (Cf f k) V)
    (heq : ∀ f, DifferentiableOn ℂ f U → ∀ x ∈ U,
      f x = Q f x * x.2 ^ d + ∑ k ∈ Finset.range d, Cf f k x.1 * x.2 ^ k)
    (hCb : ∀ (f : E × ℂ → ℂ) (M : ℝ), DifferentiableOn ℂ f U → (∀ x ∈ U, ‖f x‖ ≤ M) →
      ∀ k, ∀ z ∈ V, ‖Cf f k z‖ ≤ M / ρ ^ k)
    (hQb : ∀ (f : E × ℂ → ℂ) (M : ℝ), DifferentiableOn ℂ f U → (∀ x ∈ U, ‖f x‖ ≤ M) →
      ∀ x ∈ U, ‖Q f x‖ ≤ C * M)
    {G H v h : E × ℂ → ℂ} (hHd : DifferentiableOn ℂ H U) (hvd : DifferentiableOn ℂ v U)
    (hvm : ∀ x ∈ U, m ≤ ‖v x‖) (hGHv : ∀ x ∈ U, G x = v x * x.2 ^ d + H x)
    (hHC : ∀ x ∈ U, 2 * C * ‖H x‖ ≤ m)
    (hhd : DifferentiableOn ℂ h U) (hhM : ∀ x ∈ U, ‖h x‖ ≤ M) :
    ∃ q : E × ℂ → ℂ, (∀ x ∈ U, DifferentiableAt ℂ q x) ∧
      ∃ r : ℕ → E → ℂ, (∀ k, ∀ z ∈ V, DifferentiableAt ℂ (r k) z) ∧
        ∀ x ∈ U, h x = q x * G x + ∑ k ∈ Finset.range d, r k x.1 * x.2 ^ k := by
  have hk := neumannIter_differentiableOn_and_norm_le hm hM hQd hQb hHd hvd hvm hHC hhd hhM
  have hv0 : ∀ x ∈ U, v x ≠ 0 := fun x hx => norm_pos_iff.1 (hm.trans_le (hvm x hx))
  have hqb : ∀ k, ∀ x ∈ U,
      ‖Q (neumannIter Q H v h k) x / v x‖ ≤ C * M / m * (1 / 2) ^ k := by
    intro k x hx
    have hQ := hQb _ _ (hk k).1 (hk k).2 x hx
    rw [norm_div]
    calc ‖Q (neumannIter Q H v h k) x‖ / ‖v x‖
        ≤ ‖Q (neumannIter Q H v h k) x‖ / m :=
          div_le_div_of_nonneg_left (norm_nonneg _) hm (hvm x hx)
      _ ≤ C * (M * (1 / 2) ^ k) / m := by gcongr
      _ = C * M / m * (1 / 2) ^ k := by ring
  have hcb : ∀ k j, ∀ z ∈ V, ‖Cf (neumannIter Q H v h k) j z‖ ≤ M / ρ ^ j * (1 / 2) ^ k :=
    fun k j z hz => (hCb _ _ (hk k).1 (hk k).2 j z hz).trans_eq (by ring)
  have hsum : Summable fun k : ℕ => ((1 : ℝ) / 2) ^ k := summable_geometric_two
  refine ⟨fun x => ∑' k, Q (neumannIter Q H v h k) x / v x,
    fun x hx => differentiableAt_tsum_of_forall_norm_le hU (hsum.mul_left _)
      (fun k => by simpa only [div_eq_mul_inv] using (hQd _ (hk k).1).fun_mul (hvd.fun_inv hv0))
      hqb hx,
    fun j z => ∑' k, Cf (neumannIter Q H v h k) j z,
    fun j z hz => differentiableAt_tsum_of_forall_norm_le hV (hsum.mul_left _)
      (fun k => hCd _ (hk k).1 j) (fun k => hcb k j) hz, fun x hx => ?_⟩
  have hlim : Tendsto (fun N =>
      (∑ k ∈ Finset.range N, Q (neumannIter Q H v h k) x / v x) * G x +
        ∑ j ∈ Finset.range d,
          (∑ k ∈ Finset.range N, Cf (neumannIter Q H v h k) j x.1) * x.2 ^ j +
        neumannIter Q H v h N x) atTop
      (𝓝 ((∑' k, Q (neumannIter Q H v h k) x / v x) * G x +
        ∑ j ∈ Finset.range d, (∑' k, Cf (neumannIter Q H v h k) j x.1) * x.2 ^ j + 0)) := by
    refine ((Tendsto.mul_const _ ?_).add
      (tendsto_finsetSum _ fun j _ => Tendsto.mul_const _ ?_)).add ?_
    · exact ((hsum.mul_left _).of_norm_bounded fun k => hqb k x hx).hasSum.tendsto_sum_nat
    · exact ((hsum.mul_left _).of_norm_bounded
        fun k => hcb k j x.1 (hUV x hx)).hasSum.tendsto_sum_nat
    · refine squeeze_zero_norm (fun N => (hk N).2 x hx) ?_
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul M
      rwa [mul_zero] at this
  rw [add_zero] at hlim
  exact tendsto_nhds_unique
    (tendsto_const_nhds.congr fun N => neumannIter_telescope heq hv0 hGHv
      (fun k => (hk k).1) N hx) hlim

/-- **Weierstrass division theorem** from abstract parametric Taylor division operators
`Q` and `Cf` by `t ^ d` in the last variable: if `G (0, t) = t ^ d u(t)` with `u(0) ≠ 0`,
every holomorphic germ `h` at `0` is `q G + ∑_{k < d} r_k(z) t ^ k` with holomorphic `q`,
`r_k`. -/
theorem exists_weierstrass_division_of_taylorDivision
    (Q : (E × ℂ → ℂ) → ℝ → ℕ → E × ℂ → ℂ) (Cf : (E × ℂ → ℂ) → ℝ → ℕ → E → ℂ)
    (hCdiff : ∀ (h : E × ℂ → ℂ) (δ ρ R : ℝ), 0 < ρ → ρ < R →
      DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) →
      ∀ k, DifferentiableOn ℂ (Cf h ρ k) (ball (0 : E) δ))
    (hQdiff : ∀ (h : E × ℂ → ℂ) (δ ρ R : ℝ), 0 < ρ → ρ < R →
      DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) →
      ∀ d, DifferentiableOn ℂ (Q h ρ d) (ball (0 : E) δ ×ˢ ball (0 : ℂ) R))
    (heq : ∀ (h : E × ℂ → ℂ) (δ ρ R : ℝ), 0 < ρ → ρ < R →
      DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) →
      ∀ d, ∀ x ∈ ball (0 : E) δ ×ˢ ball (0 : ℂ) R,
        h x = Q h ρ d x * x.2 ^ d + ∑ k ∈ Finset.range d, Cf h ρ k x.1 * x.2 ^ k)
    (hCbound : ∀ (h : E × ℂ → ℂ) (δ ρ R M : ℝ), 0 < ρ → ρ < R →
      DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) →
      (∀ x ∈ ball (0 : E) δ ×ˢ ball (0 : ℂ) R, ‖h x‖ ≤ M) →
      ∀ k, ∀ z ∈ ball (0 : E) δ, ‖Cf h ρ k z‖ ≤ M / ρ ^ k)
    (hQbound : ∀ (d : ℕ) (ρ R : ℝ), 0 < ρ → ρ < R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (δ M : ℝ) (h : E × ℂ → ℂ),
        DifferentiableOn ℂ h (ball (0 : E) δ ×ˢ ball (0 : ℂ) R) →
        (∀ x ∈ ball (0 : E) δ ×ˢ ball (0 : ℂ) R, ‖h x‖ ≤ M) →
        ∀ x ∈ ball (0 : E) δ ×ˢ ball (0 : ℂ) R, ‖Q h ρ d x‖ ≤ C * M)
    {G : E × ℂ → ℂ} (hG : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ G x)
    {d : ℕ} {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hGu : ∀ᶠ t in 𝓝 (0 : ℂ), G (0, t) = t ^ d * u t)
    {h : E × ℂ → ℂ} (hh : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x) :
    ∃ q : E × ℂ → ℂ, (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x) ∧
      ∃ r : ℕ → E → ℂ, (∀ k, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (r k) z) ∧
        h =ᶠ[𝓝 0] fun x => q x * G x + ∑ k ∈ Finset.range d, r k x.1 * x.2 ^ k := by
  -- Radii on which `u`, `G` and `h` are well behaved.
  have hu' : ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableAt ℂ u t ∧ ‖u 0‖ / 2 < ‖u t‖ ∧
      G (0, t) = t ^ d * u t := by
    have hlt : ‖u 0‖ / 2 < ‖u 0‖ := half_lt_self (norm_pos_iff.2 hu0)
    filter_upwards [hu.eventually_analyticAt, hu.continuousAt.norm.eventually (lt_mem_nhds hlt),
      hGu] with t h1 h2 h3
    exact ⟨h1.differentiableAt, h2, h3⟩
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.eventually_nhds_iff_ball.1 hu'
  obtain ⟨r₂, hr₂, hr₂'⟩ := Metric.eventually_nhds_iff_ball.1 (hG.and hh)
  set R : ℝ := min r₁ r₂ / 2 with hR_def
  have hmin : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hR : 0 < R := half_pos hmin
  have hRr₁ : R < r₁ := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hRr₂ : R < r₂ := (half_lt_self hmin).trans_le (min_le_right _ _)
  set ρ : ℝ := R / 2 with hρ_def
  have hρ : 0 < ρ := half_pos hR
  have hρR : ρ < R := half_lt_self hR
  obtain ⟨C, hC0, hC⟩ := hQbound d ρ R hρ hρR
  set m : ℝ := ‖u 0‖ / 2 with hm_def
  have hm : 0 < m := half_pos (norm_pos_iff.2 hu0)
  set H : E × ℂ → ℂ := fun x => G x - x.2 ^ d * u x.2 with hH_def
  have hK : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have hKr : ∀ t ∈ closedBall (0 : ℂ) R,
      ((0 : E), t) ∈ ball (0 : E × ℂ) r₂ ∧ t ∈ ball (0 : ℂ) r₁ := by
    intro t ht
    have htR : ‖t‖ ≤ R := mem_closedBall_zero_iff.1 ht
    refine ⟨?_, mem_ball_zero_iff.2 (htR.trans_lt hRr₁)⟩
    rw [mem_ball_zero_iff, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
    exact htR.trans_lt hRr₂
  -- A bound for `h` on `{0} × closedBall 0 R`.
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (f := fun t => h ((0 : E), t))
    fun t ht => ((hr₂' _ (hKr t ht).1).2.continuousAt.comp
      (f := fun t : ℂ => ((0 : E), t))
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0 (mem_closedBall_self hR.le))
  -- Tube lemma.
  have key : ∀ᶠ z in 𝓝 (0 : E), ∀ t ∈ closedBall (0 : ℂ) R,
      ‖H (z, t)‖ < m / (2 * (C + 1)) ∧ ‖h (z, t)‖ < M₀ + 1 ∧
        (z, t) ∈ ball (0 : E × ℂ) r₂ := by
    refine hK.eventually_forall_of_forall_eventually fun t ht => ?_
    obtain ⟨hball, ht₁⟩ := hKr t ht
    have hut := hr₁' t ht₁
    have hHc : ContinuousAt H ((0 : E), t) :=
      (hr₂' _ hball).1.continuousAt.sub
        ((continuousAt_snd.pow d).mul (hut.1.continuousAt.comp continuousAt_snd))
    have hH0 : ‖H ((0 : E), t)‖ < m / (2 * (C + 1)) := by
      simp only [hH_def, hut.2.2, sub_self, norm_zero]
      positivity
    have hh0 : ‖h ((0 : E), t)‖ < M₀ + 1 := (hM₀ t ht).trans_lt (lt_add_one M₀)
    filter_upwards [hHc.norm.eventually (gt_mem_nhds hH0),
      (hr₂' _ hball).2.continuousAt.norm.eventually (gt_mem_nhds hh0),
      isOpen_ball.mem_nhds hball] with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff_ball.1 key
  set U : Set (E × ℂ) := ball (0 : E) δ ×ˢ ball (0 : ℂ) R with hU_def
  have hUmem : ∀ x ∈ U, ‖H x‖ < m / (2 * (C + 1)) ∧ ‖h x‖ < M₀ + 1 ∧
      x ∈ ball (0 : E × ℂ) r₂ ∧ x.2 ∈ ball (0 : ℂ) r₁ := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    obtain ⟨h1, h2, h3⟩ := hδ' z hz t (ball_subset_closedBall ht)
    exact ⟨h1, h2, h3, ball_subset_ball hRr₁.le ht⟩
  have hUo : IsOpen U := isOpen_ball.prod isOpen_ball
  have hU0 : (0 : E × ℂ) ∈ U := ⟨mem_ball_self hδ, mem_ball_self hR⟩
  have hud : ∀ x ∈ U, DifferentiableAt ℂ (fun x : E × ℂ => u x.2) x := fun x hx =>
    (hr₁' _ (hUmem x hx).2.2.2).1.comp x differentiableAt_snd
  have hHd : DifferentiableOn ℂ H U := fun x hx =>
    ((hr₂' x (hUmem x hx).2.2.1).1.sub
      ((differentiableAt_snd.pow d).mul (hud x hx))).differentiableWithinAt
  have hHC : ∀ x ∈ U, 2 * C * ‖H x‖ ≤ m := by
    intro x hx
    have h1 := (hUmem x hx).1
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg (H x)]
  obtain ⟨q, hq, r, hr, hdiv⟩ := exists_division_of_neumann (Q := fun f => Q f ρ d)
    (Cf := fun f k => Cf f ρ k) (d := d) (C := C) (m := m) (M := M₀ + 1) (ρ := ρ)
    (G := G) (H := H) (v := fun x => u x.2) (h := h) hUo isOpen_ball (fun x hx => hx.1) hm
    (by linarith)
    (fun f hf => hQdiff f δ ρ R hρ hρR hf d)
    (fun f hf k => hCdiff f δ ρ R hρ hρR hf k)
    (fun f hf x hx => heq f δ ρ R hρ hρR hf d x hx)
    (fun f M hf hM k z hz => hCbound f δ ρ R M hρ hρR hf hM k z hz)
    (fun f M hf hM x hx => hC δ M f hf hM x hx)
    hHd (fun x hx => (hud x hx).differentiableWithinAt)
    (fun x hx => (hr₁' _ (hUmem x hx).2.2.2).2.1.le)
    (fun x _ => by simp only [hH_def]; ring) hHC
    (fun x hx => (hr₂' x (hUmem x hx).2.2.1).2.differentiableWithinAt)
    (fun x hx => (hUmem x hx).2.1.le)
  exact ⟨q, eventually_of_mem (hUo.mem_nhds hU0) hq, r,
    fun k => eventually_of_mem (ball_mem_nhds 0 hδ) (hr k),
    eventually_of_mem (hUo.mem_nhds hU0) hdiv⟩

end SGPT.Foundations.Analysis.Pending

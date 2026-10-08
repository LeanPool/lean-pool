/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic


/-!
# Strongly continuous semigroups (Proposition 1.2)

* `C0Semigroup 𝕜 X` : strongly continuous semigroups `T` on `X` (first item of
  Definition 1.1): `T 0 = Id`, `T (t + s) = T t ∘ T s` for `t, s ≥ 0`, and `T t y → y`
  as `t → 0⁺` for every `y`.
* `C0Semigroup.exists_exp_bound` : `‖T t‖ ≤ M exp(ω t)` for `t ≥ 0`
  ([Pazy 1983, Chapter 1, Theorem 2.2], used in the proofs of Theorem 1.5 and
  Proposition 1.3); proved with the Banach–Steinhaus theorem.
* `C0Semigroup.continuousOn_orbit` : **Proposition 1.2**
  (`prop:pazy-semigroup-solution-continuous`), `t ↦ T t x°` is continuous on `ℝ₊`.

`T` is a function `ℝ → (X →L[𝕜] X)`; all axioms only involve nonnegative times, so the
values of `T t` for `t < 0` play no role. Completeness of `X` is assumed where needed.
-/

namespace AbstractLinearControl

@[expose] public section

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A strongly continuous semigroup on `X` (first item of Definition 1.1). -/
structure C0Semigroup (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  /-- the operators `T t` -/
  T : ℝ → X →L[𝕜] X
  /-- `T 0 = Id` -/
  T_zero : T 0 = ContinuousLinearMap.id 𝕜 X
  /-- `T (t + s) = T t ∘ T s` for `t, s ≥ 0` -/
  T_add : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s)
  /-- `T t y → y` as `t → 0⁺`, for every `y` -/
  T_cont : ∀ y : X, Tendsto (fun t => T t y) (nhdsWithin 0 (Set.Ici 0)) (𝓝 y)

namespace C0Semigroup

variable (S : C0Semigroup 𝕜 X)

/-! ## Exponential bound -/

/-- First step: `‖T t‖ ≤ M` on some interval `[0, τ]` (Banach–Steinhaus). -/
theorem exists_bound_near_zero [CompleteSpace X] :
    ∃ τ > 0, ∃ M ≥ 1, ∀ t, 0 ≤ t → t ≤ τ → ‖S.T t‖ ≤ M := by
  by_contra h
  -- otherwise, for every `n`, there is `t n ∈ [0, 1/(n+1)]` with `‖T (t n)‖ > n + 1`
  have key : ∀ n : ℕ, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 < ‖S.T t‖ := by
    intro n
    by_contra hn
    push Not at hn
    exact h ⟨1 / ((n : ℝ) + 1), by positivity, (n : ℝ) + 1,
      le_add_of_nonneg_left (by positivity), hn⟩
  choose t ht0 htle htbig using key
  -- `t n → 0⁺`
  have ht_lim : Tendsto t atTop (nhdsWithin 0 (Set.Ici 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact squeeze_zero ht0 htle tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Filter.Eventually.of_forall (fun n => Set.mem_Ici.2 (ht0 n))
  -- for each `x`, the sequence `T (t n) x` converges to `x`, hence is bounded
  have hbdd : ∀ x : X, ∃ C, ∀ n, ‖S.T (t n) x‖ ≤ C := by
    intro x
    have hx : Tendsto (fun n => S.T (t n) x) atTop (𝓝 x) := (S.T_cont x).comp ht_lim
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hx)
    exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩
  -- Banach–Steinhaus: the norms `‖T (t n)‖` are bounded, contradiction
  obtain ⟨C, hC⟩ := banach_steinhaus hbdd
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h1 : ‖S.T (t n)‖ ≤ C := hC n
  have h2 := htbig n
  linarith

/-- Exponential bound: `‖T t‖ ≤ M * exp (ω * t)` for all `t ≥ 0`, with `ω ≥ 0`, `M ≥ 1`. -/
theorem exists_exp_bound [CompleteSpace X] :
    ∃ ω ≥ 0, ∃ M ≥ 1, ∀ t, 0 ≤ t → ‖S.T t‖ ≤ M * Real.exp (ω * t) := by
  obtain ⟨τ, hτ, M, hM, hbound⟩ := S.exists_bound_near_zero
  have hMpos : 0 < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  -- `‖T (k τ)‖ ≤ M ^ k`, by induction on `k`
  have hpow : ∀ k : ℕ, ‖S.T (k * τ)‖ ≤ M ^ k := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_mul, S.T_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      have hk : ((k + 1 : ℕ) : ℝ) * τ = k * τ + τ := by push_cast; ring
      rw [hk, S.T_add (k * τ) τ (mul_nonneg (by positivity) hτ.le) hτ.le, pow_succ]
      calc ‖(S.T (k * τ)).comp (S.T τ)‖
          ≤ ‖S.T (k * τ)‖ * ‖S.T τ‖ := by apply ContinuousLinearMap.opNorm_comp_le
        _ ≤ M ^ k * M :=
          mul_le_mul ih (hbound τ hτ.le le_rfl) (norm_nonneg _) (pow_nonneg hMpos.le k)
  -- `ω := log M / τ`
  refine ⟨Real.log M / τ, div_nonneg hlogM hτ.le, M, hM, fun t ht => ?_⟩
  -- write `t = k τ + t'` with `k = ⌊t/τ⌋` and `t' ∈ [0, τ)`
  obtain ⟨k, hk_le, hk_lt⟩ : ∃ k : ℕ, (k : ℝ) ≤ t / τ ∧ t / τ < k + 1 :=
    ⟨⌊t / τ⌋₊, Nat.floor_le (div_nonneg ht hτ.le), Nat.lt_floor_add_one _⟩
  have h1 : (k : ℝ) * τ ≤ t := (le_div_iff₀ hτ).1 hk_le
  have h2 : t < (k + 1) * τ := (div_lt_iff₀ hτ).1 hk_lt
  -- `T t = T (k τ) ∘ T (t - k τ)`
  have hdec : S.T t = (S.T (k * τ)).comp (S.T (t - k * τ)) := by
    rw [← S.T_add (k * τ) (t - k * τ) (mul_nonneg (by positivity) hτ.le) (by linarith)]
    rw [show (k : ℝ) * τ + (t - k * τ) = t by ring]
  -- `‖T t‖ ≤ M ^ k * M`
  have h3 : ‖S.T t‖ ≤ M ^ k * M := by
    rw [hdec]
    calc ‖(S.T (k * τ)).comp (S.T (t - k * τ))‖
        ≤ ‖S.T (k * τ)‖ * ‖S.T (t - k * τ)‖ := by apply ContinuousLinearMap.opNorm_comp_le
      _ ≤ M ^ k * M :=
        mul_le_mul (hpow k) (hbound (t - k * τ) (by linarith) (by linarith))
          (norm_nonneg _) (pow_nonneg hMpos.le k)
  -- `M ^ k = exp (k log M) ≤ exp (ω t)` since `k ≤ t / τ`
  have h4 : M ^ k ≤ Real.exp (Real.log M / τ * t) := by
    calc M ^ k = Real.exp (Real.log M) ^ k := by rw [Real.exp_log hMpos]
      _ = Real.exp (k * Real.log M) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (Real.log M / τ * t) := by
        apply Real.exp_le_exp.2
        calc (k : ℝ) * Real.log M ≤ t / τ * Real.log M :=
              mul_le_mul_of_nonneg_right hk_le hlogM
          _ = Real.log M / τ * t := by ring
  calc ‖S.T t‖ ≤ M ^ k * M := h3
    _ ≤ Real.exp (Real.log M / τ * t) * M := mul_le_mul_of_nonneg_right h4 hMpos.le
    _ = M * Real.exp (Real.log M / τ * t) := mul_comm _ _

/-! ## Proposition 1.2: continuity of the orbits -/

/-- `T (a + h) y - T a y = T a (T h y - y)` -/
theorem orbit_sub (y : X) (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    S.T (a + h) y - S.T a y = S.T a (S.T h y - y) := by
  rw [S.T_add a h ha hh, ContinuousLinearMap.comp_apply, map_sub]

/-- `‖T (a + h) y - T a y‖ ≤ ‖T a‖ ‖T h y - y‖` -/
theorem norm_orbit_sub_le (y : X) (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    ‖S.T (a + h) y - S.T a y‖ ≤ ‖S.T a‖ * ‖S.T h y - y‖ := by
  rw [S.orbit_sub y a h ha hh]
  apply ContinuousLinearMap.le_opNorm

/-- **Proposition 1.2** (`prop:pazy-semigroup-solution-continuous`). For every `y`,
`t ↦ T t y` is continuous on `ℝ₊ = [0, ∞)`. -/
theorem continuousOn_orbit [CompleteSpace X] (y : X) :
    ContinuousOn (fun t => S.T t y) (Set.Ici 0) := by
  obtain ⟨ω, hω, M, hM, hexp⟩ := S.exists_exp_bound
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  rw [Set.mem_Ici] at ht₀
  -- uniform bound `‖T a‖ ≤ K` for `a ∈ [0, t₀]`, with `K := M exp (ω t₀)`
  obtain ⟨K, hKpos, hK⟩ : ∃ K > 0, ∀ a, 0 ≤ a → a ≤ t₀ → ‖S.T a‖ ≤ K := by
    refine ⟨M * Real.exp (ω * t₀), mul_pos (by linarith) (Real.exp_pos _), ?_⟩
    intro a ha hat
    calc ‖S.T a‖ ≤ M * Real.exp (ω * a) := hexp a ha
      _ ≤ M * Real.exp (ω * t₀) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hat hω)) (by linarith)
  -- strong continuity at `0`, with tolerance `ε / K`
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.tendsto_nhdsWithin_nhds.1 (S.T_cont y) (ε / K) (div_pos hε hKpos)
  -- key estimate: `‖T (a + h) y - T a y‖ < ε` for `a ∈ [0, t₀]`, `h ∈ [0, δ)`
  have key : ∀ a h : ℝ, 0 ≤ a → a ≤ t₀ → 0 ≤ h → h < δ →
      ‖S.T (a + h) y - S.T a y‖ < ε := by
    intro a h ha hat hh hhδ
    have h1 : dist (S.T h y) y < ε / K := by
      apply hcont (Set.mem_Ici.2 hh)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hh]
      exact hhδ
    rw [dist_eq_norm] at h1
    have h2 : K * ‖S.T h y - y‖ < ε := by
      rw [mul_comm]
      exact (lt_div_iff₀ hKpos).1 h1
    have h3 : ‖S.T a‖ * ‖S.T h y - y‖ ≤ K * ‖S.T h y - y‖ :=
      mul_le_mul_of_nonneg_right (hK a ha hat) (norm_nonneg _)
    have h4 := S.norm_orbit_sub_le y a h ha hh
    linarith
  refine ⟨δ, hδ, fun t ht hdist => ?_⟩
  rw [Set.mem_Ici] at ht
  rw [Real.dist_eq] at hdist
  obtain ⟨hd1, hd2⟩ := abs_lt.1 hdist
  show dist (S.T t y) (S.T t₀ y) < ε
  rw [dist_eq_norm]
  rcases le_total t₀ t with htt | htt
  · -- case `t₀ ≤ t`: apply `key` with `a = t₀`, `h = t - t₀`
    have := key t₀ (t - t₀) ht₀ le_rfl (by linarith) (by linarith)
    rwa [show t₀ + (t - t₀) = t by ring] at this
  · -- case `t ≤ t₀`: apply `key` with `a = t`, `h = t₀ - t`
    have := key t (t₀ - t) ht htt (by linarith) (by linarith)
    rwa [show t + (t₀ - t) = t₀ by ring, norm_sub_rev] at this

end C0Semigroup

end

end AbstractLinearControl

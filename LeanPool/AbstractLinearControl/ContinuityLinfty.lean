/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import LeanPool.AbstractLinearControl.ZeroClass


/-!
# Continuity of the input response for `p = ∞` (Corollary 1.6)

**Corollary 1.6** (`cor:p-infty-solution-continuous`). Let `X`, `U` be Banach spaces and
`(𝕋, Φ)` an abstract linear control system with `p = ∞`. For all `u ∈ L^∞(ℝ₊; U)`,
`t ↦ Φ_t u` is continuous on `ℝ₊`.

This answers positively Problem 2.4 of [Weiss 1989]. The proof (§ 2.4 of the paper) only
uses Theorem 1.5 (`ALCS.zero_class`), the composition property and the continuity of
semigroup orbits (Proposition 1.2, `C0Semigroup.continuousOn_orbit`):

* at `t₀ = 0`, `‖Φ_t u‖ ≤ κ(t) ‖u‖ → 0`;
* at `t₀ > 0`, with `t₁ = t₀ - δ` and `u₁ = u (t₁ + ·)`, the composition property gives
  `Φ_{t₁ + r} u = T_r (Φ_{t₁} u) + Φ_r u₁`, and `‖Φ_r u₁‖ ≤ κ(2δ) ‖u‖` for `r ≤ 2δ`.

The main statement is `ALCS.continuousOn_Phi`.
-/

namespace AbstractLinearControl

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

namespace ALCS

/-- Consequence of Theorem 1.5: for `ε > 0` there is `η > 0` such that
`‖Φ r v‖ < ε` for all `r ∈ [0, η)` and all inputs `v` with `‖v‖ ≤ ‖u‖`. -/
theorem small_Phi [CompleteSpace X] (S : ALCS 𝕜 X U ∞)
    (u : Lp U ∞ muPlus) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ r, 0 ≤ r → r < η → ∀ v : Lp U ∞ muPlus, ‖v‖ ≤ ‖u‖ → ‖S.Φ r v‖ < ε := by
  -- `κ(r) = ‖Φ r‖ < ε / (‖u‖ + 1)` for `r ∈ [0, η)`
  have hz : Tendsto (fun t => ‖S.Φ t‖) (𝓝[≥] 0) (𝓝 0) := S.zero_class
  obtain ⟨η, hη, hκ⟩ := Metric.tendsto_nhdsWithin_nhds.1 hz (ε / (‖u‖ + 1)) (by positivity)
  refine ⟨η, hη, fun r hr hrη v hv => ?_⟩
  have h1 := hκ (Set.mem_Ici.2 hr)
    (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hr]; exact hrη)
  have h2 : ‖S.Φ r‖ < ε / (‖u‖ + 1) := by simpa using h1
  have h3 : ‖S.Φ r‖ * (‖u‖ + 1) < ε := (lt_div_iff₀ (by positivity)).1 h2
  -- `‖Φ r v‖ ≤ κ(r) ‖v‖`
  calc ‖S.Φ r v‖ ≤ ‖S.Φ r‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖S.Φ r‖ * (‖u‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ < ε := h3

/-- **Corollary 1.6** (`cor:p-infty-solution-continuous`). Let `X`, `U` be real or complex
Banach spaces and `S = (𝕋, Φ)` an abstract linear control system with `p = ∞`. For every
input `u ∈ L^∞(ℝ₊; U)`, the map `t ↦ Φ t u` is continuous on `ℝ₊ = [0, ∞)`. -/
theorem continuousOn_Phi [CompleteSpace X] (S : ALCS 𝕜 X U ∞)
    (u : Lp U ∞ muPlus) :
    ContinuousOn (fun t => S.Φ t u) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  rw [Set.mem_Ici] at ht₀
  rcases ht₀.eq_or_lt with h0 | hpos
  · -- continuity at `t₀ = 0`: `‖Φ t u‖ ≤ κ(t) ‖u‖ → 0`
    subst h0
    obtain ⟨η, hη, hsmall⟩ := S.small_Phi u ε hε
    refine ⟨η, hη, fun t ht hdist => ?_⟩
    rw [Set.mem_Ici] at ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht] at hdist
    show dist (S.Φ t u) (S.Φ 0 u) < ε
    rw [S.Phi_zero, zero_apply, dist_zero_right]
    exact hsmall t ht hdist u le_rfl
  · -- continuity at `t₀ > 0`
    -- `‖Φ r v‖ < ε / 4` for `r ∈ [0, η)` and `‖v‖ ≤ ‖u‖`
    obtain ⟨η, hη, hsmall⟩ := S.small_Phi u (ε / 4) (by positivity)
    -- `0 < δ < t₀` and `2 δ < η`
    obtain ⟨δ, hδpos, hδt, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ t₀ / 2 ∧ δ ≤ η / 3 :=
      ⟨min (t₀ / 2) (η / 3), lt_min (by linarith) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    -- `t₁ := t₀ - δ`, `u₁ := u (t₁ + ·)` and `y := Φ t₁ u`
    have ht₁ : 0 ≤ t₀ - δ := by linarith
    obtain ⟨u₁, hu₁, hcat⟩ := exists_shift (t₀ - δ) ht₁ u
    obtain ⟨y, hy⟩ : ∃ y : X, y = S.Φ (t₀ - δ) u := ⟨_, rfl⟩
    -- composition: `Φ (t₁ + r) u = T r y + Φ r u₁`
    have hcomp : ∀ r, 0 ≤ r → S.Φ (t₀ - δ + r) u = S.T r y + S.Φ r u₁ := by
      intro r hr
      rw [hy]
      exact S.composition (t₀ - δ) r ht₁ hr u u₁ u hcat
    -- in particular `Φ t₀ u = T δ y + Φ δ u₁`
    have e₀ : S.Φ t₀ u = S.T δ y + S.Φ δ u₁ := by
      have h := hcomp δ hδpos.le
      rwa [sub_add_cancel] at h
    -- continuity of `s ↦ T s y` at `s = δ`
    obtain ⟨δ', hδ', horbit⟩ := Metric.continuousOn_iff.1
      (S.toC0Semigroup.continuousOn_orbit y) δ (Set.mem_Ici.2 hδpos.le) (ε / 2) (by positivity)
    refine ⟨min δ δ', lt_min hδpos hδ', fun t _ hdist => ?_⟩
    -- write `t = t₁ + r`, with `|r - δ| = |t - t₀|`
    obtain ⟨r, rfl⟩ : ∃ r, t = t₀ - δ + r := ⟨t - (t₀ - δ), by ring⟩
    rw [Real.dist_eq, show t₀ - δ + r - t₀ = r - δ by ring] at hdist
    have hd1 : |r - δ| < δ := lt_of_lt_of_le hdist (min_le_left _ _)
    have hd2 : |r - δ| < δ' := lt_of_lt_of_le hdist (min_le_right _ _)
    obtain ⟨hr1, hr2⟩ := abs_lt.1 hd1
    have hr : 0 ≤ r := by linarith
    -- the three terms
    have h1 : ‖S.T r y - S.T δ y‖ < ε / 2 := by
      have h := horbit r (Set.mem_Ici.2 hr) (by rw [Real.dist_eq]; exact hd2)
      rwa [dist_eq_norm] at h
    have h2 : ‖S.Φ r u₁‖ < ε / 4 := hsmall r hr (by linarith) u₁ hu₁
    have h3 : ‖S.Φ δ u₁‖ < ε / 4 := hsmall δ hδpos.le (by linarith) u₁ hu₁
    -- conclusion
    change dist (S.Φ (t₀ - δ + r) u) (S.Φ t₀ u) < ε
    rw [dist_eq_norm, hcomp r hr, e₀]
    have h4 := norm_three_terms_le (S.T r y) (S.Φ r u₁) (S.T δ y) (S.Φ δ u₁)
    linarith

end ALCS

end

end

end AbstractLinearControl

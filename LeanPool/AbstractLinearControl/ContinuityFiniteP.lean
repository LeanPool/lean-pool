/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import LeanPool.AbstractLinearControl.Definitions


/-!
# Continuity of the input response for `p < ∞` (Proposition 1.3)

**Proposition 1.3** (`prop:finite-p-solution-continuous`). Assume `p ∈ [1, ∞)`.
For all `u ∈ L^p(ℝ₊; U)`, `t ↦ Φ_t u` is continuous on `ℝ₊`.

The paper refers to [Weiss 1989, Proposition 2.3] and does not write out a proof.
We formalize the classical argument, which uses `p < ∞` twice:

1. `‖u‖_{L^p(0, t)} → 0` as `t → 0` (`ALCS.tendsto_norm_truncate`). With causality and
   monotonicity of `κ`, this gives `Φ_t u → 0` as `t → 0⁺` (`ALCS.tendsto_Phi_zero`).
2. Right continuity at `τ ≥ 0` then follows from the composition property
   `Φ_{τ+h} u = T_h Φ_τ u + Φ_h u(τ + ·)` (`ALCS.tendsto_Phi_right`).
3. Left continuity at `τ > 0` uses `u = u ⋄_h u(h + ·)`, which gives
   `Φ_τ u - Φ_{τ-h} u = T_{τ-h} Φ_h u + Φ_{τ-h} (u(h + ·) - u)`, and the continuity of
   translations in `L^p` (`ALCS.tendsto_norm_shiftLeft_sub`); see `ALCS.tendsto_Phi_left`.

The main statement is `ALCS.continuousOn_Phi_of_ne_top`.
-/

namespace AbstractLinearControl

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

namespace ALCS

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : ALCS 𝕜 X U p)

/-- Step 1: for `p < ∞`, `Φ t u → 0` as `t → 0⁺`.
For `t ∈ [0, 1]`, `‖Φ_t u‖ = ‖Φ_t (u ⋄_t 0)‖ ≤ ‖Φ_1‖ ‖u‖_{L^p(0, t)}`. -/
theorem tendsto_Phi_zero (hp : p ≠ ∞) (u : Lp U p muPlus) :
    Tendsto (fun t => S.Φ t u) (𝓝[≥] 0) (𝓝 0) := by
  have hbound : ∀ᶠ t in 𝓝[≥] (0 : ℝ), ‖S.Φ t u‖ ≤ ‖S.Φ 1‖ * ‖truncate t u‖ := by
    have h1 : ∀ᶠ t in 𝓝[≥] (0 : ℝ), t ≤ 1 :=
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, h1] with t ht0 ht1
    -- causality: `Φ t u = Φ t (u ⋄_t 0)`
    rw [← S.causality t ht0 u 0 (truncate t u) (concat_truncate t u)]
    calc
      ‖S.Φ t (truncate t u)‖ ≤ ‖S.Φ t‖ * ‖truncate t u‖ := (S.Φ t).le_opNorm _
      _ ≤ ‖S.Φ 1‖ * ‖truncate t u‖ :=
        mul_le_mul_of_nonneg_right (S.norm_Phi_mono ht0 ht1) (norm_nonneg _)
  have hlim : Tendsto (fun t => ‖S.Φ 1‖ * ‖truncate t u‖) (𝓝[≥] 0) (𝓝 0) := by
    simpa using ((tendsto_norm_truncate hp u).mono_left nhdsWithin_le_nhds).const_mul ‖S.Φ 1‖
  exact tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlim)

/-- Step 2 (right continuity): for `p < ∞` and `τ ≥ 0`, `Φ (τ + h) u → Φ τ u` as `h → 0⁺`,
since `Φ (τ + h) u = T h (Φ τ u) + Φ h u(τ + ·)`. -/
theorem tendsto_Phi_right (hp : p ≠ ∞) (u : Lp U p muPlus) (τ : ℝ) (hτ : 0 ≤ τ) :
    Tendsto (fun h => S.Φ (τ + h) u) (𝓝[≥] 0) (𝓝 (S.Φ τ u)) := by
  obtain ⟨u₁, -, hcat⟩ := exists_shift τ hτ u
  have heq : ∀ᶠ h in 𝓝[≥] (0 : ℝ), S.T h (S.Φ τ u) + S.Φ h u₁ = S.Φ (τ + h) u := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (S.composition τ h hτ hh u u₁ u hcat).symm
  have hlim : Tendsto (fun h => S.T h (S.Φ τ u) + S.Φ h u₁) (𝓝[≥] 0) (𝓝 (S.Φ τ u + 0)) :=
    (S.T_cont (S.Φ τ u)).add (S.tendsto_Phi_zero hp u₁)
  rw [add_zero] at hlim
  exact hlim.congr' heq

/-- Step 3 (left continuity): for `p < ∞` and `τ > 0`, `Φ (τ - h) u → Φ τ u` as `h → 0⁺`.
With `u_h := u (h + ·)`, one has `u = u ⋄_h u_h`, hence
`Φ τ u - Φ (τ - h) u = T (τ - h) (Φ h u) + Φ (τ - h) (u_h - u)`, so that
`‖Φ τ u - Φ (τ - h) u‖ ≤ K ‖Φ h u‖ + ‖Φ τ‖ ‖u_h - u‖`, where `K` bounds `‖T s‖` on `[0, τ]`. -/
theorem tendsto_Phi_left [CompleteSpace X] (hp : p ≠ ∞) (u : Lp U p muPlus)
    (τ : ℝ) (hτ : 0 < τ) :
    Tendsto (fun h => S.Φ (τ - h) u) (𝓝[≥] 0) (𝓝 (S.Φ τ u)) := by
  -- a bound `K` for `‖T s‖` on `[0, τ]`
  obtain ⟨K, hK⟩ : ∃ K, ∀ s, 0 ≤ s → s ≤ τ → ‖S.T s‖ ≤ K := by
    obtain ⟨ω, hω, M, hM, hexp⟩ := S.toC0Semigroup.exists_exp_bound
    refine ⟨M * Real.exp (ω * τ), fun s hs hsτ => (hexp s hs).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsτ hω)) (by linarith)
  -- the key estimate
  have hest : ∀ h, 0 ≤ h → h ≤ τ →
      ‖S.Φ (τ - h) u - S.Φ τ u‖ ≤ K * ‖S.Φ h u‖ + ‖S.Φ τ‖ * ‖shiftLeft h u - u‖ := by
    intro h hh hhτ
    have hcomp := S.composition h (τ - h) hh (by linarith) u (shiftLeft h u) u
      (concat_shiftLeft h hh u)
    rw [show h + (τ - h) = τ by ring] at hcomp
    have hid : S.Φ (τ - h) u - S.Φ τ u =
        -(S.T (τ - h) (S.Φ h u) + S.Φ (τ - h) (shiftLeft h u - u)) := by
      rw [hcomp, map_sub]
      abel
    rw [hid, norm_neg]
    calc
      _ ≤ ‖S.T (τ - h) (S.Φ h u)‖ + ‖S.Φ (τ - h) (shiftLeft h u - u)‖ := norm_add_le _ _
      _ ≤ K * ‖S.Φ h u‖ + ‖S.Φ τ‖ * ‖shiftLeft h u - u‖ := by
        apply add_le_add
        · exact ((S.T (τ - h)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hK _ (by linarith) (by linarith)) (norm_nonneg _))
        · exact ((S.Φ (τ - h)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (S.norm_Phi_mono (by linarith) (by linarith))
              (norm_nonneg _))
  -- both terms of the bound tend to zero
  have h1 : Tendsto (fun h => ‖S.Φ h u‖) (𝓝[≥] 0) (𝓝 0) := by
    simpa using (S.tendsto_Phi_zero hp u).norm
  have h2 : Tendsto (fun h => ‖shiftLeft h u - u‖) (𝓝[≥] 0) (𝓝 0) :=
    (tendsto_norm_shiftLeft_sub hp u).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun h => K * ‖S.Φ h u‖ + ‖S.Φ τ‖ * ‖shiftLeft h u - u‖)
      (𝓝[≥] 0) (𝓝 0) := by
    simpa using (h1.const_mul K).add (h2.const_mul ‖S.Φ τ‖)
  have hev : ∀ᶠ h in 𝓝[≥] (0 : ℝ),
      ‖S.Φ (τ - h) u - S.Φ τ u‖ ≤ K * ‖S.Φ h u‖ + ‖S.Φ τ‖ * ‖shiftLeft h u - u‖ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds hτ).filter_mono nhdsWithin_le_nhds] with h hh hhτ
    exact hest h hh hhτ
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hev hlim)

/-- **Proposition 1.3** (`prop:finite-p-solution-continuous`).
For `p ∈ [1, ∞)` and every input `u ∈ L^p(ℝ₊; U)`, the map `t ↦ Φ t u` is continuous
on `ℝ₊ = [0, ∞)`. -/
theorem continuousOn_Phi_of_ne_top [CompleteSpace X] (hp : p ≠ ∞) (u : Lp U p muPlus) :
    ContinuousOn (fun t => S.Φ t u) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro τ hτ ε hε
  rw [Set.mem_Ici] at hτ
  -- right continuity
  obtain ⟨δ₁, hδ₁, hright⟩ :=
    Metric.tendsto_nhdsWithin_nhds.1 (S.tendsto_Phi_right hp u τ hτ) ε hε
  -- left continuity (vacuous at `τ = 0`)
  obtain ⟨δ₂, hδ₂, hleft⟩ : ∃ δ₂ > 0, ∀ h : ℝ, 0 ≤ h → h < δ₂ → h ≤ τ →
      dist (S.Φ (τ - h) u) (S.Φ τ u) < ε := by
    rcases hτ.eq_or_lt with h0 | hpos
    · refine ⟨1, one_pos, fun h hh _ hhτ => ?_⟩
      rw [show τ - h = τ by linarith, dist_self]
      exact hε
    · obtain ⟨δ₂, hδ₂, hl⟩ :=
        Metric.tendsto_nhdsWithin_nhds.1 (S.tendsto_Phi_left hp u τ hpos) ε hε
      refine ⟨δ₂, hδ₂, fun h hh hhδ _ => hl (Set.mem_Ici.2 hh) ?_⟩
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hh]
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht hdist => ?_⟩
  rw [Set.mem_Ici] at ht
  rw [Real.dist_eq] at hdist
  show dist (S.Φ t u) (S.Φ τ u) < ε
  rcases le_total τ t with htτ | htτ
  · -- `t = τ + h` with `h = t - τ ≥ 0`
    have hh : 0 ≤ t - τ := sub_nonneg.2 htτ
    have hlt : t - τ < δ₁ :=
      lt_of_lt_of_le (by rwa [abs_of_nonneg hh] at hdist) (min_le_left _ _)
    have h := hright (Set.mem_Ici.2 hh) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg hh])
    rwa [show τ + (t - τ) = t by ring] at h
  · -- `t = τ - h` with `h = τ - t ∈ [0, τ]`
    have hh : 0 ≤ τ - t := sub_nonneg.2 htτ
    have hlt : τ - t < δ₂ := by
      have : |t - τ| = τ - t := by rw [abs_sub_comm, abs_of_nonneg hh]
      exact lt_of_lt_of_le (by rwa [this] at hdist) (min_le_right _ _)
    have h := hleft (τ - t) hh hlt (by linarith)
    rwa [show τ - (τ - t) = t by ring] at h

end ALCS

end

end AbstractLinearControl

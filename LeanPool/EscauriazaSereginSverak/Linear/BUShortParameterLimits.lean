/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCoreEstimate

/-!
# Removing the two compact cutoff parameters

The lower-time transition is removed first at fixed spatial radius;
the spatial shell is removed second.
-/

public section


open Filter
open scoped Topology

noncomputable section

namespace ESS

/-- Successive vanishing of a lower-time error and a spatial shell
error leaves the fixed phase-gap bound. -/
theorem bu_short_two_parameter_limit
    (L A : ℝ) (shell : ℕ → ℝ) (early : ℕ → ℝ → ℝ)
    (n₀ : ℕ) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hshell : Tendsto shell atTop (𝓝 0))
    (hearly : ∀ n : ℕ, Tendsto (early n) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hbound : ∀ n : ℕ, n₀ ≤ n →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        L ≤ A + shell n + early n ε) :
    L ≤ A := by
  have hfixed (n : ℕ) (hn : n₀ ≤ n) : L ≤ A + shell n := by
    have hεsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < ε₀ :=
      nhdsWithin_le_nhds (Iio_mem_nhds hε₀)
    have hεbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        L ≤ A + shell n + early n ε := by
      filter_upwards [self_mem_nhdsWithin, hεsmall] with ε hε hεsmall
      exact hbound n hn ε hε hεsmall
    have hlim : Tendsto (fun ε : ℝ => A + shell n + early n ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (A + shell n)) := by
      simpa only [add_zero] using tendsto_const_nhds.add (hearly n)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hεbound
  have hnBound : ∀ᶠ n : ℕ in atTop, L ≤ A + shell n :=
    Filter.eventually_atTop.2 ⟨n₀, fun n hn => hfixed n hn⟩
  have hlim : Tendsto (fun n : ℕ => A + shell n) atTop (𝓝 A) := by
    simpa only [add_zero] using tendsto_const_nhds.add hshell
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hnBound

/-- A nonnegative quantity bounded by a decaying exponential at every
large parameter must vanish. -/
theorem bu_short_eq_zero_of_exponential_bound
    {I C D a₀ : ℝ} (hI : 0 ≤ I) (hD : 0 < D)
    (hbound : ∀ a : ℝ, a₀ < a → I ≤ C * Real.exp (-(a * D))) :
    I = 0 := by
  have hlim : Tendsto (fun n : ℕ =>
      C * Real.exp (-(((n : ℝ) + max a₀ 0 + 1) * D)))
      atTop (𝓝 0) := by
    have harg : Tendsto (fun n : ℕ =>
        ((n : ℝ) + max a₀ 0 + 1) * D) atTop atTop := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have hshift : Tendsto (fun n : ℕ =>
          (n : ℝ) + (max a₀ 0 + 1)) atTop atTop :=
        tendsto_atTop_add_const_right _ _ hnat
      convert hshift.atTop_mul_const hD using 1
      funext n
      ring
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg).const_mul C
    simpa only [Function.comp_def, mul_zero] using h
  have hboundNat : ∀ n : ℕ,
      I ≤ C * Real.exp (-(((n : ℝ) + max a₀ 0 + 1) * D)) := by
    intro n
    apply hbound
    have hmax : a₀ ≤ max a₀ 0 := le_max_left _ _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith only [hmax, hn]
  have hIle : I ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Filter.Eventually.of_forall hboundNat)
  exact le_antisymm hIle hI

end ESS

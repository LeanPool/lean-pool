/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.DiscreteCompounding

/-!
# Bootstrap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The self-referential bootstrap along the perturbation path

Source: ABK26.  At the gauge exponents `(s,q) = (3/8, 2)` the per-cube
sensitivity estimate is *self-referential*: the growth rate of the coarse gauge
along the path `a + t h` is proportional to the coarse gauge itself.  The
source integrates the resulting Riccati inequality; that step presupposes
differentiability of an infinite weighted aggregate of finite maxima and is
therefore replaced here.

This module contains the gauge-free arithmetic of the replacement.  The input
is an abstract *ratio engine*

```
(∀ tau ∈ [t₁, t₂], Psi tau ≤ C)  ⟹  Psi t₂ ≤ exp (K C (t₂ - t₁)) * Psi t₁ ,
```

which is what a Grönwall estimate for the single-cube responses plus the
descendant aggregation produces, together with a *crude* uniform bound on `Psi`
over `[0,1]`.  Neither continuity nor differentiability of `Psi` is assumed.

The engine is run on a grid of mesh `T/N` with `N` chosen so large that the
crude bound only costs a factor `2` on one mesh interval.  On such an interval
the engine can be re-run with the *sharp* local bound `2 Psi (t_k)`, which turns
the exponential into the discrete Riccati step
`Psi (t_{k+1}) ≤ (1 + (4 K T / N) Psi (t_k)) Psi (t_k)` handled by
`Multiscale.riccati_step_le`.  The crude bound therefore never enters the
conclusion.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

/-! ## Elementary exponential bounds -/

/-- `exp (1/2) ≤ 2`. -/
theorem exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h := exp_le_one_add_two_mul (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  linarith only [h]

/-! ## The bootstrap -/

/-- **The self-referential bootstrap.**

Let `Psi ≥ 0` satisfy the ratio engine `hengine` and admit *some* finite bound
`B` on `[0,1]`.  If the initial value satisfies the smallness gate
`4 K Psi 0 < 1`, then `Psi` obeys the Riccati bound
`Psi T ≤ Psi 0 / (1 - 4 K Psi 0)` on all of `[0,1]`, with a constant that does
not involve `B`. -/
theorem le_riccati_of_ratio_engine {Ψ : ℝ → ℝ} {K B : ℝ}
    (hΨ : ∀ t, 0 ≤ Ψ t) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hcrude : ∀ t, 0 ≤ t → t ≤ 1 → Ψ t ≤ B)
    (hengine : ∀ t₁ t₂ C : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ 1 →
      (∀ τ, t₁ ≤ τ → τ ≤ t₂ → Ψ τ ≤ C) →
      Ψ t₂ ≤ Real.exp (K * C * (t₂ - t₁)) * Ψ t₁)
    (hsmall : 4 * K * Ψ 0 < 1) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    Ψ T ≤ Ψ 0 / (1 - 4 * K * Ψ 0) := by
  classical
  have hΨ0 : 0 ≤ Ψ 0 := hΨ 0
  have hpos : 0 < 1 - 4 * K * Ψ 0 := by linarith only [hsmall]
  -- choose a grid fine enough that the crude bound costs at most a factor two
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 8 * K * B ≤ (N : ℝ) ∧ 1 ≤ N := by
    obtain ⟨M, hM⟩ := exists_nat_gt (8 * K * B)
    exact ⟨M + 1, by push_cast; linarith only [hM], by omega⟩
  obtain ⟨hNB, hN1⟩ := hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith only [this]
  set δ : ℝ := T / (N : ℝ) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  -- the grid points
  set y : ℕ → ℝ := fun k => Ψ ((k : ℝ) * δ) with hy
  have hynn : ∀ k, 0 ≤ y k := fun k => hΨ _
  have hgrid0 : y 0 = Ψ 0 := by simp [hy]
  have hgridN : y N = Ψ T := by
    have : (N : ℝ) * δ = T := by
      rw [hδ]; field_simp
    rw [hy]; simp only []; rw [this]
  have hmem : ∀ k : ℕ, k ≤ N → 0 ≤ (k : ℝ) * δ ∧ (k : ℝ) * δ ≤ T := by
    intro k hk
    have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    refine ⟨by positivity, ?_⟩
    rw [hδ]
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ hNpos]
    linarith only [mul_le_mul_of_nonneg_left hkN hT0]
  -- the mesh cost of the crude bound
  have hKBδ : K * B * δ ≤ 1 / 8 := by
    have hδle : δ ≤ 1 / (N : ℝ) := by
      rw [hδ, div_le_div_iff_of_pos_right hNpos]
      exact hT1
    have hKB : 0 ≤ K * B := mul_nonneg hK hB
    have hstep : K * B * δ ≤ K * B * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hδle hKB
    refine hstep.trans ?_
    rw [mul_one_div, div_le_iff₀ hNpos]
    linarith only [hNB]
  -- the discrete Riccati step
  have hstep : ∀ k, k < N →
      y (k + 1) ≤ (1 + ((4 * K * T) / (N : ℝ)) * y k) * y k := by
    intro k hk
    have hk1 : k + 1 ≤ N := hk
    have hkle : k ≤ N := le_of_lt hk
    obtain ⟨ht₁0, ht₁T⟩ := hmem k hkle
    obtain ⟨ht₂0, ht₂T⟩ := hmem (k + 1) hk1
    have ht₁1 : (k : ℝ) * δ ≤ 1 := le_trans ht₁T hT1
    have ht₂1 : ((k + 1 : ℕ) : ℝ) * δ ≤ 1 := le_trans ht₂T hT1
    have hle12 : (k : ℝ) * δ ≤ ((k + 1 : ℕ) : ℝ) * δ := by
      have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith only []
      exact mul_le_mul_of_nonneg_right this hδ0
    have hdiff : ((k + 1 : ℕ) : ℝ) * δ - (k : ℝ) * δ = δ := by push_cast; ring
    -- Step 1: on the mesh interval the crude bound costs at most a factor two
    have hlocal : ∀ τ, (k : ℝ) * δ ≤ τ → τ ≤ ((k + 1 : ℕ) : ℝ) * δ →
        Ψ τ ≤ 2 * y k := by
      intro τ hτ1 hτ2
      have hτ0 : 0 ≤ τ := le_trans ht₁0 hτ1
      have hτ1' : τ ≤ 1 := le_trans hτ2 ht₂1
      have hcr : ∀ σ, (k : ℝ) * δ ≤ σ → σ ≤ τ → Ψ σ ≤ B := by
        intro σ hσ1 hσ2
        exact hcrude σ (le_trans ht₁0 hσ1) (le_trans hσ2 hτ1')
      have hmain := hengine ((k : ℝ) * δ) τ B ht₁0 hτ1 hτ1' hcr
      have hexp : Real.exp (K * B * (τ - (k : ℝ) * δ)) ≤ 2 := by
        have hle : K * B * (τ - (k : ℝ) * δ) ≤ 1 / 2 := by
          have hKB : 0 ≤ K * B := mul_nonneg hK hB
          have hsub : τ - (k : ℝ) * δ ≤ δ := by linarith only [hτ2, hdiff]
          linarith only [mul_le_mul_of_nonneg_left hsub hKB, hKBδ]
        exact le_trans (Real.exp_le_exp.mpr hle) exp_half_le_two
      calc Ψ τ ≤ Real.exp (K * B * (τ - (k : ℝ) * δ)) * Ψ ((k : ℝ) * δ) := hmain
        _ ≤ 2 * y k := mul_le_mul_of_nonneg_right hexp (hynn k)
    -- Step 2: re-run the engine with the sharp local bound
    have hsharp := hengine ((k : ℝ) * δ) (((k + 1 : ℕ) : ℝ) * δ) (2 * y k)
      ht₁0 hle12 ht₂1 hlocal
    rw [hdiff] at hsharp
    have harg : 0 ≤ K * (2 * y k) * δ :=
      mul_nonneg (mul_nonneg hK (by linarith only [hynn k])) hδ0
    have hargle : K * (2 * y k) * δ ≤ 1 / 2 := by
      have hyB : y k ≤ B := hcrude _ ht₁0 ht₁1
      have hKδ : 0 ≤ K * δ := mul_nonneg hK hδ0
      linarith only [mul_le_mul_of_nonneg_left hyB hKδ, hKBδ]
    have hexp2 : Real.exp (K * (2 * y k) * δ) ≤ 1 + 2 * (K * (2 * y k) * δ) :=
      exp_le_one_add_two_mul harg hargle
    have hfinal : Ψ (((k + 1 : ℕ) : ℝ) * δ) ≤
        (1 + 2 * (K * (2 * y k) * δ)) * y k :=
      hsharp.trans (mul_le_mul_of_nonneg_right hexp2 (hynn k))
    have hrw : (1 + 2 * (K * (2 * y k) * δ)) * y k =
        (1 + ((4 * K * T) / (N : ℝ)) * y k) * y k := by
      rw [hδ]; field_simp; ring
    rw [hrw] at hfinal
    exact hfinal
  -- run the discrete Riccati lemma
  have hKT : 0 ≤ 4 * K * T := by positivity
  have hmono : 4 * K * T * Ψ 0 ≤ 4 * K * Ψ 0 := by
    linarith only [mul_nonneg (mul_nonneg hK hΨ0) (sub_nonneg.2 hT1)]
  have huT : (4 * K * T) * y 0 < 1 := by
    rw [hgrid0]; linarith only [hmono, hsmall]
  have hric := riccati_step_le (y := y) (K := 4 * K * T) N hynn hKT huT hstep
  rw [hgridN, hgrid0] at hric
  refine hric.trans ?_
  have hle : 1 - 4 * K * Ψ 0 ≤ 1 - 4 * K * T * Ψ 0 := by linarith only [hmono]
  exact div_le_div_of_nonneg_left hΨ0 hpos hle

/-! ## The closed conclusion -/

/-- **The closed form of the bootstrap.**  Under the smallness gate
`4 K Psi 0 ≤ 1/2`, the aggregate ratio produced by the engine over the whole
segment is at most `1 + 4 K Psi 0`. -/
theorem le_one_add_four_mul_of_ratio_engine {Ψ Y : ℝ → ℝ} {K B : ℝ}
    (hΨ : ∀ t, 0 ≤ Ψ t) (hK : 0 ≤ K) (hB : 0 ≤ B) (hY : 0 ≤ Y 0)
    (hcrude : ∀ t, 0 ≤ t → t ≤ 1 → Ψ t ≤ B)
    (hengine : ∀ t₁ t₂ C : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ 1 →
      (∀ τ, t₁ ≤ τ → τ ≤ t₂ → Ψ τ ≤ C) →
      Ψ t₂ ≤ Real.exp (K * C * (t₂ - t₁)) * Ψ t₁)
    (hengineY : ∀ C : ℝ, (∀ τ, 0 ≤ τ → τ ≤ 1 → Ψ τ ≤ C) →
      Y 1 ≤ Real.exp (K * C) * Y 0)
    (hsmall : 4 * K * Ψ 0 ≤ 1 / 2) :
    Y 1 ≤ (1 + 4 * K * Ψ 0) * Y 0 := by
  have hΨ0 : 0 ≤ Ψ 0 := hΨ 0
  have hstrict : 4 * K * Ψ 0 < 1 := by linarith only [hsmall]
  have hpos : 0 < 1 - 4 * K * Ψ 0 := by linarith only [hstrict]
  set M : ℝ := Ψ 0 / (1 - 4 * K * Ψ 0) with hM
  have hMbound : ∀ τ, 0 ≤ τ → τ ≤ 1 → Ψ τ ≤ M := fun τ hτ0 hτ1 =>
    le_riccati_of_ratio_engine hΨ hK hB hcrude hengine hstrict hτ0 hτ1
  have hMle : M ≤ 2 * Ψ 0 := by
    rw [hM, div_le_iff₀ hpos]
    linarith only [mul_le_mul_of_nonneg_right hsmall hΨ0]
  have hmain := hengineY M hMbound
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hY)
  have harg : K * M ≤ 2 * (K * Ψ 0) := by
    linarith only [mul_le_mul_of_nonneg_left hMle hK]
  have hKΨ : (0 : ℝ) ≤ 2 * (K * Ψ 0) := by positivity
  have hKΨ' : 2 * (K * Ψ 0) ≤ 1 / 2 := by
    linarith only [hsmall, mul_nonneg hK hΨ0]
  have hexp := exp_le_one_add_two_mul hKΨ hKΨ'
  calc Real.exp (K * M) ≤ Real.exp (2 * (K * Ψ 0)) := Real.exp_le_exp.mpr harg
    _ ≤ 1 + 2 * (2 * (K * Ψ 0)) := hexp
    _ = 1 + 4 * K * Ψ 0 := by ring

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda

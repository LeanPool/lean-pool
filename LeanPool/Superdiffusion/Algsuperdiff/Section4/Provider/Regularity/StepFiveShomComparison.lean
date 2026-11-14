/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ShomContinuityCore

/-!
# StepFiveShomComparison

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 5: the `σ` scale comparison

## The gap, and how it is closed

ABK26 `t.regularity` Step 5, asserts inline and WITHOUT citation

```text
   3^{j/2} σ_j^{-1}  ≤  C 3^{-(1/2 - γ)(m-j)} · 3^{m/2} σ_m^{-1} .
```

Multiplying through by `σ_j σ_m 3^{-m/2} > 0`, this is exactly the growth cap

```text
   σ_m  ≤  C 3^{γ(m-j)} σ_j                     (j ≤ m) .
```

The paper never states that cap.  `l.shom.continuity` prints only the mirror
direction `σ_m ≥ (1/4) σ_n`, whose proof reads `e.shom.h.bounds` in one
direction:

```text
   (1/4) max{c⋆γ^{-1}3^{2γm}, ν²}  ≤  σ_m²  ≤  4 max{c⋆γ^{-1}3^{2γm}, ν²} .
```

The growth cap is the SAME three-line argument read in the other direction,
replacing the monotonicity of `m ↦ max{c⋆γ^{-1}3^{2γm}, ν²}` by its exact
geometric growth.  That growth is proved as
`Algsuperdiff.Section3.Provider.Diffusivity.ShomContinuityCore.diffMax_le_rpow_mul`,
so the cap follows from `e.shom.h.bounds` alone — i.e. from conjunct 1 of the
frozen `Algsuperdiff.Frozen.Section3.inductionState`, with `C = 4` explicit and
NO further regime gate (in particular no `mStarStar` gate, no `E`-budget and no
`γ ≤ E^{-10}`).

## References

* ABK26, `t.regularity` Step 5, (the uncited comparison).
* ABK26, `e.shom.h.bounds`; `l.shom.continuity`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity

variable {d : ℕ}

/-! ## 1. Abstract-real atoms

Every step whose goal would contain `Real.rpow` is factored through one of
these, so no arithmetic tactic ever meets a transcendental atom. -/

/-- The square-comparison core of the growth cap: from `s_m² ≤ 4 D_m`, `D_m ≤ t²
D_n` and `(1/4) D_n ≤ s_n²` with `t ≥ 1`, one gets `s_m ≤ 4 t s_n`.  Abstract
reals only. -/
theorem le_four_mul_of_sq_le {sm sn t Dm Dn : ℝ} (hsm : 0 ≤ sm) (hsn : 0 < sn)
    (ht : 1 ≤ t) (hup : sm ^ 2 ≤ 4 * Dm) (hcomp : Dm ≤ t * t * Dn)
    (hlo : (1 / 4 : ℝ) * Dn ≤ sn ^ 2) : sm ≤ 4 * t * sn := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have htt : (0 : ℝ) ≤ t * t := mul_nonneg ht0.le ht0.le
  have hDn4 : Dn ≤ 4 * sn ^ 2 := by linarith only [hlo]
  have h1 : 4 * Dm ≤ 4 * (t * t * Dn) := by linarith only [hcomp]
  have h2 : t * t * Dn ≤ t * t * (4 * sn ^ 2) := mul_le_mul_of_nonneg_left hDn4 htt
  have hrhs : 0 ≤ 4 * t * sn := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht0.le) hsn.le
    linarith only [this]
  have hexp : (4 * t * sn) ^ 2 = 16 * (t * t * sn ^ 2) := by ring
  have hkey : sm ^ 2 ≤ (4 * t * sn) ^ 2 := by
    rw [hexp]
    linarith only [hup, h1, h2]
  have hsqrt := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq hsm, Real.sqrt_sq hrhs] at hsqrt

/-- Inverting a one-sided comparison of positive reals: `b ≤ K a` gives `a⁻¹ ≤ K
b⁻¹`.  Abstract reals only. -/
theorem inv_le_mul_inv_of_le_mul {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : b ≤ K * a) : a⁻¹ ≤ K * b⁻¹ := by
  have hpos : 0 < a⁻¹ * b⁻¹ := mul_pos (inv_pos.mpr ha) (inv_pos.mpr hb)
  have hmul := mul_le_mul_of_nonneg_right h hpos.le
  have hL : b * (a⁻¹ * b⁻¹) = a⁻¹ := by field_simp
  have hR : K * a * (a⁻¹ * b⁻¹) = K * b⁻¹ := by field_simp
  linarith only [hmul, hL, hR]

/-- Reweighting a comparison by a nonnegative factor, with the transcendental
identity supplied as `hid: A T = R S`.  Abstract reals only. -/
theorem weighted_comparison_aux {A T R S x y : ℝ} (hA : 0 ≤ A)
    (hid : A * T = R * S) (hxy : x ≤ 4 * T * y) :
    A * x ≤ 4 * R * (S * y) := by
  have h1 : A * x ≤ A * (4 * T * y) := mul_le_mul_of_nonneg_left hxy hA
  have h2 : A * (4 * T * y) = 4 * (A * T) * y := by ring
  rw [hid] at h2
  have h3 : 4 * (R * S) * y = 4 * R * (S * y) := by ring
  linarith only [h1, h2, h3]

/-! ## 2. The `rpow`/`zpow` bridge -/

/-- `3^{a k} = (3^a)^k` for an integer `k`: the bridge that turns the source's
real-exponent comparison into the integer-exponent geometric ratio that
`StepFiveGeometricTail` sums. -/
theorem three_rpow_mul_intCast (a : ℝ) (k : ℤ) :
    (3 : ℝ) ^ (a * (k : ℝ)) = ((3 : ℝ) ^ a) ^ k := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_intCast]

/-- The Step-5 geometric ratio `r₁ := 3^{-(1/2 - γ)}` is positive. -/
theorem three_rpow_neg_half_add_gamma_pos (gamma : ℝ) :
    0 < (3 : ℝ) ^ (-(1 / 2 - gamma)) :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The Step-5 geometric ratio `r₁ := 3^{-(1/2 - γ)}` is `< 1` exactly because `γ <
1/2`, which the shell-law prefix guarantees (`γ ≤ 1/4`). -/
theorem three_rpow_neg_half_add_gamma_lt_one {gamma : ℝ} (hgamma : gamma < 1 / 2) :
    (3 : ℝ) ^ (-(1 / 2 - gamma)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hgamma])

/-! ## 3. The growth cap `σ_m ≤ 4 · 3^{γ(m-j)} σ_j` -/

/-- ```text
   σ_m  ≤  4 · 3^{γ(m-j)} · σ_j          for  j ≤ m ≤ m₀ .
``` -/
theorem sigmaBar_le_rpow_mul_sigmaBar_of_inductionState {M : ABKModel d} {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {j m : ℤ}
    (hjm : j ≤ m) (hm : m ≤ m0) :
    (Annealed.sigmaBar M m : ℝ) ≤
      4 * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (j : ℝ))) * (Annealed.sigmaBar M j : ℝ) := by
  have hj0 : j ≤ m0 := le_trans hjm hm
  have hup := (hS.1 m hm).2
  have hlo := (hS.1 j hj0).1
  have hgamma := M.shellPrefix.gamma_pos
  have hcast : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
  have hd0 : (0 : ℝ) ≤ M.gamma * ((m : ℝ) - (j : ℝ)) :=
    mul_nonneg hgamma.le (by linarith only [hcast])
  have ht : (1 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (j : ℝ))) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hd0
    rwa [Real.rpow_zero] at h
  have hexp : 2 * M.gamma * ((m : ℝ) - (j : ℝ))
      = M.gamma * ((m : ℝ) - (j : ℝ)) + M.gamma * ((m : ℝ) - (j : ℝ)) := by ring
  have hcomp := ShomContinuityCore.diffMax_le_rpow_mul
    (nu := M.nu) (cstar := Disorder.cstar M) hgamma hjm
  rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3)] at hcomp
  simp only [ShomContinuityCore.diffMax] at hcomp
  exact le_four_mul_of_sq_le (Annealed.sigmaBar M m).2.le (Annealed.sigmaBar M j).2 ht
    hup hcomp hlo

/-! ## 4. The scale comparison in the weighted form Step 5 consumes -/

/-- **The Step-5 scale comparison**, at the explicit constant `4` and with the
`(m-j)`-power written as an integer power of the fixed ratio `r₁ = 3^{-(1/2-γ)} ∈
(0,1)`, which is the shape `StepFiveGeometricTail` sums:

```text
   3^{j/2} σ_j^{-1}  ≤  4 · r₁^{m-j} · ( 3^{m/2} σ_m^{-1} )      (j ≤ m ≤ m₀) .
``` -/
theorem three_rpow_half_mul_inv_sigmaBar_le_of_inductionState {M : ABKModel d}
    {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {j m : ℤ}
    (hjm : j ≤ m) (hm : m ≤ m0) :
    (3 : ℝ) ^ ((j : ℝ) / 2) * ((Annealed.sigmaBar M j : ℝ))⁻¹ ≤
      4 * ((3 : ℝ) ^ (-(1 / 2 - M.gamma))) ^ (m - j) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) * ((Annealed.sigmaBar M m : ℝ))⁻¹) := by
  have hgrowth := sigmaBar_le_rpow_mul_sigmaBar_of_inductionState hS hjm hm
  have hinv : ((Annealed.sigmaBar M j : ℝ))⁻¹ ≤
      4 * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (j : ℝ))) *
        ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    inv_le_mul_inv_of_le_mul (Annealed.sigmaBar M j).2 (Annealed.sigmaBar M m).2 hgrowth
  have hexp : (j : ℝ) / 2 + M.gamma * ((m : ℝ) - (j : ℝ))
      = -(1 / 2 - M.gamma) * (((m - j : ℤ)) : ℝ) + (m : ℝ) / 2 := by
    push_cast
    ring
  have hid : (3 : ℝ) ^ ((j : ℝ) / 2) * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (j : ℝ)))
      = ((3 : ℝ) ^ (-(1 / 2 - M.gamma))) ^ (m - j) * (3 : ℝ) ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hexp,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3), three_rpow_mul_intCast]
  exact weighted_comparison_aux
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) ((j : ℝ) / 2)).le hid hinv

end Algsuperdiff.Section4.Provider.Regularity

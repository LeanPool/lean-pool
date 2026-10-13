/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveShomComparison

/-!
# StepFourCollapseWeights

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 4: the weights of the collapse

## The target

Step 4 of `t.regularity` consumes the excess-decay lemma one-step contraction
and re-expresses its remainder in the Step-5 slots `ε_j`, `δ_j`.  The
excess-decay lane's anchored interior one-step delivers that contraction with
its remainder in the anchor's weights,

```text
   3^{-n} · ( … + C s^{-7} σ_{n-2}^{-1} 3^{(1+s)(n-2)} [g]_{H^s(U_{n+1})} + … ) ,
```

while the Step-5 slot `δ_j` of `StepFiveDeltaFamily` is weighted

```text
   C 3^{j/2} σ_j^{-1} [g]_{W^{1/2,∞}(□_m)} + … .
```

## 1. The `σ` index shift (the shom-weight conversion)

The excess-decay legs carry `σ_{n-2}^{-1}`; the Step-5 slot carries
`σ_j^{-1}` at the SAME index `j = n` as the excess.

```text
   σ_n ≤ 4 · 3^{2γ} σ_{n-2}        hence      σ_{n-2}^{-1} ≤ 4 · 3^{2γ} σ_n^{-1} ,
```

and `4 · 3^{2γ} ≤ 8` under the standing `γ ≤ 1/4`.  The conversion costs the
absolute numeral `8`; no regime gate, no `E`-budget, no `mStarStar`.

## 2. The scale weight

```text
   3^{-n} · 3^{(1+s)(n-2)} · 3^{(n+1)(1/2-s)}  =  3^{n/2} · 3^{-(3/2+3s)} ,
```

i.e. the free index `s` cancels out of the scale weight (as it does in the
seminorm atom), and what is left is the Step-5 weight `3^{j/2}` times the
universal discount
`3^{-(3/2+3s)} ≤ 3^{-3/2}`.  The `∇h` leg collapses by the same identity; the
`L²`-datum leg collapses to the constant `3^{-n} 3^{n-2} = 1/9`.

## 3. The `δ₀` threshold factor, discharged at the consumption

The printed `δ₀` threshold omits the factor `3^{(1+d/2)k}` carried by the very
term it dominates.  Since `k = k(d)` is fixed before `δ₀`, that factor is a
`d`-constant, absorbed by taking `C₁` large enough in terms of `d`; no statement
of this formalization changes.  Here the missing factor is exhibited rather than
assumed.

The corrected threshold carries that factor inside `Cprod`, and the absorption
into `θ^k` is `excess_absorb_two_contractions`.  Nothing is discharged from `γ ≤ γ₀` alone
and nothing is hidden in a constant.

## References

* ABK26, `t.regularity` Step 1; Step 4.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The `σ` index shift -/

/-- `3^{2γ} ≤ 2` at the standing `γ ≤ 1/4`: the one transcendental step of the
two-scale `σ` conversion (`3^{1/2} = √3 ≤ 2`). -/
theorem three_rpow_two_mul_le_two {gamma : ℝ} (hgamma : gamma ≤ 1 / 4) :
    (3 : ℝ) ^ (2 * gamma) ≤ 2 := by
  have h1 : (3 : ℝ) ^ (2 * gamma) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgamma])
  have h2 : (3 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
  have h3 : Real.sqrt 3 ≤ 2 := by
    have h := Real.sqrt_le_sqrt (show (3 : ℝ) ≤ 2 ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  rw [h2] at h1
  linarith only [h1, h3]

/-- ```text
   σ_j^{-1} ≤ 4 · 3^{γ(n-j)} · σ_n^{-1}          (j ≤ n ≤ m₀) .
``` -/
theorem inv_sigmaBar_le_mul_inv_sigmaBar_of_inductionState {M : ABKModel d} {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {j n : ℤ}
    (hjn : j ≤ n) (hn : n ≤ m0) :
    ((Annealed.sigmaBar M j : ℝ))⁻¹ ≤
      4 * (3 : ℝ) ^ (M.gamma * ((n : ℝ) - (j : ℝ))) *
        ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
  inv_le_mul_inv_of_le_mul (Annealed.sigmaBar M j).2 (Annealed.sigmaBar M n).2
    (sigmaBar_le_rpow_mul_sigmaBar_of_inductionState hS hjn hn)

/-- **The shom-weight conversion at the excess-decay gap**: the one-step
display's legs are weighted `σ_{n-2}^{-1}` and the Step-5 slot `δ_n` is
weighted `σ_n^{-1}`, so the collapse pays

```text
   σ_{n-2}^{-1} ≤ 8 σ_n^{-1}          (n ≤ m₀, γ ≤ 1/4) .
``` -/
theorem inv_sigmaBar_sub_two_le_eight_mul_inv_sigmaBar {M : ABKModel d} {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    (hgamma : M.gamma ≤ 1 / 4) {n : ℤ} (hn : n ≤ m0) :
    ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ ≤ 8 * ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
  have hbase :=
    inv_sigmaBar_le_mul_inv_sigmaBar_of_inductionState hS (by omega : n - 2 ≤ n) hn
  have hexp : M.gamma * ((n : ℝ) - ((n - 2 : ℤ) : ℝ)) = 2 * M.gamma := by
    push_cast
    ring
  rw [hexp] at hbase
  have h2 := three_rpow_two_mul_le_two (gamma := M.gamma) hgamma
  have hinv : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 4)) hinv
  linarith only [hbase, hstep]

/-! ## 2. The scale weights -/

/-- **The `g`/`∇h` scale-weight collapse.**  The excess-decay remainder's outer
normalizer `3^{-n}`, its leg weight `3^{(1+s)(n-2)}`'s window weight
`3^{(n+1)(1/2-s)}` multiply to the Step-5 weight `3^{n/2}` times a universal
discount:

```text
   3^{-n} · 3^{(1+s)(n-2)} · 3^{(n+1)(1/2-s)}  =  3^{n/2} · 3^{-(3/2+3s)} .
```

The free index `s` cancels. -/
theorem three_weight_collapse (n : ℤ) (s : ℝ) :
    (3 : ℝ) ^ (-n) *
        ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
          (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s))) =
      (3 : ℝ) ^ ((n : ℝ) / 2) * (3 : ℝ) ^ (-(3 / 2 + 3 * s)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [← Real.rpow_intCast (3 : ℝ) (-n), ← Real.rpow_add h3, ← Real.rpow_add h3,
    ← Real.rpow_add h3]
  congr 1
  push_cast
  ring

/-- The collapse as an inequality against the bare Step-5 weight: the discount
`3^{-(3/2+3s)}` is at most `1` for every `s ≥ 0`, so the excess-decay leg is
strictly better weighted than the slot it fills. -/
theorem three_weight_collapse_le (n : ℤ) {s : ℝ} (hs : 0 ≤ s) :
    (3 : ℝ) ^ (-n) *
        ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
          (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s))) ≤
      (3 : ℝ) ^ ((n : ℝ) / 2) := by
  have hd : (3 : ℝ) ^ (-(3 / 2 + 3 * s)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (show -(3 / 2 + 3 * s) ≤ (0 : ℝ) by linarith only [hs])
    rwa [Real.rpow_zero] at h
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hd hw
  rw [three_weight_collapse n s]
  linarith only [hmul]

/-- **The `L²`-datum leg's scale weight**: `3^{-n} · 3^{n-2} = 1/9`.  This leg of
the excess-decay remainder carries no decay in `n` (see
the module docstring of `StepFourCollapseInterface`). -/
theorem three_weight_flat (n : ℤ) :
    (3 : ℝ) ^ (-n) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) = 1 / 9 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [← Real.rpow_intCast (3 : ℝ) (-n), ← Real.rpow_add h3]
  have hexp : ((-n : ℤ) : ℝ) + ((n - 2 : ℤ) : ℝ) = ((-2 : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_intCast]
  norm_num

/-! ## 3. -/

/-- **The Step-4 absorption.**  The one-step display contracts at `A` and the
`ε_j`-leg contributes a S contraction `B` (the term prices); when both are at
most `½ θ^k`, the collapse closes at the iteration lemma's single `θ^k`.
Abstract reals only. -/
theorem excess_absorb_two_contractions {X Exc A B rest thetaK : ℝ}
    (hExc : 0 ≤ Exc) (hA : A ≤ thetaK / 2) (hB : B ≤ thetaK / 2)
    (h : X ≤ A * Exc + (B * Exc + rest)) : X ≤ thetaK * Exc + rest := by
  have h1 : A * Exc ≤ thetaK / 2 * Exc := mul_le_mul_of_nonneg_right hA hExc
  have h2 : B * Exc ≤ thetaK / 2 * Exc := mul_le_mul_of_nonneg_right hB hExc
  linarith only [h, h1, h2]

end

end Algsuperdiff.Section4.Provider.Regularity

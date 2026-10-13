/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.FlowArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.MinimalScaleShift
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# StepOneParameters

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 1: the parameter web `(k, s, δ)`, the `C₁`-largeness
# demands, and the pins

## The target

```
k := ⌈4 log₃ (2 s^{-3/2} C_{e.excess.decay.one.step})⌉ ,   s := 1/4 ,
δ := C₁⁻¹(1 - α) ,                          C₁ = C₁(d, c⋆) large enough.
```

The excess-decay one-step constant is NOT yet fixed anywhere in the repository,
so it is carried here as the abstract real `Cedos`; every statement below is
uniform in it.

## Contents

* `stepOneKArg`, `stepOneK` — the printed `k`.  The ceiling is `Nat.ceil`
  because the source says `k ∈ ℕ`; at `C_edos ≥ 1` the argument of the
  logarithm exceeds `1`, so `Nat.ceil` and `Int.ceil` agree there.
* `stepOneThreePow`, `stepOneDelta0`, `stepOneC1Delta0` — the third Step-1
  bullet: the factor `3^{k/4}`, the threshold `δ₀` defined by
  `δ₀^{1/2} s^{-1/2} C_edos C_ann = ½ 3^{-k/4}`, and its `C₁`-floor `δ₀⁻¹`.
* `stepOneC1` and its four largeness demands.
* `stepOneEp` — the good-event threshold `⅛ s δ^{1/2}`.
* `StepOneBadSetSeparation` — the pin.

## Deviations from the printed text

1. The printed first bullet reads `γ|log γ|² ≤ s c⋆² (⅛ s δ^{1/2})` with the
   Step-1 `s = 1/4` in the first slot.  The annular producer is applied at the
   index `s/8` (that is the index inside `𝒢(j, z; ⅛s, ⅛ s δ^{1/2})` and inside
   `ε_j(z)`), so the honest requirement is at `(s/8)^{3/2}`; that is the form
   `StepOneEpsilon.lean` carries.  Both differ from the print by a fixed
   numerical factor only (`s` is the numeral `1/4`).
2. `s^{-3/2}` and `3^{-k/4}` are written with `Real.rpow`, as the
   frozen theorems do.  `3^{-k/4}` is kept opaque (only positivity and
   `Real.rpow_neg` are used), so no transcendental atom ever reaches a numeric
   tactic.

## References

* ABK26, `t.regularity` Step 1.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

/-! ## 1. The `s`-powers at the Step-1 numeral `s = 1/4` -/

/-- `s = 1/4`. -/
theorem stepOneS_eq : stepOneS = 1 / 4 := rfl

/-- `0 < s`. -/
theorem stepOneS_pos : 0 < stepOneS := by
  rw [stepOneS_eq]
  norm_num

/-! ## 2. The Step-1 integer `k` -/

/-- The argument of the logarithm in `e.parameter.choices.regularity`: `2 s^{-3/2}
C_{e.excess.decay.one.step}`.  `Cedos` is the abstract excess-decay one-step
constant. -/
noncomputable def stepOneKArg (Cedos : ℝ) : ℝ :=
  2 * Real.rpow stepOneS (-(3 / 2) : ℝ) * Cedos

/-- `k := ⌈4 log₃ (2 s^{-3/2} C_{e.excess.decay.one.step})⌉` of
`e.parameter.choices.regularity`, as a function of the abstract excess-decay
one-step constant. -/
noncomputable def stepOneK (Cedos : ℝ) : ℕ := ⌈4 * Real.logb 3 (stepOneKArg Cedos)⌉₊

/-! ## 3. The factor `3^{k/4}` -/

/-- `3^{k/4}`, the factor of the third Step-1 bullet, kept opaque. -/
noncomputable def stepOneThreePow (k : ℕ) : ℝ := Real.rpow (3 : ℝ) ((k : ℝ) / 4)

/-- `0 < 3^{k/4}`. -/
theorem stepOneThreePow_pos (k : ℕ) : 0 < stepOneThreePow k :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- `3^{-k/4} = (3^{k/4})⁻¹`. -/
theorem rpow_three_neg_quarter (k : ℕ) :
    Real.rpow (3 : ℝ) (-(k : ℝ) / 4) = (stepOneThreePow k)⁻¹ := by
  rw [neg_div, stepOneThreePow]
  exact Real.rpow_neg (by norm_num) _

/-! ## 4. The third Step-1 bullet: `δ ≤ δ₀` -/

/-- `δ₀` of the third Step-1 bullet: the largest tolerance with `δ₀^{1/2} s^{-1/2}
C_edos C_ann ≤ ½ 3^{-k/4}`, here taken with equality. -/
noncomputable def stepOneDelta0 (Cedos Cann : ℝ) (k : ℕ) : ℝ :=
  (Real.sqrt stepOneS * (2 * Cedos * Cann * stepOneThreePow k)⁻¹) ^ 2

/-- The `C₁`-floor of the largeness condition: `C₁ ≥ δ₀⁻¹` forces `δ = C₁⁻¹(1-α) ≤
δ₀`. -/
noncomputable def stepOneC1Delta0 (Cedos Cann : ℝ) (k : ℕ) : ℝ :=
  (stepOneDelta0 Cedos Cann k)⁻¹

/-! ## 5. The four largeness demands on `C₁` -/

/-- **The Step-1 constant `C₁`**, as the maximum of the largeness demands: the
`δ`-window pin `C₁ ≥ 2` of `p.minimal.scale.separation.sec4`, the Step-7
volume/transport pins `C₁ ≥ 2d` and `C₁ ≥ 2(d + γ)` (`γ ≤ 1` in the regime),
the Step-6 demand `C₁ ≥ 4 C_iter (k+1)/log 3`, and the `δ₀` threshold of the
third bullet.  `Citer` is the abstract Step-6 iteration constant, `Cann` the
annular one, `Cedos` the excess-decay one-step one; all three depend only on
`d`, so `C₁ = C₁(d)` — inside the printed `C₁ = C₁(d, c⋆)`. -/
noncomputable def stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) : ℝ :=
  max (max 2 (2 * (d : ℝ) + 2))
    (max (4 * Citer * ((k : ℝ) + 1) / Real.log 3) (stepOneC1Delta0 Cedos Cann k))

/-- pin: `C₁ ≥ 2`, the pin that puts `δ = C₁⁻¹(1-α)` inside the `(0,1/2]` window of
`p.minimal.scale.separation.sec4`. -/
theorem two_le_stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) :
    2 ≤ stepOneC1 d Cedos Cann Citer k :=
  le_trans (le_max_left _ _) (le_max_left _ _)

/-- pins (3) and (4): `C₁ ≥ 2d`, and `C₁ ≥ 2(d + γ)` whenever `γ ≤ 1` — the Step-7
volume factor `3^{(d/2)(n'-n)}` and the coarse-graining transport
`3^{(1/2)(d+γ)(m-m')}`. -/
theorem two_mul_dim_le_stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) :
    2 * (d : ℝ) + 2 ≤ stepOneC1 d Cedos Cann Citer k :=
  le_trans (le_max_right _ _) (le_max_left _ _)

/-- pin (2): `C₁ ≥ 4 C_iter (k+1)/log 3`, the Step-6 demand. -/
theorem step6_le_stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) :
    4 * Citer * ((k : ℝ) + 1) / Real.log 3 ≤ stepOneC1 d Cedos Cann Citer k :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- `0 < C₁`. -/
theorem stepOneC1_pos (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) :
    0 < stepOneC1 d Cedos Cann Citer k :=
  lt_of_lt_of_le (by norm_num) (two_le_stepOneC1 d Cedos Cann Citer k)

/-! ## 6. The good-event threshold `⅛ s δ^{1/2}` -/

/-- The Step-1 good-event threshold `⅛ s δ^{1/2}`, which is also the threshold `s'
√δ` of `p.minimal.scale.separation.sec4` at the Step-1 slot `s' = s/8`. -/
noncomputable def stepOneEp (delta : ℝ) : ℝ := stepOneSEighth * Real.sqrt delta

/-- `⅛ s δ^{1/2} ∈ (0, 1/2]`: the `ε`-range of the annular producer's clause (ii). -/
theorem stepOneEp_mem_Ioc {delta : ℝ} (hdelta : delta ∈ Set.Ioc (0:ℝ) (1 / 2)) :
    stepOneEp delta ∈ Set.Ioc (0:ℝ) (1 / 2) := by
  have hpos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta.1
  have hle : Real.sqrt delta ≤ 1 := by
    have h := Real.sqrt_le_sqrt (le_trans hdelta.2 (by norm_num : (1/2:ℝ) ≤ 1))
    rwa [Real.sqrt_one] at h
  have hval : stepOneEp delta = 1 / 32 * Real.sqrt delta := by
    rw [stepOneEp, stepOneSEighth_eq]
  rw [hval]
  exact ⟨mul_pos (by norm_num) hpos, by linarith only [hle]⟩

/-! ## 9. The pins -/

/-- **The separation side condition**, recorded as a named demand for the windows and
bad-set step: the number of bad scales in the window plus 7 must not exceed the window
length. It resolves the `n' = m'` reading by supplying exactly this condition; it is a
presentational gap in the manuscript, NOT discharged here — the bad set is not formed in
this module. -/
def StepOneBadSetSeparation (badCard : ℕ) (n m : ℤ) : Prop :=
  (badCard : ℤ) + 7 ≤ m - n

/-- The separation demand in the `ℕ`-form a bad-set cardinality bound produces. -/
theorem stepOneBadSetSeparation_of_le {badCard : ℕ} {n m : ℤ}
    (h : badCard + 7 ≤ (m - n).toNat) : StepOneBadSetSeparation badCard n m := by
  rw [StepOneBadSetSeparation]
  omega

end Algsuperdiff.Section4.Provider.Regularity

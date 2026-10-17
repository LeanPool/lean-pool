/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveBudgetSums
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveShomComparison
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons

/-!
# StepFiveDeltaFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 5: the concrete `δ_j` family

## The target

ABK26 `t.regularity` Step 5, — the `δ_j` slot of the iteration lemma at the
Step-5 instantiation:

```text
  δ_j := C 3^{j/2} σ_j^{-1} [g]_{W^{1/2,∞}(□_m)}
         + C ( 3^{j/2} [∇h]_{W^{1/2,∞}(□_m)}
               + ε_j ‖∇h‖_{L^∞(□_m)} ) 1_{z ∉ □_{m-1}} .
```

## The `ℝ≥0∞ → ℝ` layer, and where `toReal`'s convention is load-bearing

`[·]_{W^{1/2,∞}(□_m)}` is an `ℝ≥0∞`-valued
essential supremum, while `l.iteration.lemma` demands `δ: ℤ → ℝ`.  The junk
value `(⊤).toReal = 0` is therefore in play, and its status is settled here
once and for all:

* **Guarded (inert) in everything this tree proves.**  Every inequality of this
  module and of `StepFiveDeltaSum` carries the SAME `toReal` atoms on both
  sides — the family is bounded above by an expression built from its own
  seminorm values.  A `⊤` seminorm makes both sides `0`; no statement becomes
  false, and no statement becomes vacuous.
* Nor is that corner waved at: the root anchor already types the three
  cube-level data of `δ_j` by real scalars,

```lean
  Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g
  Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad
  ∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf
```

so the finiteness the `toReal` layer needs is data the roots already carry;
nothing new is assumed.

## Readings of the printed list

* **D3 (the `ε` inside `δ_j`).**  The manuscript's Step-5 list sets `ε_j:= C
  ε_j(z)` and then writes `δ_j`'s boundary leg as `C (… + ε_j ‖∇h‖_{L^∞}) 1`,
  i.e. `C² ε_j(z) ‖∇h‖_{L^∞} 1`.  The proved tree pins the iteration lemma's
  `ε` slot at the `ε_j(z)` (`e.sum.eps.j.bound` is proved at `C = 1`), so
  the family below reads `C ε_j(z) ‖∇h‖_{L^∞} 1`.  The two differ by one factor
  of the generic `C = C(d,c⋆)`.

## References

* ABK26, `t.regularity` Step 5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The two geometric ratios -/

/-- The geometric ratio for the gradient contribution in the fifth regularity step. -/
def stepFiveRatioG (M : ABKModel d) : ℝ := (3 : ℝ) ^ (-(1 / 2 - M.gamma))

/-- `r₂ := 3^{-1/2}`, the geometric ratio of `δ_j`'s `∇h`-leg. -/
def stepFiveRatioH : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))

theorem stepFiveRatioG_pos (M : ABKModel d) : 0 < stepFiveRatioG M :=
  three_rpow_neg_half_add_gamma_pos M.gamma

theorem stepFiveRatioG_lt_one {M : ABKModel d} (hgamma : M.gamma < 1 / 2) :
    stepFiveRatioG M < 1 :=
  three_rpow_neg_half_add_gamma_lt_one hgamma

theorem stepFiveRatioH_pos : (0 : ℝ) < stepFiveRatioH :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem stepFiveRatioH_lt_one : stepFiveRatioH < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- The exact scale identity behind the `∇h`-leg's domination: `3^{j/2} = 3^{m/2} ·
(3^{-1/2})^{m-j}`, with the `(m-j)`-power an integer power of the fixed ratio — the
shape `StepFiveGeometricTail` sums. -/
theorem three_rpow_half_eq_mul_ratioH_zpow (m j : ℤ) :
    (3 : ℝ) ^ ((j : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) * stepFiveRatioH ^ (m - j) := by
  rw [stepFiveRatioH, ← three_rpow_mul_intCast (-(1 / 2 : ℝ)) (m - j),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  push_cast
  ring

end

end Algsuperdiff.Section4.Provider.Regularity

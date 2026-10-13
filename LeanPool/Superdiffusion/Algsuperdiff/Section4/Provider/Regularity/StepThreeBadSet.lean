/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.MinimalScaleX
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepOneEpsilon
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Api

/-!
# StepThreeBadSet

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 3: the bad-scale set `𝓑_z`, as a `Finset`

## The target

```
𝓑_z := { j ∈ [n, m-1] ∩ ℤ  :  𝒢(j, z; ⅛s, ⅛ s δ^{1/2}) is not valid } .
```

## Contents

* `stepThreeGoodEvent` — the Step-3 good event, named once so that the
  identification with the producer's own event is a `rfl`
  (`stepThreeGoodEvent_eq_goodEventAt`).
* `stepThreeBadSet` — `𝓑_z` as a `Finset ℤ`, the `Finset.filter` of `Finset.Icc
  n (m-1)`.
* `mem_stepThreeBadSet_iff`, `stepThreeBadSet_subset_Icc` — membership, and
  the inclusion into the counting window `[n, m]` of
  `e.bad.scale.proportion.bound` (whose sum runs to `m`, one scale beyond the
  set).
* `measurableSet_mem_stepThreeBadSet`, `measurable_stepThreeBadSet_card` — the
  measurability story: each scale's membership event is the complement of a
  measurable good event, and the cardinality is the corresponding finite sum of
  indicators, hence measurable.  (: all downstream use is `a.e.`, so no
  pointwise finiteness is claimed anywhere.)
* `stepThreeBadSet_card_eq_sum`, `stepThreeBadSet_card_le_sum_Icc` — the
  cardinality as the `ℝ≥0∞` indicator sum, and its domination by the sum over
  the full counting window, which is the left half of
  `e.bad.scale.proportion.bound`.

## References

* ABK26, `t.regularity` Step 3.
* ABK26, `d.good.event.for.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The Step-3 good event -/

noncomputable def stepThreeGoodEvent (M : ABKModel d) (delta : ℝ) (j : ℤ)
    (z : Vec d) : Set (Cutoff.CutoffSample d) :=
  Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d) j z
    ⟨stepOneSEighth, stepOneSEighth_pos⟩ (stepOneEp delta)

/-- The Step-3 good event IS the event of the frozen
`p.minimal.scale.separation.sec4` clause at the Step-1 parameters: the same
`goodEventAt` at the same index `s/8` and the same threshold `(s/8)·δ^{1/2}`. -/
theorem stepThreeGoodEvent_eq_goodEventAt (M : ABKModel d) (delta : ℝ) (j : ℤ)
    (z : Vec d) :
    stepThreeGoodEvent M delta j z =
      Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d) j z
        ⟨stepOneSEighth, stepOneSEighth_pos⟩ (stepOneSEighth * Real.sqrt delta) := rfl


/-! ## 2. The bad-scale set -/

open Classical in
/-- **The bad-scale set** `𝓑_z`: the scales of the window `[n, m-1]` at which the
Step-3 good event fails. -/
noncomputable def stepThreeBadSet (M : ABKModel d) (delta : ℝ) (n m : ℤ)
    (z : Vec d) (omega : Cutoff.CutoffSample d) : Finset ℤ :=
  Finset.filter (fun j => omega ∉ stepThreeGoodEvent M delta j z) (Finset.Icc n (m - 1))

/-- Membership in `𝓑_z`. -/
theorem mem_stepThreeBadSet_iff (M : ABKModel d) (delta : ℝ) (n m : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) (j : ℤ) :
    j ∈ stepThreeBadSet M delta n m z omega ↔
      (n ≤ j ∧ j ≤ m - 1) ∧ omega ∉ stepThreeGoodEvent M delta j z := by
  classical
  rw [stepThreeBadSet, Finset.mem_filter, Finset.mem_Icc]

/-- `𝓑_z ⊆ [n, m-1]`. -/
theorem stepThreeBadSet_subset (M : ABKModel d) (delta : ℝ) (n m : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) :
    stepThreeBadSet M delta n m z omega ⊆ Finset.Icc n (m - 1) := by
  classical
  exact Finset.filter_subset _ _

/-- `𝓑_z ⊆ [n, m]`, the counting window of `e.bad.scale.proportion.bound`, and the
form the iteration lemma's binder `B ⊆ Finset.Icc n m` wants. -/
theorem stepThreeBadSet_subset_Icc (M : ABKModel d) (delta : ℝ) (n m : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) :
    stepThreeBadSet M delta n m z omega ⊆ Finset.Icc n m :=
  subset_trans (stepThreeBadSet_subset M delta n m z omega)
    (Finset.Icc_subset_Icc_right (by linarith only [] : m - 1 ≤ m))

/-! ## 4. The cardinality as an indicator sum -/

/-- **`|𝓑_z|` as the indicator sum** over the window `[n, m-1]`, in `ℝ≥0∞` — the
shape the frozen `p.minimal.scale.separation.sec4` density clause carries. -/
theorem stepThreeBadSet_card_eq_sum (M : ABKModel d) (delta : ℝ) (n m : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) :
    ((stepThreeBadSet M delta n m z omega).card : ℝ≥0∞) =
      ∑ j ∈ Finset.Icc n (m - 1),
        Set.indicator ((stepThreeGoodEvent M delta j z)ᶜ) (fun _ => (1 : ℝ≥0∞)) omega := by
  classical
  rw [stepThreeBadSet, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Set.indicator_apply]
  simp only [Set.mem_compl_iff]

/-- **The left half of `e.bad.scale.proportion.bound`**: `|𝓑_z|` is at most the
count of failures over the counting window `[n, m]` — the sum the frozen
producer's density clause bounds. -/
theorem stepThreeBadSet_card_le_sum_Icc (M : ABKModel d) (delta : ℝ) (n m : ℤ)
    (z : Vec d) (omega : Cutoff.CutoffSample d) :
    ((stepThreeBadSet M delta n m z omega).card : ℝ≥0∞) ≤
      ∑ j ∈ Finset.Icc n m,
        Set.indicator ((stepThreeGoodEvent M delta j z)ᶜ) (fun _ => (1 : ℝ≥0∞)) omega := by
  classical
  rw [stepThreeBadSet_card_eq_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (by linarith only [] : m - 1 ≤ m)) ?_
  intro j _ _
  exact zero_le

end Algsuperdiff.Section4.Provider.Regularity

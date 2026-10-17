/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeBadSet
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max

/-!
# StepSevenGoodScales

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7a: the extreme good scales `n'`, `m'`

## The target

```text
  n' := min { j ∈ [n+3, m-3] ∩ ℤ : j ∉ 𝓑 } ,
  m' := max { j ∈ [n+3, m-3] ∩ ℤ : j ∉ 𝓑 } ,
  max{ n' - n , m - m' } ≤ |𝓑| + 6 .
```

This module supplies them.

## What is delivered

* `StepSevenSelection B n m n' m'` — the selection as a named proposition: the
  two range facts, the two goodness facts, and the two facts (`n'` minimal,
  `m'` maximal among the good scales of `[n+3, m-3]`).  The extremality form is
  what the gaps are proved from, so no consumer has to re-run a `min`/`max`.
* `StepSevenSelection.lower_gap` / `upper_gap` — `n' - n ≤ |𝓑| + 3` and `m - m'
  ≤ |𝓑| + 3`, the sharp gaps; `max_gap_le` is the printed `max{n'-n, m-m'} ≤
  |𝓑| + 6`.  (The consumer asks for `m - m' ≤ |𝓑| + 3`,
  i.e. the sharp form, so both are exported.)
* the Step-3 instantiation: `exists_stepSevenSelection_stepThreeBadSet` at
  `𝓑 = stepThreeBadSet`, and `mem_stepThreeGoodEvent_of_stepSevenSelection`,
  which turns "`n'` is a good scale" into the good-event membership
  `ω ∈ 𝒢(n', z; ⅛s, ⅛ s δ^{1/2})` that Step 7b (`l.lambdas.stability`) consumes.

## The two combinatorial arguments, in one line each

*Non-emptiness*: `#(Icc (n+3) (m-3)) = m - n - 5` and
`#(Icc (n+3) (m-3)) ≤ #(Icc (n+3) (m-3) \ 𝓑) + #𝓑`, so `|𝓑| + 6 ≤ m - n`
forces the difference to be non-empty.

*The gaps*: minimality of `n'` puts the whole interval `[n+3, n'-1]` inside
`𝓑`, and that interval has `n' - n - 3` elements; symmetrically `(m', m-3]`
has `m - m' - 3` elements.  Both gaps are therefore `≤ |𝓑| + 3`.

## References

* ABK26, `t.regularity` Step 7.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The candidate index set -/

/-- **The Step-7a candidate range** `[n+3, m-3] ∩ ℤ`. -/
noncomputable def stepSevenCandidates (n m : ℤ) : Finset ℤ := Finset.Icc (n + 3) (m - 3)

/-- The candidate range has `m - n - 5` elements. -/
theorem card_stepSevenCandidates (n m : ℤ) :
    (stepSevenCandidates n m).card = (m - n - 5).toNat := by
  rw [stepSevenCandidates, Int.card_Icc]
  congr 1
  ring

/-- **The good scales of the Step-7a range**: the candidates outside the bad set. -/
noncomputable def stepSevenGoodScales (B : Finset ℤ) (n m : ℤ) : Finset ℤ :=
  stepSevenCandidates n m \ B

theorem mem_stepSevenGoodScales_iff {B : Finset ℤ} {n m j : ℤ} :
    j ∈ stepSevenGoodScales B n m ↔ (n + 3 ≤ j ∧ j ≤ m - 3) ∧ j ∉ B := by
  rw [stepSevenGoodScales, Finset.mem_sdiff, stepSevenCandidates, Finset.mem_Icc]

theorem stepSevenGoodScales_nonempty {B : Finset ℤ} {n m : ℤ}
    (hsep : (B.card : ℤ) + 6 ≤ m - n) : (stepSevenGoodScales B n m).Nonempty := by
  have hunion : (stepSevenGoodScales B n m).card + B.card =
      (stepSevenCandidates n m ∪ B).card :=
    Finset.card_sdiff_add_card _ _
  have hle : (stepSevenCandidates n m).card ≤ (stepSevenCandidates n m ∪ B).card :=
    Finset.card_le_card Finset.subset_union_left
  have hcard := card_stepSevenCandidates n m
  refine Finset.card_pos.mp ?_
  omega

/-! ## 2. The selection, as a named proposition -/

/-- **The Step-7a selection**: `n'` is the smallest and `m'` the largest good scale
of `[n+3, m-3]`.  The two extremality clauses are stated as universally
quantified minimality/maximality, which is what the gap bounds are proved from,
so a consumer never has to re-run the `min`/`max`. -/
structure StepSevenSelection (B : Finset ℤ) (n m n' m' : ℤ) : Prop where
  /-- `n+3 ≤ n'`. -/
  lower_lo : n + 3 ≤ n'
  /-- `n' ≤ m-3`. -/
  lower_hi : n' ≤ m - 3
  /-- `n+3 ≤ m'`. -/
  upper_lo : n + 3 ≤ m'
  /-- `m' ≤ m-3`. -/
  upper_hi : m' ≤ m - 3
  /-- `n'` is a good scale. -/
  lower_good : n' ∉ B
  /-- `m'` is a good scale. -/
  upper_good : m' ∉ B
  /-- `n'` is the smallest good scale of the range. -/
  lower_min : ∀ j : ℤ, n + 3 ≤ j → j ≤ m - 3 → j ∉ B → n' ≤ j
  /-- `m'` is the largest good scale of the range. -/
  upper_max : ∀ j : ℤ, n + 3 ≤ j → j ≤ m - 3 → j ∉ B → j ≤ m'

namespace StepSevenSelection

variable {B : Finset ℤ} {n m n' m' : ℤ}

/-- `n' ≤ m'`. -/
theorem le (h : StepSevenSelection B n m n' m') : n' ≤ m' :=
  h.lower_min m' h.upper_lo h.upper_hi h.upper_good

/-- **The sharp lower gap** `n' - n ≤ |𝓑| + 3`: minimality of `n'` puts the whole
interval `[n+3, n'-1]` — which has `n' - n - 3` elements — inside `𝓑`. -/
theorem lower_gap (h : StepSevenSelection B n m n' m') :
    n' - n ≤ (B.card : ℤ) + 3 := by
  have hlo := h.lower_lo
  have hhi := h.lower_hi
  have hsub : Finset.Ico (n + 3) n' ⊆ B := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    by_contra hjB
    have hmin := h.lower_min j hj.1 (by omega) hjB
    omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Ico] at hcard
  omega

/-- **The sharp upper gap** `m - m' ≤ |𝓑| + 3` — the form the consumer asks
for. -/
theorem upper_gap (h : StepSevenSelection B n m n' m') :
    m - m' ≤ (B.card : ℤ) + 3 := by
  have hlo := h.upper_lo
  have hhi := h.upper_hi
  have hsub : Finset.Ioc m' (m - 3) ⊆ B := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    by_contra hjB
    have hmax := h.upper_max j (by omega) hj.2 hjB
    omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Ioc] at hcard
  omega

/-- **The printed observation**: `max{ n' - n, m - m' } ≤ |𝓑| + 6`. -/
theorem max_gap_le (h : StepSevenSelection B n m n' m') :
    max (n' - n) (m - m') ≤ (B.card : ℤ) + 6 :=
  max_le (by linarith only [h.lower_gap]) (by linarith only [h.upper_gap])

/-- The pigeonhole: if `m' ≤ n'` then extremality forces every good scale
of `[n+3, m-3]` to equal `n'`, so all `m - n - 6` other candidates are bad. -/
theorem lt (h : StepSevenSelection B n m n' m')
    (hsep : (B.card : ℤ) + 7 ≤ m - n) : n' < m' := by
  rcases lt_or_ge n' m' with hlt | hge
  · exact hlt
  exfalso
  have hle := h.le
  have hlo := h.lower_lo
  have hhi := h.lower_hi
  have hsub : stepSevenCandidates n m \ {n'} ⊆ B := by
    intro j hj
    rw [Finset.mem_sdiff, stepSevenCandidates, Finset.mem_Icc,
      Finset.mem_singleton] at hj
    by_contra hjB
    have hmin := h.lower_min j hj.1.1 hj.1.2 hjB
    have hmax := h.upper_max j hj.1.1 hj.1.2 hjB
    omega
  have hmem : ({n'} : Finset ℤ) ⊆ stepSevenCandidates n m := by
    rw [Finset.singleton_subset_iff, stepSevenCandidates, Finset.mem_Icc]
    exact ⟨hlo, hhi⟩
  have hcard := Finset.card_le_card hsub
  have hsplit : (stepSevenCandidates n m \ {n'}).card + ({n'} : Finset ℤ).card =
      (stepSevenCandidates n m).card := Finset.card_sdiff_add_card_eq_card hmem
  rw [Finset.card_singleton, card_stepSevenCandidates] at hsplit
  omega

end StepSevenSelection

/-! ## 3. The witnesses -/

/-- **The Step-7a selection exists**, as soon as the printed window demand `|𝓑| + 6
≤ m - n` holds.  The witnesses are literally the manuscript's `min` and `max`
over the good scales of `[n+3, m-3]`. -/
theorem exists_stepSevenSelection {B : Finset ℤ} {n m : ℤ}
    (hsep : (B.card : ℤ) + 6 ≤ m - n) :
    ∃ n' m' : ℤ, StepSevenSelection B n m n' m' := by
  have hne := stepSevenGoodScales_nonempty hsep
  refine ⟨(stepSevenGoodScales B n m).min' hne,
    (stepSevenGoodScales B n m).max' hne, ?_⟩
  have hminmem := mem_stepSevenGoodScales_iff.mp
    ((stepSevenGoodScales B n m).min'_mem hne)
  have hmaxmem := mem_stepSevenGoodScales_iff.mp
    ((stepSevenGoodScales B n m).max'_mem hne)
  exact
    { lower_lo := hminmem.1.1
      lower_hi := hminmem.1.2
      upper_lo := hmaxmem.1.1
      upper_hi := hmaxmem.1.2
      lower_good := hminmem.2
      upper_good := hmaxmem.2
      lower_min := fun j hj1 hj2 hj3 =>
        (stepSevenGoodScales B n m).min'_le j (mem_stepSevenGoodScales_iff.mpr ⟨⟨hj1, hj2⟩, hj3⟩)
      upper_max := fun j hj1 hj2 hj3 =>
        (stepSevenGoodScales B n m).le_max' j
          (mem_stepSevenGoodScales_iff.mpr ⟨⟨hj1, hj2⟩, hj3⟩) }

/-! ## 4. The Step-3 instantiation -/

/-- **The selection at the Step-3 bad set** `𝓑_z`'s separation
`StepOneBadSetSeparation` (`|𝓑_z| + 7 ≤ m - n`) — which supplies both the
printed demand `+6` and the extra unit, so `n' < m'` comes for free. -/
theorem exists_stepSevenSelection_stepThreeBadSet {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {z : Vec d} {omega : Cutoff.CutoffSample d}
    (hsep : StepOneBadSetSeparation (stepThreeBadSet M delta n m z omega).card n m) :
    ∃ n' m' : ℤ,
      StepSevenSelection (stepThreeBadSet M delta n m z omega) n m n' m' ∧ n' < m' := by
  rw [StepOneBadSetSeparation] at hsep
  obtain ⟨n', m', hsel⟩ :=
    exists_stepSevenSelection (B := stepThreeBadSet M delta n m z omega) (n := n)
      (m := m) (by linarith only [hsep])
  exact ⟨n', m', hsel, hsel.lt hsep⟩

/-- **A selected scale IS a good scale of Step 3**: `j ∉ 𝓑_z` together with `n ≤ j
≤ m-1` is exactly `ω ∈ 𝒢(j, z; ⅛s, ⅛ s δ^{1/2})`, the good event
`l.lambdas.stability` (Step 7b) is applied on. -/
theorem mem_stepThreeGoodEvent_of_notMem_stepThreeBadSet {M : ABKModel d}
    {delta : ℝ} {n m j : ℤ} {z : Vec d} {omega : Cutoff.CutoffSample d}
    (hlo : n ≤ j) (hhi : j ≤ m - 1)
    (hj : j ∉ stepThreeBadSet M delta n m z omega) :
    omega ∈ stepThreeGoodEvent M delta j z := by
  by_contra hnot
  exact hj ((mem_stepThreeBadSet_iff M delta n m z omega j).mpr ⟨⟨hlo, hhi⟩, hnot⟩)

/-- The good event at the two selected scales, packaged.  The range facts `n ≤ n',
m' ≤ m - 1` are read off the selection's own `[n+3, m-3]` range. -/
theorem mem_stepThreeGoodEvent_of_stepSevenSelection {M : ABKModel d} {delta : ℝ}
    {n m n' m' : ℤ} {z : Vec d} {omega : Cutoff.CutoffSample d}
    (h : StepSevenSelection (stepThreeBadSet M delta n m z omega) n m n' m') :
    omega ∈ stepThreeGoodEvent M delta n' z ∧
      omega ∈ stepThreeGoodEvent M delta m' z := by
  refine ⟨mem_stepThreeGoodEvent_of_notMem_stepThreeBadSet ?_ ?_ h.lower_good,
    mem_stepThreeGoodEvent_of_notMem_stepThreeBadSet ?_ ?_ h.upper_good⟩
  · linarith only [h.lower_lo]
  · linarith only [h.lower_hi]
  · linarith only [h.upper_lo]
  · linarith only [h.upper_hi]

end Algsuperdiff.Section4.Provider.Regularity

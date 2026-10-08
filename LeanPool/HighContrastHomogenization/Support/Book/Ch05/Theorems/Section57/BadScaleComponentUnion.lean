/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.BadScaleUnion
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.BadScaleSplit

/-!
# Coarse-graining support: Support.Book.Ch05.Theorems.Section57.BadScaleComponentUnion

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Union bounds for the split bad-scale components

The bad-scale proof estimates each deterministic branch by summing its
fixed-pair events.  This file contains only those set identities and union
bounds.
-/

noncomputable section

variable {Ω : Type*}

/-- The fixed-pair bad event in the top branch `q ≤ n`, with the selected
bad-pair scale strictly below `n`. -/
@[expose]
def highTopPairEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q m n : ℕ) : Set Ω :=
  {ω | q ≤ n ∧ selectedBadPairScale K a t α q m n < n ∧
    ω ∈ badPairEvent H t α q m n}

/-- The fixed-pair bad event in the bottom branch `n ≤ q`, with the selected
bad-pair scale strictly below `n`. -/
@[expose]
def highBottomPairEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q m n : ℕ) : Set Ω :=
  {ω | n ≤ q ∧ selectedBadPairScale K a t α q m n < n ∧
    ω ∈ badPairEvent H t α q m n}

/-- The fixed-pair bad event in the bottom branch `n ≤ q`, with `n` no larger
than the selected bad-pair scale. -/
@[expose]
def crudeBottomPairEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q m n : ℕ) : Set Ω :=
  {ω | n ≤ q ∧ n ≤ selectedBadPairScale K a t α q m n ∧
    ω ∈ badPairEvent H t α q m n}

/-- The fixed-pair bad event in the top branch `q ≤ n`, with `n` no larger
than the selected bad-pair scale. -/
@[expose]
def crudeTopPairEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q m n : ℕ) : Set Ω :=
  {ω | q ≤ n ∧ n ≤ selectedBadPairScale K a t α q m n ∧
    ω ∈ badPairEvent H t α q m n}

theorem highTopBadScaleEvent_eq_iUnion_unpair
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    highTopBadScaleEvent H K a t α q =
      ⋃ k : ℕ,
        highTopPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2 := by
  ext ω
  constructor
  · rintro ⟨m, n, hqn, hhigh, hpair⟩
    refine Set.mem_iUnion.2 ⟨Nat.pair m n, ?_⟩
    simpa [highTopPairEvent, Nat.unpair_pair] using ⟨hqn, hhigh, hpair⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
    rcases hk with ⟨hqn, hhigh, hpair⟩
    exact ⟨(Nat.unpair k).1, (Nat.unpair k).2, hqn, hhigh, hpair⟩

theorem highBottomBadScaleEvent_eq_iUnion_unpair
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    highBottomBadScaleEvent H K a t α q =
      ⋃ k : ℕ,
        highBottomPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2 := by
  ext ω
  constructor
  · rintro ⟨m, n, hnq, hhigh, hpair⟩
    refine Set.mem_iUnion.2 ⟨Nat.pair m n, ?_⟩
    simpa [highBottomPairEvent, Nat.unpair_pair] using ⟨hnq, hhigh, hpair⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
    rcases hk with ⟨hnq, hhigh, hpair⟩
    exact ⟨(Nat.unpair k).1, (Nat.unpair k).2, hnq, hhigh, hpair⟩

theorem crudeBottomBadScaleEvent_eq_iUnion_unpair
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    crudeBottomBadScaleEvent H K a t α q =
      ⋃ k : ℕ,
        crudeBottomPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2 := by
  ext ω
  constructor
  · rintro ⟨m, n, hnq, hnot, hpair⟩
    refine Set.mem_iUnion.2 ⟨Nat.pair m n, ?_⟩
    have hnℓ : n ≤ selectedBadPairScale K a t α q m n := le_of_not_gt hnot
    simpa [crudeBottomPairEvent, Nat.unpair_pair] using ⟨hnq, hnℓ, hpair⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
    rcases hk with ⟨hnq, hnℓ, hpair⟩
    exact ⟨(Nat.unpair k).1, (Nat.unpair k).2, hnq, not_lt.mpr hnℓ, hpair⟩

theorem crudeTopBadScaleEvent_eq_iUnion_unpair
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    crudeTopBadScaleEvent H K a t α q =
      ⋃ k : ℕ,
        crudeTopPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2 := by
  ext ω
  constructor
  · rintro ⟨m, n, hqn, hnot, hpair⟩
    refine Set.mem_iUnion.2 ⟨Nat.pair m n, ?_⟩
    have hnℓ : n ≤ selectedBadPairScale K a t α q m n := le_of_not_gt hnot
    simpa [crudeTopPairEvent, Nat.unpair_pair] using ⟨hqn, hnℓ, hpair⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
    rcases hk with ⟨hqn, hnℓ, hpair⟩
    exact ⟨(Nat.unpair k).1, (Nat.unpair k).2, hqn, not_lt.mpr hnℓ, hpair⟩

variable [MeasurableSpace Ω]

theorem measureReal_highTopBadScaleEvent_le_tsum_unpair
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    (hsum : Summable fun k : ℕ =>
      μ.real
        (highTopPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2)) :
    μ.real (highTopBadScaleEvent H K a t α q) ≤
      ∑' k : ℕ,
        μ.real
          (highTopPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2) := by
  rw [highTopBadScaleEvent_eq_iUnion_unpair]
  exact measureReal_iUnion_nat_le_tsum (μ := μ) hsum

theorem measureReal_highBottomBadScaleEvent_le_tsum_unpair
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    (hsum : Summable fun k : ℕ =>
      μ.real
        (highBottomPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2)) :
    μ.real (highBottomBadScaleEvent H K a t α q) ≤
      ∑' k : ℕ,
        μ.real
          (highBottomPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2) := by
  rw [highBottomBadScaleEvent_eq_iUnion_unpair]
  exact measureReal_iUnion_nat_le_tsum (μ := μ) hsum

theorem measureReal_crudeBottomBadScaleEvent_le_tsum_unpair
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    (hsum : Summable fun k : ℕ =>
      μ.real
        (crudeBottomPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2)) :
    μ.real (crudeBottomBadScaleEvent H K a t α q) ≤
      ∑' k : ℕ,
        μ.real
          (crudeBottomPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2) := by
  rw [crudeBottomBadScaleEvent_eq_iUnion_unpair]
  exact measureReal_iUnion_nat_le_tsum (μ := μ) hsum

theorem measureReal_crudeTopBadScaleEvent_le_tsum_unpair
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    (hsum : Summable fun k : ℕ =>
      μ.real
        (crudeTopPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2)) :
    μ.real (crudeTopBadScaleEvent H K a t α q) ≤
      ∑' k : ℕ,
        μ.real
          (crudeTopPairEvent H K a t α q (Nat.unpair k).1 (Nat.unpair k).2) := by
  rw [crudeTopBadScaleEvent_eq_iUnion_unpair]
  exact measureReal_iUnion_nat_le_tsum (μ := μ) hsum

end

end Section57
end Ch05
end Book
end HCPolySupport

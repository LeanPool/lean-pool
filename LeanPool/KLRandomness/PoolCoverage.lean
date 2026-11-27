/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolQuery
import Mathlib.Tactic.Linarith

/-!
# Query fractions and exact missed-position counts

The analytic pool estimates use the fraction of a finite pool read by a scan.
The paper states the conclusion using missed positions.  For a nonempty finite
pool these formulations agree exactly, including the strict inequality in
"fewer than `τ * M` missed positions".
-/

@[expose] public section

noncomputable section

namespace Klr.PoolQuery

open Set
open scoped BigOperators

/-- The number of positions in the pool never queried on the prescribed answer
sequence. -/
def missedCount (π : ScanRule) (G : Finset ℕ) (Z : Cantor) : ℕ := by
  classical
  exact (G.filter fun a => ¬ Reads π a Z).card

theorem missedCount_le_card (π : ScanRule) (G : Finset ℕ) (Z : Cantor) :
    missedCount π G Z ≤ G.card := by
  classical
  exact Finset.card_filter_le _ _

open Classical in
theorem sum_indicator_eq_readCount (π : ScanRule) (G : Finset ℕ) (Z : Cantor) :
    (∑ a ∈ G, indicator π a Z) = ((G.filter fun a => Reads π a Z).card : ℝ) := by
  classical
  simp [indicator, Set.indicator_apply]

theorem sum_indicator_add_missedCount (π : ScanRule) (G : Finset ℕ) (Z : Cantor) :
    (∑ a ∈ G, indicator π a Z) + (missedCount π G Z : ℝ) = G.card := by
  classical
  rw [sum_indicator_eq_readCount]
  exact_mod_cast (Finset.card_filter_add_card_filter_not (s := G) (fun a => Reads π a Z))

theorem sum_indicator_eq_card_sub_missedCount (π : ScanRule) (G : Finset ℕ) (Z : Cantor) :
    (∑ a ∈ G, indicator π a Z) = (G.card : ℝ) - missedCount π G Z := by
  have h := sum_indicator_add_missedCount π G Z
  linarith

/-- The exact numerical identity relating read fraction and missed count. -/
theorem readFraction_eq_one_sub_missedCount (π : ScanRule) {G : Finset ℕ}
    (hG : G.Nonempty) (Z : Cantor) :
    readFraction π G Z = 1 - (missedCount π G Z : ℝ) / G.card := by
  have hcard : (G.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hG.card_pos)
  rw [readFraction, sum_indicator_eq_card_sub_missedCount, sub_div, div_self hcard]

theorem missedCount_pos_iff (π : ScanRule) (G : Finset ℕ) (Z : Cantor) :
    0 < missedCount π G Z ↔ ∃ a ∈ G, ¬ Reads π a Z := by
  classical
  simp [missedCount, Finset.card_pos, Finset.filter_nonempty_iff]

theorem missedCount_eq_zero_iff (π : ScanRule) (G : Finset ℕ) (Z : Cantor) :
    missedCount π G Z = 0 ↔ ∀ a ∈ G, Reads π a Z := by
  classical
  simp [missedCount, Finset.filter_eq_empty_iff]

theorem readFraction_lt_one_iff_missedCount_pos (π : ScanRule) {G : Finset ℕ}
    (hG : G.Nonempty) (Z : Cantor) :
    readFraction π G Z < 1 ↔ 0 < missedCount π G Z := by
  have hcard : 0 < (G.card : ℝ) := by exact_mod_cast hG.card_pos
  rw [readFraction_eq_one_sub_missedCount π hG, sub_lt_self_iff,
    div_pos_iff_of_pos_right hcard, Nat.cast_pos]

/-- Failure to read the whole nonempty pool means that at least one pool
position is missed. -/
theorem readFraction_lt_one_iff_exists_missed (π : ScanRule) {G : Finset ℕ}
    (hG : G.Nonempty) (Z : Cantor) :
    readFraction π G Z < 1 ↔ ∃ a ∈ G, ¬ Reads π a Z :=
  (readFraction_lt_one_iff_missedCount_pos π hG Z).trans (missedCount_pos_iff π G Z)

/-- The paper's strict missed-count inequality is exactly the strict
near-full-coverage inequality.  No rounding of the real threshold occurs. -/
theorem one_sub_lt_readFraction_iff_missedCount_lt (π : ScanRule) {G : Finset ℕ}
    (hG : G.Nonempty) (Z : Cantor) (τ : ℝ) :
    1 - τ < readFraction π G Z ↔ (missedCount π G Z : ℝ) < τ * G.card := by
  have hcard : 0 < (G.card : ℝ) := by exact_mod_cast hG.card_pos
  rw [readFraction_eq_one_sub_missedCount π hG]
  calc
    1 - τ < 1 - (missedCount π G Z : ℝ) / G.card ↔
        (missedCount π G Z : ℝ) / G.card < τ := by constructor <;> intro h <;> linarith
    _ ↔ (missedCount π G Z : ℝ) < τ * G.card := div_lt_iff₀ hcard

/-- The implication needed for soundness also holds for an empty pool. -/
theorem readFraction_lt_one_of_exists_missed (π : ScanRule) {G : Finset ℕ} (Z : Cantor)
    (h : ∃ a ∈ G, ¬ Reads π a Z) : readFraction π G Z < 1 := by
  obtain ⟨a, ha, hmiss⟩ := h
  exact (readFraction_lt_one_iff_exists_missed π ⟨a, ha⟩ Z).mpr ⟨a, ha, hmiss⟩

/-- The strict count event is empty for an empty pool, so this implication
does not need a nonempty hypothesis. -/
theorem one_sub_lt_readFraction_of_missedCount_lt (π : ScanRule) (G : Finset ℕ)
    (Z : Cantor) (τ : ℝ) (h : (missedCount π G Z : ℝ) < τ * G.card) :
    1 - τ < readFraction π G Z := by
  rcases G.eq_empty_or_nonempty with rfl | hG
  · simp [missedCount] at h
  · exact (one_sub_lt_readFraction_iff_missedCount_lt π hG Z τ).mpr h

theorem high_failure_eq_missing_event (π : ScanRule) {G : Finset ℕ}
    (hG : G.Nonempty) (H : Set Cantor) :
    {Z | Z ∈ H ∧ readFraction π G Z < 1} =
      {Z | Z ∈ H ∧ ∃ a ∈ G, ¬ Reads π a Z} := by
  ext Z
  simp only [mem_ofPred_eq, readFraction_lt_one_iff_exists_missed π hG]

theorem low_failure_eq_missedCount_event (π : ScanRule) {G : Finset ℕ}
    (hG : G.Nonempty) (L : Set Cantor) (τ : ℝ) :
    {Z | Z ∈ L ∧ 1 - τ < readFraction π G Z} =
      {Z | Z ∈ L ∧ (missedCount π G Z : ℝ) < τ * G.card} := by
  ext Z
  simp only [mem_ofPred_eq, one_sub_lt_readFraction_iff_missedCount_lt π hG]

end Klr.PoolQuery

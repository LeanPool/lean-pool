/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.BlockProductAnswer
import Mathlib.Tactic.Measurability

/-!
# Actual rank-drop events along fresh scans

Times are zero based: `atTime B π j X t` concerns the query made after `t`
answers, and compares the unread ranks after `t + 1` and `t` answers.  Thus
`lateEvent B π V j` means that block `j` has a rank drop after its first
`V j` queries have been answered.  These are events of actual input paths,
with no stopping-time or measurability hypotheses left to the caller.
-/

@[expose] public section

namespace Klr.DropEvents

open MeasureTheory AffineObservation

/-- A rank-losing next query belonging to the specified block. -/
def atBlock (B : ℕ → AffineBlock) (π : ScanRule) (j : ℕ) (v : List Bool) : Prop :=
  π.query v ∈ (B j).support ∧
    (B j).remainingRank π (v ++ [false]) < (B j).remainingRank π v

/-- The actual query at time `t` causes a rank drop in block `j`. -/
def atTime (B : ℕ → AffineBlock) (π : ScanRule) (j : ℕ) (X : Cantor) (t : ℕ) : Prop :=
  atBlock B π j (π.transcript X t)

/-- At least one drop in block `j` occurs at or after its prescribed horizon. -/
def lateEvent (B : ℕ → AffineBlock) (π : ScanRule) (V : ℕ → ℕ) (j : ℕ) : Set Cantor :=
  {X | ∃ t, V j ≤ t ∧ atTime B π j X t}

theorem forced_iff (B : ℕ → AffineBlock) (π : ScanRule) (v : List Bool) :
    BlockProductAnswer.forced B π v ↔ ∃ j, atBlock B π j v := Iff.rfl

/-- A query outside a block cannot change its unread rank. -/
theorem remainingRank_snoc_of_query_not_mem (B : AffineBlock) (π : ScanRule)
    (v : List Bool) (hq : π.query v ∉ B.support) (b : Bool) :
    B.remainingRank π (v ++ [b]) = B.remainingRank π v := by
  apply congrArg (fun S : Submodule (ZMod 2) (Fin B.rank → ZMod 2) =>
    Module.finrank (ZMod 2) S)
  apply AffineAnswer.unreadMap_range_congr
  ext i
  have hi : (i : ℕ) ≠ π.query v := fun h => hq (h ▸ i.property)
  simp [AffineBlock.observed, π.queriedPositions_snoc, hi]

/-- The predictable false-answer definition is exactly the actual numerical rank drop. -/
theorem atTime_iff_rank_drop (B : ℕ → AffineBlock) (π : ScanRule)
    (j : ℕ) (X : Cantor) (t : ℕ) :
    atTime B π j X t ↔
      (B j).remainingRank π (π.transcript X (t + 1)) <
        (B j).remainingRank π (π.transcript X t) := by
  rw [ScanRule.transcript_succ,
    (B j).remainingRank_snoc_answer_independent π _ _ false]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hq
    rw [remainingRank_snoc_of_query_not_mem (B j) π _ hq false] at h
    exact lt_irrefl _ h

/-- A function of any fixed finite transcript is measurable, even when the function
on transcripts is noncomputable.  Its domain of possible transcripts is countable. -/
theorem measurable_transcript_eval {α : Type*} [MeasurableSpace α]
    (π : ScanRule) (n : ℕ) (f : List Bool → α) :
    Measurable (fun X : Cantor => f (π.transcript X n)) := by
  let : MeasurableSpace (List Bool) := ⊤
  have ht : Measurable (fun X : Cantor => π.transcript X n) := by
    apply measurable_to_countable'
    intro v
    by_cases hv : v.length = n
    · change MeasurableSet {X : Cantor | π.transcript X n = v}
      simpa only [hv] using π.measurableSet_transcript v
    · have hempty : (fun X : Cantor => π.transcript X n) ⁻¹' {v} = ∅ := by
        ext X
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        intro h
        exact hv (by rw [← h, π.length_transcript])
      rw [hempty]
      exact MeasurableSet.empty
  exact Measurable.of_discrete.comp ht

theorem measurableSet_transcript_pred (π : ScanRule) (n : ℕ) (P : List Bool → Prop) :
    MeasurableSet {X : Cantor | P (π.transcript X n)} := by
  classical
  have h := measurable_transcript_eval π n (fun v => decide (P v))
  have he : MeasurableSet {X : Cantor | decide (P (π.transcript X n)) = true} :=
    h (measurableSet_singleton true)
  simpa only [decide_eq_true_eq] using he

theorem measurableSet_atTime (B : ℕ → AffineBlock) (π : ScanRule) (j t : ℕ) :
    MeasurableSet {X | atTime B π j X t} :=
  measurableSet_transcript_pred π t (atBlock B π j)

theorem measurableSet_lateEvent (B : ℕ → AffineBlock) (π : ScanRule)
    (V : ℕ → ℕ) (j : ℕ) : MeasurableSet (lateEvent B π V j) := by
  have he : lateEvent B π V j = ⋃ t : {t : ℕ // V j ≤ t},
      {X | atTime B π j X t.val} := by
    ext X
    simp only [lateEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨t, ht, hd⟩ => ⟨⟨t, ht⟩, hd⟩,
      fun ⟨t, hd⟩ => ⟨t.val, t.property, hd⟩⟩
  rw [he]
  exact MeasurableSet.iUnion fun t => measurableSet_atTime B π j t.val

/-- Freshness alone makes the set of all drops in any fixed block finite. -/
theorem finite_drop_times (B : ℕ → AffineBlock) (π : ScanRule) (j : ℕ) (X : Cantor) :
    {t | atTime B π j X t}.Finite := by
  have hf : ((fun t => π.query (π.transcript X t)) ⁻¹'
      ((B j).support : Set ℕ)).Finite :=
    (B j).support.finite_toSet.preimage (π.query_injective X).injOn
  exact hf.subset fun _ ht => ht.1

end Klr.DropEvents

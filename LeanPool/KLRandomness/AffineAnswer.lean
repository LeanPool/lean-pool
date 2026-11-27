/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineAnswerAlgebra
public import LeanPool.KLRandomness.AffineAnswerMeasure
import Mathlib.Tactic.NormNum

/-!
# Conditional fair and forced answers after arbitrary rank loss

The conditioning event contains a finite family of old block equations, one
disjoint block, and an actual adaptive transcript.  No full-unread-rank
assumption is made.  A kernel translation proves fairness when the queried
column is redundant; otherwise all compatible inputs agree on the answer.
The nonnull-history hypothesis is explicit in every conditional probability.
-/

@[expose] public section

namespace Klr

open MeasureTheory ProbabilityTheory AffineObservation FiniteMeasure StoppingTranscript
open scoped ENNReal

namespace ScanRule

/-- The next query has not already appeared in the prescribed transcript. -/
theorem query_not_mem_queriedPositions (π : ScanRule) (v : List Bool) :
    π.query v ∉ π.queriedPositions v := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact π.fresh v i.val i.isLt hi

/-- The query chosen from `v` is the only position added by its next answer. -/
theorem queriedPositions_snoc (π : ScanRule) (v : List Bool) (b : Bool) :
    π.queriedPositions (v ++ [b]) = insert (π.query v) (π.queriedPositions v) := by
  apply Finset.Subset.antisymm
  · intro q hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    have hlen : i.val ≤ v.length := by simpa using i.isLt
    rcases lt_or_eq_of_le hlen with hlt | heq
    · apply Finset.mem_insert_of_mem
      refine Finset.mem_image.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, ?_⟩
      simpa only [List.take_append_of_le_length hlt.le] using hi
    · apply Finset.mem_insert.mpr
      left
      simpa [heq] using hi.symm
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · refine Finset.mem_image.mpr ⟨⟨v.length, by simp⟩, Finset.mem_univ _, ?_⟩
      simp
    · exact π.queriedPositions_mono (List.prefix_append v [b]) hq

/-- A prescribed transcript depends exactly on its finitely many queried coordinates. -/
theorem dependsOn_inputEvent (π : ScanRule) (v : List Bool) :
    DependsOn (fun X : Cantor => X ∈ inputEvent π v) (π.queriedPositions v : Set ℕ) := by
  intro X Y hxy
  apply propext
  change π.transcript X v.length = v ↔ π.transcript Y v.length = v
  rw [π.transcript_eq_iff, π.transcript_eq_iff]
  constructor <;> intro h i hi
  · rw [← hxy _ (π.query_mem_queriedPositions v ⟨i, hi⟩)]
    exact h i hi
  · rw [hxy _ (π.query_mem_queriedPositions v ⟨i, hi⟩)]
    exact h i hi

/-- Inputs realizing the same transcript agree at every position it queried. -/
theorem inputEvent_agree (π : ScanRule) (v : List Bool) {X Y : Cantor}
    (hX : X ∈ inputEvent π v) (hY : Y ∈ inputEvent π v)
    {q : ℕ} (hq : q ∈ π.queriedPositions v) : X q = Y q := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  exact ((π.transcript_eq_iff X v).mp hX i.val i.isLt).trans
    ((π.transcript_eq_iff Y v).mp hY i.val i.isLt).symm

end ScanRule

namespace AffineBlock

/-- Within this block, the next query adds its column to the observed set. -/
theorem observed_snoc (B : AffineBlock) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ B.support) (b : Bool) :
    B.observed π (v ++ [b]) = insert ⟨π.query v, hq⟩ (B.observed π v) := by
  ext i
  simp [observed, π.queriedPositions_snoc, Subtype.ext_iff]

/-- The numerical rank after the next query is chosen before its answer is known. -/
theorem remainingRank_snoc_answer_independent (B : AffineBlock) (π : ScanRule)
    (v : List Bool) (b c : Bool) :
    B.remainingRank π (v ++ [b]) = B.remainingRank π (v ++ [c]) := by
  apply congrArg (fun S : Submodule (ZMod 2) (Fin B.rank → ZMod 2) =>
    Module.finrank (ZMod 2) S)
  apply AffineAnswer.unreadMap_range_congr
  simp only [observed, queriedPositions_append_singleton_eq π v b c]

/-- Numerical remaining rank after the next query, expressed by deleting its column. -/
theorem remainingRank_snoc_eq (B : AffineBlock) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ B.support) (b : Bool) :
    B.remainingRank π (v ++ [b]) = Module.finrank (ZMod 2)
      (LinearMap.range (unreadMap B.matrix (insert ⟨π.query v, hq⟩ (B.observed π v)))) := by
  exact congrArg (fun S : Submodule (ZMod 2) (Fin B.rank → ZMod 2) =>
    Module.finrank (ZMod 2) S)
    (AffineAnswer.unreadMap_range_congr B.matrix (B.observed_snoc π v hq b))

/-- The adaptive numerical rank-drop criterion, at any current remaining rank. -/
theorem rank_drop_iff_nextColumn_not_mem (B : AffineBlock) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ B.support) :
    B.remainingRank π (v ++ [false]) < B.remainingRank π v ↔
      AffineAnswer.column B.matrix ⟨π.query v, hq⟩ ∉
        LinearMap.range (unreadMap B.matrix (insert ⟨π.query v, hq⟩ (B.observed π v))) := by
  rw [B.remainingRank_snoc_eq π v hq false]
  exact AffineAnswer.rank_drop_iff_column_not_mem B.matrix (B.observed π v)
    ⟨π.query v, hq⟩ (π.query_not_mem_queriedPositions v)

end AffineBlock

namespace AffineAnswer

/-- Earlier equations, the current block equations, and the observed adaptive transcript. -/
def history {κ : Type*} (old : κ → AffineBlock) (B : AffineBlock)
    (π : ScanRule) (v : List Bool) : Set Cantor :=
  (AffineBlock.familyEvent old ∩ B.event) ∩ inputEvent π v

theorem measurableSet_history {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock) (π : ScanRule) (v : List Bool) :
    MeasurableSet (history old B π v) :=
  ((AffineBlock.measurableSet_familyEvent old).inter B.measurableSet_event).inter
    (measurableSet_inputEvent π v)

/-- Conditioning the actual current stage law on the transcript is exactly conditioning
fair coin on all the corresponding equations and observations together. -/
theorem cond_stage_transcript {κ : Type*} [Finite κ] (old : κ → AffineBlock)
    (B : AffineBlock) (π : ScanRule) (v : List Bool) :
    cond (cond fairCoin (AffineBlock.familyEvent old ∩ B.event)) (inputEvent π v) =
      cond fairCoin (history old B π v) :=
  cond_cond_eq_cond_inter
    ((AffineBlock.measurableSet_familyEvent old).inter B.measurableSet_event)
    (measurableSet_inputEvent π v) fairCoin

/-- Extend a vector on the block by zero on all other input positions. -/
def blockVector (B : AffineBlock) (k : B.support → ZMod 2) (n : ℕ) : ZMod 2 :=
  if h : n ∈ B.support then k ⟨n, h⟩ else 0

@[simp] theorem blockVector_apply (B : AffineBlock) (k : B.support → ZMod 2)
    (i : B.support) : blockVector B k i.val = k i := by
  simp [blockVector, i.property]

theorem coordinateValues_translate_blockVector (B : AffineBlock)
    (k : B.support → ZMod 2) (X : Cantor) :
    coordinateValues (fun i : B.support => i.val) (translate (blockVector B k) X) =
      coordinateValues (fun i : B.support => i.val) X + k := by
  funext i
  simp [translate]

theorem blockVector_eq_zero_on_queries (B : AffineBlock) (π : ScanRule) (v : List Bool)
    (k : B.support → ZMod 2) (hk : observedPart (B.observed π v) k = 0) :
    ∀ n ∈ π.queriedPositions v, blockVector B k n = 0 := by
  intro n hn
  by_cases hs : n ∈ B.support
  · have hki : k ⟨n, hs⟩ = 0 := congrFun hk ⟨⟨n, hs⟩, hn⟩
    simpa [blockVector, hs] using hki
  · simp [blockVector, hs]

/-- An unread kernel vector preserves the entire compatible-history event. -/
theorem translate_mem_history {κ : Type*} (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ j, Disjoint (old j).support B.support) (π : ScanRule) (v : List Bool)
    (k : B.support → ZMod 2) (hkO : observedPart (B.observed π v) k = 0)
    (hkD : B.matrix k = 0) (X : Cantor) :
    translate (blockVector B k) X ∈ history old B π v ↔ X ∈ history old B π v := by
  have hold : translate (blockVector B k) X ∈ AffineBlock.familyEvent old ↔
      X ∈ AffineBlock.familyEvent old := by
    apply forall_congr'
    intro j
    apply translate_mem_of_dependsOn (old j).event (old j).support
      (old j).dependsOn_event
    intro n hn
    simp [blockVector, Finset.disjoint_left.mp (hdis j) hn]
  have hblock : translate (blockVector B k) X ∈ B.event ↔ X ∈ B.event := by
    change B.matrix (coordinateValues _ (translate (blockVector B k) X)) = B.syndrome ↔ _
    rw [coordinateValues_translate_blockVector, map_add, hkD, add_zero]
    rfl
  have htrans := translate_mem_of_dependsOn (inputEvent π v) (π.queriedPositions v)
    (π.dependsOn_inputEvent v) (blockVector B k) (blockVector_eq_zero_on_queries B π v k hkO) X
  exact and_congr (and_congr hold hblock) htrans

/-- A redundant queried column gives a fair conditional answer, regardless of how
much row rank has already been lost.  Only compatibility of the history is required. -/
theorem cond_next_bit_eq_half_of_column_mem {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ j, Disjoint (old j).support B.support) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ B.support) (hpos : fairCoin (history old B π v) ≠ 0)
    (hc : column B.matrix ⟨π.query v, hq⟩ ∈
      LinearMap.range (unreadMap B.matrix (insert ⟨π.query v, hq⟩ (B.observed π v))))
    (b : Bool) :
    (cond fairCoin (history old B π v)) (bitEvent (π.query v) b) = (1 / 2 : ℝ≥0∞) := by
  obtain ⟨k, hkO, hkD, hkq⟩ := (column_mem_iff_kernel_vector B.matrix (B.observed π v)
    ⟨π.query v, hq⟩ (π.query_not_mem_queriedPositions v)).mp hc
  apply cond_bit_eq_half_of_translation (history old B π v)
    (measurableSet_history old B π v) hpos (blockVector B k)
    (translate_mem_history old B hdis π v k hkO hkD) (π.query v) _ b
  simpa [blockVector, hq] using hkq

/-- The next answer is fair whenever this query does not strictly decrease the
block's current numerical remaining rank. -/
theorem cond_next_bit_eq_half_of_no_rank_drop {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ j, Disjoint (old j).support B.support) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ B.support) (hpos : fairCoin (history old B π v) ≠ 0)
    (hnodrop : ¬B.remainingRank π (v ++ [false]) < B.remainingRank π v) (b : Bool) :
    (cond fairCoin (history old B π v)) (bitEvent (π.query v) b) = (1 / 2 : ℝ≥0∞) := by
  apply cond_next_bit_eq_half_of_column_mem old B hdis π v hq hpos _ b
  by_contra hc
  exact hnodrop ((B.rank_drop_iff_nextColumn_not_mem π v hq).mpr hc)

/-- At a rank drop, every two inputs satisfying the equations and the fixed transcript
give the same answer.  This is a pointwise conclusion, stronger than almost sure forcing. -/
theorem next_bits_eq_of_rank_drop {κ : Type*} (old : κ → AffineBlock) (B : AffineBlock)
    (π : ScanRule) (v : List Bool) (hq : π.query v ∈ B.support)
    (hdrop : B.remainingRank π (v ++ [false]) < B.remainingRank π v)
    {X Y : Cantor} (hX : X ∈ history old B π v) (hY : Y ∈ history old B π v) :
    X (π.query v) = Y (π.query v) := by
  apply boolEquivF2.injective
  apply answer_eq_of_column_not_mem B.matrix (B.observed π v) ⟨π.query v, hq⟩
    (π.query_not_mem_queriedPositions v)
    ((B.rank_drop_iff_nextColumn_not_mem π v hq).mp hdrop)
    (x := coordinateValues (fun i : B.support => i.val) X)
    (y := coordinateValues (fun i : B.support => i.val) Y)
  · funext i
    change boolEquivF2 (X i.val.val) = boolEquivF2 (Y i.val.val)
    rw [π.inputEvent_agree v hX.2 hY.2 i.property]
  · exact hX.1.2.trans hY.1.2.symm

/-- At a rank drop in a compatible history, exactly one bit is possible; it has
conditional probability one and its opposite has conditional probability zero. -/
theorem cond_next_bit_forced_of_rank_drop {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ B.support) (hpos : fairCoin (history old B π v) ≠ 0)
    (hdrop : B.remainingRank π (v ++ [false]) < B.remainingRank π v) :
    ∃ b : Bool, history old B π v ⊆ bitEvent (π.query v) b ∧
      (cond fairCoin (history old B π v)) (bitEvent (π.query v) b) = 1 ∧
      (cond fairCoin (history old B π v)) (bitEvent (π.query v) (!b)) = 0 := by
  obtain ⟨X, hX⟩ := nonempty_of_measure_ne_zero hpos
  have hsub : history old B π v ⊆ bitEvent (π.query v) (X (π.query v)) := by
    intro Y hY
    exact next_bits_eq_of_rank_drop old B π v hq hdrop hY hX
  exact ⟨X (π.query v), hsub, cond_bit_eq_one_zero_of_subset (history old B π v)
    (measurableSet_history old B π v) hpos (π.query v) (X (π.query v)) hsub⟩

/-- Fairness of the next answer is equivalent to absence of a strict rank decrease,
under the actual finite equations-and-transcript conditional law. -/
theorem cond_next_answer_fair_iff_no_rank_drop {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ j, Disjoint (old j).support B.support) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ B.support) (hpos : fairCoin (history old B π v) ≠ 0) :
    (∀ b : Bool, (cond fairCoin (history old B π v)) (bitEvent (π.query v) b) =
      (1 / 2 : ℝ≥0∞)) ↔ ¬B.remainingRank π (v ++ [false]) < B.remainingRank π v := by
  constructor
  · intro hfair hdrop
    obtain ⟨b, _, hb, _⟩ := cond_next_bit_forced_of_rank_drop old B π v hq hpos hdrop
    have h := hfair b
    rw [hb] at h
    have hm := congrArg (fun a : ℝ≥0∞ => a * 2) h
    rw [one_mul, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)] at hm
    norm_num at hm
  · intro hnodrop b
    exact cond_next_bit_eq_half_of_no_rank_drop old B hdis π v hq hpos hnodrop b

/-- The same fair-or-rank-drop equivalence stated by first conditioning on all block
equations, then conditioning that genuine stage law on the observed transcript. -/
theorem stage_next_answer_fair_iff_no_rank_drop {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ j, Disjoint (old j).support B.support) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ B.support) (hpos : fairCoin (history old B π v) ≠ 0) :
    (∀ b : Bool,
      (cond (cond fairCoin (AffineBlock.familyEvent old ∩ B.event)) (inputEvent π v))
        (bitEvent (π.query v) b) = (1 / 2 : ℝ≥0∞)) ↔
      ¬B.remainingRank π (v ++ [false]) < B.remainingRank π v := by
  rw [cond_stage_transcript]
  exact cond_next_answer_fair_iff_no_rank_drop old B hdis π v hq hpos

/-- A fresh query outside every conditioned block is fair, independently of all
remaining block ranks. -/
theorem cond_next_bit_eq_half_of_free {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock) (π : ScanRule) (v : List Bool)
    (hqB : π.query v ∉ B.support) (hqold : ∀ j, π.query v ∉ (old j).support)
    (hpos : fairCoin (history old B π v) ≠ 0) (b : Bool) :
    (cond fairCoin (history old B π v)) (bitEvent (π.query v) b) = (1 / 2 : ℝ≥0∞) := by
  let z : ℕ → ZMod 2 := Pi.single (π.query v) 1
  have hz (S : Finset ℕ) (hq : π.query v ∉ S) : ∀ n ∈ S, z n = 0 := by
    intro n hn
    have hne : n ≠ π.query v := by intro h; exact hq (h ▸ hn)
    simp [z, hne]
  have hinv (X : Cantor) : translate z X ∈ history old B π v ↔ X ∈ history old B π v := by
    have hold : translate z X ∈ AffineBlock.familyEvent old ↔ X ∈ AffineBlock.familyEvent old := by
      apply forall_congr'
      intro j
      exact translate_mem_of_dependsOn (old j).event (old j).support
        (old j).dependsOn_event z (hz _ (hqold j)) X
    exact and_congr (and_congr hold
      (translate_mem_of_dependsOn B.event B.support B.dependsOn_event z (hz _ hqB) X))
      (translate_mem_of_dependsOn (inputEvent π v) (π.queriedPositions v)
        (π.dependsOn_inputEvent v) z (hz _ (π.query_not_mem_queriedPositions v)) X)
  exact cond_bit_eq_half_of_translation (history old B π v)
    (measurableSet_history old B π v) hpos z hinv (π.query v) (by simp [z]) b

end AffineAnswer
end Klr

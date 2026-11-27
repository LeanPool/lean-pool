/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.BlockProduct

/-!
# Fair and forced next answers under the infinite block law

Parent and child transcript events depend on finitely many coordinates.  Their
probabilities under the constructed infinite law therefore agree with one
sufficiently late finite stage.  At that stage the affine next-answer theorem
applies, including after partial rank loss.  Null parent events are handled by
monotonicity, so the child-mass identities have no compatibility premise.
-/

@[expose] public section

namespace Klr.BlockProductAnswer

open MeasureTheory ProbabilityTheory AffineAnswer StoppingTranscript
open scoped ENNReal

/-- A query is forced when its own block loses unread rank at that query. -/
def forced (B : ℕ → AffineBlock) (π : ScanRule) (v : List Bool) : Prop :=
  ∃ k, π.query v ∈ (B k).support ∧
    (B k).remainingRank π (v ++ [false]) < (B k).remainingRank π v

/-- The child transcript also specifies the next queried input bit. -/
theorem inputEvent_snoc (π : ScanRule) (v : List Bool) (b : Bool) :
    inputEvent π (v ++ [b]) = inputEvent π v ∩ bitEvent (π.query v) b := by
  ext X
  constructor
  · intro h
    change π.transcript X (v ++ [b]).length = v ++ [b] at h
    simp only [List.length_append, List.length_singleton] at h
    have ht := π.transcript_take X (m := v.length) (n := v.length + 1) (by omega)
    rw [h] at ht
    have hp : π.transcript X v.length = v := by simpa using ht.symm
    rw [ScanRule.transcript_succ, hp] at h
    have hb : X (π.query v) = b := by simpa using List.append_cancel_left h
    exact ⟨hp, hb⟩
  · rintro ⟨hp, hb⟩
    change π.transcript X v.length = v at hp
    change X (π.query v) = b at hb
    simp [inputEvent, ScanRule.transcript_succ, hp, hb]

theorem inputEvent_snoc_subset (π : ScanRule) (v : List Bool) (b : Bool) :
    inputEvent π (v ++ [b]) ⊆ inputEvent π v := by
  rw [inputEvent_snoc]
  exact Set.inter_subset_left

/-- A conditional fair-answer identity gives a mass identity even for a null parent. -/
theorem child_mass_of_cond_fair (μ : Measure Cantor) [IsFiniteMeasure μ]
    (π : ScanRule) (v : List Bool) (b : Bool)
    (hfair : μ (inputEvent π v) ≠ 0 →
      (cond μ (inputEvent π v)) (bitEvent (π.query v) b) = (1 / 2 : ℝ≥0∞)) :
    μ (inputEvent π (v ++ [b])) = (1 / 2 : ℝ≥0∞) * μ (inputEvent π v) := by
  by_cases hzero : μ (inputEvent π v) = 0
  · rw [measure_mono_null (inputEvent_snoc_subset π v b) hzero, hzero, mul_zero]
  · rw [inputEvent_snoc, ← cond_mul_eq_inter (measurableSet_inputEvent π v)
      (bitEvent (π.query v) b) μ, hfair hzero]

/-- Conditional forcing gives an unconditional deterministic split, with both children
null when the parent is null. -/
theorem child_mass_of_cond_forced (μ : Measure Cantor) [IsFiniteMeasure μ]
    (π : ScanRule) (v : List Bool)
    (hforce : μ (inputEvent π v) ≠ 0 → ∃ b : Bool,
      (cond μ (inputEvent π v)) (bitEvent (π.query v) b) = 1 ∧
      (cond μ (inputEvent π v)) (bitEvent (π.query v) (!b)) = 0) :
    ∃ b : Bool, μ (inputEvent π (v ++ [b])) = μ (inputEvent π v) ∧
      μ (inputEvent π (v ++ [!b])) = 0 := by
  by_cases hzero : μ (inputEvent π v) = 0
  · refine ⟨false, ?_, ?_⟩
    · rw [measure_mono_null (inputEvent_snoc_subset π v false) hzero, hzero]
    · exact measure_mono_null (inputEvent_snoc_subset π v (!false)) hzero
  · obtain ⟨b, hb, hnb⟩ := hforce hzero
    refine ⟨b, ?_, ?_⟩
    · rw [inputEvent_snoc, ← cond_mul_eq_inter (measurableSet_inputEvent π v)
        (bitEvent (π.query v) b) μ, hb, one_mul]
    · rw [inputEvent_snoc, ← cond_mul_eq_inter (measurableSet_inputEvent π v)
        (bitEvent (π.query v) (!b)) μ, hnb, zero_mul]

/-- The other members of a finite prefix, with one selected block removed. -/
def otherPrefix (B : ℕ → AffineBlock) (n k : ℕ) : {i : Fin n // i.val ≠ k} → AffineBlock :=
  fun i => B i.val.val

theorem prefixEvent_eq_otherPrefix (B : ℕ → AffineBlock) (n k : ℕ) (hk : k < n) :
    PrefixStage.prefixEvent B n =
      AffineBlock.familyEvent (otherPrefix B n k) ∩ (B k).event := by
  ext X
  rw [PrefixStage.mem_prefixEvent]
  change (∀ j < n, X ∈ (B j).event) ↔
    (∀ i : {i : Fin n // i.val ≠ k}, X ∈ (B i.val.val).event) ∧ X ∈ (B k).event
  constructor
  · intro h
    exact ⟨fun i => h i.val.val i.val.isLt, h k hk⟩
  · rintro ⟨h, hkX⟩ j hj
    by_cases he : j = k
    · simpa [he] using hkX
    · exact h ⟨⟨j, hj⟩, he⟩

private theorem prefix_history_ne_zero (B : ℕ → AffineBlock) (n k : ℕ) (hk : k < n)
    (π : ScanRule) (v : List Bool) (h : PrefixStage.law B n (inputEvent π v) ≠ 0) :
    fairCoin (history (otherPrefix B n k) (B k) π v) ≠ 0 := by
  have hp := inter_pos_of_cond_ne_zero (PrefixStage.measurableSet_prefixEvent B n) h
  rw [prefixEvent_eq_otherPrefix B n k hk] at hp
  exact hp.ne'

private theorem prefix_cond_transcript (B : ℕ → AffineBlock) (n k : ℕ) (hk : k < n)
    (π : ScanRule) (v : List Bool) :
    cond (PrefixStage.law B n) (inputEvent π v) =
      cond fairCoin (history (otherPrefix B n k) (B k) π v) := by
  rw [PrefixStage.law_eq_cond, prefixEvent_eq_otherPrefix B n k hk]
  exact cond_stage_transcript (otherPrefix B n k) (B k) π v

/-- The finite-prefix child identity, with the queried block isolated from all others. -/
theorem prefix_child_mass_of_no_rank_drop (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n k : ℕ) (hk : k < n) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ (B k).support)
    (hnodrop : ¬(B k).remainingRank π (v ++ [false]) < (B k).remainingRank π v) (b : Bool) :
    PrefixStage.law B n (inputEvent π (v ++ [b])) =
      (1 / 2 : ℝ≥0∞) * PrefixStage.law B n (inputEvent π v) := by
  let _ := PrefixStage.law_isProbabilityMeasure B hdis n
  apply child_mass_of_cond_fair (PrefixStage.law B n) π v b
  intro hpos
  rw [prefix_cond_transcript B n k hk π v]
  exact cond_next_bit_eq_half_of_no_rank_drop (otherPrefix B n k) (B k)
    (fun i => hdis i.property) π v hq (prefix_history_ne_zero B n k hk π v hpos) hnodrop b

/-- The finite-prefix child identity for a query outside every block. -/
theorem prefix_child_mass_of_free (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (hn : 0 < n) (π : ScanRule) (v : List Bool)
    (hfree : ∀ k, π.query v ∉ (B k).support) (b : Bool) :
    PrefixStage.law B n (inputEvent π (v ++ [b])) =
      (1 / 2 : ℝ≥0∞) * PrefixStage.law B n (inputEvent π v) := by
  let _ := PrefixStage.law_isProbabilityMeasure B hdis n
  apply child_mass_of_cond_fair (PrefixStage.law B n) π v b
  intro hpos
  rw [prefix_cond_transcript B n 0 hn π v]
  exact cond_next_bit_eq_half_of_free (otherPrefix B n 0) (B 0) π v
    (hfree 0) (fun i => hfree i.val.val) (prefix_history_ne_zero B n 0 hn π v hpos) b

/-- A strict rank drop gives a deterministic child split at a finite prefix stage. -/
theorem prefix_child_mass_forced (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n k : ℕ) (hk : k < n) (π : ScanRule) (v : List Bool)
    (hq : π.query v ∈ (B k).support)
    (hdrop : (B k).remainingRank π (v ++ [false]) < (B k).remainingRank π v) :
    ∃ b : Bool, PrefixStage.law B n (inputEvent π (v ++ [b])) =
      PrefixStage.law B n (inputEvent π v) ∧
      PrefixStage.law B n (inputEvent π (v ++ [!b])) = 0 := by
  let _ := PrefixStage.law_isProbabilityMeasure B hdis n
  apply child_mass_of_cond_forced (PrefixStage.law B n) π v
  intro hpos
  rw [prefix_cond_transcript B n k hk π v]
  obtain ⟨b, _, hb, hnb⟩ := cond_next_bit_forced_of_rank_drop
    (otherPrefix B n k) (B k) π v hq (prefix_history_ne_zero B n k hk π v hpos) hdrop
  exact ⟨b, hb, hnb⟩

/-- The finite coordinates needed to distinguish a parent transcript and both its children. -/
def nextSupport (π : ScanRule) (v : List Bool) : Finset ℕ :=
  insert (π.query v) (π.queriedPositions v)

private theorem parent_dependsOn_nextSupport (π : ScanRule) (v : List Bool) :
    DependsOn (fun X : Cantor => X ∈ inputEvent π v) (nextSupport π v : Set ℕ) :=
  (π.dependsOn_inputEvent v).mono (by intro q hq; exact Finset.mem_insert_of_mem hq)

private theorem child_dependsOn_nextSupport (π : ScanRule) (v : List Bool) (b : Bool) :
    DependsOn (fun X : Cantor => X ∈ inputEvent π (v ++ [b])) (nextSupport π v : Set ℕ) := by
  simpa only [nextSupport, π.queriedPositions_snoc] using π.dependsOn_inputEvent (v ++ [b])

theorem parent_mass_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (v : List Bool) (n : ℕ) (hn : BlockProduct.cutoff B (nextSupport π v) ≤ n) :
    BlockProduct.law B hdis (inputEvent π v) = PrefixStage.law B n (inputEvent π v) :=
  BlockProduct.law_apply_eq_stage B hdis (nextSupport π v) (inputEvent π v)
    (parent_dependsOn_nextSupport π v) n hn

theorem child_mass_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (v : List Bool) (b : Bool)
    (n : ℕ) (hn : BlockProduct.cutoff B (nextSupport π v) ≤ n) :
    BlockProduct.law B hdis (inputEvent π (v ++ [b])) =
      PrefixStage.law B n (inputEvent π (v ++ [b])) :=
  BlockProduct.law_apply_eq_stage B hdis (nextSupport π v) (inputEvent π (v ++ [b]))
    (child_dependsOn_nextSupport π v b) n hn

/-- Under the actual infinite law, a block query with no rank drop splits its
transcript mass equally between its two children.  Null histories are included. -/
theorem child_mass_of_no_rank_drop_in_block (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (k : ℕ) (π : ScanRule) (v : List Bool) (hq : π.query v ∈ (B k).support)
    (hnodrop : ¬(B k).remainingRank π (v ++ [false]) < (B k).remainingRank π v) (b : Bool) :
    BlockProduct.law B hdis (inputEvent π (v ++ [b])) =
      (1 / 2 : ℝ≥0∞) * BlockProduct.law B hdis (inputEvent π v) := by
  let n := max (BlockProduct.cutoff B (nextSupport π v)) (k + 1)
  rw [child_mass_eq_stage B hdis π v b n (Nat.le_max_left _ _),
    parent_mass_eq_stage B hdis π v n (Nat.le_max_left _ _)]
  exact prefix_child_mass_of_no_rank_drop B hdis n k
    (lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right _ _)) π v hq hnodrop b

/-- A query outside all blocks is fair under the infinite law, including null histories. -/
theorem child_mass_of_free (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (v : List Bool) (hfree : ∀ k, π.query v ∉ (B k).support) (b : Bool) :
    BlockProduct.law B hdis (inputEvent π (v ++ [b])) =
      (1 / 2 : ℝ≥0∞) * BlockProduct.law B hdis (inputEvent π v) := by
  let n := max (BlockProduct.cutoff B (nextSupport π v)) 1
  rw [child_mass_eq_stage B hdis π v b n (Nat.le_max_left _ _),
    parent_mass_eq_stage B hdis π v n (Nat.le_max_left _ _)]
  exact prefix_child_mass_of_free B hdis n
    (lt_of_lt_of_le (by omega : 0 < 1) (Nat.le_max_right _ _)) π v hfree b

/-- Every non-forced query obeys the exact fair child-mass identity for the constructed
infinite block law.  This is the input required by the fair/forced capital argument. -/
theorem child_mass_of_not_forced (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (v : List Bool) (hnot : ¬forced B π v) (b : Bool) :
    BlockProduct.law B hdis (inputEvent π (v ++ [b])) =
      (1 / 2 : ℝ≥0∞) * BlockProduct.law B hdis (inputEvent π v) := by
  classical
  by_cases hmem : ∃ k, π.query v ∈ (B k).support
  · obtain ⟨k, hk⟩ := hmem
    apply child_mass_of_no_rank_drop_in_block B hdis k π v hk _ b
    intro hdrop
    exact hnot ⟨k, hk, hdrop⟩
  · exact child_mass_of_free B hdis π v (fun k hk => hmem ⟨k, hk⟩) b

/-- A forced query gives all parent mass to one child and zero mass to the other under
the actual infinite block law.  The statement also includes null parent events. -/
theorem child_mass_forced (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (v : List Bool) (hforce : forced B π v) :
    ∃ b : Bool, BlockProduct.law B hdis (inputEvent π (v ++ [b])) =
      BlockProduct.law B hdis (inputEvent π v) ∧
      BlockProduct.law B hdis (inputEvent π (v ++ [!b])) = 0 := by
  obtain ⟨k, hq, hdrop⟩ := hforce
  let n := max (BlockProduct.cutoff B (nextSupport π v)) (k + 1)
  obtain ⟨b, hb, hnb⟩ := prefix_child_mass_forced B hdis n k
    (lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right _ _)) π v hq hdrop
  refine ⟨b, ?_, ?_⟩
  · rw [child_mass_eq_stage B hdis π v b n (Nat.le_max_left _ _),
      parent_mass_eq_stage B hdis π v n (Nat.le_max_left _ _)]
    exact hb
  · rw [child_mass_eq_stage B hdis π v (!b) n (Nat.le_max_left _ _)]
    exact hnb

/-- The equivalent convenient hypothesis that no block loses rank at this query. -/
theorem child_mass_of_no_rank_drop (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (v : List Bool)
    (hnodrop : ∀ k, ¬(B k).remainingRank π (v ++ [false]) < (B k).remainingRank π v)
    (b : Bool) :
    BlockProduct.law B hdis (inputEvent π (v ++ [b])) =
      (1 / 2 : ℝ≥0∞) * BlockProduct.law B hdis (inputEvent π v) :=
  child_mass_of_not_forced B hdis π v (fun ⟨k, _, hk⟩ => hnodrop k hk) b

/-- For a positive-probability transcript, a non-forced next answer is conditionally fair
under the constructed infinite law. -/
theorem cond_next_bit_eq_half (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (v : List Bool) (hnot : ¬forced B π v)
    (hpos : BlockProduct.law B hdis (inputEvent π v) ≠ 0) (b : Bool) :
    (cond (BlockProduct.law B hdis) (inputEvent π v)) (bitEvent (π.query v) b) =
      (1 / 2 : ℝ≥0∞) := by
  rw [cond_apply (measurableSet_inputEvent π v), ← inputEvent_snoc,
    child_mass_of_not_forced B hdis π v hnot b, mul_left_comm,
    ENNReal.inv_mul_cancel hpos (measure_ne_top _ _), mul_one]

/-- For a positive-probability transcript, a forced query has a deterministic conditional
answer under the constructed infinite law. -/
theorem cond_next_bit_forced (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (v : List Bool) (hforce : forced B π v)
    (hpos : BlockProduct.law B hdis (inputEvent π v) ≠ 0) :
    ∃ b : Bool,
      (cond (BlockProduct.law B hdis) (inputEvent π v)) (bitEvent (π.query v) b) = 1 ∧
      (cond (BlockProduct.law B hdis) (inputEvent π v)) (bitEvent (π.query v) (!b)) = 0 := by
  obtain ⟨b, hb, hnb⟩ := child_mass_forced B hdis π v hforce
  refine ⟨b, ?_, ?_⟩
  · rw [cond_apply (measurableSet_inputEvent π v), ← inputEvent_snoc, hb,
      ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)]
  · rw [cond_apply (measurableSet_inputEvent π v), ← inputEvent_snoc, hnb, mul_zero]

end Klr.BlockProductAnswer

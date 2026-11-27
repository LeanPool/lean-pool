/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineAnswer
import Mathlib.Tactic.NormNum

/-!
# Prefixes of the finite-stage block laws

For a sequence of pairwise disjoint affine blocks, stage `n` conditions fair
coin on blocks `0, ..., n - 1`.  The laws are probability measures.  Adding a
block preserves a transcript while its unread columns have full rank, and
preserves every event on coordinates disjoint from the added block.

Both identities telescope across arbitrary finite intervals of stages.  The
supported-event identity supplies the consistency needed to construct the
eventual block law from its finite-coordinate marginals.
-/

@[expose] public section

namespace Klr.PrefixStage

open MeasureTheory ProbabilityTheory AffineBlock FiniteStage StoppingTranscript
open scoped ENNReal

/-- The first `n` blocks, indexed by `Fin n`. -/
def prefixFamily (B : ℕ → AffineBlock) (n : ℕ) : Fin n → AffineBlock := fun i => B i.val

/-- All equations imposed before stage `n`. -/
def prefixEvent (B : ℕ → AffineBlock) (n : ℕ) : Set Cantor :=
  familyEvent (prefixFamily B n)

/-- All coordinates used by the first `n` blocks. -/
def prefixSupport (B : ℕ → AffineBlock) (n : ℕ) : Finset ℕ :=
  familySupport (prefixFamily B n)

/-- The actual stage-`n` probability law, before block `n` is imposed. -/
noncomputable def law (B : ℕ → AffineBlock) (n : ℕ) : Measure Cantor :=
  finiteStageLaw (prefixFamily B n)

theorem law_eq_cond (B : ℕ → AffineBlock) (n : ℕ) :
    law B n = cond fairCoin (prefixEvent B n) := rfl

@[simp] theorem mem_prefixEvent (B : ℕ → AffineBlock) (n : ℕ) (X : Cantor) :
    X ∈ prefixEvent B n ↔ ∀ k < n, X ∈ (B k).event := by
  change (∀ i : Fin n, X ∈ (B i.val).event) ↔ _
  exact ⟨fun h k hk => h ⟨k, hk⟩, fun h i => h i.val i.isLt⟩

@[simp] theorem prefixEvent_zero (B : ℕ → AffineBlock) : prefixEvent B 0 = Set.univ := by
  ext X
  simp

theorem prefixEvent_succ (B : ℕ → AffineBlock) (n : ℕ) :
    prefixEvent B (n + 1) = prefixEvent B n ∩ (B n).event := by
  ext X
  simp only [mem_prefixEvent, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h n (by omega)⟩
  · rintro ⟨h, hn⟩ k hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkn | rfl
    · exact h k hkn
    · exact hn

theorem prefixEvent_antitone (B : ℕ → AffineBlock) : Antitone (prefixEvent B) := by
  intro n m hnm X hX
  exact (mem_prefixEvent B n X).mpr (fun k hk =>
    (mem_prefixEvent B m X).mp hX k (lt_of_lt_of_le hk hnm))

theorem measurableSet_prefixEvent (B : ℕ → AffineBlock) (n : ℕ) :
    MeasurableSet (prefixEvent B n) := measurableSet_familyEvent (prefixFamily B n)

theorem prefixEvent_dependsOn (B : ℕ → AffineBlock) (n : ℕ) :
    DependsOn (fun X : Cantor => X ∈ prefixEvent B n) (prefixSupport B n : Set ℕ) :=
  familyEvent_dependsOn (prefixFamily B n)

@[simp] theorem mem_prefixSupport (B : ℕ → AffineBlock) (n q : ℕ) :
    q ∈ prefixSupport B n ↔ ∃ k, k < n ∧ q ∈ (B k).support := by
  simp only [prefixSupport, familySupport, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.isLt, hi⟩, fun ⟨k, hk, hq⟩ => ⟨⟨k, hk⟩, hq⟩⟩

theorem prefixSupport_mono (B : ℕ → AffineBlock) : Monotone (prefixSupport B) := by
  intro n m hnm q hq
  obtain ⟨k, hk, hqk⟩ := (mem_prefixSupport B n q).mp hq
  exact (mem_prefixSupport B m q).mpr ⟨k, lt_of_lt_of_le hk hnm, hqk⟩

theorem prefixFamily_pairwise (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (n : ℕ) :
    Pairwise (fun i j : Fin n =>
      Disjoint (prefixFamily B n i).support (prefixFamily B n j).support) := by
  intro i j hij
  exact hdis (fun h => hij (Fin.ext h))

theorem prefixSupport_disjoint_of_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    {n k : ℕ} (hnk : n ≤ k) : Disjoint (prefixSupport B n) (B k).support := by
  apply Finset.disjoint_left.mpr
  intro q hq hqk
  obtain ⟨j, hj, hqj⟩ := (mem_prefixSupport B n q).mp hq
  exact Finset.disjoint_left.mp (hdis (by omega : j ≠ k)) hqj hqk

theorem fairCoin_prefixEvent_ne_zero (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (n : ℕ) :
    fairCoin (prefixEvent B n) ≠ 0 :=
  fairCoin_familyEvent_ne_zero (prefixFamily B n) (prefixFamily_pairwise B hdis n)

theorem law_isProbabilityMeasure (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (n : ℕ) :
    IsProbabilityMeasure (law B n) :=
  finiteStageLaw_isProbabilityMeasure_of_disjoint (prefixFamily B n)
    (prefixFamily_pairwise B hdis n)

@[simp] theorem law_zero (B : ℕ → AffineBlock) : law B 0 = fairCoin := by
  rw [law_eq_cond, prefixEvent_zero]
  simp

/-- Successor stages add exactly the next affine constraint. -/
theorem law_succ (B : ℕ → AffineBlock) (n : ℕ) :
    law B (n + 1) = cond fairCoin (prefixEvent B n ∩ (B n).event) := by
  rw [law_eq_cond, prefixEvent_succ]

/-- The next stage is obtained by conditioning the present stage on its next block. -/
theorem law_succ_eq_cond (B : ℕ → AffineBlock) (n : ℕ) :
    law B (n + 1) = cond (law B n) (B n).event := by
  rw [law_succ, law_eq_cond,
    cond_cond_eq_cond_inter (measurableSet_prefixEvent B n) (B n).measurableSet_event fairCoin]

/-- A block not yet imposed has its uniform syndrome mass under the current stage. -/
theorem law_next_block_event (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (n : ℕ) :
    law B n (B n).event = (1 / 2 : ℝ≥0∞) ^ (B n).rank := by
  apply finiteStageLaw_event_of_disjoint (prefixFamily B n) (B n)
    (prefixFamily_pairwise B hdis n)
  intro i
  exact hdis (ne_of_lt i.isLt)

/-- Every block already imposed holds with probability one at the current stage. -/
theorem law_block_event (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n k : ℕ) (hk : k < n) : law B n (B k).event = 1 := by
  have hsub : prefixEvent B n ⊆ (B k).event := fun X hX => (mem_prefixEvent B n X).mp hX k hk
  rw [law_eq_cond, cond_apply (measurableSet_prefixEvent B n), Set.inter_eq_left.mpr hsub,
    ENNReal.inv_mul_cancel (fairCoin_prefixEvent_ne_zero B hdis n) (measure_ne_top _ _)]

/-- One stage preserves a transcript whenever the new block's unread columns retain full rank. -/
theorem law_succ_transcript (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (π : ScanRule) (v : List Bool) (hfull : (B n).UnreadFullRank π v) :
    law B (n + 1) (inputEvent π v) = law B n (inputEvent π v) := by
  rw [law_succ]
  exact nextStageLaw_transcript (prefixFamily B n) (B n)
    (prefixFamily_pairwise B hdis n) (fun i => hdis (ne_of_lt i.isLt)) π v hfull

/-- Transcript equality telescopes through any finite interval of blocks that still
have full unread rank at the specified transcript. -/
theorem law_transcript_eq_of_fullRank (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n m : ℕ) (hnm : n ≤ m) (π : ScanRule) (v : List Bool)
    (hfull : ∀ k, n ≤ k → k < m → (B k).UnreadFullRank π v) :
    law B m (inputEvent π v) = law B n (inputEvent π v) := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hnm' : n ≤ m
    · rw [law_succ_transcript B hdis m π v (hfull m hnm' (by omega))]
      exact ih hnm' (fun k hnk hkm => hfull k hnk (by omega))
    · have hn : n = m + 1 := by omega
      subst n
      rfl

/-- A finite-coordinate event independent of the next block has the exact syndrome
factor under the current stage, including when that event has probability zero. -/
theorem law_inter_next_of_disjoint (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (G : Finset ℕ) (A : Set Cantor)
    (hA : DependsOn (fun X : Cantor => X ∈ A) (G : Set ℕ))
    (hnew : Disjoint G (B n).support) :
    law B n (A ∩ (B n).event) = (1 / 2 : ℝ≥0∞) ^ (B n).rank * law B n A := by
  have hdep : DependsOn (fun X : Cantor => X ∈ prefixEvent B n ∩ A)
      ((prefixSupport B n ∪ G : Finset ℕ) : Set ℕ) := by
    intro X Y hxy
    have hP := prefixEvent_dependsOn B n (fun q hq => hxy q (Finset.mem_union_left _ hq))
    have hA' := hA (fun q hq => hxy q (Finset.mem_union_right _ hq))
    change ((X ∈ prefixEvent B n) ∧ X ∈ A) = ((Y ∈ prefixEvent B n) ∧ Y ∈ A)
    exact congrArg₂ And hP hA'
  have hd : Disjoint (prefixSupport B n ∪ G) (B n).support :=
    Finset.disjoint_union_left.mpr ⟨prefixSupport_disjoint_of_le B hdis le_rfl, hnew⟩
  have hind := fairCoin_inter_of_disjoint_support (prefixEvent B n ∩ A) (B n).event
    (prefixSupport B n ∪ G) (B n).support hdep (B n).dependsOn_event hd
  rw [law_eq_cond, cond_apply (measurableSet_prefixEvent B n),
    cond_apply (measurableSet_prefixEvent B n), ← Set.inter_assoc, hind, (B n).fairCoin_event]
  ac_rfl

/-- Adding a block leaves every event on disjoint finite coordinates unchanged. -/
theorem law_succ_apply_eq_of_disjoint (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (G : Finset ℕ) (A : Set Cantor)
    (hA : DependsOn (fun X : Cantor => X ∈ A) (G : Set ℕ))
    (hnew : Disjoint G (B n).support) : law B (n + 1) A = law B n A := by
  rw [law_succ_eq_cond, cond_apply (B n).measurableSet_event, Set.inter_comm,
    law_inter_next_of_disjoint B hdis n G A hA hnew, law_next_block_event B hdis n,
    ← mul_assoc, ENNReal.inv_mul_cancel (pow_ne_zero _ (by norm_num)) (by finiteness), one_mul]

/-- Finite-coordinate probabilities stabilize across every finite interval of new
blocks disjoint from those coordinates.  This is the marginal consistency identity. -/
theorem law_apply_eq_of_disjoint (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    {n m : ℕ} (hnm : n ≤ m) (G : Finset ℕ) (A : Set Cantor)
    (hA : DependsOn (fun X : Cantor => X ∈ A) (G : Set ℕ))
    (hnew : ∀ k, n ≤ k → k < m → Disjoint G (B k).support) :
    law B m A = law B n A := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hnm' : n ≤ m
    · rw [law_succ_apply_eq_of_disjoint B hdis m G A hA (hnew m hnm' (by omega))]
      exact ih hnm' (fun k hnk hkm => hnew k hnk (by omega))
    · have hn : n = m + 1 := by omega
      subst n
      rfl

end Klr.PrefixStage

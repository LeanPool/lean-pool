/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StoppingTranscript

/-!
# Numerical remaining rank and the first rank-drop event

The remaining rank is the dimension of the image of the unread-column map.
It can only decrease as more coordinates are queried.  Its initial value is
the block's row rank, so the first loss of surjectivity is exactly the first
strict numerical rank decrease.

The final event uses the paper's one-based query numbering: a drop at query
`t` compares the ranks after `t` and `t - 1` answers.  Thus a drop after horizon
`N` has a pre-drop transcript of length at least `N`.
-/

@[expose] public section

namespace Klr

open AffineObservation

namespace AffineObservation

/-- Observing more coordinates can only shrink the remaining-column image. -/
theorem unreadMap_range_antitone {ι : Type*} {r : ℕ}
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    {O P : Set ι} [DecidablePred (· ∈ O)] [DecidablePred (· ∈ P)]
    (hOP : O ⊆ P) :
    LinearMap.range (unreadMap D P) ≤ LinearMap.range (unreadMap D O) := by
  rintro y ⟨u, rfl⟩
  refine ⟨unreadPart O (extendUnread P u), ?_⟩
  change D (extendUnread O (unreadPart O (extendUnread P u))) = D (extendUnread P u)
  congr 1
  apply extendUnread_unreadPart_of_observed_zero
  funext i
  simp [observedPart, extendUnread, hOP i.property]

end AffineObservation

namespace ScanRule

/-- Extending a transcript retains every previously queried position. -/
theorem queriedPositions_mono (π : ScanRule) {u v : List Bool} (h : u <+: v) :
    π.queriedPositions u ⊆ π.queriedPositions v := by
  rintro q hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  let j : Fin v.length := ⟨i.val, lt_of_lt_of_le i.isLt h.length_le⟩
  refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
  change π.query (v.take i.val) = π.query (u.take i.val)
  rcases h with ⟨w, rfl⟩
  rw [List.take_append_of_le_length i.isLt.le]

end ScanRule

namespace AffineBlock

/-- The dimension of the image of the block's unread-column map. -/
noncomputable def remainingRank (B : AffineBlock) (π : ScanRule) (v : List Bool) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (unreadMap B.matrix (B.observed π v)))

/-- Full unread row rank is exactly equality with the block's initial row rank. -/
theorem unreadFullRank_iff_remainingRank (B : AffineBlock) (π : ScanRule)
    (v : List Bool) : B.UnreadFullRank π v ↔ B.remainingRank π v = B.rank := by
  change Function.Surjective (unreadMap B.matrix (B.observed π v)) ↔ _
  rw [← LinearMap.range_eq_top]
  constructor
  · intro h
    change Module.finrank (ZMod 2)
      (LinearMap.range (unreadMap B.matrix (B.observed π v))) = B.rank
    rw [h, finrank_top]
    simp
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa [remainingRank] using h

/-- The unread image never has dimension larger than the row space. -/
theorem remainingRank_le (B : AffineBlock) (π : ScanRule) (v : List Bool) :
    B.remainingRank π v ≤ B.rank := by
  simpa [remainingRank] using
    Submodule.finrank_le (LinearMap.range (unreadMap B.matrix (B.observed π v)))

@[simp] theorem remainingRank_nil (B : AffineBlock) (π : ScanRule) :
    B.remainingRank π [] = B.rank :=
  (B.unreadFullRank_iff_remainingRank π []).mp (B.unreadFullRank_nil π)

/-- Remaining rank is antitone in the set of positions already queried. -/
theorem remainingRank_le_of_queriedPositions_subset (B : AffineBlock) (π : ScanRule)
    {u v : List Bool} (h : π.queriedPositions u ⊆ π.queriedPositions v) :
    B.remainingRank π v ≤ B.remainingRank π u := by
  apply Submodule.finrank_mono
  apply unreadMap_range_antitone
  intro i hi
  exact h hi

/-- Remaining rank can only decrease along an extending transcript. -/
theorem remainingRank_antitone_prefix (B : AffineBlock) (π : ScanRule)
    {u v : List Bool} (h : u <+: v) :
    B.remainingRank π v ≤ B.remainingRank π u :=
  B.remainingRank_le_of_queriedPositions_subset π (π.queriedPositions_mono h)

/-- Remaining rank is a nonincreasing sequence along every input. -/
theorem remainingRank_transcript_antitone (B : AffineBlock) (π : ScanRule) (X : Cantor) :
    Antitone (fun n => B.remainingRank π (π.transcript X n)) :=
  fun _ _ h => B.remainingRank_antitone_prefix π (π.transcript_prefix X h)

/-- Before the first strict decrease, the numerical rank is still its initial value. -/
theorem remainingRank_eq_rank_of_no_drop (B : AffineBlock) (π : ScanRule)
    (X : Cantor) (n : ℕ)
    (h : ∀ k < n, ¬B.remainingRank π (π.transcript X (k + 1)) <
      B.remainingRank π (π.transcript X k)) :
    B.remainingRank π (π.transcript X n) = B.rank := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun k hk => h k (by omega))
    have hle := B.remainingRank_transcript_antitone π X (Nat.le_succ n)
    have hge := Nat.le_of_not_gt (h n (Nat.lt_succ_self n))
    exact (le_antisymm hle hge).trans hn

end AffineBlock

namespace StoppingTranscript

open MeasureTheory ProbabilityTheory

/-- The predictable trigger occurs exactly before the first strict numerical rank drop. -/
theorem rankDropTrigger_iff_first_rank_drop (B : AffineBlock) (π : ScanRule)
    (X : Cantor) (n : ℕ) :
    rankDropTrigger B π (π.transcript X n) ↔
      B.remainingRank π (π.transcript X (n + 1)) < B.remainingRank π (π.transcript X n) ∧
        ∀ k < n, ¬B.remainingRank π (π.transcript X (k + 1)) <
          B.remainingRank π (π.transcript X k) := by
  rw [rankDropTrigger_transcript_iff,
    B.unreadFullRank_iff_remainingRank, B.unreadFullRank_iff_remainingRank]
  constructor
  · rintro ⟨hn, hn1⟩
    have hbefore : ∀ k ≤ n, B.remainingRank π (π.transcript X k) = B.rank := by
      intro k hk
      apply le_antisymm (B.remainingRank_le π _)
      rw [← hn]
      exact B.remainingRank_transcript_antitone π X hk
    constructor
    · rw [hn]
      exact lt_of_le_of_ne (B.remainingRank_le π _) hn1
    · intro k hk
      rw [hbefore k hk.le, hbefore (k + 1) (by omega)]
      exact lt_irrefl _
  · rintro ⟨hdrop, hfirst⟩
    have hn := B.remainingRank_eq_rank_of_no_drop π X n hfirst
    refine ⟨hn, ?_⟩
    intro hn1
    rw [hn, hn1] at hdrop
    exact lt_irrefl _ hdrop

/-- The stopping event is exactly the first strict numerical rank decrease after `N`.
The witness `t` is a one-based query number, as in the paper. -/
theorem mem_rankDropTailEvent_iff_remainingRank (B : AffineBlock) (π : ScanRule)
    (N : ℕ) (X : Cantor) :
    X ∈ rankDropTailEvent B π N ↔
      ∃ t, N < t ∧
        B.remainingRank π (π.transcript X t) < B.remainingRank π (π.transcript X (t - 1)) ∧
        ∀ s, 0 < s → s < t →
          ¬B.remainingRank π (π.transcript X s) <
            B.remainingRank π (π.transcript X (s - 1)) := by
  rw [← unionEvent_rankDropTriggerTail, mem_unionEvent_firstTriggerTail_iff]
  constructor
  · rintro ⟨n, hN, htrigger, _⟩
    obtain ⟨hdrop, hfirst⟩ := (rankDropTrigger_iff_first_rank_drop B π X n).mp htrigger
    refine ⟨n + 1, by omega, by simpa using hdrop, ?_⟩
    intro s hs hsn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by omega)
    simpa using hfirst k (by omega)
  · rintro ⟨t, hN, hdrop, hfirst⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
    simp only [Nat.succ_sub_one] at hdrop
    have hfirst' : ∀ k < n, ¬B.remainingRank π (π.transcript X (k + 1)) <
        B.remainingRank π (π.transcript X k) := by
      intro k hk
      simpa using hfirst (k + 1) (by omega) (by omega)
    refine ⟨n, by omega,
      (rankDropTrigger_iff_first_rank_drop B π X n).mpr ⟨hdrop, hfirst'⟩, ?_⟩
    intro k hk htrigger
    exact hfirst' k hk ((rankDropTrigger_iff_first_rank_drop B π X k).mp htrigger).1

/-- The event `N < T < ∞`, where `T` is the first strict numerical rank-drop query. -/
def strictRankDropTailEvent (B : AffineBlock) (π : ScanRule) (N : ℕ) : Set Cantor :=
  {X | ∃ t, N < t ∧
    B.remainingRank π (π.transcript X t) < B.remainingRank π (π.transcript X (t - 1)) ∧
    ∀ s, 0 < s → s < t →
      ¬B.remainingRank π (π.transcript X s) < B.remainingRank π (π.transcript X (s - 1))}

theorem rankDropTailEvent_eq_strictRankDropTailEvent (B : AffineBlock)
    (π : ScanRule) (N : ℕ) :
    rankDropTailEvent B π N = strictRankDropTailEvent B π N := by
  ext X
  exact mem_rankDropTailEvent_iff_remainingRank B π N X

/-- Adding a disjoint full-rank block preserves the tail distribution of the actual
first strict rank decrease, with the paper's one-based query indexing. -/
theorem nextStage_strictRankDropTail {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support) (π : ScanRule) (N : ℕ) :
    (cond fairCoin (AffineBlock.familyEvent old ∩ B.event)) (strictRankDropTailEvent B π N) =
      (AffineBlock.finiteStageLaw old) (strictRankDropTailEvent B π N) := by
  rw [← rankDropTailEvent_eq_strictRankDropTailEvent]
  exact nextStage_rankDropTail old B hold hnew π N

end StoppingTranscript
end Klr

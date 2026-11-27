/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.FutureNoDrop
public import LeanPool.KLRandomness.DropEvents

/-!
# The Section 6 bound for late rank drops

The hypotheses are estimates under the actual finite-stage laws.  The infinite
law is the constructed `BlockProduct.law`.  Horizon avoidance transfers the
partial-rank event, and the first-future-drop identity transfers the remaining
event.  A measurable transcript partition then gives the late-drop bound.

The separate constants below correspond to the paper's `4e_j`, `2e_j`, `e_j`,
and the sum of the later `e_k`.  No candidate-pool or stage-existence premise is
hidden in this measure-theoretic implication.
-/

@[expose] public section

namespace Klr.LateDropBound

open MeasureTheory ProbabilityTheory StoppingTranscript
open scoped ENNReal

/-- A block has some finite rank drop; equivalently its first-drop time is finite. -/
def hasDrop (B : AffineBlock) (π : ScanRule) : Set Cantor :=
  (NoDrop.noDropEvent B π)ᶜ

theorem measurableSet_hasDrop (B : AffineBlock) (π : ScanRule) :
    MeasurableSet (hasDrop B π) := (NoDrop.measurableSet_noDropEvent B π).compl

theorem hasDrop_eq_rankDropTailEvent (B : AffineBlock) (π : ScanRule) :
    hasDrop B π = rankDropTailEvent B π 0 := by
  rw [hasDrop, NoDrop.noDropEvent_eq_compl_rankDropTailEvent, compl_compl]

theorem mem_hasDrop_of_rank_lt (B : AffineBlock) (π : ScanRule) (X : Cantor)
    {m n : ℕ} (h : B.remainingRank π (π.transcript X m) <
      B.remainingRank π (π.transcript X n)) : X ∈ hasDrop B π := by
  intro hno
  rw [(B.unreadFullRank_iff_remainingRank π _).mp (hno m),
    (B.unreadFullRank_iff_remainingRank π _).mp (hno n)] at h
  exact lt_irrefl _ h

/-- A first drop is later than `N` whenever rank is still full at `N` and a drop occurs. -/
theorem mem_rankDropTail_of_full_and_hasDrop (B : AffineBlock) (π : ScanRule)
    (N : ℕ) (X : Cantor) (hfull : B.UnreadFullRank π (π.transcript X N))
    (hdrop : X ∈ hasDrop B π) : X ∈ rankDropTailEvent B π N := by
  rw [hasDrop_eq_rankDropTailEvent] at hdrop
  obtain ⟨n, _, hbefore, hfail⟩ := hdrop
  refine ⟨n, ?_, hbefore, hfail⟩
  by_contra h
  have hn : n + 1 ≤ N := by omega
  exact hfail (NoDrop.survivalEvent_antitone B π hn hfull)

/-- Partial unread row rank at a finite horizon. -/
def partialEvent (B : AffineBlock) (π : ScanRule) (N : ℕ) : Set Cantor :=
  {X | 0 < B.remainingRank π (π.transcript X N) ∧
    B.remainingRank π (π.transcript X N) < B.rank}

theorem measurableSet_partialEvent (B : AffineBlock) (π : ScanRule) (N : ℕ) :
    MeasurableSet (partialEvent B π N) :=
  DropEvents.measurableSet_transcript_pred π N
    (fun v => 0 < B.remainingRank π v ∧ B.remainingRank π v < B.rank)

/-- The fixed-length transcripts satisfying an arbitrary horizon predicate. -/
def horizonWords (N : ℕ) (P : List Bool → Prop) : Set (List Bool) :=
  {v | v.length = N ∧ P v}

theorem horizonWords_prefixFree (N : ℕ) (P : List Bool → Prop) :
    PrefixFree (horizonWords N P) := by
  intro u v hu hv huv
  exact huv.eq_of_length (hu.1.trans hv.1.symm)

theorem horizonEvent_eq_union (π : ScanRule) (N : ℕ) (P : List Bool → Prop) :
    {X : Cantor | P (π.transcript X N)} = unionEvent π (horizonWords N P) := by
  ext X
  constructor
  · intro h
    apply Set.mem_iUnion.mpr
    refine ⟨⟨π.transcript X N, π.length_transcript X N, h⟩, ?_⟩
    change π.transcript X (π.transcript X N).length = π.transcript X N
    rw [π.length_transcript]
  · intro h
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h
    change π.transcript X v.val.length = v.val at hv
    rw [v.property.1] at hv
    change P (π.transcript X N)
    rw [hv]
    exact v.property.2

/-- All horizon events have their actual finite-stage probabilities when the later
blocks retain full rank on every possible transcript through that horizon. -/
theorem law_horizon_event (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (π : ScanRule) (N : ℕ)
    (hfull : ∀ v, v.length = N → ∀ k, n ≤ k → (B k).UnreadFullRank π v)
    (P : List Bool → Prop) :
    BlockProduct.law B hdis {X | P (π.transcript X N)} =
      PrefixStage.law B n {X | P (π.transcript X N)} := by
  rw [horizonEvent_eq_union]
  exact BlockProduct.law_unionEvent_eq_of_fullRank B hdis n π
    (horizonWords_prefixFree N P) (fun v hv => hfull v hv.1)

/-- Rank zero at the horizon rules out every later drop in that block. -/
theorem not_mem_lateEvent_of_rank_zero (B : ℕ → AffineBlock) (π : ScanRule)
    (V : ℕ → ℕ) (j : ℕ) (X : Cantor)
    (hzero : (B j).remainingRank π (π.transcript X (V j)) = 0) :
    X ∉ DropEvents.lateEvent B π V j := by
  rintro ⟨t, ht, hdrop⟩
  have hd := (DropEvents.atTime_iff_rank_drop B π j X t).mp hdrop
  have hm := (B j).remainingRank_transcript_antitone π X ht
  dsimp only at hm
  omega

/-- A late drop is covered by partial rank at the horizon or by the first future-drop
event.  The latter includes the currently imposed block and all subsequent blocks. -/
theorem lateEvent_subset_partial_union_firstDropAfter (B : ℕ → AffineBlock)
    (π : ScanRule) (V : ℕ → ℕ) (j : ℕ)
    (havoid : ∀ v, v.length = V j → ∀ k, j < k → (B k).UnreadFullRank π v) :
    DropEvents.lateEvent B π V j ⊆
      partialEvent (B j) π (V j) ∪ FutureNoDrop.firstDropAfter B j π (V j) := by
  rintro X ⟨t, ht, hdrop⟩
  have hd := (DropEvents.atTime_iff_rank_drop B π j X t).mp hdrop
  have hm := (B j).remainingRank_transcript_antitone π X ht
  dsimp only at hm
  have hpos : 0 < (B j).remainingRank π (π.transcript X (V j)) := by omega
  by_cases hp : (B j).remainingRank π (π.transcript X (V j)) < (B j).rank
  · exact Or.inl ⟨hpos, hp⟩
  · have heq : (B j).remainingRank π (π.transcript X (V j)) = (B j).rank :=
      le_antisymm ((B j).remainingRank_le π _) (Nat.le_of_not_gt hp)
    have hsafe : FutureNoDrop.Safe B j π (π.transcript X (V j)) := by
      intro k hk
      rcases eq_or_lt_of_le hk with rfl | hjk
      · exact ((B j).unreadFullRank_iff_remainingRank π _).mpr heq
      · exact havoid _ (π.length_transcript X _) k hjk
    apply Or.inr
    apply (FutureNoDrop.mem_firstDropAfter_iff B j π (V j) X).mpr
    exact ⟨hsafe, j, le_rfl, t + 1, by omega, by simpa using hd⟩

/-- The first-future-drop event splits according to whether the current block ever drops
and, on its no-drop part, according to the Borel transcript partition `H, Hᶜ`. -/
theorem firstDropAfter_subset (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule)
    (N : ℕ) (H : Set Cantor) :
    FutureNoDrop.firstDropAfter B j π N ⊆
      (rankDropTailEvent (B j) π N ∪
        (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π)) ∪
      ⋃ k : {k : ℕ // j < k}, π.observationMap ⁻¹' Hᶜ ∩ hasDrop (B k.val) π := by
  classical
  intro X hX
  obtain ⟨hN, k, hk, t, ht, hdrop⟩ :=
    (FutureNoDrop.mem_firstDropAfter_iff B j π N X).mp hX
  by_cases hno : X ∈ NoDrop.noDropEvent (B j) π
  · by_cases hH : π.observationMap X ∈ H
    · exact Or.inl (Or.inr ⟨hH, hno⟩)
    · have hkd : X ∈ hasDrop (B k) π := mem_hasDrop_of_rank_lt (B k) π X hdrop
      have hkj : k ≠ j := by
        intro he
        subst k
        exact hkd hno
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨⟨k, by omega⟩, hH, hkd⟩
  · exact Or.inl (Or.inl (mem_rankDropTail_of_full_and_hasDrop (B j) π N X
      (hN j le_rfl) hno))

/-- Adding the current block preserves the `H` part of its no-drop transcript law. -/
theorem stage_H_noDrop (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) {H : Set Cantor} (hH : MeasurableSet H) :
    PrefixStage.law B (j + 1) (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π) =
      PrefixStage.law B j (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π) := by
  rw [PrefixStage.law_succ]
  exact NoDrop.nextStage_noDrop_borel (PrefixStage.prefixFamily B j) (B j)
    (PrefixStage.prefixFamily_pairwise B hdis j)
    (fun k => hdis (ne_of_lt k.isLt)) π hH

/-- The stage estimate for the first future drop, before adding the partial-rank term. -/
theorem stage_firstDropAfter_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) (N : ℕ) (H : Set Cantor) (hH : MeasurableSet H)
    (β γ : ℝ≥0∞) (e : ℕ → ℝ≥0∞)
    (htail : PrefixStage.law B (j + 1) (rankDropTailEvent (B j) π N) ≤ β)
    (hhigh : PrefixStage.law B j
      (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π) ≤ γ)
    (hlater : ∀ k, j < k → PrefixStage.law B (j + 1)
      (π.observationMap ⁻¹' Hᶜ ∩ hasDrop (B k) π) ≤ e k) :
    PrefixStage.law B (j + 1) (FutureNoDrop.firstDropAfter B j π N) ≤
      β + γ + ∑' k : {k : ℕ // j < k}, e k.val := by
  have hhigh' : PrefixStage.law B (j + 1)
      (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π) ≤ γ := by
    rw [stage_H_noDrop B hdis j π hH]
    exact hhigh
  calc
    _ ≤ PrefixStage.law B (j + 1)
        ((rankDropTailEvent (B j) π N ∪
          (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π)) ∪
        ⋃ k : {k : ℕ // j < k}, π.observationMap ⁻¹' Hᶜ ∩ hasDrop (B k.val) π) :=
      measure_mono (firstDropAfter_subset B j π N H)
    _ ≤ PrefixStage.law B (j + 1)
          (rankDropTailEvent (B j) π N ∪
            (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π)) +
        PrefixStage.law B (j + 1)
          (⋃ k : {k : ℕ // j < k}, π.observationMap ⁻¹' Hᶜ ∩ hasDrop (B k.val) π) :=
      measure_union_le _ _
    _ ≤ (PrefixStage.law B (j + 1) (rankDropTailEvent (B j) π N) +
          PrefixStage.law B (j + 1)
            (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π)) +
        ∑' k : {k : ℕ // j < k}, PrefixStage.law B (j + 1)
          (π.observationMap ⁻¹' Hᶜ ∩ hasDrop (B k.val) π) :=
      add_le_add (measure_union_le _ _) (measure_iUnion_le _)
    _ ≤ _ := add_le_add (add_le_add htail hhigh')
      (tsum_le_tsum (fun k => hlater k.val k.property))

/-- The Section 6 late-drop estimate from genuine finite-stage hypotheses.
With `α = 4e_j`, `β = 2e_j`, and `γ = e_j`, the right side is `7e_j + ∑_{k>j} e_k`. -/
theorem law_lateEvent_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (V : ℕ → ℕ) (j : ℕ) (H : Set Cantor) (hH : MeasurableSet H)
    (α β γ : ℝ≥0∞) (e : ℕ → ℝ≥0∞)
    (havoid : ∀ v, v.length = V j → ∀ k, j < k → (B k).UnreadFullRank π v)
    (hpartial : PrefixStage.law B (j + 1) (partialEvent (B j) π (V j)) ≤ α)
    (htail : PrefixStage.law B (j + 1) (rankDropTailEvent (B j) π (V j)) ≤ β)
    (hhigh : PrefixStage.law B j
      (π.observationMap ⁻¹' H ∩ NoDrop.noDropEvent (B j) π) ≤ γ)
    (hlater : ∀ k, j < k → PrefixStage.law B (j + 1)
      (π.observationMap ⁻¹' Hᶜ ∩ hasDrop (B k) π) ≤ e k) :
    BlockProduct.law B hdis (DropEvents.lateEvent B π V j) ≤
      α + β + γ + ∑' k : {k : ℕ // j < k}, e k.val := by
  have hp : BlockProduct.law B hdis (partialEvent (B j) π (V j)) =
      PrefixStage.law B (j + 1) (partialEvent (B j) π (V j)) := by
    exact law_horizon_event B hdis (j + 1) π (V j)
      (fun v hv k hk => havoid v hv k (by omega))
      (fun v => 0 < (B j).remainingRank π v ∧ (B j).remainingRank π v < (B j).rank)
  calc
    _ ≤ BlockProduct.law B hdis
        (partialEvent (B j) π (V j) ∪ FutureNoDrop.firstDropAfter B j π (V j)) :=
      measure_mono (lateEvent_subset_partial_union_firstDropAfter B π V j havoid)
    _ ≤ BlockProduct.law B hdis (partialEvent (B j) π (V j)) +
        BlockProduct.law B hdis (FutureNoDrop.firstDropAfter B j π (V j)) :=
      measure_union_le _ _
    _ = PrefixStage.law B (j + 1) (partialEvent (B j) π (V j)) +
        PrefixStage.law B (j + 1) (FutureNoDrop.firstDropAfter B j π (V j)) := by
      rw [hp, FutureNoDrop.law_firstDropAfter_of_le B hdis j (j + 1) (Nat.le_succ j)]
    _ ≤ α + (β + γ + ∑' k : {k : ℕ // j < k}, e k.val) :=
      add_le_add hpartial (stage_firstDropAfter_le B hdis j π (V j) H hH β γ e
        htail hhigh hlater)
    _ = _ := by ac_rfl

end Klr.LateDropBound

/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.LateDropBound
public import LeanPool.KLRandomness.PoolCoverage
public import Mathlib.Order.OrderIsoNat

/-!
# The eventual rank events of an actual affine block

Remaining rank is a nonincreasing natural number along every input, hence
stabilizes. The limiting partial-rank event is measurable and is contained
in the event of a rank drop and in the event that some support coordinate
is never queried. Splitting these two inclusions along an arbitrary answer
partition gives the stage construction's high-miss / low-drop bound.

All rank events below are events in input space. The pool missed count and
the partition are evaluated on the scan's actual infinite observation map.
-/

@[expose] public section

namespace Klr.StageRankLimit

open MeasureTheory Filter PoolQuery
open scoped Topology

/-- Remaining rank stabilizes on every input. No uniform stopping time or
computable modulus is asserted. -/
theorem remainingRank_stabilizes (B : AffineBlock) (π : ScanRule) (X : Cantor) :
    ∃ N, ∀ n, N ≤ n →
      B.remainingRank π (π.transcript X n) = B.remainingRank π (π.transcript X N) := by
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition
    (B.remainingRank_transcript_antitone π X)
  exact ⟨N, fun n hn => (hN n hn).symm⟩

/-- Inputs whose eventual remaining rank is positive but below the initial rank. -/
def eventualPartialEvent (B : AffineBlock) (π : ScanRule) : Set Cantor :=
  {X | ∀ᶠ n in atTop, X ∈ LateDropBound.partialEvent B π n}

theorem measurableSet_eventualPartialEvent (B : AffineBlock) (π : ScanRule) :
    MeasurableSet (eventualPartialEvent B π) := by
  have he : eventualPartialEvent B π =
      ⋃ N : ℕ, ⋂ n : {n : ℕ // N ≤ n}, LateDropBound.partialEvent B π n.val := by
    ext X
    simp only [eventualPartialEvent, Set.mem_ofPred_eq, eventually_atTop,
      Set.mem_iUnion, Set.mem_iInter]
    exact ⟨fun ⟨N, hN⟩ => ⟨N, fun n => hN n.val n.property⟩,
      fun ⟨N, hN⟩ => ⟨N, fun n hn => hN ⟨n, hn⟩⟩⟩
  rw [he]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    LateDropBound.measurableSet_partialEvent B π n.val

/-- Membership in finite partial-rank events eventually agrees with the
limiting event on each individual input. -/
theorem eventually_partialEvent_iff (B : AffineBlock) (π : ScanRule) (X : Cantor) :
    ∀ᶠ n in atTop,
      X ∈ LateDropBound.partialEvent B π n ↔ X ∈ eventualPartialEvent B π := by
  obtain ⟨N, hN⟩ := remainingRank_stabilizes B π X
  have hsame (n : ℕ) (hn : N ≤ n) :
      X ∈ LateDropBound.partialEvent B π n ↔ X ∈ LateDropBound.partialEvent B π N := by
    simp only [LateDropBound.partialEvent, Set.mem_ofPred_eq, hN n hn]
  have hlim : X ∈ eventualPartialEvent B π ↔ X ∈ LateDropBound.partialEvent B π N := by
    constructor
    · intro h
      obtain ⟨n, hn, hp⟩ := ((eventually_ge_atTop N).and h).exists
      exact (hsame n hn).mp hp
    · intro h
      exact (eventually_ge_atTop N).mono fun n hn => (hsame n hn).mpr h
  exact (eventually_ge_atTop N).mono fun n hn => (hsame n hn).trans hlim.symm

/-- Having read every support coordinate forces the remaining rank to zero. -/
theorem remainingRank_eq_zero_of_all_observed (B : AffineBlock) (π : ScanRule)
    (v : List Bool) (hobs : ∀ p : B.support, p ∈ B.observed π v) :
    B.remainingRank π v = 0 := by
  classical
  let : IsEmpty {p : B.support // p ∉ B.observed π v} :=
    ⟨fun p => p.property (hobs p.val)⟩
  have hmap : AffineObservation.unreadMap B.matrix (B.observed π v) = 0 := by
    apply LinearMap.ext
    intro u
    rw [Subsingleton.elim u 0, map_zero, LinearMap.zero_apply]
  simp [AffineBlock.remainingRank, hmap]

/-- If every support coordinate is eventually read, a finite input-dependent
horizon has zero remaining rank, and it stays zero thereafter. -/
theorem eventually_remainingRank_zero_of_reads (B : AffineBlock) (π : ScanRule)
    (X : Cantor) (hall : ∀ a ∈ B.support, Reads π a (π.observationMap X)) :
    ∀ᶠ n in atTop, B.remainingRank π (π.transcript X n) = 0 := by
  classical
  choose t ht using (fun p : B.support => hall p.val p.property)
  let N := Finset.univ.sup fun p : B.support => t p + 1
  have hobs : ∀ p : B.support, p ∈ B.observed π (π.transcript X N) := by
    intro p
    have htN : t p < N := lt_of_lt_of_le (Nat.lt_succ_self _)
      (Finset.le_sup (f := fun p : B.support => t p + 1) (Finset.mem_univ p))
    change p.val ∈ π.queriedPositions (π.transcript X N)
    unfold ScanRule.queriedPositions
    apply Finset.mem_image.mpr
    refine ⟨⟨t p, by simpa using htN⟩, Finset.mem_univ _, ?_⟩
    simpa only [PoolQuery.queryAt, π.inputPrefix_observationMap,
      π.transcript_take X htN.le] using ht p
  have hzero := remainingRank_eq_zero_of_all_observed B π (π.transcript X N) hobs
  filter_upwards [eventually_ge_atTop N] with n hn
  have hle := B.remainingRank_transcript_antitone π X hn
  exact Nat.eq_zero_of_le_zero (hzero ▸ hle)

/-- Positive limiting rank requires that some coordinate of any containing
pool is never queried. The pool event is pulled back from answer space. -/
theorem eventualPartialEvent_subset_missed (B : AffineBlock) (π : ScanRule)
    (G : Finset ℕ) (hBG : B.support ⊆ G) :
    eventualPartialEvent B π ⊆
      {X | 0 < missedCount π G (π.observationMap X)} := by
  intro X hX
  by_contra hmiss
  have hall := (missedCount_eq_zero_iff π G (π.observationMap X)).mp
    (Nat.eq_zero_of_not_pos hmiss)
  have hz := eventually_remainingRank_zero_of_reads B π X (fun a ha => hall a (hBG ha))
  obtain ⟨n, hpartial, hzero⟩ := (hX.and hz).exists
  exact (Nat.ne_of_gt hpartial.1) hzero

/-- Loss of full rank by a fixed finite horizon; this is the event `T ≤ n`
for the one-based first-drop query number. -/
def droppedBy (B : AffineBlock) (π : ScanRule) (n : ℕ) : Set Cantor :=
  (NoDrop.survivalEvent B π n)ᶜ

theorem measurableSet_droppedBy (B : AffineBlock) (π : ScanRule) (n : ℕ) :
    MeasurableSet (droppedBy B π n) :=
  (NoDrop.measurableSet_survivalEvent B π n).compl

theorem droppedBy_mono (B : AffineBlock) (π : ScanRule) : Monotone (droppedBy B π) :=
  fun _ _ h => Set.compl_subset_compl.mpr (NoDrop.survivalEvent_antitone B π h)

theorem mem_droppedBy_iff (B : AffineBlock) (π : ScanRule) (n : ℕ) (X : Cantor) :
    X ∈ droppedBy B π n ↔ B.remainingRank π (π.transcript X n) < B.rank := by
  change ¬B.UnreadFullRank π (π.transcript X n) ↔ _
  rw [B.unreadFullRank_iff_remainingRank]
  have hle := B.remainingRank_le π (π.transcript X n)
  omega

theorem iUnion_droppedBy (B : AffineBlock) (π : ScanRule) :
    (⋃ n, droppedBy B π n) = LateDropBound.hasDrop B π := by
  ext X
  simp only [droppedBy, Set.mem_iUnion, Set.mem_compl_iff, NoDrop.survivalEvent,
    Set.mem_ofPred_eq, LateDropBound.hasDrop, NoDrop.noDropEvent, not_forall]

theorem droppedBy_subset_hasDrop (B : AffineBlock) (π : ScanRule) (n : ℕ) :
    droppedBy B π n ⊆ LateDropBound.hasDrop B π := by
  rw [← iUnion_droppedBy]
  exact Set.subset_iUnion _ n

/-- The first-drop tail is exactly the part of the eventual-drop event not
yet seen by the horizon. This retains the paper's one-based query indexing. -/
theorem rankDropTailEvent_eq_sdiff (B : AffineBlock) (π : ScanRule) (N : ℕ) :
    StoppingTranscript.rankDropTailEvent B π N =
      LateDropBound.hasDrop B π \ droppedBy B π N := by
  classical
  ext X
  constructor
  · rintro ⟨n, hN, hfull, hfail⟩
    refine ⟨fun hno => hfail (hno (n + 1)), ?_⟩
    simpa only [droppedBy, Set.mem_compl_iff, not_not, NoDrop.survivalEvent,
      Set.mem_ofPred_eq] using hfull N hN
  · rintro ⟨hdrop, hfull⟩
    apply LateDropBound.mem_rankDropTail_of_full_and_hasDrop B π N X _ hdrop
    simpa only [droppedBy, Set.mem_compl_iff, not_not, NoDrop.survivalEvent,
      Set.mem_ofPred_eq] using hfull

theorem eventualPartialEvent_subset_hasDrop (B : AffineBlock) (π : ScanRule) :
    eventualPartialEvent B π ⊆ LateDropBound.hasDrop B π := by
  intro X hX
  obtain ⟨n, hn⟩ := hX.exists
  exact droppedBy_subset_hasDrop B π n ((mem_droppedBy_iff B π n X).mpr hn.2)

/-- The limiting partial-rank event is covered by the high-part pool-miss
event and the low-part rank-drop event used in the simultaneous score. -/
theorem eventualPartialEvent_subset_highMiss_union_lowDrop
    (B : AffineBlock) (π : ScanRule) (G : Finset ℕ) (hBG : B.support ⊆ G)
    (H : Set Cantor) :
    eventualPartialEvent B π ⊆
      (π.observationMap ⁻¹' H ∩ {X | 0 < missedCount π G (π.observationMap X)}) ∪
      (π.observationMap ⁻¹' Hᶜ ∩ LateDropBound.hasDrop B π) := by
  intro X hX
  by_cases hH : π.observationMap X ∈ H
  · exact Or.inl ⟨hH, eventualPartialEvent_subset_missed B π G hBG hX⟩
  · exact Or.inr ⟨hH, eventualPartialEvent_subset_hasDrop B π hX⟩

end Klr.StageRankLimit

/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineAnswer
public import Mathlib.Data.List.OfFn

/-!
# A finite avoidance set for every branch up to a query horizon

The first `N` queries are chosen from transcripts of lengths strictly less than
`N`.  We enumerate those transcripts explicitly as the finite type
`Σ t : Fin N, (Fin t.val → Bool)` and apply the scan rule to each word.
Consequently a block outside this finite set has no observed coordinates on
any transcript of length at most `N`, and retains full unread rank there.

Finite unions handle finitely many scan rules with individual horizons.  The
corresponding numerical bounds allow later supports to be chosen above every
position that must be avoided.
-/

@[expose] public section

namespace Klr.HorizonAvoidance

open AffineObservation

/-- All positions a scan can query among its first `N` queries, over every branch. -/
def queryPositions (π : ScanRule) (N : ℕ) : Finset ℕ :=
  Finset.univ.image (fun p : Σ t : Fin N, (Fin t.val → Bool) => π.query (List.ofFn p.2))

/-- The explicit enumeration contains exactly the queries from all shorter transcripts. -/
theorem mem_queryPositions (π : ScanRule) (N q : ℕ) :
    q ∈ queryPositions π N ↔ ∃ v : List Bool, v.length < N ∧ π.query v = q := by
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
    exact ⟨List.ofFn p.2, by rw [List.length_ofFn]; exact p.1.isLt, hp⟩
  · rintro ⟨v, hv, rfl⟩
    refine Finset.mem_image.mpr ⟨⟨⟨v.length, hv⟩, v.get⟩, Finset.mem_univ _, ?_⟩
    simp [List.ofFn_get]

@[simp] theorem queryPositions_zero (π : ScanRule) : queryPositions π 0 = ∅ := by
  ext q
  simp [mem_queryPositions]

theorem query_mem_queryPositions (π : ScanRule) (N : ℕ) (v : List Bool)
    (hv : v.length < N) : π.query v ∈ queryPositions π N :=
  (mem_queryPositions π N _).mpr ⟨v, hv, rfl⟩

theorem queryPositions_mono (π : ScanRule) : Monotone (queryPositions π) := by
  intro N M hNM q hq
  obtain ⟨v, hv, hvq⟩ := (mem_queryPositions π N q).mp hq
  exact (mem_queryPositions π M q).mpr ⟨v, lt_of_lt_of_le hv hNM, hvq⟩

/-- Every position read along a transcript of length at most `N` is in the avoidance set. -/
theorem queriedPositions_subset (π : ScanRule) (N : ℕ) {v : List Bool}
    (hv : v.length ≤ N) : π.queriedPositions v ⊆ queryPositions π N := by
  intro q hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  exact query_mem_queryPositions π N (v.take i.val)
    (lt_of_le_of_lt (List.length_take_le _ _) (lt_of_lt_of_le i.isLt hv))

/-- An explicit strict upper bound for every coordinate queried before horizon `N`. -/
def queryBound (π : ScanRule) (N : ℕ) : ℕ := (queryPositions π N).sup id + 1

theorem lt_queryBound_of_mem (π : ScanRule) (N : ℕ) {q : ℕ}
    (hq : q ∈ queryPositions π N) : q < queryBound π N :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hq)

theorem query_lt_queryBound (π : ScanRule) (N : ℕ) (v : List Bool) (hv : v.length < N) :
    π.query v < queryBound π N :=
  lt_queryBound_of_mem π N (query_mem_queryPositions π N v hv)

/-- Any finite support above the bound is disjoint from the all-branch avoidance set. -/
theorem disjoint_of_queryBound_le (π : ScanRule) (N : ℕ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, queryBound π N ≤ q) : Disjoint (queryPositions π N) S := by
  apply Finset.disjoint_left.mpr
  intro q hq hqS
  exact (not_lt_of_ge (hS q hqS)) (lt_queryBound_of_mem π N hq)

/-- A block with no queried coordinate retains its full initial row rank. -/
theorem unreadFullRank_of_disjoint_queriedPositions (B : AffineBlock) (π : ScanRule)
    (v : List Bool) (hdis : Disjoint (π.queriedPositions v) B.support) :
    B.UnreadFullRank π v := by
  intro y
  obtain ⟨x, hx⟩ := B.fullRank y
  refine ⟨fun i => x i.val, ?_⟩
  change B.matrix (extendUnread (B.observed π v) (fun i => x i.val)) = y
  have he : extendUnread (B.observed π v) (fun i => x i.val) = x := by
    funext i
    have hi : i ∉ B.observed π v := fun h => Finset.disjoint_left.mp hdis h i.property
    simp [extendUnread, hi]
  rw [he, hx]

/-- Avoiding the explicit finite set preserves full unread rank on every branch
through the horizon, including the transcript after exactly `N` answers. -/
theorem unreadFullRank_of_disjoint (B : AffineBlock) (π : ScanRule) (N : ℕ)
    (hdis : Disjoint (queryPositions π N) B.support)
    (v : List Bool) (hv : v.length ≤ N) : B.UnreadFullRank π v :=
  unreadFullRank_of_disjoint_queriedPositions B π v
    (hdis.mono_left (queriedPositions_subset π N hv))

theorem unreadFullRank_of_queryBound_le (B : AffineBlock) (π : ScanRule) (N : ℕ)
    (hB : ∀ q ∈ B.support, queryBound π N ≤ q)
    (v : List Bool) (hv : v.length ≤ N) : B.UnreadFullRank π v :=
  unreadFullRank_of_disjoint B π N (disjoint_of_queryBound_le π N B.support hB) v hv

/-- A finite collection of scans may have different finite horizons. -/
def familyPositions {ι : Type*} [Fintype ι] (π : ι → ScanRule) (N : ι → ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => queryPositions (π i) (N i))

theorem queryPositions_subset_familyPositions {ι : Type*} [Fintype ι]
    (π : ι → ScanRule) (N : ι → ℕ) (i : ι) :
    queryPositions (π i) (N i) ⊆ familyPositions π N := by
  intro q hq
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hq⟩

theorem queriedPositions_subset_familyPositions {ι : Type*} [Fintype ι]
    (π : ι → ScanRule) (N : ι → ℕ) (i : ι) {v : List Bool} (hv : v.length ≤ N i) :
    (π i).queriedPositions v ⊆ familyPositions π N :=
  (queriedPositions_subset (π i) (N i) hv).trans (queryPositions_subset_familyPositions π N i)

/-- One finite bound works simultaneously for every scan in the finite family. -/
def familyBound {ι : Type*} [Fintype ι] (π : ι → ScanRule) (N : ι → ℕ) : ℕ :=
  (familyPositions π N).sup id + 1

theorem lt_familyBound_of_mem {ι : Type*} [Fintype ι]
    (π : ι → ScanRule) (N : ι → ℕ) {q : ℕ} (hq : q ∈ familyPositions π N) :
    q < familyBound π N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hq)

theorem query_lt_familyBound {ι : Type*} [Fintype ι]
    (π : ι → ScanRule) (N : ι → ℕ) (i : ι) (v : List Bool) (hv : v.length < N i) :
    (π i).query v < familyBound π N :=
  lt_familyBound_of_mem π N
    (queryPositions_subset_familyPositions π N i (query_mem_queryPositions (π i) (N i) v hv))

theorem disjoint_of_familyBound_le {ι : Type*} [Fintype ι]
    (π : ι → ScanRule) (N : ι → ℕ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, familyBound π N ≤ q) : Disjoint (familyPositions π N) S := by
  apply Finset.disjoint_left.mpr
  intro q hq hqS
  exact (not_lt_of_ge (hS q hqS)) (lt_familyBound_of_mem π N hq)

/-- Avoiding the finite union guarantees full unread rank for every scan through
its assigned horizon, on every possible transcript. -/
theorem family_unreadFullRank_of_disjoint {ι : Type*} [Fintype ι]
    (B : AffineBlock) (π : ι → ScanRule) (N : ι → ℕ)
    (hdis : Disjoint (familyPositions π N) B.support)
    (i : ι) (v : List Bool) (hv : v.length ≤ N i) : B.UnreadFullRank (π i) v :=
  unreadFullRank_of_disjoint_queriedPositions B (π i) v
    (hdis.mono_left (queriedPositions_subset_familyPositions π N i hv))

theorem family_unreadFullRank_of_bound_le {ι : Type*} [Fintype ι]
    (B : AffineBlock) (π : ι → ScanRule) (N : ι → ℕ)
    (hB : ∀ q ∈ B.support, familyBound π N ≤ q)
    (i : ι) (v : List Bool) (hv : v.length ≤ N i) : B.UnreadFullRank (π i) v :=
  family_unreadFullRank_of_disjoint B π N (disjoint_of_familyBound_le π N B.support hB) i v hv

end Klr.HorizonAvoidance

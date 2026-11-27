/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageCandidate
public import LeanPool.KLRandomness.PoolCoverage
public import LeanPool.KLRandomness.PoolAdviceMeasure

/-!
# Actual unread coordinates and sparse-candidate rank

The unread mask is formed from the complete prescribed answer sequence.
If the executable rank test accepts that mask, every finite answer prefix
retains full unread rank. Conversely, a positive-rank block cannot retain
full unread rank after all of its pool has been queried.
-/

@[expose] public section

noncomputable section

namespace Klr.StageRank

open SparseListSearch SparseListWeights SparseSearch SparseListCode
open StageCandidate RandomMatrix AffineObservation PoolQuery
open scoped BigOperators

variable {M m r : ℕ}

theorem extendUnread_apply_of_mem {ι : Type*} (O : Set ι) [DecidablePred (· ∈ O)]
    (x : {i // i ∉ O} → ZMod 2) (p : ι) (hp : p ∈ O) :
    extendUnread O x p = 0 := by
  change (if h : p ∈ O then 0 else x ⟨p, h⟩) = 0
  exact dite_eq_left hp

/-- Extending a single unread coordinate gives the corresponding ambient singleton. -/
theorem unreadMap_single {ι : Type*} [DecidableEq ι]
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (p : ι) (hp : p ∉ O) :
    unreadMap D O (Pi.single (⟨p, hp⟩ : {i // i ∉ O}) 1) = D (Pi.single p 1) := by
  apply congrArg D
  ext i
  by_cases hi : i = p
  · subst i
    simp [extendUnread, hp]
  · by_cases hO : i ∈ O
    · simp [extendUnread, hO, hi]
    · have hs : (⟨i, hO⟩ : {i // i ∉ O}) ≠ ⟨p, hp⟩ :=
        fun h => hi (congrArg Subtype.val h)
      simp [extendUnread, hO, hi, hs]

/-- Full row rank on any unqueried mask guarantees full unread rank of the
actual affine block. Columns outside the candidate support are genuinely zero. -/
theorem unreadFullRank_of_maskedFullRank
    (e : Fin M → ℕ) (he : Function.Injective e) (a : Entry)
    (ha : GoodEntry M m r a) (y : Fin r → ZMod 2)
    (π : ScanRule) (v : List Bool) (d : List Bool)
    (hd : maskedFullRank a.2 d = true)
    (hunread : ∀ j : Fin M, d.getD j.val false = true →
      e j ∉ π.queriedPositions v) :
    (block e he a ha y).UnreadFullRank π v := by
  classical
  let B := block e he a ha y
  let U := unreadMap B.matrix (B.observed π v)
  have hcol : ∀ j : maskSet M d, columns a M r j.val ∈ LinearMap.range U := by
    intro j
    by_cases hj : j.val ∈ support M a
    · let p : B.support := positionEquiv e he a ⟨j.val, hj⟩
      have hp : p ∉ B.observed π v :=
        hunread j.val ((mem_maskSet M d j.val).mp j.property)
      refine ⟨Pi.single (⟨p, hp⟩ : {p : B.support // p ∉ B.observed π v}) 1, ?_⟩
      change unreadMap B.matrix (B.observed π v) _ = _
      exact (unreadMap_single B.matrix (B.observed π v) p hp).trans
        (block_matrix_single e he a ha y ⟨j.val, hj⟩)
    · rw [columns_zero_off_support ha hj]
      exact (LinearMap.range U).zero_mem
  intro z
  obtain ⟨x, hx⟩ := masked_columns_surjective ha d hd z
  have hz : z ∈ LinearMap.range U := by
    rw [← hx]
    change (∑ j : maskSet M d, x j • columns a M r j.val) ∈ LinearMap.range U
    exact (LinearMap.range U).sum_mem fun j _ =>
      (LinearMap.range U).smul_mem (x j) (hcol j)
  exact hz

/-- The finite unread pool mask after one specified answer transcript. -/
def unreadPool (e : Fin M → ℕ) (π : ScanRule) (v : List Bool) : Finset (Fin M) :=
  Finset.univ.filter fun j => e j ∉ π.queriedPositions v

@[simp] theorem mem_unreadPool (e : Fin M → ℕ) (π : ScanRule) (v : List Bool)
    (j : Fin M) : j ∈ unreadPool e π v ↔ e j ∉ π.queriedPositions v := by
  simp [unreadPool]

/-- The executable rank test on the exact finite unread-pool mask agrees
in both directions with the affine block's unread-rank predicate. -/
theorem unreadFullRank_iff_maskedFullRank
    (e : Fin M → ℕ) (he : Function.Injective e) (a : Entry)
    (ha : GoodEntry M m r a) (y : Fin r → ZMod 2)
    (π : ScanRule) (v : List Bool) :
    (block e he a ha y).UnreadFullRank π v ↔
      maskedFullRank a.2 (mask (unreadPool e π v)) = true := by
  classical
  constructor
  · intro hfull
    by_contra hbad
    have hn : ¬ Function.Surjective
        (restrictedMap (columns a M r) (maskSet M (mask (unreadPool e π v)))
          (K := ZMod 2)) := by
      exact fun h => hbad ((maskedFullRank_iff_columns_surjective ha _).mpr h)
    obtain ⟨φ, hφ, hzero⟩ := (restricted_not_surjective_iff _ _).mp hn
    apply hφ
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := hfull z
    change φ (∑ j : support M a,
      (extendUnread ((block e he a ha y).observed π v) x)
        (positionEquiv e he a j) • columns a M r j.val) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul]
    by_cases hj : e j.val ∈ π.queriedPositions v
    · have ho : positionEquiv e he a j ∈ (block e he a ha y).observed π v := hj
      rw [extendUnread_apply_of_mem _ x _ ho, zero_smul]
    · have hmem : j.val ∈ maskSet M (mask (unreadPool e π v)) := by
        simpa using hj
      have hz : φ (columns a M r j.val) = 0 := congrFun hzero ⟨j.val, hmem⟩
      rw [hz, smul_zero]
  · intro h
    apply unreadFullRank_of_maskedFullRank e he a ha y π v _ h
    intro j hj
    rw [getD_mask, decide_eq_true_eq] at hj
    exact (mem_unreadPool e π v j).mp hj

/-- Pool indices never queried on the infinite prescribed answer sequence. -/
def neverRead (e : Fin M → ℕ) (π : ScanRule) (Z : Cantor) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun j => ¬ Reads π (e j) Z

@[simp] theorem mem_neverRead (e : Fin M → ℕ) (π : ScanRule) (Z : Cantor)
    (j : Fin M) : j ∈ neverRead e π Z ↔ ¬ Reads π (e j) Z := by
  classical
  simp [neverRead]

theorem reads_of_mem_queriedPositions (π : ScanRule) (Z : Cantor) (n a : ℕ)
    (h : a ∈ π.queriedPositions (ScanRule.inputPrefix Z n)) : Reads π a Z := by
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
  exact ⟨j.val, by
    simpa only [queryAt, PoolAdvice.inputPrefix_take Z
      (by simpa using j.isLt.le)] using hj⟩

/-- A successful finite rank check on the actual never-read mask prevents
rank drops along every finite prefix of these answers. -/
theorem noDropTranscripts_of_maskedFullRank
    (e : Fin M → ℕ) (he : Function.Injective e) (a : Entry)
    (ha : GoodEntry M m r a) (y : Fin r → ZMod 2)
    (π : ScanRule) (Z : Cantor)
    (hd : maskedFullRank a.2 (mask (neverRead e π Z)) = true) :
    Z ∈ NoDrop.noDropTranscripts (block e he a ha y) π := by
  intro n
  apply unreadFullRank_of_maskedFullRank e he a ha y π _ _ hd
  intro j hj hread
  have hm : j ∈ neverRead e π Z := by
    rw [getD_mask, decide_eq_true_eq] at hj
    exact hj
  exact (mem_neverRead e π Z j).mp hm
    (reads_of_mem_queriedPositions π Z n (e j) hread)

/-- The cardinality of the actual never-read mask is the pool missed count. -/
theorem card_neverRead (e : Fin M → ℕ) (he : Function.Injective e)
    (π : ScanRule) (Z : Cantor) :
    (neverRead e π Z).card = missedCount π (Finset.univ.image e) Z := by
  classical
  have hset : (neverRead e π Z).image e =
      (Finset.univ.image e).filter (fun a => ¬ Reads π a Z) := by
    ext a
    simp only [Finset.mem_image, mem_neverRead, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, hj⟩
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, hj, rfl⟩
  rw [← Finset.card_image_of_injective (neverRead e π Z) he, hset]
  rfl

/-- Once every coordinate of a finite block has been read, the unread rank
cannot remain positive. The horizon may depend on the complete answer sequence. -/
theorem noDropTranscripts_subset_missed (B : AffineBlock) (π : ScanRule)
    (G : Finset ℕ) (hBG : B.support ⊆ G) (hr : 0 < B.rank) :
    NoDrop.noDropTranscripts B π ⊆ {Z | 0 < missedCount π G Z} := by
  classical
  intro Z hZ
  by_contra hmiss
  have hzero : missedCount π G Z = 0 := Nat.eq_zero_of_not_pos hmiss
  have hall := (missedCount_eq_zero_iff π G Z).mp hzero
  choose t ht using (fun p : B.support => hall p.val (hBG p.property))
  let N := Finset.univ.sup fun p : B.support => t p + 1
  have hobs : ∀ p : B.support, p ∈ B.observed π (ScanRule.inputPrefix Z N) := by
    intro p
    have htN : t p < N := lt_of_lt_of_le (Nat.lt_succ_self _)
      (Finset.le_sup (f := fun p : B.support => t p + 1) (Finset.mem_univ p))
    change p.val ∈ π.queriedPositions (ScanRule.inputPrefix Z N)
    apply Finset.mem_image.mpr
    refine ⟨⟨t p, by simpa using htN⟩, Finset.mem_univ _, ?_⟩
    simpa only [queryAt, PoolAdvice.inputPrefix_take Z htN.le] using ht p
  let : IsEmpty {p : B.support // p ∉ B.observed π (ScanRule.inputPrefix Z N)} :=
    ⟨fun p => p.property (hobs p.val)⟩
  have hbound := unread_rank_le B.matrix (B.observed π (ScanRule.inputPrefix Z N)) (hZ N)
  have hc : Fintype.card {p : B.support // p ∉ B.observed π (ScanRule.inputPrefix Z N)} = 0 :=
    Fintype.card_eq_zero
  rw [hc] at hbound
  exact (Nat.not_lt_of_ge hbound) hr

/-- The high-part no-drop mass is bounded by the actual high-part pool-miss mass. -/
theorem measure_high_noDrop_le (B : AffineBlock) (π : ScanRule)
    (G : Finset ℕ) (hBG : B.support ⊆ G) (hr : 0 < B.rank)
    (H : Set Cantor) (μ : MeasureTheory.Measure Cantor) :
    μ (H ∩ NoDrop.noDropTranscripts B π) ≤
      μ {Z | Z ∈ H ∧ 0 < missedCount π G Z} :=
  MeasureTheory.measure_mono fun _Z hZ =>
    ⟨hZ.1, noDropTranscripts_subset_missed B π G hBG hr hZ.2⟩

/-- Entries are indexed by their list positions, preserving multiplicities. -/
def listBlock {J : ℕ} {τ θ : ℚ} {L : CodeList}
    (hL : Good M m r J τ θ L) (e : Fin M → ℕ) (he : Function.Injective e)
    (y : Fin L.length → Fin r → ZMod 2) (j : Fin L.length) : AffineBlock :=
  block e he (L.get j) (hL.2.1 _ (List.get_mem _ _)) (y j)

open Classical in
/-- For every complete answer sequence with a dense never-read pool mask,
only the verifier's allowed fraction of candidates can undergo a rank drop. -/
theorem card_hasDrop_le {J : ℕ} {τ θ : ℚ} {L : CodeList}
    (hL : Good M m r J τ θ L) (e : Fin M → ℕ) (he : Function.Injective e)
    (y : Fin L.length → Fin r → ZMod 2) (π : ScanRule) (Z : Cantor)
    (hdense : τ * (M : ℚ) ≤ ((neverRead e π Z).card : ℚ)) :
    ((Finset.univ.filter fun j : Fin L.length =>
      Z ∉ NoDrop.noDropTranscripts (listBlock hL e he y j) π).card : ℚ) ≤ θ * J := by
  classical
  let d := mask (neverRead e π Z)
  have hbound := hL.2.2.2 d (length_mask _) (by simpa [d] using hdense)
  apply le_trans _ hbound
  apply Nat.cast_le.mpr
  rw [countP_eq_card_filter_get]
  apply Finset.card_le_card
  intro j hj
  have hbad := (Finset.mem_filter.mp hj).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ j, ?_⟩
  have hnot : maskedFullRank (L.get j).2 d ≠ true := by
    intro hgood
    exact hbad (noDropTranscripts_of_maskedFullRank e he (L.get j)
      (hL.2.1 _ (List.get_mem _ _)) (y j) π Z hgood)
  simpa using hnot

end Klr.StageRank

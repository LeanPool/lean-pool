/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineFamily
import Mathlib.Tactic.NormNum

/-!
# Countable unions of first-trigger transcripts

A prefix-free family of finite transcripts specifies disjoint input events.
Consequently an equality or a constant affine-syndrome factor on each member
passes to the countable union. This is the measure-theoretic step needed when
a proof stops immediately before a first rank drop at an unbounded time.

The trigger is a predicate of the transcript already observed. For a pre-drop
stopping event it describes the next query, before its answer is revealed.
-/

@[expose] public section

namespace Klr.StoppingTranscript

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The input event producing one prescribed finite transcript. -/
def inputEvent (π : ScanRule) (v : List Bool) : Set Cantor :=
  {X | π.transcript X v.length = v}

/-- No two distinct members of a prefix-free family extend one another. -/
def PrefixFree (W : Set (List Bool)) : Prop :=
  ∀ ⦃u v⦄, u ∈ W → v ∈ W → u <+: v → u = v

/-- The countable union of the input events indexed by a transcript family. -/
def unionEvent (π : ScanRule) (W : Set (List Bool)) : Set Cantor :=
  ⋃ v : W, inputEvent π v.val

theorem measurableSet_inputEvent (π : ScanRule) (v : List Bool) :
    MeasurableSet (inputEvent π v) := π.measurableSet_transcript v

theorem measurableSet_unionEvent (π : ScanRule) (W : Set (List Bool)) :
    MeasurableSet (unionEvent π W) :=
  MeasurableSet.iUnion fun v => measurableSet_inputEvent π v.val

theorem PrefixFree.mono {W V : Set (List Bool)} (hW : PrefixFree W) (hVW : V ⊆ W) :
    PrefixFree V := fun _ _ hu hv huv => hW (hVW hu) (hVW hv) huv

/-- Two transcripts observed on the same input must be comparable by the prefix relation. -/
theorem comparable_of_mem_inputEvent (π : ScanRule) {u v : List Bool} {X : Cantor}
    (hu : X ∈ inputEvent π u) (hv : X ∈ inputEvent π v) : u <+: v ∨ v <+: u := by
  change π.transcript X u.length = u at hu
  change π.transcript X v.length = v at hv
  rcases le_total u.length v.length with h | h
  · exact Or.inl (by simpa only [hu, hv] using π.transcript_prefix X h)
  · exact Or.inr (by simpa only [hu, hv] using π.transcript_prefix X h)

/-- Prefix-free transcript families determine pairwise disjoint input events. -/
theorem pairwiseDisjoint_inputEvent (π : ScanRule) {W : Set (List Bool)}
    (hW : PrefixFree W) : Pairwise (fun u v : W => Disjoint (inputEvent π u.val)
      (inputEvent π v.val)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro X hu hv
  rcases comparable_of_mem_inputEvent π hu hv with h | h
  · exact huv (Subtype.ext (hW u.property v.property h))
  · exact huv (Subtype.ext (hW v.property u.property h).symm)

/-- Exact countable additivity over a prefix-free transcript family. -/
theorem measure_unionEvent (μ : Measure Cantor) (π : ScanRule)
    {W : Set (List Bool)} (hW : PrefixFree W) :
    μ (unionEvent π W) = ∑' v : W, μ (inputEvent π v.val) :=
  measure_iUnion (pairwiseDisjoint_inputEvent π hW)
    (fun v => measurableSet_inputEvent π v.val)

/-- Equality of transcript probabilities transfers to their prefix-free countable union. -/
theorem measure_unionEvent_eq (μ ν : Measure Cantor) (π : ScanRule)
    {W : Set (List Bool)} (hW : PrefixFree W)
    (h : ∀ v ∈ W, μ (inputEvent π v) = ν (inputEvent π v)) :
    μ (unionEvent π W) = ν (unionEvent π W) := by
  rw [measure_unionEvent μ π hW, measure_unionEvent ν π hW]
  exact tsum_congr fun v => h v.val v.property

/-- A fixed syndrome factor transfers from individual stopping transcripts to their union. -/
theorem measure_unionEvent_inter (μ : Measure Cantor) (π : ScanRule)
    {W : Set (List Bool)} (hW : PrefixFree W) {E : Set Cantor}
    (hE : MeasurableSet E) (p : ℝ≥0∞)
    (h : ∀ v ∈ W, μ (inputEvent π v ∩ E) = p * μ (inputEvent π v)) :
    μ (unionEvent π W ∩ E) = p * μ (unionEvent π W) := by
  rw [unionEvent, Set.iUnion_inter]
  have hd : Pairwise (fun u v : W => Disjoint (inputEvent π u.val ∩ E)
      (inputEvent π v.val ∩ E)) := by
    intro u v huv
    exact (pairwiseDisjoint_inputEvent π hW huv).mono
      Set.inter_subset_left Set.inter_subset_left
  rw [measure_iUnion hd (fun v => (measurableSet_inputEvent π v.val).inter hE)]
  simp_rw [h _ (Subtype.property _)]
  rw [ENNReal.tsum_mul_left]
  congr 1
  exact (measure_unionEvent μ π hW).symm

/-- Conditioning on a syndrome preserves the law of a prefix-free stopping union when
its cylinder factors agree with the syndrome's nonzero finite probability. -/
theorem cond_unionEvent (μ : Measure Cantor) (π : ScanRule)
    {W : Set (List Bool)} (hW : PrefixFree W) {E : Set Cantor}
    (hE : MeasurableSet E) (p : ℝ≥0∞) (hprob : μ E = p)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (h : ∀ v ∈ W, μ (inputEvent π v ∩ E) = p * μ (inputEvent π v)) :
    (cond μ E) (unionEvent π W) = μ (unionEvent π W) := by
  rw [cond_apply hE, Set.inter_comm, measure_unionEvent_inter μ π hW hE p h,
    hprob, ← mul_assoc, ENNReal.inv_mul_cancel hp0 hpTop, one_mul]

/-- The first place where a predicate of the currently observed transcript triggers. -/
def firstTrigger (B : List Bool → Prop) : Set (List Bool) :=
  {v | B v ∧ ∀ n < v.length, ¬B (v.take n)}

/-- First-trigger transcripts are prefix-free, without any monotonicity assumption on `B`. -/
theorem firstTrigger_prefixFree (B : List Bool → Prop) : PrefixFree (firstTrigger B) := by
  intro u v hu hv huv
  by_contra hne
  have hlen : u.length < v.length := by
    have hle := huv.length_le
    have hn : u.length ≠ v.length := fun h => hne (huv.eq_of_length h)
    omega
  have hn := hv.2 u.length hlen
  rw [← List.prefix_iff_eq_take.mp huv] at hn
  exact hn hu.1

/-- The union of first-trigger cylinders is exactly the event that a trigger ever occurs. -/
theorem mem_unionEvent_firstTrigger_iff (π : ScanRule) (B : List Bool → Prop) (X : Cantor) :
    X ∈ unionEvent π (firstTrigger B) ↔ ∃ n, B (π.transcript X n) := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h
    exact ⟨v.val.length, hv.symm ▸ v.property.1⟩
  · intro h
    let n := Nat.find h
    have hv : π.transcript X n ∈ firstTrigger B := by
      constructor
      · exact Nat.find_spec h
      · intro k hk
        rw [π.transcript_take X (by simpa using hk.le)]
        exact Nat.find_min h (by simpa [n] using hk)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨π.transcript X n, hv⟩, ?_⟩
    change π.transcript X (π.transcript X n).length = π.transcript X n
    simp

/-- First-trigger cylinders restricted to times at or beyond a fixed horizon. Query
numbering in the paper is one greater than transcript length. -/
def firstTriggerTail (B : List Bool → Prop) (N : ℕ) : Set (List Bool) :=
  {v | v ∈ firstTrigger B ∧ N ≤ v.length}

theorem firstTriggerTail_prefixFree (B : List Bool → Prop) (N : ℕ) :
    PrefixFree (firstTriggerTail B N) :=
  (firstTrigger_prefixFree B).mono (fun _ h => h.1)

/-- A tail union records the first trigger, not an arbitrary later trigger. -/
theorem mem_unionEvent_firstTriggerTail_iff (π : ScanRule) (B : List Bool → Prop)
    (N : ℕ) (X : Cantor) :
    X ∈ unionEvent π (firstTriggerTail B N) ↔
      ∃ n, N ≤ n ∧ B (π.transcript X n) ∧ ∀ k < n, ¬B (π.transcript X k) := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h
    refine ⟨v.val.length, v.property.2, hv.symm ▸ v.property.1.1, ?_⟩
    intro k hk
    have hn := v.property.1.2 k hk
    rw [← hv, π.transcript_take X hk.le] at hn
    exact hn
  · rintro ⟨n, hN, hB, hfirst⟩
    have hv : π.transcript X n ∈ firstTriggerTail B N := by
      constructor
      · constructor
        · exact hB
        · intro k hk
          rw [π.transcript_take X (by simpa using hk.le)]
          exact hfirst k (by simpa using hk)
      · simpa using hN
    apply Set.mem_iUnion.mpr
    refine ⟨⟨π.transcript X n, hv⟩, ?_⟩
    change π.transcript X (π.transcript X n).length = π.transcript X n
    simp

/-- The next queried position is chosen before its bit is revealed, so the set of
positions read after that query is independent of the answer. -/
theorem queriedPositions_append_singleton_eq (π : ScanRule) (v : List Bool) (b c : Bool) :
    π.queriedPositions (v ++ [b]) = π.queriedPositions (v ++ [c]) := by
  have hsub (a d : Bool) : π.queriedPositions (v ++ [a]) ⊆
      π.queriedPositions (v ++ [d]) := by
    intro q hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    have hi0 : i.val ≤ v.length := by
      have ht := i.isLt
      simp only [List.length_append, List.length_singleton] at ht
      omega
    let j : Fin (v ++ [d]).length := ⟨i.val, by simpa using i.isLt⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    change π.query ((v ++ [d]).take i.val) = q
    simpa only [List.take_append_of_le_length hi0] using hi
  exact Finset.Subset.antisymm (hsub b c) (hsub c b)

/-- Whether the next query destroys full unread rank is independent of the next answer. -/
theorem unreadFullRank_append_singleton_iff (B : AffineBlock) (π : ScanRule)
    (v : List Bool) (b c : Bool) :
    B.UnreadFullRank π (v ++ [b]) ↔ B.UnreadFullRank π (v ++ [c]) := by
  have hO : B.observed π (v ++ [b]) = B.observed π (v ++ [c]) := by
    simp only [AffineBlock.observed, queriedPositions_append_singleton_eq π v b c]
  have aux (O T : Set B.support) (dO : DecidablePred (· ∈ O))
      (dT : DecidablePred (· ∈ T)) (h : O = T) :
      Function.Surjective (@AffineObservation.unreadMap _ _ B.matrix O dO) ↔
        Function.Surjective (@AffineObservation.unreadMap _ _ B.matrix T dT) := by
    subst T
    cases Subsingleton.elim dO dT
    rfl
  exact aux _ _ _ _ hO

/-- A predictable trigger for the first drop from full row rank. The test using `false`
is valid for either answer by `unreadFullRank_append_singleton_iff`. -/
def rankDropTrigger (B : AffineBlock) (π : ScanRule) (v : List Bool) : Prop :=
  B.UnreadFullRank π v ∧ ¬B.UnreadFullRank π (v ++ [false])

theorem rankDropTrigger_transcript_iff (B : AffineBlock) (π : ScanRule)
    (X : Cantor) (n : ℕ) :
    rankDropTrigger B π (π.transcript X n) ↔
      B.UnreadFullRank π (π.transcript X n) ∧
        ¬B.UnreadFullRank π (π.transcript X (n + 1)) := by
  rw [ScanRule.transcript_succ]
  exact and_congr Iff.rfl (not_congr (unreadFullRank_append_singleton_iff B π
    (π.transcript X n) false (X (π.query (π.transcript X n)))))

/-- The first loss of full unread rank occurs after at least `N` answers have been
observed. The event is recorded immediately before the rank-destroying query. -/
def rankDropTailEvent (B : AffineBlock) (π : ScanRule) (N : ℕ) : Set Cantor :=
  {X | ∃ n, N ≤ n ∧
    (∀ k ≤ n, B.UnreadFullRank π (π.transcript X k)) ∧
    ¬B.UnreadFullRank π (π.transcript X (n + 1))}

/-- The predictable first-trigger union is exactly the first-rank-drop tail event. -/
theorem unionEvent_rankDropTriggerTail (B : AffineBlock) (π : ScanRule) (N : ℕ) :
    unionEvent π (firstTriggerTail (rankDropTrigger B π) N) =
      rankDropTailEvent B π N := by
  classical
  ext X
  rw [mem_unionEvent_firstTriggerTail_iff]
  constructor
  · rintro ⟨n, hN, hdrop, hfirst⟩
    obtain ⟨_, hfail⟩ := (rankDropTrigger_transcript_iff B π X n).mp hdrop
    refine ⟨n, hN, ?_, hfail⟩
    intro k hk
    induction k with
    | zero => simpa using B.unreadFullRank_nil π
    | succ k ih =>
      have hkn : k < n := by omega
      have hprev := ih (by omega)
      by_contra hbad
      exact hfirst k hkn ((rankDropTrigger_transcript_iff B π X k).mpr ⟨hprev, hbad⟩)
  · rintro ⟨n, hN, hfull, hfail⟩
    refine ⟨n, hN, (rankDropTrigger_transcript_iff B π X n).mpr
      ⟨hfull n le_rfl, hfail⟩, ?_⟩
    intro k hk hdrop
    exact ((rankDropTrigger_transcript_iff B π X k).mp hdrop).2
      (hfull (k + 1) (by omega))

/-- The exact affine stage factor passes to an unbounded prefix-free stopping family. -/
theorem finiteStage_unionEvent_inter {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ k, Disjoint (old k).support B.support) (π : ScanRule)
    {W : Set (List Bool)} (hW : PrefixFree W)
    (hfull : ∀ v ∈ W, B.UnreadFullRank π v) :
    (AffineBlock.finiteStageLaw old) (unionEvent π W ∩ B.event) =
      (1 / 2 : ℝ≥0∞) ^ B.rank * (AffineBlock.finiteStageLaw old) (unionEvent π W) := by
  apply measure_unionEvent_inter (AffineBlock.finiteStageLaw old) π hW
    B.measurableSet_event ((1 / 2 : ℝ≥0∞) ^ B.rank)
  intro v hv
  exact AffineBlock.finiteStage_identity old B hdis π v (hfull v hv)

/-- Once the syndrome's mass is known, conditioning preserves every such stopping event. -/
theorem finiteStage_cond_unionEvent {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ k, Disjoint (old k).support B.support) (π : ScanRule)
    {W : Set (List Bool)} (hW : PrefixFree W)
    (hfull : ∀ v ∈ W, B.UnreadFullRank π v)
    (hprob : (AffineBlock.finiteStageLaw old) B.event = (1 / 2 : ℝ≥0∞) ^ B.rank) :
    (cond (AffineBlock.finiteStageLaw old) B.event) (unionEvent π W) =
      (AffineBlock.finiteStageLaw old) (unionEvent π W) := by
  apply cond_unionEvent (AffineBlock.finiteStageLaw old) π hW B.measurableSet_event
    ((1 / 2 : ℝ≥0∞) ^ B.rank) hprob
  · exact pow_ne_zero _ (by norm_num)
  · finiteness
  · intro v hv
    exact AffineBlock.finiteStage_identity old B hdis π v (hfull v hv)

/-- For an actual nonnull old block family, the new syndrome has the needed mass. -/
theorem finiteStage_cond_unionEvent_of_nonnull {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ k, Disjoint (old k).support B.support) (π : ScanRule)
    {W : Set (List Bool)} (hW : PrefixFree W)
    (hfull : ∀ v ∈ W, B.UnreadFullRank π v)
    (hold : fairCoin (AffineBlock.familyEvent old) ≠ 0) :
    (cond (AffineBlock.finiteStageLaw old) B.event) (unionEvent π W) =
      (AffineBlock.finiteStageLaw old) (unionEvent π W) :=
  finiteStage_cond_unionEvent old B hdis π hW hfull
    (AffineBlock.finiteStageLaw_event old B hdis hold)

/-- The two finite-stage laws agree on the stopping union: conditioning directly on all
old constraints and the new syndrome gives the same result as the old stage alone. -/
theorem finiteStage_unionEvent_preserved {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ k, Disjoint (old k).support B.support) (π : ScanRule)
    {W : Set (List Bool)} (hW : PrefixFree W)
    (hfull : ∀ v ∈ W, B.UnreadFullRank π v)
    (hold : fairCoin (AffineBlock.familyEvent old) ≠ 0) :
    (cond fairCoin (AffineBlock.familyEvent old ∩ B.event)) (unionEvent π W) =
      (AffineBlock.finiteStageLaw old) (unionEvent π W) := by
  rw [← cond_cond_eq_cond_inter (AffineBlock.measurableSet_familyEvent old)
    B.measurableSet_event fairCoin]
  exact finiteStage_cond_unionEvent_of_nonnull old B hdis π hW hfull hold

/-- The stage laws agree on the first-rank-drop tail, with no bound on the stopping time. -/
theorem finiteStage_rankDropTail_preserved {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hdis : ∀ k, Disjoint (old k).support B.support) (π : ScanRule) (N : ℕ)
    (hold : fairCoin (AffineBlock.familyEvent old) ≠ 0) :
    (cond fairCoin (AffineBlock.familyEvent old ∩ B.event))
        (unionEvent π (firstTriggerTail (rankDropTrigger B π) N)) =
      (AffineBlock.finiteStageLaw old)
        (unionEvent π (firstTriggerTail (rankDropTrigger B π) N)) := by
  apply finiteStage_unionEvent_preserved old B hdis π
    (firstTriggerTail_prefixFree (rankDropTrigger B π) N) _ hold
  intro v hv
  exact hv.1.1.1

/-- For pairwise disjoint old blocks, the stopping-union transfer needs no separate
assumption that the old constraint event has nonzero measure. -/
theorem nextStage_unionEvent {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support) (π : ScanRule)
    {W : Set (List Bool)} (hW : PrefixFree W)
    (hfull : ∀ v ∈ W, B.UnreadFullRank π v) :
    (cond fairCoin (AffineBlock.familyEvent old ∩ B.event)) (unionEvent π W) =
      (AffineBlock.finiteStageLaw old) (unionEvent π W) :=
  finiteStage_unionEvent_preserved old B hnew π hW hfull
    (AffineBlock.fairCoin_familyEvent_ne_zero old hold)

/-- Adding a disjoint full-rank block preserves the distribution of its own first
rank-drop tail, including unbounded stopping times. -/
theorem nextStage_rankDropTail {κ : Type*} [Finite κ]
    (old : κ → AffineBlock) (B : AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (hnew : ∀ k, Disjoint (old k).support B.support) (π : ScanRule) (N : ℕ) :
    (cond fairCoin (AffineBlock.familyEvent old ∩ B.event)) (rankDropTailEvent B π N) =
      (AffineBlock.finiteStageLaw old) (rankDropTailEvent B π N) := by
  rw [← unionEvent_rankDropTriggerTail]
  exact finiteStage_rankDropTail_preserved old B hnew π N
    (AffineBlock.fairCoin_familyEvent_ne_zero old hold)

end Klr.StoppingTranscript

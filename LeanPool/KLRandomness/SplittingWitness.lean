/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SplittingClopen
public import LeanPool.KLRandomness.SplittingReserve
import Mathlib.Tactic.Push

/-!
# Witness times and executable finite bets for the splitting argument

The mathematical witness times are supplied by a failing ML test. Bounded
search on an oracle prefix recovers any finite batch of those times. The
resulting rational stakes are ordinary computable functions of two finite
words; no oracle-computability framework is assumed.
-/

@[expose] public section

namespace Klr.Splitting

open RationalComputability SparseSearch
open scoped BigOperators

/-- First successful bounded simulation within the available oracle prefix. -/
def firstTime (c : Nat.Partrec.Code) (n : ℕ) (s : List Bool) : ℕ :=
  (List.range (s.length + 1)).findIdx (fun t => accepts c n t s)

theorem primrec_firstTime (c : Nat.Partrec.Code) : Primrec₂ (firstTime c) := by
  have hproj : Primrec (fun p : (ℕ × List Bool) × ℕ =>
      ((c, (p.1.1, p.2)), p.1.2)) :=
    ((Primrec.const c).pair ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).pair
      (Primrec.snd.comp Primrec.fst)
  have hp := primrec_accepts.comp hproj
  exact (Primrec.list_findIdx
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.snd)))
    hp.to₂).to₂

/-- The full finite batch needed before the next target bet has been found. -/
def ready (c : Nat.Partrec.Code) (s : List Bool) (n : ℕ) : Bool :=
  (List.range (SmallMartingales.cutoff n)).all fun m =>
    accepts c (2 * m + 2) s.length s

theorem ready_iff (c : Nat.Partrec.Code) (s : List Bool) (n : ℕ) :
    ready c s n = true ↔
      ∀ m < SmallMartingales.cutoff n, accepts c (2 * m + 2) s.length s = true := by
  simp [ready, List.all_eq_true]

theorem primrec_ready (c : Nat.Partrec.Code) : Primrec₂ (ready c) := by
  have hn : Primrec (fun p : List Bool × ℕ => SmallMartingales.cutoff p.2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
      (Primrec.const 6)
  have hs : Primrec (fun p : (List Bool × ℕ) × ℕ => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hm : Primrec (fun p : (List Bool × ℕ) × ℕ => 2 * p.2 + 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
      (Primrec.const 2)
  have ha := primrec_accepts.comp
    (((Primrec.const c).pair (hm.pair (Primrec.list_length.comp hs))).pair hs)
  exact (Primrec.list_all (Primrec.list_range.comp hn) ha.to₂).to₂

/-- A prefix length by which the test program detects the input at the given level. -/
noncomputable def witnessTime (T : MartinLofTest) (A : Cantor) (hA : T.Fails A)
    (m : ℕ) : ℕ := by
  classical
  exact Nat.find ((mem_programOpen_iff T.code (2 * m + 2) A).mp (hA (2 * m + 2)))

theorem witnessTime_spec (T : MartinLofTest) (A : Cantor) (hA : T.Fails A) (m : ℕ) :
    A ∈ event T.code (2 * m + 2) (witnessTime T A hA m) := by
  classical
  exact Nat.find_spec ((mem_programOpen_iff T.code (2 * m + 2) A).mp (hA (2 * m + 2)))

theorem witnessTime_min (T : MartinLofTest) (A : Cantor) (hA : T.Fails A)
    (m k : ℕ) (hk : k < witnessTime T A hA m) :
    A ∉ event T.code (2 * m + 2) k := by
  classical
  exact Nat.find_min ((mem_programOpen_iff T.code (2 * m + 2) A).mp (hA (2 * m + 2))) hk

theorem witnessTime_le (T : MartinLofTest) (A : Cantor) (hA : T.Fails A)
    (m k : ℕ) (hk : A ∈ event T.code (2 * m + 2) k) :
    witnessTime T A hA m ≤ k := by
  classical
  exact Nat.find_min' ((mem_programOpen_iff T.code (2 * m + 2) A).mp (hA (2 * m + 2))) hk

theorem firstTime_eq_witnessTime (T : MartinLofTest) (A : Cantor) (hA : T.Fails A)
    (m k : ℕ) (hk : A ∈ event T.code (2 * m + 2) k) :
    firstTime T.code (2 * m + 2) (ScanRule.inputPrefix A k) = witnessTime T A hA m := by
  have hle := witnessTime_le T A hA m k hk
  unfold firstTime
  apply (List.findIdx_eq (by simpa using Nat.lt_succ_of_le hle)).mpr
  constructor
  · simpa only [event, Set.mem_ofPred_eq, List.getElem_range, accepts_prefix T.code (2 * m + 2)
      (witnessTime T A hA m) k hle A] using witnessTime_spec T A hA m
  · intro j hj
    apply Bool.eq_false_iff.mpr
    intro ha
    have hjk : j ≤ k := (Nat.le_of_lt hj).trans hle
    have he : A ∈ event T.code (2 * m + 2) j := by
      simpa only [event, Set.mem_ofPred_eq, List.getElem_range,
        accepts_prefix T.code (2 * m + 2) j k hjk A] using ha
    exact witnessTime_min T A hA m j hj he

theorem eventually_ready (T : MartinLofTest) (A : Cantor) (hA : T.Fails A) (n : ℕ) :
    ∃ K, ∀ k ≥ K, ready T.code (ScanRule.inputPrefix A k) n = true := by
  classical
  let K := (Finset.range (SmallMartingales.cutoff n)).sup (witnessTime T A hA)
  refine ⟨K, fun k hk => (ready_iff _ _ _).mpr ?_⟩
  intro m hm
  have hmK : witnessTime T A hA m ≤ K :=
    Finset.le_sup (f := witnessTime T A hA) (Finset.mem_range.mpr hm)
  have he := event_mono T.code (2 * m + 2) (hmK.trans hk)
    (witnessTime_spec T A hA m)
  simpa only [event, Set.mem_ofPred_eq, ScanRule.length_inputPrefix] using he

/-- The fixed finite-event martingales, using witness times from the oracle half. -/
def family (T : MartinLofTest) (f : ℕ → ℕ) : SmallMartingales where
  value m v := clopenCapital T.code (2 * m + 2) (f m) v
  nonneg m v := clopenCapital_nonneg T.code (2 * m + 2) (f m) v
  fair m v := clopenCapital_fair T.code (2 * m + 2) (f m) v
  initial_le m := clopenCapital_initial_le T (2 * m + 2) (f m)

/-- A finite sum computed from an available oracle prefix. -/
def knownCapital (oracle target : Nat.Partrec.Code) (s : List Bool) (K : ℕ)
    (v : List Bool) : ℚ :=
  ((List.range K).map fun m => (2 : ℚ) ^ m *
    clopenCapital target (2 * m + 2) (firstTime oracle (2 * m + 2) s) v).sum

/-- The next signed stake computed from the bounded clopen martingales. -/
def bet (oracle target : Nat.Partrec.Code) (s v : List Bool) : ℚ :=
  (knownCapital oracle target s (SmallMartingales.cutoff v.length) (v ++ [true]) -
    knownCapital oracle target s (SmallMartingales.cutoff v.length) (v ++ [false])) / 2

theorem computable_knownCapital (oracle target : Nat.Partrec.Code) :
    Computable (fun p : List Bool × (ℕ × List Bool) =>
      knownCapital oracle target p.1 p.2.1 p.2.2) := by
  let α := List Bool × (ℕ × List Bool)
  have hs : Computable (fun p : α × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hv : Computable (fun p : α × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hl : Computable (fun p : α × ℕ => 2 * p.2 + 2) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2)
      Computable.snd) (Computable.const 2)
  have ht := (primrec_firstTime oracle).to_comp.comp hl hs
  have hc := computable_clopenCapital.comp
    (((Computable.const target).pair (hl.pair ht)).pair hv)
  have hw : Computable (fun p : α × ℕ => (2 : ℚ) ^ p.2) := by
    apply (primrec_rat_natCast.to_comp.comp
      (Computable.list_length.comp (computable_words.comp Computable.snd))).of_eq
    intro p
    simp only [PoolAdvice.length_words, Nat.cast_pow, Nat.cast_ofNat]
  exact PoolAdvice.computable_list_sum
    (Primrec.list_range.to_comp.comp (Computable.fst.comp Computable.snd))
    (primrec_rat_mul.to_comp.comp hw hc).to₂

theorem computable_bet (oracle target : Nat.Partrec.Code) : Computable₂ (bet oracle target) := by
  have hn : Computable (fun p : List Bool × List Bool => SmallMartingales.cutoff p.2.length) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2)
        (Computable.list_length.comp Computable.snd)) (Computable.const 6)
  have hc (b : Bool) : Computable (fun p : List Bool × List Bool =>
      knownCapital oracle target p.1 (SmallMartingales.cutoff p.2.length) (p.2 ++ [b])) := by
    have hproj : Computable (fun p : List Bool × List Bool =>
        (p.1, (SmallMartingales.cutoff p.2.length, p.2 ++ [b]))) :=
      Computable.fst.pair (hn.pair
        (Primrec.list_concat.to_comp.comp Computable.snd (Computable.const b)))
    have hh := (computable_knownCapital oracle target).comp hproj
    exact hh
  exact (primrec_rat_div.to_comp.comp
    (primrec_rat_sub.to_comp.comp (hc true) (hc false)) (Computable.const 2)).to₂

theorem knownCapital_eq (O T : MartinLofTest) (A : Cantor) (hA : O.Fails A)
    (k K : ℕ) (hk : ∀ m < K, A ∈ event O.code (2 * m + 2) k) (v : List Bool) :
    knownCapital O.code T.code (ScanRule.inputPrefix A k) K v =
      (family T (witnessTime O A hA)).sumCapital K v := by
  unfold knownCapital SmallMartingales.sumCapital
  rw [← List.sum_toFinset _ (List.nodup_range (n := K))]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro m hm
  rw [firstTime_eq_witnessTime O A hA m k (hk m (Finset.mem_range.mp hm))]
  rfl

theorem bet_correct (O T : MartinLofTest) (A : Cantor) (hA : O.Fails A)
    (k : ℕ) (v : List Bool)
    (hready : ready O.code (ScanRule.inputPrefix A k) v.length = true) :
    bet O.code T.code (ScanRule.inputPrefix A k) v =
      (family T (witnessTime O A hA)).stake v := by
  have hk : ∀ m < SmallMartingales.cutoff v.length, A ∈ event O.code (2 * m + 2) k := by
    simpa only [event, Set.mem_ofPred_eq, ScanRule.length_inputPrefix] using
      (ready_iff _ _ _).mp hready
  unfold bet SmallMartingales.stake
  rw [knownCapital_eq O T A hA k _ hk, knownCapital_eq O T A hA k _ hk]

theorem witness_comparison (f g : ℕ → ℕ) :
    (∀ N, ∃ m ≥ N, f m ≤ g m) ∨ (∀ N, ∃ m ≥ N, g m ≤ f m) := by
  classical
  by_cases h : ∀ N, ∃ m ≥ N, f m ≤ g m
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨N, hN⟩ := h
    intro M
    refine ⟨max M N, Nat.le_max_left _ _, ?_⟩
    exact (hN _ (Nat.le_max_right _ _)).le

theorem reserve_unbounded (O T : MartinLofTest) (A B : Cantor)
    (hA : O.Fails A) (hB : T.Fails B)
    (hcomp : ∀ N, ∃ m ≥ N, witnessTime T B hB m ≤ witnessTime O A hA m) :
    ∀ bound : ℝ, ∃ n,
      bound < ((family T (witnessTime O A hA)).reserveValue (ScanRule.inputPrefix B n) : ℝ) := by
  intro bound
  obtain ⟨N, hN⟩ := exists_nat_gt bound
  obtain ⟨m, hmN, hm⟩ := hcomp N
  let n := max (witnessTime O A hA m) m
  have hn : witnessTime O A hA m ≤ n := Nat.le_max_left _ _
  have hmn : m < SmallMartingales.cutoff (ScanRule.inputPrefix B n).length := by
    simp only [ScanRule.length_inputPrefix, SmallMartingales.cutoff]
    have := Nat.le_max_right (witnessTime O A hA m) m
    omega
  have he := event_mono T.code (2 * m + 2) hm (witnessTime_spec T B hB m)
  have hv : (family T (witnessTime O A hA)).value m (ScanRule.inputPrefix B n) = 1 :=
    clopenCapital_eq_one T.code (2 * m + 2) (witnessTime O A hA m) B he hn
  have hq := (family T (witnessTime O A hA)).term_le_reserveValue
    (ScanRule.inputPrefix B n) m hmn
  rw [hv, mul_one] at hq
  have hqr : (2 : ℝ) ^ m ≤
      ((family T (witnessTime O A hA)).reserveValue (ScanRule.inputPrefix B n) : ℝ) := by
    exact_mod_cast hq
  have hpow : (m : ℝ) < (2 : ℝ) ^ m := by exact_mod_cast m.lt_two_pow_self
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast hmN
  exact ⟨n, hN.trans_le (hNm.trans (hpow.le.trans hqr))⟩

end Klr.Splitting

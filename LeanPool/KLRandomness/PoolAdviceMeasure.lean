/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolAdvice
public import LeanPool.KLRandomness.PoolQuery
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Exact measure interpretation of the finite pool tests

The rational averages used by the pool verifier are the fair-coin integrals
of the actual finite-horizon query fractions and finite-prefix advice. This
file connects the executable checker to the Borel probability space.
-/

@[expose] public section

namespace Klr.PoolAdvice

open MeasureTheory SparseSearch
open scoped BigOperators

theorem inputPrefix_eq_iff_mem_cylinder (Z : Cantor) (n : ℕ) (s : List Bool)
    (hs : s.length = n) :
    ScanRule.inputPrefix Z n = s ↔ Z ∈ cylinder s := by
  constructor
  · intro h
    rw [← h]
    exact ScanRule.mem_cylinder_inputPrefix Z n
  · intro h
    apply List.ext_getElem (by simp [hs])
    intro i hi hj
    rw [← List.getD_eq_getElem _ false hi, ← List.getD_eq_getElem _ false hj]
    exact (ScanRule.getD_inputPrefix Z (by simpa using hi)).trans (h i hj)

theorem inputPrefix_take (Z : Cantor) {n d : ℕ} (hd : d ≤ n) :
    (ScanRule.inputPrefix Z n).take d = ScanRule.inputPrefix Z d := by
  simpa only [ScanRule.monotone_transcript] using ScanRule.monotone.transcript_take Z hd

/-- A function of a finite prefix is exactly a finite cylinder-simple function. -/
theorem prefixFunction_eq_sum (n : ℕ) (f : List Bool → ℝ) :
    (fun Z : Cantor => f (ScanRule.inputPrefix Z n)) =
      fun Z => ∑ s ∈ (words n).toFinset, (cylinder s).indicator (fun _ => f s) Z := by
  classical
  funext Z
  have hm : ScanRule.inputPrefix Z n ∈ (words n).toFinset := by
    simp [mem_words_iff]
  rw [Finset.sum_eq_single (ScanRule.inputPrefix Z n)]
  · exact (Set.indicator_of_mem (ScanRule.mem_cylinder_inputPrefix Z n)
      (fun _ : Cantor => f (ScanRule.inputPrefix Z n))).symm
  · intro s hs hne
    have hlen : s.length = n := (mem_words_iff n s).mp (List.mem_toFinset.mp hs)
    have hn : Z ∉ cylinder s := by
      intro hz
      exact hne ((inputPrefix_eq_iff_mem_cylinder Z n s hlen).mpr hz).symm
    simp [hn]
  · exact fun hn => False.elim (hn hm)

theorem integrable_prefixFunction (n : ℕ) (f : List Bool → ℝ) :
    Integrable (fun Z : Cantor => f (ScanRule.inputPrefix Z n)) fairCoin := by
  rw [prefixFunction_eq_sum]
  exact integrable_finsetSum _ fun s _ =>
    (integrable_const (f s)).indicator (measurableSet_cylinder s)

/-- Uniform finite averaging agrees exactly with fair-coin integration. -/
theorem integral_prefixFunction (n : ℕ) (f : List Bool → ℝ) :
    (∫ Z : Cantor, f (ScanRule.inputPrefix Z n) ∂fairCoin) =
      ((words n).map f).sum / (2 : ℝ) ^ n := by
  classical
  rw [prefixFunction_eq_sum, integral_finsetSum _ fun s _ =>
    (integrable_const (f s)).indicator (measurableSet_cylinder s)]
  rw [← List.sum_toFinset f (nodup_words n), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  have hlen : s.length = n := (mem_words_iff n s).mp (List.mem_toFinset.mp hs)
  rw [integral_indicator_const _ (measurableSet_cylinder s)]
  simp [measureReal_def, hlen, ENNReal.toReal_pow,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem average_eq_integral (n : ℕ) (f : List Bool → ℚ) :
    (average n f : ℝ) =
      ∫ Z : Cantor, (f (ScanRule.inputPrefix Z n) : ℝ) ∂fairCoin := by
  rw [integral_prefixFunction n (fun s => (f s : ℝ))]
  simp [average, Rat.cast_list_sum, List.map_map, Function.comp_def]

theorem measurableSet_highSet (A : Advice) (i : ℕ) : MeasurableSet (highSet A i) := by
  have hm : Measurable (fun Z => highTable A i (ScanRule.inputPrefix Z A.depth)) := by
    simpa only [ScanRule.monotone_transcript] using
      DropEvents.measurable_transcript_eval ScanRule.monotone A.depth (highTable A i)
  exact hm (measurableSet_singleton true)

theorem measurable_approx (A : Advice) (i : ℕ) : Measurable (approx A i) := by
  change Measurable (fun Z : Cantor => (approxTable A i (ScanRule.inputPrefix Z A.depth) : ℝ))
  simpa only [ScanRule.monotone_transcript] using
    DropEvents.measurable_transcript_eval ScanRule.monotone A.depth
      (fun s => (approxTable A i s : ℝ))

theorem integrable_approx (A : Advice) (i : ℕ) : Integrable (approx A i) fairCoin :=
  integrable_prefixFunction A.depth (fun s => (approxTable A i s : ℝ))

theorem readsBefore_inputPrefix {rules : List ScanRule} {i : ℕ} {π : ScanRule}
    (hi : rules[i]? = some π) (a V n : ℕ) (hV : V ≤ n) (Z : Cantor) :
    readsBefore rules i a V (ScanRule.inputPrefix Z n) = true ↔
      PoolQuery.ReadsBy π a V Z := by
  rw [readsBefore_eq_true]
  unfold PoolQuery.ReadsBy PoolQuery.queryAt
  constructor <;> rintro ⟨t, ht, h⟩ <;> refine ⟨t, ht, ?_⟩
  · simpa only [inputPrefix_take Z (ht.le.trans hV), query_of_getElem? hi] using h
  · simpa only [inputPrefix_take Z (ht.le.trans hV), query_of_getElem? hi] using h

private theorem cast_countP_eq_sum (G : List ℕ) (p : ℕ → Bool) :
    (G.countP p : ℝ) = (G.map (fun a => if p a then (1 : ℝ) else 0)).sum := by
  induction G with
  | nil => simp
  | cons a G ih => cases hp : p a <;> simp [hp, ih, add_comm]

/-- The rational count is exactly the actual finite-horizon coverage fraction. -/
theorem finiteReads_eq_readFractionBy {rules : List ScanRule} {i : ℕ} {π : ScanRule}
    (hi : rules[i]? = some π) (G : List ℕ) (hG : G.Nodup)
    (V n : ℕ) (hV : V ≤ n) (Z : Cantor) :
    (finiteReads rules i G V (ScanRule.inputPrefix Z n) : ℝ) =
      PoolQuery.readFractionBy π G.toFinset V Z := by
  classical
  unfold finiteReads PoolQuery.readFractionBy
  push_cast
  rw [List.toFinset_card_of_nodup hG, cast_countP_eq_sum, ← List.sum_toFinset _ hG]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have he := readsBefore_inputPrefix hi a V n hV Z
  by_cases h : PoolQuery.ReadsBy π a V Z
  · simp [PoolQuery.indicatorBy, h, he.mpr h]
  · have hn : readsBefore rules i a V (ScanRule.inputPrefix Z n) = false :=
      Bool.eq_false_iff.mpr (fun ht => h (he.mp ht))
    simp [PoolQuery.indicatorBy, h, hn]

theorem highTable_inputPrefix (A : Advice) (i n : ℕ) (hd : A.depth ≤ n) (Z : Cantor) :
    highTable A i (ScanRule.inputPrefix Z n) =
      highTable A i (ScanRule.inputPrefix Z A.depth) := by
  simp only [highTable, inputPrefix_take Z hd, inputPrefix_take Z le_rfl]

theorem approxTable_inputPrefix (A : Advice) (i n : ℕ) (hd : A.depth ≤ n) (Z : Cantor) :
    approxTable A i (ScanRule.inputPrefix Z n) =
      approxTable A i (ScanRule.inputPrefix Z A.depth) := by
  simp only [approxTable, inputPrefix_take Z hd, inputPrefix_take Z le_rfl]

/-- Exact interpretation of the L1 acceptance test. -/
theorem distance_eq_integral {rules : List ScanRule} {i : ℕ} {π : ScanRule}
    (hi : rules[i]? = some π) (A : Advice) (G : List ℕ) (hG : G.Nodup) (V : ℕ) :
    (distance rules A G V i : ℝ) =
      ∫ Z, |PoolQuery.readFractionBy π G.toFinset V Z - approx A i Z| ∂fairCoin := by
  rw [distance, average_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with Z
  push_cast
  rw [finiteReads_eq_readFractionBy hi G hG V (testDepth A V) (Nat.le_max_left _ _) Z,
    approxTable_inputPrefix A i (testDepth A V) (Nat.le_max_right _ _) Z]
  rfl

/-- Exact interpretation of the high-set missed-mass acceptance test. -/
theorem highMiss_eq_measureReal {rules : List ScanRule} {i : ℕ} {π : ScanRule}
    (hi : rules[i]? = some π) (A : Advice) (G : List ℕ) (hG : G.Nodup) (V : ℕ) :
    (highMiss rules A G V i : ℝ) =
      fairCoin.real {Z | Z ∈ highSet A i ∧ PoolQuery.readFractionBy π G.toFinset V Z < 1} := by
  classical
  rw [highMiss, average_eq_integral]
  let S := {Z | Z ∈ highSet A i ∧ PoolQuery.readFractionBy π G.toFinset V Z < 1}
  have hS : MeasurableSet S := (measurableSet_highSet A i).inter
    (measurableSet_lt (PoolQuery.measurable_readFractionBy π G.toFinset V) measurable_const)
  rw [← integral_indicator_one hS]
  apply integral_congr_ae
  filter_upwards [] with Z
  have hf := finiteReads_eq_readFractionBy hi G hG V (testDepth A V)
    (Nat.le_max_left _ _) Z
  have hlt : finiteReads rules i G V (ScanRule.inputPrefix Z (testDepth A V)) < 1 ↔
      PoolQuery.readFractionBy π G.toFinset V Z < 1 := by
    rw [← hf]
    exact_mod_cast Iff.rfl
  have ht := highTable_inputPrefix A i (testDepth A V) (Nat.le_max_right _ _) Z
  have he : (highTable A i (ScanRule.inputPrefix Z (testDepth A V)) &&
      decide (finiteReads rules i G V (ScanRule.inputPrefix Z (testDepth A V)) < 1)) = true ↔
      Z ∈ S := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, ht, hlt]
    rfl
  by_cases hz : Z ∈ S
  · simp [he.mpr hz, Set.indicator_of_mem hz]
  · have hh := mt he.mp hz
    simp [hh, Set.indicator_of_notMem hz]

/-- Exact interpretation of one finite expected read fraction. -/
theorem average_finiteReads_eq_integral {rules : List ScanRule} {i : ℕ} {π : ScanRule}
    (hi : rules[i]? = some π) (A : Advice) (G : List ℕ) (hG : G.Nodup) (V : ℕ) :
    (average (testDepth A V) (finiteReads rules i G V) : ℝ) =
      ∫ Z, PoolQuery.readFractionBy π G.toFinset V Z ∂fairCoin := by
  rw [average_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun Z =>
    finiteReads_eq_readFractionBy hi G hG V (testDepth A V) (Nat.le_max_left _ _) Z

/-- The weighted finite check integrates the actual scans supplied in the fixed list. -/
theorem weightedMass_eq_sum_integral {rules : List ScanRule} (π : ℕ → ScanRule)
    (hπ : ∀ i < rules.length, rules[i]? = some (π i))
    (A : Advice) (G : List ℕ) (hG : G.Nodup) (V : ℕ) :
    (weightedMass rules A G V : ℝ) =
      ∑ i ∈ Finset.range rules.length,
        (weight i : ℝ) * ∫ Z, PoolQuery.readFractionBy (π i) G.toFinset V Z ∂fairCoin := by
  unfold weightedMass
  push_cast
  rw [List.map_map, ← List.sum_toFinset _ (List.nodup_range (n := rules.length))]
  simp only [List.toFinset_range, Function.comp_def]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Rat.cast_mul, average_finiteReads_eq_integral
    (hπ i (Finset.mem_range.mp hi)) A G hG V]

/-- Every accepted pair passes the three actual measure-theoretic tests. -/
theorem Accepted.measure_spec {rules : List ScanRule} {A : Advice} {M : ℕ}
    {C : Candidate} (h : Accepted rules A M C) (π : ℕ → ScanRule)
    (hπ : ∀ i < rules.length, rules[i]? = some (π i))
    (hℓ : A.protectedCount ≤ rules.length) :
    (∀ i < A.protectedCount,
      fairCoin.real {Z | Z ∈ highSet A i ∧
        PoolQuery.readFractionBy (π i) C.1.toFinset C.2 Z < 1} < 3 * (A.error : ℝ)) ∧
    (∀ i < A.protectedCount,
      (∫ Z, |PoolQuery.readFractionBy (π i) C.1.toFinset C.2 Z - approx A i Z| ∂fairCoin) <
        3 * (A.error : ℝ)) ∧
    (A.threshold : ℝ) < ∑ i ∈ Finset.range rules.length,
      (weight i : ℝ) * ∫ Z, PoolQuery.readFractionBy (π i) C.1.toFinset C.2 Z ∂fairCoin := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have ht := h.2.2.2.1 i hi
    have hr : (highMiss rules A C.1 C.2 i : ℝ) < 3 * (A.error : ℝ) := by exact_mod_cast ht
    rwa [highMiss_eq_measureReal (hπ i (hi.trans_le hℓ)) A C.1 h.2.1 C.2] at hr
  · intro i hi
    have ht := h.2.2.2.2.1 i hi
    have hr : (distance rules A C.1 C.2 i : ℝ) < 3 * (A.error : ℝ) := by exact_mod_cast ht
    rwa [distance_eq_integral (hπ i (hi.trans_le hℓ)) A C.1 h.2.1 C.2] at hr
  · have ht : (A.threshold : ℝ) < (weightedMass rules A C.1 C.2 : ℝ) := by
      exact_mod_cast h.2.2.2.2.2
    rwa [weightedMass_eq_sum_integral π hπ A C.1 h.2.1 C.2] at ht

end Klr.PoolAdvice

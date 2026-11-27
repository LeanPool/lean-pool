/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.MartinLof
public import LeanPool.KLRandomness.PoolAdviceComputable
public import LeanPool.KLRandomness.PoolAdviceMeasure
public import LeanPool.KLRandomness.BlockProductAnswer
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded clopen approximants and their rational martingales

A bounded simulation of an effective-open code gives a finite-prefix event.
Its conditional probability is an exactly computable rational martingale.
These are the finite objects used by the KL splitting argument.
-/

@[expose] public section

namespace Klr.Splitting

open MeasureTheory SparseSearch RationalComputability
open scoped ENNReal

/-- Check all prefixes of length at most the simulation budget. -/
def accepts (c : Nat.Partrec.Code) (n t : ℕ) (s : List Bool) : Bool :=
  (List.range (t + 1)).any fun k =>
    (c.evaln t (Encodable.encode (n, s.take k))).isSome

theorem accepts_iff (c : Nat.Partrec.Code) (n t : ℕ) (s : List Bool) :
    accepts c n t s = true ↔
      ∃ k ≤ t, ∃ a, c.evaln t (Encodable.encode (n, s.take k)) = some a := by
  simp only [accepts, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨k, hk, h⟩
    change (c.evaln t (Encodable.encode (n, s.take k))).isSome = true at h
    cases he : c.evaln t (Encodable.encode (n, s.take k)) with
    | none => rw [he] at h; cases h
    | some a => exact ⟨k, by omega, a, he⟩
  · rintro ⟨k, hk, a, ha⟩
    refine ⟨k, by omega, ?_⟩
    rw [ha]
    rfl

theorem accepts_take (c : Nat.Partrec.Code) (n t : ℕ) (s : List Bool) :
    accepts c n t (s.take t) = accepts c n t s := by
  rw [Bool.eq_iff_iff, accepts_iff, accepts_iff]
  constructor <;> rintro ⟨k, hk, a, ha⟩ <;> refine ⟨k, hk, a, ?_⟩
  · simpa only [List.take_take, Nat.min_eq_left hk] using ha
  · simpa only [List.take_take, Nat.min_eq_left hk] using ha

theorem accepts_prefix (c : Nat.Partrec.Code) (n t d : ℕ) (hd : t ≤ d)
    (X : Cantor) :
    accepts c n t (ScanRule.inputPrefix X d) =
      accepts c n t (ScanRule.inputPrefix X t) := by
  rw [← accepts_take c n t, PoolAdvice.inputPrefix_take X hd]

/-- The event discovered by time `t`, with all its cylinders truncated at depth `t`. -/
def event (c : Nat.Partrec.Code) (n t : ℕ) : Set Cantor :=
  {X | accepts c n t (ScanRule.inputPrefix X t) = true}

theorem measurableSet_event (c : Nat.Partrec.Code) (n t : ℕ) :
    MeasurableSet (event c n t) :=
  measurableSet_prefix_event (fun s => accepts c n t s = true) t

theorem event_subset (c : Nat.Partrec.Code) (n t : ℕ) :
    event c n t ⊆ programOpen c n := by
  intro X hX
  obtain ⟨k, hk, a, ha⟩ := (accepts_iff _ _ _ _).mp hX
  refine ⟨(ScanRule.inputPrefix X t).take k, ?_, ?_⟩
  · exact Part.dom_iff_mem.mpr ⟨a, Nat.Partrec.Code.evaln_sound ha⟩
  · rw [PoolAdvice.inputPrefix_take X hk]
    exact ScanRule.mem_cylinder_inputPrefix X k

theorem event_mono (c : Nat.Partrec.Code) (n : ℕ) {s t : ℕ} (hst : s ≤ t) :
    event c n s ⊆ event c n t := by
  intro X hX
  obtain ⟨k, hk, a, ha⟩ := (accepts_iff _ _ _ _).mp hX
  apply (accepts_iff _ _ _ _).mpr
  refine ⟨k, hk.trans hst, a, ?_⟩
  rw [PoolAdvice.inputPrefix_take X hk] at ha
  rw [PoolAdvice.inputPrefix_take X (hk.trans hst)]
  exact Nat.Partrec.Code.evaln_mono hst ha

theorem mem_programOpen_iff (c : Nat.Partrec.Code) (n : ℕ) (X : Cantor) :
    X ∈ programOpen c n ↔ ∃ t, X ∈ event c n t := by
  constructor
  · rintro ⟨s, hs, hX⟩
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hs
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp ha
    refine ⟨max t s.length, (accepts_iff _ _ _ _).mpr ?_⟩
    refine ⟨s.length, Nat.le_max_right _ _, a, ?_⟩
    rw [PoolAdvice.inputPrefix_take X (Nat.le_max_right _ _),
      (PoolAdvice.inputPrefix_eq_iff_mem_cylinder X s.length s rfl).mpr hX]
    exact Nat.Partrec.Code.evaln_mono (Nat.le_max_left _ _) ht
  · rintro ⟨t, ht⟩
    exact event_subset c n t ht

theorem primrec_accepts :
    Primrec (fun p : (Nat.Partrec.Code × (ℕ × ℕ)) × List Bool =>
      accepts p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let α := (Nat.Partrec.Code × (ℕ × ℕ)) × List Bool
  have hc : Primrec (fun p : α × ℕ => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec (fun p : α × ℕ => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have ht : Primrec (fun p : α × ℕ => p.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hs : Primrec (fun p : α × ℕ => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hp := Primrec.list_take.comp Primrec.snd hs
  have he := Nat.Partrec.Code.primrec_evaln.comp
    ((ht.pair hc).pair (Primrec.encode.comp (hn.pair hp)))
  have hb := Primrec.option_isSome.comp he
  exact Primrec.list_any
    (Primrec.list_range.comp (Primrec.succ.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) hb.to₂

theorem computable_accepts :
    Computable (fun p : (Nat.Partrec.Code × (ℕ × ℕ)) × List Bool =>
      accepts p.1.1 p.1.2.1 p.1.2.2 p.2) := primrec_accepts.to_comp

/-- Exact conditional probability of the bounded event after a finite prefix. -/
def clopenCapital (c : Nat.Partrec.Code) (n t : ℕ) (v : List Bool) : ℚ :=
  (2 : ℚ) ^ v.length * PoolAdvice.average (max t v.length) (fun s =>
    if accepts c n t s && decide (s.take v.length = v) then 1 else 0)

theorem clopenCapital_eq_measure (c : Nat.Partrec.Code) (n t : ℕ) (v : List Bool) :
    (clopenCapital c n t v : ℝ) =
      (2 : ℝ) ^ v.length * fairCoin.real (event c n t ∩ cylinder v) := by
  rw [clopenCapital, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    PoolAdvice.average_eq_integral,
    ← integral_indicator_one ((measurableSet_event c n t).inter (measurableSet_cylinder v))]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with X
  have hp := PoolAdvice.inputPrefix_take X (Nat.le_max_right t v.length)
  have ha := accepts_prefix c n t (max t v.length) (Nat.le_max_left _ _) X
  have he : (accepts c n t (ScanRule.inputPrefix X (max t v.length)) &&
      decide ((ScanRule.inputPrefix X (max t v.length)).take v.length = v)) = true ↔
      X ∈ event c n t ∩ cylinder v := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, hp, ha,
      PoolAdvice.inputPrefix_eq_iff_mem_cylinder X v.length v rfl]
    rfl
  by_cases hX : X ∈ event c n t ∩ cylinder v
  · simp [he.mpr hX, Set.indicator_of_mem hX]
  · simp [mt he.mp hX, Set.indicator_of_notMem hX]

theorem clopenCapital_nonneg (c : Nat.Partrec.Code) (n t : ℕ) (v : List Bool) :
    0 ≤ clopenCapital c n t v := by
  apply (Rat.cast_nonneg (K := ℝ)).mp
  rw [clopenCapital_eq_measure]
  positivity

theorem cylinder_snoc (v : List Bool) (b : Bool) :
    cylinder (v ++ [b]) = cylinder v ∩ {X | X v.length = b} := by
  rw [cylinder_eq_monotone_inputEvent, BlockProductAnswer.inputEvent_snoc,
    ← cylinder_eq_monotone_inputEvent]
  rfl

theorem cylinder_children_union (v : List Bool) :
    cylinder (v ++ [false]) ∪ cylinder (v ++ [true]) = cylinder v := by
  rw [cylinder_snoc, cylinder_snoc]
  ext X
  cases h : X v.length <;> simp [h]

theorem cylinder_children_disjoint (v : List Bool) :
    Disjoint (cylinder (v ++ [false])) (cylinder (v ++ [true])) := by
  rw [cylinder_snoc, cylinder_snoc]
  exact Set.disjoint_left.mpr (fun X h₀ h₁ => Bool.false_ne_true (h₀.2.symm.trans h₁.2))

theorem clopenCapital_fair (c : Nat.Partrec.Code) (n t : ℕ) (v : List Bool) :
    clopenCapital c n t (v ++ [false]) + clopenCapital c n t (v ++ [true]) =
      2 * clopenCapital c n t v := by
  apply (Rat.cast_injective (α := ℝ))
  push_cast
  rw [clopenCapital_eq_measure, clopenCapital_eq_measure, clopenCapital_eq_measure]
  have hd : Disjoint (event c n t ∩ cylinder (v ++ [false]))
      (event c n t ∩ cylinder (v ++ [true])) :=
    (cylinder_children_disjoint v).mono Set.inter_subset_right Set.inter_subset_right
  have hm := measureReal_union (μ := fairCoin) hd
    ((measurableSet_event c n t).inter (measurableSet_cylinder (v ++ [true])))
  rw [← Set.inter_union_distrib_left, cylinder_children_union] at hm
  simp only [List.length_append, List.length_singleton, pow_succ]
  rw [hm]
  ring

theorem clopenCapital_initial_le (T : MartinLofTest) (n t : ℕ) :
    clopenCapital T.code n t [] ≤ (1 / 2 : ℚ) ^ n := by
  apply (Rat.cast_le (K := ℝ)).mp
  rw [clopenCapital_eq_measure]
  simp only [List.length_nil, pow_zero, cylinder_nil, Set.inter_univ, one_mul]
  push_cast
  have h := ENNReal.toReal_mono (by finiteness : (1 / 2 : ℝ≥0∞) ^ n ≠ ∞)
    ((measure_mono (event_subset T.code n t)).trans (T.measure_le n))
  simpa only [measureReal_def, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat] using h

theorem clopenCapital_eq_one (c : Nat.Partrec.Code) (n t : ℕ) (X : Cantor)
    (hX : X ∈ event c n t) {d : ℕ} (hd : t ≤ d) :
    clopenCapital c n t (ScanRule.inputPrefix X d) = 1 := by
  have hsub : cylinder (ScanRule.inputPrefix X d) ⊆ event c n t := by
    intro Y hY
    have hp := (PoolAdvice.inputPrefix_eq_iff_mem_cylinder Y d
      (ScanRule.inputPrefix X d) (by simp)).mpr hY
    change accepts c n t (ScanRule.inputPrefix Y t) = true
    rw [← accepts_prefix c n t d hd Y, hp, accepts_prefix c n t d hd X]
    exact hX
  apply (Rat.cast_injective (α := ℝ))
  rw [clopenCapital_eq_measure, Set.inter_eq_right.mpr hsub]
  simp only [measureReal_def, fairCoin_cylinder, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, Rat.cast_one]
  rw [← mul_pow]
  norm_num

theorem computable_clopenCapital :
    Computable (fun p : (Nat.Partrec.Code × (ℕ × ℕ)) × List Bool =>
      clopenCapital p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let α := (Nat.Partrec.Code × (ℕ × ℕ)) × List Bool
  have hv : Computable (fun p : α × List Bool => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hlen : Computable (fun p : α => p.2.length) :=
    Computable.list_length.comp Computable.snd
  have hacc : Computable (fun p : α × List Bool =>
      accepts p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.2) := by
    have hproj : Computable (fun p : α × List Bool => (p.1.1, p.2)) :=
      (Computable.fst.comp Computable.fst).pair Computable.snd
    have hh := computable_accepts.comp hproj
    exact hh
  have hp : Computable (fun p : α × List Bool => p.2.take p.1.2.length) :=
    Primrec.list_take.to_comp.comp (Computable.list_length.comp hv) Computable.snd
  have he : Computable (fun p : α × List Bool => decide (p.2.take p.1.2.length = p.1.2)) :=
    Primrec.eq.decide.to_comp.comp hp hv
  have hb : Computable (fun p : α × List Bool =>
      accepts p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.2 && decide (p.2.take p.1.2.length = p.1.2)) :=
    Primrec.and.to_comp.comp hacc he
  have hi : Computable (fun p : α × List Bool =>
      if accepts p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.2 &&
        decide (p.2.take p.1.2.length = p.1.2) then (1 : ℚ) else 0) :=
    (Computable.cond hb (Computable.const (1 : ℚ)) (Computable.const 0)).of_eq
      (fun _ => by simp only [Bool.cond_eq_ite])
  have hdepth : Computable (fun p : α => max p.1.2.2 p.2.length) :=
    Primrec.nat_max.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) hlen
  have hav : Computable (fun p : α => PoolAdvice.average (max p.1.2.2 p.2.length)
      (fun s => if accepts p.1.1 p.1.2.1 p.1.2.2 s &&
        decide (s.take p.2.length = p.2) then (1 : ℚ) else 0)) :=
    PoolAdvice.computable_average hdepth hi.to₂
  have hpow : Computable (fun p : α => (2 : ℚ) ^ p.2.length) := by
    apply (primrec_rat_natCast.to_comp.comp
      (Computable.list_length.comp (computable_words.comp hlen))).of_eq
    intro p
    simp only [PoolAdvice.length_words, Nat.cast_pow, Nat.cast_ofNat]
  exact primrec_rat_mul.to_comp.comp hpow hav

end Klr.Splitting

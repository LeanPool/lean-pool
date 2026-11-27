/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolAdvice

/-!
# Computability of the finite pool tests

A finite list of total computable scans is fixed before the requested pool
size. List induction compiles that family to a single total query dispatcher.
The tests then use only bounded loops, exact rational arithmetic, and the
finite advice tables. No code for a weak limit or a Borel partition is assumed.
-/

@[expose] public section

namespace Klr.PoolAdvice

open SparseSearch SparseListSearch RationalComputability

theorem computable_query (rules : List ScanRule) : Computable₂ (query rules) := by
  induction rules with
  | nil => exact Computable.const 0
  | cons π rules ih =>
    have hh : Computable₂ (fun p : ℕ × List Bool => fun i => query rules i p.2) :=
      ih.comp Computable.snd (Computable.snd.comp Computable.fst)
    have h := Computable.nat_casesOn Computable.fst
      (π.computable_query.comp Computable.snd) hh
    exact h.of_eq fun p => by cases p.1 <;> rfl

/-- A rational bounded sum, used to retain the external parameters in finite
summation of a merely computable (not necessarily primitive recursive) term. -/
def boundedSum (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => boundedSum f n + f n

theorem boundedSum_succ_shift (f : ℕ → ℚ) (n : ℕ) :
    boundedSum f (n + 1) = f 0 + boundedSum (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp [boundedSum]
  | succ n ih => rw [boundedSum, ih, boundedSum, add_assoc]

theorem boundedSum_getD {β : Type*} (f : β → ℚ) (l : List β) (d : β) :
    boundedSum (fun i => f (l.getD i d)) l.length = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.length_cons, boundedSum_succ_shift]
    simpa only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.sum_cons] using
      congrArg (fun q => f b + q) ih

theorem computable_boundedSum {α : Type*} [Primcodable α] {f : α → ℕ → ℚ}
    (hf : Computable₂ f) : Computable (fun a : α × ℕ => boundedSum (f a.1) a.2) := by
  have ha : Computable (fun a : (α × ℕ) × (ℕ × ℚ) => a.1.1) :=
    Computable.fst.comp Computable.fst
  have hi : Computable (fun a : (α × ℕ) × (ℕ × ℚ) => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hq : Computable (fun a : (α × ℕ) × (ℕ × ℚ) => a.2.2) :=
    Computable.snd.comp Computable.snd
  have hs := primrec_rat_add.to_comp.comp hq (hf.comp ha hi)
  apply (Computable.nat_rec Computable.snd (Computable.const 0) hs.to₂).of_eq
  intro a
  induction a.2 with
  | zero => rfl
  | succ n ih =>
    simpa only [boundedSum, Nat.rec_add_one] using congrArg (fun q => q + f a.1 n) ih

/-- Rational summation of computable terms along a computable finite list. -/
theorem computable_list_sum {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {l : α → List β} {f : α → β → ℚ}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable (fun a => ((l a).map (f a)).sum) := by
  have hg : Computable (fun a : α × ℕ => (l a.1).getD a.2 default) :=
    (Primrec.list_getD default).to_comp.comp (hl.comp Computable.fst) Computable.snd
  have hc := (computable_boundedSum
    (f := fun a i => f a ((l a).getD i default)) (hf.comp Computable.fst hg)).comp
      (Computable.id.pair (Computable.list_length.comp hl))
  exact hc.of_eq fun a => boundedSum_getD (f a) (l a) default

theorem computable_rat_abs : Computable (fun q : ℚ => |q|) :=
  (primrec_rat_max.to_comp.comp Computable.id primrec_rat_neg.to_comp).of_eq
    fun _ => abs_eq_max_neg.symm

theorem computable_rat_lt : Computable₂ (fun p q : ℚ => decide (p < q)) := by
  have h := Primrec.not.to_comp.comp
    (primrec_rat_le.decide.to_comp.comp Computable.snd Computable.fst)
  exact h.of_eq fun p => by
    by_cases hp : p.2 ≤ p.1
    · simp [hp, not_lt_of_ge hp]
    · simp [hp, lt_of_not_ge hp]

/-- Exact averaging over the full binary tree at a computable depth is computable. -/
theorem computable_average {α : Type*} [Primcodable α] {n : α → ℕ}
    {f : α → List Bool → ℚ} (hn : Computable n) (hf : Computable₂ f) :
    Computable (fun a => average (n a) (f a)) := by
  have hw := computable_words.comp hn
  have hs := computable_list_sum hw hf
  have hd := primrec_rat_natCast.to_comp.comp (Computable.list_length.comp hw)
  exact (primrec_rat_div.to_comp.comp hs hd).of_eq fun a => by
    simp [average, length_words]

/-- Fixed Boolean prefix tables are computable without any membership oracle. -/
theorem computable_highTable (A : Advice) {α : Type*} [Primcodable α]
    {i : α → ℕ} {s : α → List Bool} (hi : Computable i) (hs : Computable s) :
    Computable (fun a => highTable A (i a) (s a)) := by
  have ht := (Primrec.list_getD ([], [])).to_comp.comp (Computable.const A.tables) hi
  have hk := Computable.encode.comp (Primrec.list_take.to_comp.comp (Computable.const A.depth) hs)
  exact (Primrec.list_getD false).to_comp.comp (Computable.fst.comp ht) hk

theorem computable_approxTable (A : Advice) {α : Type*} [Primcodable α]
    {i : α → ℕ} {s : α → List Bool} (hi : Computable i) (hs : Computable s) :
    Computable (fun a => approxTable A (i a) (s a)) := by
  have ht := (Primrec.list_getD ([], [])).to_comp.comp (Computable.const A.tables) hi
  have hk := Computable.encode.comp (Primrec.list_take.to_comp.comp (Computable.const A.depth) hs)
  exact (Primrec.list_getD 0).to_comp.comp (Computable.snd.comp ht) hk

theorem computable_readsBefore (rules : List ScanRule) {α : Type*} [Primcodable α]
    {i a V : α → ℕ} {s : α → List Bool}
    (hi : Computable i) (ha : Computable a) (hV : Computable V) (hs : Computable s) :
    Computable (fun p => readsBefore rules (i p) (a p) (V p) (s p)) := by
  have hp := Primrec.list_take.to_comp.comp Computable.snd (hs.comp Computable.fst)
  have hq := (computable_query rules).comp (hi.comp Computable.fst) hp
  have he := Primrec.eq.decide.to_comp.comp hq (ha.comp Computable.fst)
  exact computable_list_any (p := fun p t => decide (query rules (i p) ((s p).take t) = a p))
    (Primrec.list_range.to_comp.comp hV) he

theorem computable_finiteReads (rules : List ScanRule) {α : Type*} [Primcodable α]
    {i : α → ℕ} {G : α → List ℕ} {V : α → ℕ} {s : α → List Bool}
    (hi : Computable i) (hG : Computable G) (hV : Computable V) (hs : Computable s) :
    Computable (fun p => finiteReads rules (i p) (G p) (V p) (s p)) := by
  have hb := computable_readsBefore rules (hi.comp Computable.fst) Computable.snd
    (hV.comp Computable.fst) (hs.comp Computable.fst)
  have hc := computable_list_countP (p := fun p a => readsBefore rules (i p) a (V p) (s p)) hG hb
  exact primrec_rat_div.to_comp.comp (primrec_rat_natCast.to_comp.comp hc)
    (primrec_rat_natCast.to_comp.comp (Computable.list_length.comp hG))

theorem computable_testDepth (A : Advice) : Computable (testDepth A) :=
  Primrec.nat_max.to_comp.comp Computable.id (Computable.const A.depth)

theorem computable_highMiss (rules : List ScanRule) (A : Advice) :
    Computable (fun p : Candidate × ℕ => highMiss rules A p.1.1 p.1.2 p.2) := by
  have hG : Computable (fun p : (Candidate × ℕ) × List Bool => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hV : Computable (fun p : (Candidate × ℕ) × List Bool => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable (fun p : (Candidate × ℕ) × List Bool => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hv := computable_finiteReads rules hi hG hV Computable.snd
  have hH := computable_highTable A hi Computable.snd
  have hm := Primrec.and.to_comp.comp hH
    (computable_rat_lt.comp hv (Computable.const 1))
  have hf := Computable.cond hm (Computable.const (1 : ℚ)) (Computable.const 0)
  have hn : Computable (fun p : Candidate × ℕ => testDepth A p.1.2) :=
    (computable_testDepth A).comp (Computable.snd.comp Computable.fst)
  exact (computable_average
    (n := fun p : Candidate × ℕ => testDepth A p.1.2)
    (f := fun p : Candidate × ℕ => fun s =>
      cond (highTable A p.2 s && decide (finiteReads rules p.2 p.1.1 p.1.2 s < 1))
        (1 : ℚ) 0) hn hf).of_eq fun _ => by simp [highMiss, Bool.cond_eq_ite]

theorem computable_distance (rules : List ScanRule) (A : Advice) :
    Computable (fun p : Candidate × ℕ => distance rules A p.1.1 p.1.2 p.2) := by
  have hG : Computable (fun p : (Candidate × ℕ) × List Bool => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hV : Computable (fun p : (Candidate × ℕ) × List Bool => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable (fun p : (Candidate × ℕ) × List Bool => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hv := computable_finiteReads rules hi hG hV Computable.snd
  have hψ := computable_approxTable A hi Computable.snd
  have hf := computable_rat_abs.comp (primrec_rat_sub.to_comp.comp hv hψ)
  have hn : Computable (fun p : Candidate × ℕ => testDepth A p.1.2) :=
    (computable_testDepth A).comp (Computable.snd.comp Computable.fst)
  exact computable_average
    (n := fun p : Candidate × ℕ => testDepth A p.1.2)
    (f := fun p : Candidate × ℕ => fun s =>
      |finiteReads rules p.2 p.1.1 p.1.2 s - approxTable A p.2 s|) hn hf

theorem computable_weight : Computable weight := by
  have hs : Computable₂ (fun (_ : ℕ) (p : ℕ × ℚ) => p.2 * (1 / 2)) :=
    (primrec_rat_mul.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.const (1 / 2))).to₂
  apply (Computable.nat_rec Computable.id (Computable.const (1 / 2 : ℚ)) hs).of_eq
  intro i
  induction i with
  | zero => simp [weight]
  | succ i ih =>
    simpa only [weight, pow_succ, Nat.rec_add_one, id_eq] using
      congrArg (fun q : ℚ => q * (1 / 2)) ih

theorem computable_weightedMass (rules : List ScanRule) (A : Advice) :
    Computable (fun C : Candidate => weightedMass rules A C.1 C.2) := by
  have hG : Computable (fun p : (Candidate × ℕ) × List Bool => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hV : Computable (fun p : (Candidate × ℕ) × List Bool => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable (fun p : (Candidate × ℕ) × List Bool => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hv := computable_finiteReads rules hi hG hV Computable.snd
  have hn : Computable (fun p : Candidate × ℕ => testDepth A p.1.2) :=
    (computable_testDepth A).comp (Computable.snd.comp Computable.fst)
  have ha := computable_average
    (n := fun p : Candidate × ℕ => testDepth A p.1.2)
    (f := fun p : Candidate × ℕ => finiteReads rules p.2 p.1.1 p.1.2) hn hv
  have hf := primrec_rat_mul.to_comp.comp (computable_weight.comp Computable.snd) ha
  exact computable_list_sum
    (l := fun _ : Candidate => List.range rules.length)
    (f := fun C : Candidate => fun i =>
      weight i * average (testDepth A C.2) (finiteReads rules i C.1 C.2))
    (Computable.const (List.range rules.length)) hf

end Klr.PoolAdvice

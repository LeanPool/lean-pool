/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.ComputableNonrandom
public import LeanPool.KLRandomness.EffectiveSearch
public import LeanPool.KLRandomness.ScanMeasure

/-!
# Effective open events defined by finite adaptive transcripts

A computable condition on a finite transcript gives a uniformly effectively
open input event. Finite input strings are accepted when they contain every
queried coordinate and agree with all the transcript's prescribed answers.
-/

@[expose] public section

namespace Klr.EffectiveScan

/-- Bounded conjunction, retaining the computation parameter outside the loop. -/
def boundedAll (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => boundedAll p n && p n

theorem boundedAll_eq_true (p : ℕ → Bool) (n : ℕ) :
    boundedAll p n = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [boundedAll]
  | succ n ih =>
    rw [boundedAll, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · exact h i hlt
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem computable_boundedAll {α : Type*} [Primcodable α] {p : α → ℕ → Bool}
    (hp : Computable₂ p) : Computable (fun a : α × ℕ => boundedAll (p a.1) a.2) := by
  have hs : Computable₂ (fun (a : α × ℕ) (b : ℕ × Bool) => b.2 && p a.1 b.1) :=
    (Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (hp.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec Computable.snd (Computable.const true) hs).of_eq
  intro a
  induction a.2 with
  | zero => rfl
  | succ n ih => simpa only [boundedAll, Nat.rec_add_one] using congrArg (· && p a.1 n) ih

/-- A finite input prefix determines every queried bit of a finite transcript. -/
def agrees (π : ScanRule) (v s : List Bool) : Bool :=
  boundedAll (fun i => decide (π.query (v.take i) < s.length) &&
    decide (s.getD (π.query (v.take i)) false = v.getD i false)) v.length

theorem agrees_eq_true (π : ScanRule) (v s : List Bool) :
    agrees π v s = true ↔ ∀ i < v.length,
      π.query (v.take i) < s.length ∧
        s.getD (π.query (v.take i)) false = v.getD i false := by
  simp only [agrees, boundedAll_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem computable_agrees (π : ScanRule) :
    Computable (fun p : List Bool × List Bool => agrees π p.1 p.2) := by
  have hq : Computable (fun p : (List Bool × List Bool) × ℕ =>
      π.query (p.1.1.take p.2)) :=
    π.computable_query.comp (Primrec.list_take.to_comp.comp Computable.snd
      (Computable.fst.comp Computable.fst))
  have hlen : Computable (fun p : (List Bool × List Bool) × ℕ => p.1.2.length) :=
    Computable.list_length.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun p : (List Bool × List Bool) × ℕ =>
      p.1.2.getD (π.query (p.1.1.take p.2)) false) :=
    (Primrec.list_getD false).to_comp.comp (Computable.snd.comp Computable.fst) hq
  have hv : Computable (fun p : (List Bool × List Bool) × ℕ =>
      p.1.1.getD p.2 false) :=
    (Primrec.list_getD false).to_comp.comp (Computable.fst.comp Computable.fst) Computable.snd
  have hp : Computable₂ (fun p : List Bool × List Bool => fun i =>
      decide (π.query (p.1.take i) < p.2.length) &&
        decide (p.2.getD (π.query (p.1.take i)) false = p.1.getD i false)) := by
    have hc := Primrec.and.to_comp.comp
      (Primrec.nat_lt.decide.to_comp.comp hq hlen)
      (Primrec.eq.decide.to_comp.comp hs hv)
    exact hc.of_eq fun _ => rfl
  have hc := (computable_boundedAll hp).comp
    (Computable.id.pair (Computable.list_length.comp Computable.fst))
  exact hc.of_eq fun _ => rfl

theorem transcript_of_agrees (π : ScanRule) (v s : List Bool) (h : agrees π v s = true)
    {X : Cantor} (hX : X ∈ cylinder s) : π.transcript X v.length = v := by
  apply (π.transcript_eq_iff X v).mpr
  intro i hi
  obtain ⟨hq, hb⟩ := (agrees_eq_true π v s).mp h i hi
  exact (hX _ hq).trans hb

theorem exists_prefix_agrees (π : ScanRule) (X : Cantor) (v : List Bool)
    (hv : π.transcript X v.length = v) :
    ∃ s : List Bool, X ∈ cylinder s ∧ agrees π v s = true := by
  classical
  let N := (Finset.univ : Finset (Fin v.length)).sup
    (fun i => π.query (v.take i.val)) + 1
  refine ⟨ScanRule.inputPrefix X N, ScanRule.mem_cylinder_inputPrefix X N, ?_⟩
  rw [agrees_eq_true]
  intro i hi
  have hq : π.query (v.take i) < N := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j : Fin v.length =>
      π.query (v.take j.val)) (Finset.mem_univ ⟨i, hi⟩))
  constructor
  · simpa only [ScanRule.length_inputPrefix] using hq
  · rw [ScanRule.getD_inputPrefix X hq]
    exact (π.transcript_eq_iff X v).mp hv i hi

/-- Input events specified by a condition on some finite adaptive transcript. -/
def openEvent (π : ScanRule) (R : ℕ × List Bool → Prop) (m : ℕ) : Set Cantor :=
  {X | ∃ v, R (m, v) ∧ π.transcript X v.length = v}

/-- A finite witness checks the transcript condition and all queried input bits. -/
def accepts (π : ScanRule) (r : ℕ × List Bool → Bool)
    (p : (ℕ × List Bool) × List Bool) : Bool :=
  r (p.1.1, p.2) && agrees π p.2 p.1.2

theorem computable_accepts (π : ScanRule) {r : ℕ × List Bool → Bool}
    (hr : Computable r) : Computable (accepts π r) := by
  have hleft : Computable (fun p : (ℕ × List Bool) × List Bool => (p.1.1, p.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have hright : Computable (fun p : (ℕ × List Bool) × List Bool => (p.2, p.1.2)) :=
    Computable.snd.pair (Computable.snd.comp Computable.fst)
  have hR := hr.comp hleft
  have hA := (computable_agrees π).comp hright
  have hc := Primrec.and.to_comp.comp hR hA
  exact hc.of_eq fun _ => rfl

theorem computablePred_accepts (π : ScanRule) {r : ℕ × List Bool → Bool}
    (hr : Computable r) : ComputablePred (fun p => accepts π r p = true) :=
  ComputablePred.computable_iff.mpr ⟨accepts π r, computable_accepts π hr, rfl⟩

/-- Uniformly computable transcript conditions yield uniformly effectively open input events. -/
theorem openEvent_uniform (π : ScanRule) {R : ℕ × List Bool → Prop}
    (hR : ComputablePred R) : IsUniformlyEffectivelyOpen (openEvent π R) := by
  classical
  obtain ⟨r, hr, rfl⟩ := ComputablePred.computable_iff.mp hR
  refine ⟨fun p => ∃ v, accepts π r (p, v) = true,
    rePred_exists (computablePred_accepts π hr).to_re, fun m => ?_⟩
  ext X
  constructor
  · rintro ⟨v, hR, hv⟩
    obtain ⟨s, hXs, hs⟩ := exists_prefix_agrees π X v hv
    refine ⟨s, ⟨v, ?_⟩, hXs⟩
    simpa only [accepts, Bool.and_eq_true] using And.intro hR hs
  · rintro ⟨s, ⟨v, h⟩, hXs⟩
    have hvhs : r (m, v) = true ∧ agrees π v s = true := by
      simpa only [accepts, Bool.and_eq_true] using h
    obtain ⟨hv, hs⟩ := hvhs
    exact ⟨v, hv, transcript_of_agrees π v s hs hXs⟩

end Klr.EffectiveScan

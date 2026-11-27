/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageFiniteProbability
public import LeanPool.KLRandomness.HorizonAvoidance

/-!
# Computable finite-stage statistics for adaptive scans

At a finite query horizon there are only finitely many possible query
positions, including all adaptive branches. We give a computable bound for
them, simulate the scan on a finite input word, and prove that the exact
rational conditional average is the actual finite-stage expectation.
-/

@[expose] public section

namespace Klr.StageFiniteScan

open MeasureTheory SparseSearch

/-- Sum the first `n` values of a natural-number-valued sequence. -/
def boundedSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => boundedSum f n + f n

theorem boundedSum_succ_shift (f : ℕ → ℕ) (n : ℕ) :
    boundedSum f (n + 1) = f 0 + boundedSum (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp [boundedSum]
  | succ n ih => rw [boundedSum, ih, boundedSum, Nat.add_assoc]

theorem boundedSum_getD {β : Type*} (f : β → ℕ) (l : List β) (d : β) :
    boundedSum (fun i => f (l.getD i d)) l.length = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.length_cons, boundedSum_succ_shift]
    simpa only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.sum_cons] using
      congrArg (fun q => f b + q) ih

theorem computable_boundedSum {α : Type*} [Primcodable α] {f : α → ℕ → ℕ}
    (hf : Computable₂ f) : Computable (fun a : α × ℕ => boundedSum (f a.1) a.2) := by
  have hs : Computable (fun p : (α × ℕ) × (ℕ × ℕ) =>
      p.2.2 + f p.1.1 p.2.1) := Primrec.nat_add.to_comp.comp
    (Computable.snd.comp Computable.snd)
    (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
  apply (Computable.nat_rec Computable.snd (Computable.const 0) hs.to₂).of_eq
  intro a
  induction a.2 with
  | zero => rfl
  | succ n ih =>
    simpa only [boundedSum, Nat.rec_add_one] using congrArg (fun q => q + f a.1 n) ih

theorem computable_list_sum {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {l : α → List β} {f : α → β → ℕ}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable (fun a => ((l a).map (f a)).sum) := by
  have hg := (Primrec.list_getD default).to_comp.comp
    (hl.comp Computable.fst) Computable.snd
  have hc := (computable_boundedSum
    (f := fun a i => f a ((l a).getD i default)) (hf.comp Computable.fst hg)).comp
      (Computable.id.pair (Computable.list_length.comp hl))
  exact hc.of_eq fun a => boundedSum_getD (f a) (l a) default

/-- A deliberately generous bound, obtained by summing over every branch. -/
def branchBound (π : ScanRule) (V : ℕ) : ℕ :=
  ((List.range V).map (fun t => ((words t).map (fun v => π.query v + 1)).sum)).sum

theorem computable_branchBound (π : ScanRule) : Computable (branchBound π) := by
  have hi : Computable (fun t => ((words t).map (fun v => π.query v + 1)).sum) :=
    computable_list_sum computable_words
      ((Primrec.succ.to_comp.comp π.computable_query).comp Computable.snd)
  exact computable_list_sum Primrec.list_range.to_comp (hi.comp Computable.snd)

theorem query_lt_branchBound (π : ScanRule) (V : ℕ) (v : List Bool)
    (hv : v.length < V) : π.query v < branchBound π V := by
  have hin : π.query v + 1 ≤ ((words v.length).map (fun w => π.query w + 1)).sum :=
    List.le_sum_of_mem
      (List.mem_map.mpr ⟨v, (mem_words_iff _ _).mpr rfl, rfl⟩)
  have hout : ((words v.length).map (fun w => π.query w + 1)).sum ≤ branchBound π V :=
    List.le_sum_of_mem
      (List.mem_map.mpr ⟨v.length, List.mem_range.mpr hv, rfl⟩)
  exact Nat.lt_of_succ_le (hin.trans hout)

/-- An input depth covering both the old constraints and every scan branch. -/
def depth (cs : List AffineCode.Data) (π : ScanRule) (V : ℕ) : ℕ :=
  (cs.map AffineCode.width).sum + branchBound π V

theorem width_le_depth {cs : List AffineCode.Data} (π : ScanRule) (V : ℕ)
    {c : AffineCode.Data} (hc : c ∈ cs) : AffineCode.width c ≤ depth cs π V := by
  exact (List.le_sum_of_mem
    (List.mem_map.mpr ⟨c, hc, rfl⟩)).trans (Nat.le_add_right _ _)

theorem query_lt_depth (cs : List AffineCode.Data) (π : ScanRule) (V : ℕ)
    (v : List Bool) (hv : v.length < V) : π.query v < depth cs π V :=
  (query_lt_branchBound π V v hv).trans_le (Nat.le_add_left _ _)

theorem computable_depth (π : ScanRule) :
    Computable (fun p : List AffineCode.Data × ℕ => depth p.1 π p.2) := by
  have hw := computable_list_sum (l := fun p : List AffineCode.Data × ℕ => p.1)
    (f := fun _ c => AffineCode.width c) Computable.fst
    (AffineCode.computable_width.comp Computable.snd)
  exact Primrec.nat_add.to_comp.comp hw ((computable_branchBound π).comp Computable.snd)

/-- Simulate a finite adaptive scan, zero-filling outside the supplied word. -/
def run (π : ScanRule) (s : List Bool) (t : ℕ) : List Bool :=
  π.transcript (fun n => s.getD n false) t

theorem computable_run (π : ScanRule) : Computable₂ (run π) := by
  have hprev : Computable (fun p : (List Bool × ℕ) × (ℕ × List Bool) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hs : Computable (fun p : (List Bool × ℕ) × (ℕ × List Bool) => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hb := (Primrec.list_getD false).to_comp.comp hs (π.computable_query.comp hprev)
  have hstep := Computable.list_append.comp hprev
    (Primrec.list_cons.to_comp.comp hb (Computable.const []))
  apply (Computable.nat_rec Computable.snd (Computable.const []) hstep.to₂).of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ t ih =>
    simpa only [run, ScanRule.transcript_succ, Nat.rec_add_one] using
      congrArg (fun v => v ++ [p.1.getD (π.query v) false]) ih

/-- The all-branch bound proves simulation correct on every input, with no
almost-everywhere or termination exception. -/
theorem run_inputPrefix_of_bound (π : ScanRule) (V n : ℕ)
    (hn : ∀ v : List Bool, v.length < V → π.query v < n)
    (X : Cantor) {t : ℕ} (ht : t ≤ V) :
    run π (ScanRule.inputPrefix X n) t = π.transcript X t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (by omega)
    change run π (ScanRule.inputPrefix X n) t ++
      [(ScanRule.inputPrefix X n).getD (π.query (run π (ScanRule.inputPrefix X n) t)) false] = _
    rw [he, ScanRule.getD_inputPrefix X
      (hn (π.transcript X t) (by simpa using Nat.lt_of_succ_le ht))]
    rfl

/-- Specialization to the explicit computable depth. -/
theorem run_inputPrefix (cs : List AffineCode.Data) (π : ScanRule) (V : ℕ)
    (X : Cantor) {t : ℕ} (ht : t ≤ V) :
    run π (ScanRule.inputPrefix X (depth cs π V)) t = π.transcript X t := by
  exact run_inputPrefix_of_bound π V _ (query_lt_depth cs π V) X ht

/-- Exact rational expectation of a statistic on the length-`V` transcript. -/
def expectation (cs : List AffineCode.Data) (π : ScanRule) (V : ℕ)
    (f : List Bool → ℚ) : ℚ :=
  StageFiniteProbability.expectation cs (depth cs π V) (fun s => f (run π s V))

theorem computable_expectation (π : ScanRule) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {V : α → ℕ} {f : α → List Bool → ℚ}
    (hcs : Computable cs) (hV : Computable V) (hf : Computable₂ f) :
    Computable (fun a => expectation (cs a) π (V a) (f a)) := by
  have hn := (computable_depth π).comp (hcs.pair hV)
  have hr := (computable_run π).comp Computable.snd (hV.comp Computable.fst)
  exact StageFiniteProbability.computable_expectation hcs hn (hf.comp Computable.fst hr)

/-- The finite algorithm computes the actual conditional expectation. -/
theorem expectation_eq_integral (cs : List AffineCode.Data) (π : ScanRule) (V : ℕ)
    (f : List Bool → ℚ) :
    (expectation cs π V f : ℝ) =
      ∫ X, (f (π.transcript X V) : ℝ) ∂StageFiniteProbability.law cs := by
  rw [expectation, StageFiniteProbability.expectation_eq_integral cs _
    (fun _ hc => width_le_depth π V hc)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X => by
    dsimp only
    rw [run_inputPrefix cs π V X le_rfl]

/-- Exact finite-horizon event probability, uniformly in the affine codes. -/
def probability (cs : List AffineCode.Data) (π : ScanRule) (V : ℕ)
    (p : List Bool → Bool) : ℚ :=
  expectation cs π V (fun v => if p v then 1 else 0)

theorem computable_probability (π : ScanRule) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {V : α → ℕ} {p : α → List Bool → Bool}
    (hcs : Computable cs) (hV : Computable V) (hp : Computable₂ p) :
    Computable (fun a => probability (cs a) π (V a) (p a)) := by
  exact (computable_expectation π (f := fun a s => cond (p a s) (1 : ℚ) 0) hcs hV
    (Computable.cond hp (Computable.const (1 : ℚ)) (Computable.const 0))).of_eq
      fun _ => by simp only [probability, Bool.cond_eq_ite]

theorem probability_eq_measureReal (cs : List AffineCode.Data) (π : ScanRule) (V : ℕ)
    (p : List Bool → Bool) :
    (probability cs π V p : ℝ) =
      (StageFiniteProbability.law cs).real {X | p (π.transcript X V) = true} := by
  have hs : MeasurableSet {X | p (π.transcript X V) = true} :=
    (DropEvents.measurable_transcript_eval π V p) (measurableSet_singleton true)
  rw [probability, expectation_eq_integral, ← integral_indicator_one hs]
  apply integral_congr_ae
  filter_upwards [] with X
  by_cases h : p (π.transcript X V) = true <;> simp [h, Set.indicator]

end Klr.StageFiniteScan

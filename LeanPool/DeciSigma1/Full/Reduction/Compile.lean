/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Full.Reduction.Realization
public import LeanPool.DeciSigma1.Readers.Basic

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # The structural readers of a disjunctive entailment over `{⊥, f, ⊤}`

For each mode `m : Fin k → Bool` the queries are compiled into a structural reader (`compile`).
Coordinate `i` follows the upper run of the seed and the lower run of the exclusion of query `i`,
guarded so that the exclusion and the opposite sign of the seed stay outside the least closure; the
channel from coordinate `i` to coordinate `j` carries an admitted pair when the seed of `j` derives
the exclusion of `i` or the opposite sign of the seed of `i` (`channel_iff_events`). The holes of
the reader are exactly the tuples of words whose seeds and exclusions satisfy
`TerminalRootConditions` (`hole_iff_terminalRootConditions`).
Hence, for a satisfiable constraint, the disjunctive entailment fails exactly when the reader of
some mode has a hole (`not_disjEntails_iff_hole`).

## Main declarations

- `Reduction.compile`: the structural reader of a mode.
- `Reduction.hole_iff_terminalRootConditions`: holes are the tuples whose seeds and exclusions
  satisfy `TerminalRootConditions`.
- `Reduction.not_disjEntails_iff_hole`, `Reduction.disjEntails_iff_no_hole`: failure of the
  entailment is the existence of a hole for some mode.
-/

@[expose] public section


namespace DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure

variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]

/-- The states of the compiled reader: a pair of upper and lower states over signed variables, or
the dead state `none`. -/
abbrev State (V : Type) := Option (Finset (V × Bool) × Finset (V × Bool))

/-- The guard of the compiled states: neither the lower state nor the upper state with exchanged
signs meets the signed variables reachable from facts. -/
abbrev Good (c : Fin n → Bool) (Γ : List (LitT n V)) (P Q : Finset (V × Bool)) : Prop :=
  Disjoint (Q ∪ P.map flipEmb) (factReachableVariables c Γ)

/-- The state `(P, Q)` if it satisfies the guard `Good`, and the dead state otherwise. -/
def mkState (c : Fin n → Bool) (Γ : List (LitT n V))
    (P Q : Finset (V × Bool)) : State V :=
  Automata.guardedPair (Good c Γ) P Q

namespace Compile

/-- One step of the compiled reader: both runs advance, guarded by `Good`. -/
def step (c : Fin n → Bool) (Γ : List (LitT n V)) : State V → Fin n → State V :=
  Automata.guardedStep (Automata.upperStep (signed c Γ))
      (Automata.lowerStep (signed c Γ))
    (Good c Γ)

/-- A state is rejected when its upper state contains no signed variable below a negative fact. -/
def rejected (c : Fin n → Bool) (Γ : List (LitT n V)) : State V → Bool
  | none => false
  | some (P, _) => decide (Disjoint P (forbiddenPredecessors c Γ))

/-- A pair of states is admitted when the upper state of the second meets the lower state of the
first or the upper state of the first with exchanged signs. -/
def admitted : State V → State V → Bool
  | some (Ph, Qh), some (Pt, _) => decide ((Pt ∩ (Qh ∪ Ph.map flipEmb)).Nonempty)
  | _, _ => false

theorem step_of_rejected {c : Fin n → Bool} {Γ : List (LitT n V)} {s : State V}
    (hr : rejected c Γ s = true) (l : Fin n) (hne : step c Γ s l ≠ none) :
    ∃ Q', step c Γ s l = some (∅, Q') := by
  match s with
  | none => simp [rejected] at hr
  | some (P, Q) =>
    simp only [rejected, decide_eq_true_eq] at hr
    simp only [step, Automata.guardedStep, Automata.guardedPair,
      upperStep_eq_empty_of_disjoint P l hr] at hne ⊢
    split_ifs at hne ⊢
    · exact ⟨_, rfl⟩
    · exact absurd rfl hne

end Compile

/-- The signed variable of the seed selected by a mode. -/
def seedName (q : V × V) (m : Bool) : V × Bool :=
  (if m then q.2 else q.1, m)

/-- The signed variable of the exclusion selected by a mode. -/
def exclusionName (q : V × V) (m : Bool) : V × Bool :=
  (if m then q.1 else q.2, m)

/-- The structural reader of `Γ`, the queries `q` and the mode `m`: coordinate `i` starts at the
upper state of its seed and the lower state of its exclusion. -/
def compile (c : Fin n → Bool) (Γ : List (LitT n V))
    (q : Fin k → V × V) (m : Fin k → Bool) : Readers.StructuralReader (Fin n) (State V) k where
  step := Compile.step c Γ
  start := fun i => mkState c Γ
    (Automata.up (signed c Γ) (seedName (q i) (m i)))
    (Automata.down (signed c Γ) (exclusionName (q i) (m i)))
  dead := none
  rejected := Compile.rejected c Γ
  admitted := Compile.admitted
  step_dead := fun _ => rfl
  rejected_dead := rfl
  rejected_step := by
    intro s l hr hne
    obtain ⟨Q', he⟩ := Compile.step_of_rejected hr l hne
    rw [he]; simp [Compile.rejected]
  not_admitted_step_of_rejected := by
    intro p s l hr hne
    obtain ⟨Q', he⟩ := Compile.step_of_rejected hr l hne
    rw [he]
    cases p with
    | none => rfl
    | some p => simp [Compile.admitted]

end DeciSigma1.Full.Reduction

namespace DeciSigma1.Full.Reduction
open DeciSigma1.Readers
open DeciSigma1.Constraints DeciSigma1.Full.Closure
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]

/-- The guard of the compiled reader at the path `w`. -/
def EligibleWord (c : Fin n → Bool) (Γ : List (LitT n V)) (x y : V × Bool) (w : List (Fin n)) :
    Prop :=
  Disjoint (Automata.lowerRun (signed c Γ) y w ∪
    (Automata.upperRun (signed c Γ) x w).map flipEmb) (factReachableVariables c Γ)

theorem compile_live_iff (c : Fin n → Bool) (Γ : List (LitT n V)) (q : Fin k → V × V)
    (m : Fin k → Bool) (W : Fin k → List (Fin n)) (i : Fin k) {a : ℕ}
    (ha : a ≤ (W i).length) :
    (compile c Γ q m).runPrefix W i a ≠ none ↔
      ∀ a' ≤ a, EligibleWord c Γ (seedName (q i) (m i))
        (exclusionName (q i) (m i)) ((W i).take a') :=
  Automata.foldl_take_guardedStep_ne_none_iff _ _ _ _ _ ha

theorem compile_runPrefix (c : Fin n → Bool) (Γ : List (LitT n V)) (q : Fin k → V × V)
    (m : Fin k → Bool) (W : Fin k → List (Fin n)) (i : Fin k) {a : ℕ}
    (h : (compile c Γ q m).runPrefix W i a ≠ none) :
    (compile c Γ q m).runPrefix W i a =
      some (Automata.upperRun (signed c Γ) (seedName (q i) (m i)) ((W i).take a),
          Automata.lowerRun (signed c Γ) (exclusionName (q i) (m i)) ((W i).take a)) :=
  Automata.foldl_guardedStep_eq_some _ _ _ _ _ h

variable {c : Fin n → Bool} {Γ : List (LitT n V)}
  {q : Fin k → V × V} {m : Fin k → Bool}

theorem eligibleWord_prefixes_iff (p r : V × Bool) (w : List (Fin n)) :
    (∀ a ≤ w.length, EligibleWord c Γ p r (w.take a)) ↔
      (r.1, r.2, w) ∉ leastClosure c Γ ∧ (p.1, !p.2, w) ∉ leastClosure c Γ := by
  rw [leastClosure_membership, leastClosure_flip_membership]
  simp only [EligibleWord, FlippedIntersectsFacts,
    Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty,
    Finset.union_inter_distrib_right, Finset.union_nonempty, not_or,
    not_exists, not_and, forall_and, Prod.mk.eta]

theorem compile_liveAlong_iff (W : Fin k → List (Fin n)) (i : Fin k) :
    (∀ a ≤ (W i).length, (compile c Γ q m).runPrefix W i a ≠ none) ↔
      exclusion (q i) (m i) (W i) ∉ leastClosure c Γ ∧
        flipC (seed (q i) (m i) (W i)) ∉ leastClosure c Γ := by
  have hg := eligibleWord_prefixes_iff (c := c) (Γ := Γ)
    (seedName (q i) (m i)) (exclusionName (q i) (m i)) (W i)
  change (∀ a ≤ (W i).length, (compile c Γ q m).runPrefix W i a ≠ none) ↔ _
  apply Iff.trans ?_ hg
  constructor
  · intro h
    exact (compile_live_iff c Γ q m W i le_rfl).mp (h _ le_rfl)
  · intro h a ha
    exact (compile_live_iff c Γ q m W i ha).mpr (fun b hb => h b (hb.trans ha))

theorem compile_runPrefix_of_eligible {W : Fin k → List (Fin n)} {i : Fin k}
    (h : (compile c Γ q m).Eligible W i) (a : Nat) :
    (compile c Γ q m).runPrefix W i a =
      some (Automata.upperRun (signed c Γ) (seedName (q i) (m i)) ((W i).take a),
        Automata.lowerRun (signed c Γ) (exclusionName (q i) (m i)) ((W i).take a)) :=
  compile_runPrefix c Γ q m W i (h.runPrefix_ne a)

theorem compile_eligible_iff (W : Fin k → List (Fin n)) (i : Fin k) :
    (compile c Γ q m).Eligible W i ↔
      Disjoint (Automata.upperRun (signed c Γ) (seedName (q i) (m i)) (W i))
          (forbiddenPredecessors c Γ) ∧
      exclusion (q i) (m i) (W i) ∉ leastClosure c Γ ∧
        flipC (seed (q i) (m i) (W i)) ∉ leastClosure c Γ := by
  constructor
  · intro h
    refine ⟨?_, (compile_liveAlong_iff W i).mp h.1⟩
    have hr := h.2
    simp only [Table.endState] at hr
    rw [compile_runPrefix_of_eligible h, List.take_length] at hr
    exact of_decide_eq_true hr
  · rintro ⟨hr, hm⟩
    have hl := (compile_liveAlong_iff W i).mpr hm
    refine ⟨hl, ?_⟩
    simp only [Table.endState]
    rw [compile_runPrefix c Γ q m W i (hl _ le_rfl), List.take_length]
    exact decide_eq_true hr

end DeciSigma1.Full.Reduction

namespace DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure DeciSigma1.Readers.Table
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
  {q : Fin k → V × V} {m : Fin k → Bool}

omit [Fintype V] in
theorem admitted_some_iff (Ph Qh Pt Qt : Finset (V × Bool)) :
    Compile.admitted (some (Ph, Qh)) (some (Pt, Qt)) = true ↔
      (Pt ∩ Qh).Nonempty ∨ (Pt ∩ Ph.map flipEmb).Nonempty := by
  simp only [Compile.admitted, decide_eq_true_eq, Finset.inter_union_distrib_left,
    Finset.union_nonempty]

/-- The channel from coordinate `i` to coordinate `j` carries an admitted pair exactly when the
seed of `j` derives the exclusion of `i` or the opposite sign of the seed of `i`. -/
theorem channel_iff_events {W : Fin k → List (Fin n)} (i j : Fin k)
    (hi : (compile c Γ q m).Eligible W i) (hj : (compile c Γ q m).Eligible W j) :
    (∃ pq ∈ (compile c Γ q m).channel W i j, (compile c Γ q m).admitted pq.1 pq.2 = true) ↔
      Event c Γ (seed (q j) (m j) (W j)) (exclusion (q i) (m i) (W i)) ∨
      Event c Γ (seed (q j) (m j) (W j)) (flipC (seed (q i) (m i) (W i))) := by
  have hflip (b : Nat) :
      Automata.lowerRun (signed c Γ) (flipV (seedName (q i) (m i))) ((W i).take b) =
      (Automata.upperRun (signed c Γ) (seedName (q i) (m i))
          ((W i).take b)).map flipEmb :=
    lowerRun_flip _ _
  change _ ↔
    (∃ a ≤ (W j).length, ∃ b ≤ (W i).length, (W j).drop a <+: (W i).drop b ∧
      (Automata.upperRun (signed c Γ) (seedName (q j) (m j)) ((W j).take a) ∩
        Automata.lowerRun (signed c Γ) (exclusionName (q i) (m i))
            ((W i).take b)).Nonempty) ∨
    (∃ a ≤ (W j).length, ∃ b ≤ (W i).length, (W j).drop a <+: (W i).drop b ∧
      (Automata.upperRun (signed c Γ) (seedName (q j) (m j)) ((W j).take a) ∩
        Automata.lowerRun (signed c Γ) (flipV (seedName (q i) (m i)))
            ((W i).take b)).Nonempty)
  simp only [hflip]
  constructor
  · rintro ⟨pq, hpq, hadm⟩
    obtain ⟨b, hb, a, ha, hp, rfl⟩ := mem_channel.mp hpq
    rw [compile_runPrefix_of_eligible hi, compile_runPrefix_of_eligible hj] at hadm
    rcases (admitted_some_iff _ _ _ ∅).mp hadm with h | h
    · exact Or.inl ⟨a, ha, b, hb, hp, h⟩
    · exact Or.inr ⟨a, ha, b, hb, hp, h⟩
  · rintro (⟨a, ha, b, hb, hp, h⟩ | ⟨a, ha, b, hb, hp, h⟩)
    all_goals
      refine ⟨((compile c Γ q m).runPrefix W i b, (compile c Γ q m).runPrefix W j a),
        pair_mem_channel hb ha hp, ?_⟩
      rw [compile_runPrefix_of_eligible hi, compile_runPrefix_of_eligible hj]
    · exact (admitted_some_iff _ _ _ (Automata.lowerRun (signed c Γ)
        (exclusionName (q j) (m j)) ((W j).take a))).mpr (Or.inl h)
    · exact (admitted_some_iff _ _ _ (Automata.lowerRun (signed c Γ)
        (exclusionName (q j) (m j)) ((W j).take a))).mpr (Or.inr h)

/-- A tuple is a hole of the reader of mode `m` exactly when its seeds and exclusions satisfy
`TerminalRootConditions`. -/
theorem hole_iff_terminalRootConditions (m : Fin k → Bool) (W : Fin k → List (Fin n)) :
    (compile c Γ q m).IsHole W ↔ TerminalRootConditions c Γ
      (fun i => seed (q i) (m i) (W i))
      (fun i => exclusion (q i) (m i) (W i)) := by
  constructor
  · rintro ⟨he, hc⟩
    refine ⟨fun i => ((compile_eligible_iff W i).mp (he i)).1,
      fun i => ((compile_eligible_iff W i).mp (he i)).2, ?_⟩
    intro j i
    have hn : ¬ (Event c Γ (seed (q j) (m j) (W j)) (exclusion (q i) (m i) (W i)) ∨
        Event c Γ (seed (q j) (m j) (W j)) (flipC (seed (q i) (m i) (W i)))) := by
      intro h
      obtain ⟨pq, hpq, ht⟩ := (channel_iff_events i j (he i) (he j)).mpr h
      have := hc i j pq hpq
      simp [this] at ht
    exact not_or.mp hn
  · rintro ⟨hr, hm, hn⟩
    have he : ∀ i, (compile c Γ q m).Eligible W i :=
      fun i => (compile_eligible_iff W i).mpr ⟨hr i, hm i⟩
    refine ⟨he, fun i j pq hpq => ?_⟩
    apply Bool.eq_false_iff.mpr
    intro ht
    exact (not_or.mpr (hn j i))
      ((channel_iff_events i j (he i) (he j)).mp ⟨pq, hpq, ht⟩)

end DeciSigma1.Full.Reduction

namespace DeciSigma1.Full.Reduction
open DeciSigma1.Constraints
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}

theorem hasCountermodelIn_iff_exists_hole (hs : ∃ ρ, SatT c ρ Γ) :
    HasCountermodelIn (fun _ => True) c Γ q ↔
      ∃ m : Fin k → Bool, ∃ W, (compile c Γ q m).IsHole W := by
  rw [hasCountermodelIn_iff_exists_seedConsistency hs q]
  apply exists_congr
  intro m
  apply exists_congr
  intro W
  rw [seedConsistency_iff_terminalRootConditions, hole_iff_terminalRootConditions]

/-- For a satisfiable constraint, the disjunctive entailment fails exactly when the reader of some
mode has a hole. -/
theorem not_disjEntails_iff_hole (hs : ∃ ρ, SatT c ρ Γ) :
    ¬ DisjEntailsIn (fun _ => True) c Γ q ↔
      ∃ m : Fin k → Bool, ∃ W, (compile c Γ q m).IsHole W := by
  rw [not_disjEntailsIn_iff, hasCountermodelIn_iff_exists_hole hs]

/-- For a satisfiable constraint, the disjunctive entailment holds exactly when the reader of no
mode has a hole. -/
theorem disjEntails_iff_no_hole (hs : ∃ ρ, SatT c ρ Γ) :
    DisjEntailsIn (fun _ => True) c Γ q ↔
      ¬ ∃ m : Fin k → Bool, ∃ W, (compile c Γ q m).IsHole W := by
  classical
  simpa only [not_not] using (not_disjEntails_iff_hole (q := q) hs).not

end DeciSigma1.Full.Reduction

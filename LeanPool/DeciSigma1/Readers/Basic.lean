/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Automata.Basic
import Mathlib.Order.SuccPred.Nat
import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Data.Finset.Prod

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Tables, structural readers and holes

The decision procedures compile a constraint and a family of `k` query inequalities into a
finite automaton with `k` start states, one for each query, and look for a *hole*: a tuple
`W : Fin k → List α` of words, one for each start. One automaton is built for each choice of
witness modes; when the constraint is satisfiable, all queries fail in one solution exactly when
one of these automata has a hole. This module defines
these automata and holes, and the comparison of tuples that the shortening arguments use.

A `Table` is a deterministic complete automaton with `k` (not necessarily distinct) start
states. Reading `W i` from start `i` gives a run; its state after the first `a` letters is
`runPrefix W i a`, the state at *cut* `a`. The *channel* from a host coordinate `i` to a target
coordinate `j` is the set of state pairs at cuts `a` of `W i` and `b` of `W j` such that the
rest of the target word after `b` is a prefix of the rest of the host word after `a`.

A `StructuralReader` adds an absorbing dead state, a set of rejected states that is closed
under steps that stay alive, and an admission relation on pairs (host state, target state)
that never admits a live successor of a rejected state. A tuple is a hole if every run stays
alive and ends in a rejected state (`Eligible`) and no channel carries an admitted pair
(`IsHole`). The small-hole theorem (`Holes.exists_small_hole`) bounds the total length of a
shortest hole.

A tuple `U` *dominates* `W` if it has the same endpoints, visits only states that `W` visits on
the same coordinate, and has smaller channels. Holes are closed under domination
(`IsHole.of_dominates`), so a hole may be replaced by any dominating tuple. A coordinate is *fresh*
if its endpoint does not occur at an earlier cut; the fresh-tuple bound of `Holes.Fresh`
concerns minimal fresh tuples. A state is *immortal* if arbitrarily long words can be read from
it without reaching the dead state; the coordinates with immortal endpoints are those whose
rejected tails `Holes.Tail` shortens.

## Main declarations

- `Table`, `Table.runPrefix`, `Table.endState`, `Table.channel`, `Table.Fresh`: tables with
  several starts, runs, endpoints, channels and fresh coordinates.
- `totalLength`, `wordTuplesUpTo`: the size of a tuple and the finite set of short tuples.
- `Dominates`, `FreshDominates`, `IsMinimalFresh`: domination and minimal fresh tuples.
- `exists_isMinimalFresh_freshDominates`: every fresh tuple has a minimal fresh dominator.
- `StructuralReader`, `StructuralReader.Eligible`, `StructuralReader.IsHole`: structural
  readers and holes.
- `StructuralReader.Immortal`, `StructuralReader.immortal_iff_card`: immortal states, decided
  by one live word of length `|S|`.
- `StructuralReader.firstRejection`, `StructuralReader.rejectedTailLength`: the first rejected
  cut and the length of the rejected tail.
- `StructuralReader.IsHole.of_dominates`: holes are closed under domination.
- `StructuralReader.runPrefix_ne_of_mortal`, `StructuralReader.runPrefix_ne_of_le_firstRejection`:
  comparable suffix starts carry distinct states.
-/

@[expose] public section


namespace DeciSigma1.Readers

open DeciSigma1.Automata

/-- A deterministic complete automaton on the state type `S` over the alphabet `α`, with `k`
start states, which need not be distinct. -/
structure Table (α S : Type) (k : ℕ) where
  /-- The transition function. -/
  step : S → α → S
  /-- The start state of each coordinate. -/
  start : Fin k → S

variable {α S : Type} {k : ℕ}

namespace Table

variable (T : Table α S k)

/-- The state of coordinate `i` at cut `a`: the state reached from the start of `i` by reading
the first `a` letters of `W i` (all of `W i` if `a` exceeds its length). -/
def runPrefix (W : Fin k → List α) (i : Fin k) (a : ℕ) : S :=
  runFrom T.step (T.start i) ((W i).take a)

/-- The endpoint of coordinate `i`: the state reached after reading all of `W i`. -/
def endState (W : Fin k → List α) (i : Fin k) : S := T.runPrefix W i (W i).length

/-- The states of coordinate `i` at the cuts `0, …, |W i|`. -/
def visitedStates [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Finset S :=
  (Finset.range ((W i).length + 1)).image (T.runPrefix W i)

/-- The states of coordinate `i` at the cuts `0, …, |W i| - 1`, before the end. -/
def properVisitedStates [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Finset S :=
  (Finset.range (W i).length).image (T.runPrefix W i)

/-- The channel of a host word `x` read from `p` to a target word `y` read from `q`: the pairs
of states at cuts `a` of `x` and `b` of `y` such that `y.drop b` is a prefix of `x.drop a`.
Both cuts range over all positions, ends included, so the empty rest of the target is
compared with every cut of the host. -/
def pathChannel [DecidableEq α] [DecidableEq S] (p : S) (x : List α) (q : S) (y : List α) :
    Finset (S × S) :=
  (((Finset.range (x.length + 1)) ×ˢ (Finset.range (y.length + 1))).filter
      (fun ab => y.drop ab.2 <+: x.drop ab.1)).image
    (fun ab => (runFrom T.step p (x.take ab.1), runFrom T.step q (y.take ab.2)))

/-- The channel from host coordinate `i` to target coordinate `j`; `i = j` is allowed. -/
def channel [DecidableEq α] [DecidableEq S] (W : Fin k → List α) (i j : Fin k) : Finset (S × S) :=
  T.pathChannel (T.start i) (W i) (T.start j) (W j)

/-- Coordinate `i` is fresh if its endpoint does not occur at an earlier cut. An empty word is
fresh. -/
def Fresh [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Prop :=
  T.endState W i ∉ T.properVisitedStates W i

instance [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Decidable (T.Fresh W i) :=
  inferInstanceAs (Decidable (_ ∉ _))

/-! ## Basic run and cut lemmas -/

variable {T}

@[simp] theorem runPrefix_zero (W : Fin k → List α) (i : Fin k) :
    T.runPrefix W i 0 = T.start i := by
  simp [runPrefix]

theorem runPrefix_succ (W : Fin k → List α) (i : Fin k) {a : ℕ} (h : a < (W i).length) :
    T.runPrefix W i (a + 1) = T.step (T.runPrefix W i a) ((W i)[a]) := by
  simp only [runPrefix]
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, runFrom_snoc]

theorem runPrefix_of_le (W : Fin k → List α) (i : Fin k) {a : ℕ} (h : (W i).length ≤ a) :
    T.runPrefix W i a = T.endState W i := by
  simp [endState, runPrefix, List.take_of_length_le h]

theorem runPrefix_add (W : Fin k → List α) (i : Fin k) (a t : ℕ) :
    T.runPrefix W i (a + t) = runFrom T.step (T.runPrefix W i a) (((W i).drop a).take t) := by
  simp only [runPrefix]
  rw [List.take_add, runFrom_append]

/-- Reading the whole suffix from cut `a` reaches the endpoint. -/
theorem runFrom_runPrefix_drop (W : Fin k → List α) (i : Fin k) (a : ℕ) :
    runFrom T.step (T.runPrefix W i a) ((W i).drop a) = T.endState W i := by
  simp only [endState, runPrefix]
  rw [← runFrom_append, List.take_length]
  by_cases h : a ≤ (W i).length
  · rw [List.take_append_drop]
  · rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil]

theorem mem_visitedStates [DecidableEq S] {W : Fin k → List α} {i : Fin k} {s : S} :
    s ∈ T.visitedStates W i ↔ ∃ a ≤ (W i).length, T.runPrefix W i a = s := by
  simp [visitedStates]

theorem mem_properVisitedStates [DecidableEq S] {W : Fin k → List α} {i : Fin k} {s : S} :
    s ∈ T.properVisitedStates W i ↔ ∃ a < (W i).length, T.runPrefix W i a = s := by
  simp [properVisitedStates]

theorem runPrefix_mem_visitedStates [DecidableEq S] (W : Fin k → List α) (i : Fin k) {a : ℕ}
    (h : a ≤ (W i).length) : T.runPrefix W i a ∈ T.visitedStates W i :=
        mem_visitedStates.mpr ⟨a, h, rfl⟩

theorem mem_pathChannel [DecidableEq α] [DecidableEq S] {p q : S} {x y : List α} {pq : S × S} :
    pq ∈ T.pathChannel p x q y ↔ ∃ a ≤ x.length, ∃ b ≤ y.length,
      y.drop b <+: x.drop a ∧ pq = (runFrom T.step p (x.take a), runFrom T.step q (y.take b)) := by
  simp only [pathChannel, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Nat.lt_succ_iff, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hp⟩, rfl⟩
    exact ⟨a, ha, b, hb, hp, rfl⟩
  · rintro ⟨a, ha, b, hb, hp, rfl⟩
    exact ⟨a, b, ⟨⟨ha, hb⟩, hp⟩, rfl⟩

theorem mem_channel [DecidableEq α] [DecidableEq S] {W : Fin k → List α} {i j : Fin k}
    {pq : S × S} :
    pq ∈ T.channel W i j ↔ ∃ a ≤ (W i).length, ∃ b ≤ (W j).length,
      (W j).drop b <+: (W i).drop a ∧ pq = (T.runPrefix W i a, T.runPrefix W j b) := mem_pathChannel

theorem pair_mem_channel [DecidableEq α] [DecidableEq S] {W : Fin k → List α} {i j : Fin k}
    {a b : ℕ} (ha : a ≤ (W i).length) (hb : b ≤ (W j).length)
    (h : (W j).drop b <+: (W i).drop a) : (T.runPrefix W i a, T.runPrefix W j b) ∈
        T.channel W i j :=
  mem_channel.mpr ⟨a, ha, b, hb, h, rfl⟩

theorem fresh_iff [DecidableEq S] {W : Fin k → List α} {i : Fin k} :
    T.Fresh W i ↔ ∀ a < (W i).length, T.runPrefix W i a ≠ T.endState W i := by
  simp only [Fresh, mem_properVisitedStates, not_exists, not_and]

/-- The endpoint of a coordinate depends only on its word. -/
theorem endState_congr {U W : Fin k → List α} {i : Fin k} (h : U i = W i) :
    T.endState U i = T.endState W i := by
  simp only [endState, runPrefix, h]

/-- A channel depends only on the words of its two coordinates. -/
theorem channel_congr [DecidableEq α] [DecidableEq S] {U W : Fin k → List α} {i j : Fin k}
    (hi : U i = W i) (hj : U j = W j) : T.channel U i j = T.channel W i j := by
  simp only [channel, hi, hj]

end Table

/-- The total length of a tuple: the sum of the lengths of its words. -/
def totalLength (W : Fin k → List α) : ℕ := ∑ i, (W i).length

theorem length_le_totalLength (W : Fin k → List α) (i : Fin k) : (W i).length ≤ totalLength W :=
  Finset.single_le_sum (f := fun i => (W i).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

/-- The finite set of tuples of total length at most `B`. -/
def wordTuplesUpTo [Fintype α] [DecidableEq α] (k B : ℕ) : Finset (Fin k → List α) :=
  (Fintype.piFinset fun _ => wordsUpTo B).filter (fun W => totalLength W ≤ B)

@[simp] theorem mem_wordTuplesUpTo [Fintype α] [DecidableEq α] {B : ℕ} {W : Fin k → List α} :
    W ∈ wordTuplesUpTo k B ↔ totalLength W ≤ B := by
  simp only [wordTuplesUpTo, Finset.mem_filter, Fintype.mem_piFinset, mem_wordsUpTo,
    and_iff_right_iff_imp]
  intro h i
  exact (length_le_totalLength W i).trans h

open Table

/-! ## Domination and minimal fresh tuples -/

section Domination

variable [DecidableEq α] [DecidableEq S]

/-- `U` dominates `W` if, coordinate by coordinate, the endpoints agree, every state visited by
`U` is visited by `W`, and every channel of `U` (from any host to any target, including
`i = j`) is contained in the corresponding channel of `W`. -/
structure Dominates (T : Table α S k) (U W : Fin k → List α) : Prop where
  endState_eq : ∀ i, T.endState U i = T.endState W i
  visitedStates_subset : ∀ i, T.visitedStates U i ⊆ T.visitedStates W i
  channel_subset : ∀ i j, T.channel U i j ⊆ T.channel W i j

/-- `U` freshly dominates `W` if it dominates `W` and all coordinates of `U` are fresh. -/
def FreshDominates (T : Table α S k) (U W : Fin k → List α) : Prop :=
  Dominates T U W ∧ ∀ i, T.Fresh U i

/-- A minimal fresh tuple: all coordinates are fresh, and no fresh dominator has smaller total
length. -/
def IsMinimalFresh (T : Table α S k) (W : Fin k → List α) : Prop :=
  (∀ i, T.Fresh W i) ∧ ∀ U, FreshDominates T U W → totalLength W ≤ totalLength U

variable {T : Table α S k} {U V W : Fin k → List α}

theorem dominates_iff : Dominates T U W ↔ (∀ i, T.endState U i = T.endState W i) ∧
    (∀ i, T.visitedStates U i ⊆ T.visitedStates W i) ∧ ∀ i j, T.channel U i j ⊆ T.channel W i j :=
  ⟨fun h => ⟨h.endState_eq, h.visitedStates_subset, h.channel_subset⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

instance (T : Table α S k) (U W : Fin k → List α) : Decidable (Dominates T U W) :=
  decidable_of_iff _ dominates_iff.symm

instance (T : Table α S k) (U W : Fin k → List α) : Decidable (FreshDominates T U W) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Dominates.refl (T : Table α S k) (W : Fin k → List α) : Dominates T W W :=
  ⟨fun _ => rfl, fun _ => Finset.Subset.refl _, fun _ _ => Finset.Subset.refl _⟩

theorem Dominates.trans (h₁ : Dominates T U V) (h₂ : Dominates T V W) : Dominates T U W :=
  ⟨fun i => (h₁.endState_eq i).trans (h₂.endState_eq i),
      fun i => (h₁.visitedStates_subset i).trans (h₂.visitedStates_subset i),
    fun i j => (h₁.channel_subset i j).trans (h₂.channel_subset i j)⟩

theorem FreshDominates.refl (hW : ∀ i, T.Fresh W i) :
    FreshDominates T W W := ⟨Dominates.refl T W, hW⟩

theorem FreshDominates.trans (h₁ : FreshDominates T U V) (h₂ : FreshDominates T V W) :
    FreshDominates T U W :=
  ⟨h₁.1.trans h₂.1, h₁.2⟩

/-- Minimality need only be checked against tuples of at most the same total length, which
makes it decidable. -/
theorem isMinimalFresh_iff_bounded [Fintype α] : IsMinimalFresh T W ↔ (∀ i, T.Fresh W i) ∧
    ∀ U ∈ wordTuplesUpTo k (totalLength W), FreshDominates T U W → totalLength W ≤
        totalLength U := by
  constructor
  · exact fun h => ⟨h.1, fun U _ hU => h.2 U hU⟩
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun U hU => ?_⟩
    by_contra hlt
    exact hlt (h U (mem_wordTuplesUpTo.mpr (by omega)) hU)

instance [Fintype α] (T : Table α S k) (W : Fin k → List α) : Decidable (IsMinimalFresh T W) :=
  decidable_of_iff _ isMinimalFresh_iff_bounded.symm

/-- Every fresh tuple has a minimal fresh dominator: a fresh dominator of least total length
is minimal, since fresh domination is transitive. -/
theorem exists_isMinimalFresh_freshDominates (hW : ∀ i, T.Fresh W i) :
    ∃ U, FreshDominates T U W ∧ IsMinimalFresh T U := by
  classical
  have hex : ∃ n, ∃ U, FreshDominates T U W ∧ totalLength U = n :=
      ⟨_, W, FreshDominates.refl hW, rfl⟩
  obtain ⟨U, hU, hn⟩ := Nat.find_spec hex
  refine ⟨U, hU, hU.2, fun V hV => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨V, hV.trans hU, rfl⟩

end Domination

/-! ## Structural readers -/

/-- A structural reader: a table with `k` starts, an absorbing dead state, a set of rejected
states and an admission relation `admitted host target` on pairs of states. Rejection is
closed under steps that stay alive, and no live successor of a rejected state is admitted as a
target. -/
structure StructuralReader (α S : Type) (k : ℕ) extends Table α S k where
  /-- The absorbing dead state. -/
  dead : S
  /-- The rejected states. -/
  rejected : S → Bool
  /-- The admitted pairs (host state, target state). -/
  admitted : S → S → Bool
  step_dead : ∀ a, step dead a = dead
  rejected_dead : rejected dead = false
  rejected_step : ∀ q a, rejected q = true → step q a ≠ dead → rejected (step q a) = true
  not_admitted_step_of_rejected : ∀ p q a, rejected q = true → step q a ≠ dead →
      admitted p (step q a) = false

namespace StructuralReader

variable (M : StructuralReader α S k)

/-- Coordinate `i` is eligible if its run never reaches the dead state and its endpoint is
rejected. -/
def Eligible (W : Fin k → List α) (i : Fin k) : Prop :=
  (∀ a ≤ (W i).length, M.runPrefix W i a ≠ M.dead) ∧ M.rejected (M.endState W i) = true

/-- A hole: every coordinate is eligible, and no channel (from any host to any target,
including `i = j`) contains an admitted pair. -/
def IsHole [DecidableEq α] [DecidableEq S] (W : Fin k → List α) : Prop :=
  (∀ i, M.Eligible W i) ∧ ∀ i j, ∀ pq ∈ M.channel W i j, M.admitted pq.1 pq.2 = false

instance [DecidableEq S] (W : Fin k → List α) (i : Fin k) : Decidable (M.Eligible W i) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [DecidableEq α] [DecidableEq S] (W : Fin k → List α) : Decidable (M.IsHole W) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A state is immortal if words of every length can be read from it without reaching the dead
state. -/
def Immortal (q : S) : Prop :=
  ∀ n, ∃ u : List α, u.length = n ∧ ∀ a ≤ n, runFrom M.step q (u.take a) ≠ M.dead

/-- Reading `u` from `q` never reaches the dead state, at any cut. -/
def LiveAlong (q : S) (u : List α) : Prop := ∀ a ≤ u.length, runFrom M.step q (u.take a) ≠ M.dead

instance [DecidableEq S] (q : S) (u : List α) : Decidable (M.LiveAlong q u) :=
  inferInstanceAs (Decidable (∀ a ≤ u.length, _))

/-- The first cut of coordinate `i` at which the state is rejected, or the length of `W i` if
there is none. -/
def firstRejection (W : Fin k → List α) (i : Fin k) : ℕ :=
  ((List.range ((W i).length + 1)).find? (fun a => M.rejected (M.runPrefix W i a))).getD
      (W i).length

/-- The length of the rejected tail `(W i).drop (firstRejection W i)` of coordinate `i`. -/
def rejectedTailLength (W : Fin k → List α) (i : Fin k) : ℕ := (W i).length - M.firstRejection W i

/-- A tuple has mixed mortality if it has an immortal endpoint and a mortal endpoint. -/
def HasMixedMortality (W : Fin k → List α) : Prop :=
  (∃ i, M.Immortal (M.endState W i)) ∧ ∃ j, ¬ M.Immortal (M.endState W j)

variable {M}

/-! ## Liveness along words -/

/-- The transition structure of the reader as an automaton; the start state plays no role. -/
private def toSemiautomaton (M : StructuralReader α S k) : Automata.Semiautomaton α S :=
  ⟨M.dead, M.step⟩

private theorem liveAlong_iff_pathSafe (q : S) (u : List α) :
    M.LiveAlong q u ↔ (toSemiautomaton M).PathSafe (· ≠ M.dead) q u := by
  rw [Automata.Semiautomaton.pathSafe_iff]; rfl

theorem liveAlong_append (q : S) (u v : List α) :
    M.LiveAlong q (u ++ v) ↔ M.LiveAlong q u ∧ M.LiveAlong (runFrom M.step q u) v := by
  simp only [liveAlong_iff_pathSafe]
  exact Automata.Semiautomaton.pathSafe_append _ _ q u v

theorem LiveAlong.take {q : S} {u : List α} (h : M.LiveAlong q u) (n : ℕ) :
    M.LiveAlong q (u.take n) := by
  have h' := (liveAlong_append q (u.take n) (u.drop n)).mp (by rwa [List.take_append_drop])
  exact h'.1

theorem LiveAlong.self {q : S} {u : List α} (h : M.LiveAlong q u) : q ≠ M.dead := by
  simpa using h 0 (Nat.zero_le _)

theorem liveAlong_nil {q : S} (h : q ≠ M.dead) : M.LiveAlong q [] := by
  intro a _; simpa using h

private theorem liveAlong_flatten_replicate {p : S} {v : List α} (hv : M.LiveAlong p v)
    (hc : runFrom M.step p v = p) (m : ℕ) : M.LiveAlong p (List.replicate m v).flatten := by
  induction m with
  | zero => exact liveAlong_nil hv.self
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, liveAlong_append, hc]
    exact ⟨hv, ih⟩

/-- A state from which arbitrarily long live words can be read is immortal. -/
theorem immortal_of_long {q : S} (h : ∀ n, ∃ u : List α, n ≤ u.length ∧ M.LiveAlong q u) :
    M.Immortal q := by
  intro n
  obtain ⟨u, hn, hu⟩ := h n
  refine ⟨u.take n, by simp [hn], fun a ha => ?_⟩
  have := hu.take n a (by simp; omega)
  exact this

/-- A state from which a live cycle can be reached is immortal. -/
theorem immortal_of_cycle {q : S} {u v : List α} (hv : v ≠ []) (hl : M.LiveAlong q (u ++ v))
    (hc : runFrom M.step (runFrom M.step q u) v = runFrom M.step q u) : M.Immortal q := by
  rw [liveAlong_append] at hl
  apply immortal_of_long
  intro n
  refine ⟨u ++ (List.replicate n v).flatten, ?_, ?_⟩
  · have hv1 : 1 ≤ v.length := List.length_pos_iff.mpr hv
    simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
      smul_eq_mul]
    nlinarith
  · rw [liveAlong_append]
    exact ⟨hl.1, liveAlong_flatten_replicate hl.2 hc n⟩

/-- A state is immortal if and only if one live word of length `|S|` can be read from it. -/
theorem immortal_iff_card [Fintype S] {q : S} : M.Immortal q ↔ ∃ u : List α,
    u.length = Fintype.card S ∧ ∀ a ≤ u.length, runFrom M.step q (u.take a) ≠ M.dead := by
  constructor
  · intro h
    obtain ⟨u, hu, hl⟩ := h (Fintype.card S)
    exact ⟨u, hu, hu ▸ hl⟩
  · rintro ⟨u, hu, hl⟩
    have hl' : M.LiveAlong q u := hl
    let f : Fin (Fintype.card S + 1) → S := fun a => runFrom M.step q (u.take a)
    obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    wlog hlt : a < b generalizing a b
    · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.mp hlt) hab.symm)
    have ha : (a : ℕ) < b := hlt
    have hb : (b : ℕ) ≤ u.length := by have := b.isLt; omega
    refine immortal_of_cycle (u := u.take a) (v := (u.drop a).take (b - a)) ?_ ?_ ?_
    · simp; omega
    · rw [← List.take_add, show (a : ℕ) + (b - a) = b by omega]
      exact hl'.take b
    · rw [← runFrom_append, ← List.take_add, show (a : ℕ) + (b - a) = b by omega]
      exact he.symm

/-- Along a live word read from a rejected state every state is rejected. -/
theorem rejected_along {q : S} {u : List α} (hq : M.rejected q = true) (hl : M.LiveAlong q u) :
    ∀ a ≤ u.length, M.rejected (runFrom M.step q (u.take a)) = true := by
  intro a ha
  induction a with
  | zero => simpa using hq
  | succ a ih =>
    have hlt : a < u.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      runFrom_snoc]
    apply M.rejected_step _ _ (ih (by omega))
    have := hl (a + 1) ha
    rwa [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      runFrom_snoc] at this

/-- The words of length `n`, the candidate witnesses of immortality for `n = |S|`. -/
def wordsOfLength [Fintype α] [DecidableEq α] (n : ℕ) : Finset (List α) :=
  (Automata.wordsUpTo n).filter (fun u : List α => u.length = n)

theorem mem_wordsOfLength [Fintype α] [DecidableEq α] {n : ℕ} {u : List α} :
    u ∈ wordsOfLength n ↔ u.length = n := by
  simp only [wordsOfLength, Finset.mem_filter, Automata.mem_wordsUpTo, and_iff_right_iff_imp]
  exact fun h => h.le

instance [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S] : DecidablePred M.Immortal :=
  fun q => decidable_of_iff (∃ u ∈ wordsOfLength (α := α) (Fintype.card S), M.LiveAlong q u)
    (by
      rw [immortal_iff_card]
      simp only [mem_wordsOfLength]
      rfl)

instance [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S] (W : Fin k → List α) :
    Decidable (M.HasMixedMortality W) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Eligible runs -/

/-- Eligibility of a coordinate depends only on its word. -/
theorem eligible_congr {U W : Fin k → List α} {i : Fin k} (h : U i = W i) :
    M.Eligible U i ↔ M.Eligible W i := by
  simp only [Eligible, Table.endState, Table.runPrefix, h]

/-- The first rejected cut of a coordinate depends only on its word. -/
theorem firstRejection_congr {U W : Fin k → List α} {i : Fin k} (h : U i = W i) :
    M.firstRejection U i = M.firstRejection W i := by
  simp only [firstRejection, Table.runPrefix, h]

theorem Eligible.runPrefix_ne {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) (a : ℕ) :
    M.runPrefix W i a ≠ M.dead := by
  by_cases ha : a ≤ (W i).length
  · exact h.1 a ha
  · rw [runPrefix_of_le W i (by omega)]; exact h.1 _ le_rfl

theorem Eligible.liveAlong {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) (a : ℕ) :
    M.LiveAlong (M.runPrefix W i a) ((W i).drop a) := by
  intro t _
  rw [← runPrefix_add]
  exact h.runPrefix_ne _

theorem firstRejection_spec {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) :
    M.firstRejection W i ≤ (W i).length ∧ M.rejected (M.runPrefix W i (M.firstRejection W i)) =
        true ∧
      ∀ a < M.firstRejection W i, M.rejected (M.runPrefix W i a) = false := by
  unfold firstRejection
  cases hf : (List.range ((W i).length + 1)).find? (fun a => M.rejected (M.runPrefix W i a)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd h.2 (by simpa [endState] using hf (W i).length (by simp))
  | some j =>
    rw [List.find?_range_eq_some] at hf
    obtain ⟨h1, h2, h3⟩ := hf
    simp only [List.mem_range] at h2
    refine ⟨by simp; omega, by simpa using h1, fun a ha => ?_⟩
    simpa using h3 a ha

theorem firstRejection_le {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) :
    M.firstRejection W i ≤ (W i).length := (firstRejection_spec h).1

/-- On an eligible coordinate every cut from the first rejected cut on is rejected. -/
theorem rejected_of_firstRejection_le {W : Fin k → List α} {i : Fin k} {a : ℕ} (h : M.Eligible W i)
    (h1 : M.firstRejection W i ≤ a) (h2 : a ≤ (W i).length) : M.rejected (M.runPrefix W i a) =
        true := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
  rw [runPrefix_add]
  exact rejected_along (firstRejection_spec h).2.1 (h.liveAlong _) t (by simp; omega)

theorem rejected_iff_firstRejection_le {W : Fin k → List α} {i : Fin k} {a : ℕ} (h : M.Eligible W i)
    (h2 : a ≤ (W i).length) : M.rejected (M.runPrefix W i a) = true ↔ M.firstRejection W i ≤ a := by
  constructor
  · intro hr
    by_contra hlt
    rw [(firstRejection_spec h).2.2 a (by omega)] at hr
    exact Bool.false_ne_true hr
  · exact fun h1 => rejected_of_firstRejection_le h h1 h2

/-- The first rejected cut is the cut that is rejected and preceded only by cuts that are not. -/
theorem firstRejection_eq_of_rejected
    {M : StructuralReader α S k} {W : Fin k → List α}
    {i : Fin k} (h : M.Eligible W i) {a : ℕ}
    (hr : M.rejected (M.runPrefix W i a) = true)
        (hb : ∀ a' < a, M.rejected (M.runPrefix W i a') = false) :
    M.firstRejection W i = a := by
  obtain ⟨_, h2, h3⟩ := StructuralReader.firstRejection_spec h
  rcases lt_trichotomy (M.firstRejection W i) a with hlt | heq | hgt
  · rw [hb _ hlt] at h2; exact absurd h2 Bool.false_ne_true
  · exact heq
  · rw [h3 _ hgt] at hr; exact absurd hr Bool.false_ne_true

/-- On an eligible target coordinate, an admitted target state lies at or before the first
rejected cut. -/
theorem admitted_target_le_firstRejection {W : Fin k → List α} {j : Fin k} {b : ℕ} {p : S}
    (h : M.Eligible W j) (hb : b ≤ (W j).length) (hadm : M.admitted p (M.runPrefix W j b) = true) :
    b ≤ M.firstRejection W j := by
  by_contra hlt
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [runPrefix_succ W j (by omega)] at hadm
  have hr := rejected_of_firstRejection_le h (by omega) (by omega : c ≤ (W j).length)
  have hne : M.step (M.runPrefix W j c) ((W j)[c]'(by omega)) ≠ M.dead := by
    rw [← runPrefix_succ W j (by omega)]; exact h.runPrefix_ne _
  rw [M.not_admitted_step_of_rejected p _ _ hr hne] at hadm
  exact Bool.false_ne_true hadm

/-- An eligible coordinate that is not fresh ends on a live cycle, so its endpoint is
immortal. -/
theorem immortal_of_not_fresh [DecidableEq S] {W : Fin k → List α} {i : Fin k}
    (h : M.Eligible W i) (hf : ¬ M.Fresh W i) : M.Immortal (M.endState W i) := by
  rw [fresh_iff] at hf
  push Not at hf
  obtain ⟨c, hc, he⟩ := hf
  have hl := h.liveAlong c
  rw [he] at hl
  refine immortal_of_cycle (u := []) (v := (W i).drop c) (by simp; omega) (by simpa using hl) ?_
  simp only [runFrom_nil]
  rw [← he, runFrom_runPrefix_drop, he]

/-- An eligible coordinate with a mortal endpoint is fresh. -/
theorem fresh_of_mortal [DecidableEq S] {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i)
    (hm : ¬ M.Immortal (M.endState W i)) : M.Fresh W i := by
  by_contra hf
  exact hm (immortal_of_not_fresh h hf)

/-- A tuple that dominates a hole is a hole with the same endpoints. -/
theorem IsHole.of_dominates [DecidableEq α] [DecidableEq S] {U W : Fin k → List α}
    (hW : M.IsHole W) (hU : Dominates M.toTable U W) :
    M.IsHole U ∧ ∀ i, M.endState U i = M.endState W i := by
  refine ⟨⟨fun i => ⟨fun a ha => ?_, ?_⟩, fun i j pq hpq => ?_⟩, hU.endState_eq⟩
  · obtain ⟨b, hb, hq⟩ :=
      mem_visitedStates.mp (hU.visitedStates_subset i (runPrefix_mem_visitedStates U i ha))
    rw [← hq]; exact (hW.1 i).1 b hb
  · rw [hU.endState_eq i]; exact (hW.1 i).2
  · exact hW.2 i j pq (hU.channel_subset i j hpq)

/-- If the suffix of `w` after `b` is a prefix of the suffix after `a`, the two suffixes agree on
their first `t ≤ |w| - b` letters. -/
private theorem take_drop_eq_of_prefix {w : List α} {a b t : ℕ} (hp : w.drop b <+: w.drop a)
    (ht : t ≤ w.length - b) : (w.drop a).take t = (w.drop b).take t := by
  obtain ⟨r, hr⟩ := hp
  rw [← hr, List.take_append_of_le_length (by simp; omega)]

/-- On an eligible coordinate with a mortal endpoint, two cuts `a < b` whose suffixes are
comparable (the suffix after `b` is a prefix of the suffix after `a`) carry distinct states.
The empty suffix `b = |W i|` is included. -/
theorem runPrefix_ne_of_mortal {W : Fin k → List α} {i : Fin k} {a b : ℕ}
    (h : M.Eligible W i) (hm : ¬ M.Immortal (M.endState W i)) (hab : a < b) (hb : b ≤ (W i).length)
    (hp : (W i).drop b <+: (W i).drop a) : M.runPrefix W i a ≠ M.runPrefix W i b := by
  classical
  intro he
  have hf := fresh_of_mortal h hm
  rw [fresh_iff] at hf
  apply hf (a + ((W i).length - b)) (by omega)
  rw [runPrefix_add, take_drop_eq_of_prefix hp le_rfl, he,
    List.take_of_length_le (by simp), runFrom_runPrefix_drop]

/-- On an eligible coordinate, two cuts `a < b ≤ firstRejection` whose suffixes are
comparable carry distinct states. -/
theorem runPrefix_ne_of_le_firstRejection {W : Fin k → List α} {i : Fin k} {a b : ℕ}
    (h : M.Eligible W i) (hab : a < b)
    (hb : b ≤ M.firstRejection W i) (hp : (W i).drop b <+: (W i).drop a) :
    M.runPrefix W i a ≠ M.runPrefix W i b := by
  intro he
  have hJ := firstRejection_spec h
  have hra : M.rejected (M.runPrefix W i (a + (M.firstRejection W i - b))) = true := by
    rw [runPrefix_add, take_drop_eq_of_prefix hp (by omega), he, ← runPrefix_add,
      show b + (M.firstRejection W i - b) = M.firstRejection W i by omega]
    exact hJ.2.1
  rw [hJ.2.2 _ (by omega)] at hra
  exact Bool.false_ne_true hra

end StructuralReader

end DeciSigma1.Readers

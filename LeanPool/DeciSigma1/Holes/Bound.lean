/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Fresh.Bound
public import LeanPool.DeciSigma1.Holes.Tail.Compression
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # The small-hole theorem

A structural reader that has a hole has one of total length at most `smallHoleBound σ k N`,
where `σ` is the size of the alphabet, `k` the number of starts and `N` the number of states.
The proof composes two bounds.

* The *rejected-tail bound* (`Tail.exists_hole_rejectedTailLength_le`): a reader with a hole
  has a hole whose immortal coordinates have rejected tails of length at most
  `L = tailLengthBound σ k N`. `Holes.Tail` proves it by replacing tails with periodic
  continuations and compressing their periodic factors.
* The *fresh-tuple bound* (`Fresh.exists_freshDominates_totalLength_le`): every tuple of fresh
  words of a table with `k` starts and `N'` states has a fresh dominator of total length at
  most `freshTupleBound k N'`. `Holes.Fresh` proves it by deleting repeated blocks from a
  minimal fresh tuple.

They are connected by the *cover* of a hole `W` of a reader `M` whose immortal coordinates have
rejected tails of length at most `L`: a table whose states are the states of `M` together with
a counter `0, …, L` for each coordinate. On coordinate `i` it runs `M` up to the first rejected
cut of `W i`; if the rejected tail of `W i` has length at most `L`, it then reads exactly that
tail, counting its letters, and moves to an absorbing state on every other continuation. All
coordinates of `W` are fresh in the cover (`cover_fresh`): a coordinate with a mortal endpoint
is fresh in `M`, and the counter makes a bounded tail fresh. Mapping the counter back to the
corresponding state of `W i` projects runs of the cover to runs of `M`, so a tuple that
dominates `W` in the cover is a hole of `M` with the same endpoints (`cover_project_of_dom`).

The cover has `k · (N + L + 1) + 1` states, so the fresh-tuple bound applied to it gives a hole
of total length at most `freshTupleBound k (k · (N + L + 1) + 1)`
(`exists_hole_totalLength_le_of_tails`). With `L = tailLengthBound σ k N` this is
`exists_small_hole`. Since the bound is computable, the existence of a hole is decided by
searching all tuples up to it (`decideHole`).

## Main declarations

- `cover`, `coverProjection`: the cover of a hole and its projection to the reader.
- `cover_fresh`, `cover_project_of_dom`: the hole is fresh in its cover, and dominators in the
  cover are holes.
- `smallHoleBound`, `exists_small_hole`: the small-hole theorem.
- `decideHole`: the decision procedure for the existence of a hole.
-/

@[expose] public section


namespace DeciSigma1.Holes

open DeciSigma1.Readers
open DeciSigma1.Readers.Table DeciSigma1.Readers.StructuralReader

/-- The states of the cover: a coordinate together with a state of the reader or a counter
`0, …, L`, and an absorbing state `none`. -/
abbrev CoverState (S : Type) (k L : ℕ) := Option (Fin k × (S ⊕ Fin (L + 1)))

variable {α S : Type} [DecidableEq α] [DecidableEq S] {k : ℕ}

namespace Cover

variable (M : StructuralReader α S k) (W : Fin k → List α) (L : ℕ)

/-- One step of the cover. On coordinate `i` with a rejected tail of length at most `L` it
follows the reader through states that are not rejected, switches to the counter when it
reaches the first rejected state of `W i`, and then follows only the letters of the tail, moving
to `none` on any other letter. -/
def step : CoverState S k L → α → CoverState S k L
  | none, _ => none
  | some (i, Sum.inl s), c =>
    if M.rejectedTailLength W i ≤ L then
      if M.rejected s = false then
        if M.step s c = M.runPrefix W i (M.firstRejection W i) then some (i, Sum.inr 0)
        else if M.rejected (M.step s c) = false then some (i, Sum.inl (M.step s c))
        else none
      else none
    else some (i, Sum.inl (M.step s c))
  | some (i, Sum.inr m), c =>
    if h : (m : ℕ) + 1 ≤ L ∧ (m : ℕ) < M.rejectedTailLength W i ∧
        (W i)[M.firstRejection W i + m]? = some c then
      some (i, Sum.inr ⟨m + 1, by omega⟩)
    else none

/-- The start of coordinate `i`: the counter `0` if the rejected tail of `W i` is followed by
the counter and starts at cut `0`, and the start of the reader otherwise. -/
def start (i : Fin k) : CoverState S k L :=
  if M.rejectedTailLength W i ≤ L ∧ M.firstRejection W i = 0 then some (i, Sum.inr 0)
  else some (i, Sum.inl (M.start i))

/-- The expected cover state of coordinate `i` at cut `a`. -/
def expect (i : Fin k) (a : ℕ) : CoverState S k L :=
  if M.rejectedTailLength W i ≤ L ∧ M.firstRejection W i ≤ a then
    some (i, Sum.inr ⟨min (a - M.firstRejection W i) L, by omega⟩)
  else some (i, Sum.inl (M.runPrefix W i a))

end Cover

/-- The cover of a tuple `W`, following rejected tails of length at most `L` letter by letter. -/
def cover (M : StructuralReader α S k) (W : Fin k → List α) (L : ℕ) :
    Table α (CoverState S k L) k :=
  ⟨Cover.step M W L, Cover.start M W L⟩

/-- The projection of cover states to reader states: the counter `m` of coordinate `i` maps to
the state of `W i` at cut `firstRejection W i + m`, and `none` to the dead state. -/
def coverProjection (M : StructuralReader α S k) (W : Fin k → List α) (L : ℕ) : CoverState S k L → S
  | none => M.dead
  | some (_, Sum.inl s) => s
  | some (i, Sum.inr m) => M.runPrefix W i (M.firstRejection W i + m)

omit [DecidableEq S] in
theorem cover_card [Fintype S] (L : ℕ) :
    Fintype.card (CoverState S k L) = k * (Fintype.card S + L + 1) + 1 := by
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_sum]
  ring

variable {M : StructuralReader α S k} {W : Fin k → List α} {L : ℕ}

/-- The run of `W i` in the cover follows `Cover.expect`. -/
theorem cover_runPrefix {i : Fin k} (hE : M.Eligible W i) {a : ℕ} (ha : a ≤ (W i).length) :
    (cover M W L).runPrefix W i a = Cover.expect M W L i a := by
  have hJ := firstRejection_spec hE
  induction a with
  | zero =>
    simp only [runPrefix_zero, cover, Cover.start, Cover.expect, Nat.le_zero, Nat.zero_sub,
      Nat.zero_min]
    split_ifs <;> simp_all
  | succ a ih =>
    have hlt : a < (W i).length := by omega
    rw [runPrefix_succ W i hlt, ih (by omega)]
    simp only [cover]
    by_cases hw : M.rejectedTailLength W i ≤ L
    · by_cases haJ : M.firstRejection W i ≤ a
      · have hm : a - M.firstRejection W i ≤ L := by unfold rejectedTailLength at hw; omega
        simp only [Cover.expect, hw, haJ, true_and, ite_true,
          show M.firstRejection W i ≤ a + 1 by omega, Cover.step]
        rw [dite_eq_left]
        · congr 3
          simp only [Fin.ext_iff]
          unfold rejectedTailLength at hw
          omega
        · refine
            ⟨by unfold rejectedTailLength at hw; omega,
                by simp only [min_lt_iff]; unfold rejectedTailLength; omega, ?_⟩
          simp only [min_eq_left hm,
            show M.firstRejection W i + (a - M.firstRejection W i) = a by omega]
          exact List.getElem?_eq_getElem hlt
      · have hra : M.rejected (M.runPrefix W i a) = false := hJ.2.2 a (by omega)
        simp only [Cover.expect, hw, haJ, true_and, ite_false, Cover.step, ite_true, hra]
        rw [← runPrefix_succ W i hlt]
        by_cases hJa : M.firstRejection W i = a + 1
        · rw [ite_eq_left (by rw [hJa]), ite_eq_left (by omega)]
          congr 3
          simp only [Fin.ext_iff, Fin.val_zero]
          omega
        · have hr1 : M.rejected (M.runPrefix W i (a + 1)) = false := hJ.2.2 (a + 1) (by omega)
          have hne : M.runPrefix W i (a + 1) ≠ M.runPrefix W i (M.firstRejection W i) := by
            intro he; rw [he, hJ.2.1] at hr1; exact Bool.noConfusion hr1
          rw [ite_eq_right hne, ite_eq_left hr1, ite_eq_right (by omega)]
    · simp only [Cover.expect, hw, false_and, ite_false, Cover.step]
      rw [runPrefix_succ W i hlt]

/-- The projection of the run of `W i` in the cover is the run of `W i` in the reader. -/
theorem cover_run (hW : M.IsHole W) (i : Fin k) {a : ℕ} (ha : a ≤ (W i).length) :
    coverProjection M W L ((cover M W L).runPrefix W i a) = M.runPrefix W i a := by
  rw [cover_runPrefix (hW.1 i) ha]
  unfold Cover.expect
  split_ifs with h
  · simp only [coverProjection]
    congr 1
    have : a - M.firstRejection W i ≤ L := by
      have := h.1; unfold rejectedTailLength at this; omega
    rw [min_eq_left this]
    omega
  · rfl

omit [DecidableEq α] [DecidableEq S] in
theorem cover_expect_ne_none (i : Fin k) (a : ℕ) : Cover.expect M W L i a ≠ none := by
  unfold Cover.expect; split_ifs <;> simp

/-- If the immortal rejected tails of a hole have length at most `L`, every coordinate of the
hole is fresh in its cover. -/
theorem cover_fresh [Finite α] [Finite S] (hW : M.IsHole W)
  (hL : ∀ i, M.Immortal (M.endState W i) → M.rejectedTailLength W i ≤ L) (i : Fin k) :
  (cover M W L).Fresh W i := by
  classical
  let := Fintype.ofFinite S
  classical
  let := Fintype.ofFinite α
  rw [fresh_iff]
  intro a ha
  simp only [endState]
  rw [cover_runPrefix (hW.1 i) ha.le, cover_runPrefix (hW.1 i) le_rfl]
  by_cases hw : M.rejectedTailLength W i ≤ L
  · have hJ := firstRejection_le (hW.1 i)
    unfold Cover.expect
    have hlen : M.rejectedTailLength W i = (W i).length - M.firstRejection W i := rfl
    simp only [hw, true_and, show M.firstRejection W i ≤ (W i).length from hJ, ite_true]
    split_ifs with h
    · simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, true_and, Sum.inr.injEq,
        Fin.ext_iff]
      omega
    · simp
  · have hm : ¬ M.Immortal (M.endState W i) := fun hi => hw (hL i hi)
    have hf := fresh_of_mortal (hW.1 i) hm
    rw [fresh_iff] at hf
    simp only [Cover.expect, hw, false_and, ite_false, ne_eq, Option.some.injEq,
      Prod.mk.injEq, true_and, Sum.inl.injEq]
    exact hf a ha

/-- A defined cover step commutes with the projection. -/
theorem coverProjection_step {c : CoverState S k L} {x : α} (h : Cover.step M W L c x ≠ none) :
    coverProjection M W L (Cover.step M W L c x) = M.step (coverProjection M W L c) x := by
  match c with
  | none => exact absurd rfl h
  | some (i, Sum.inl s) =>
    simp only [Cover.step] at h ⊢
    split_ifs at h ⊢ with h1 h2 h3 h4
    · simp only [coverProjection, Nat.add_zero, Fin.val_zero]; exact h3.symm
    · rfl
    · exact absurd rfl h
    · exact absurd rfl h
    · rfl
  | some (i, Sum.inr m) =>
    simp only [Cover.step] at h ⊢
    split_ifs at h ⊢ with h1
    · obtain ⟨_, h2, h3⟩ := h1
      have hlt : M.firstRejection W i + m < (W i).length := by
        rcases Nat.lt_or_ge (M.firstRejection W i + m) (W i).length with h4 | h4
        · exact h4
        · rw [List.getElem?_eq_none h4] at h3; exact absurd h3 (by simp)
      simp only [coverProjection]
      rw [show M.firstRejection W i + (m + 1) = M.firstRejection W i + m + 1 by omega,
          runPrefix_succ W i hlt]
      congr 1
      rw [List.getElem?_eq_getElem hlt] at h3
      exact Option.some.inj h3
    · exact absurd rfl h

theorem coverProjection_start (i : Fin k) :
    coverProjection M W L ((cover M W L).start i) = M.start i := by
  simp only [cover, Cover.start]
  split_ifs with h
  · simp only [coverProjection, h.2, Nat.add_zero, Fin.val_zero, runPrefix_zero]
  · rfl

/-- Along a run that avoids `none`, the projection follows the reader. -/
theorem coverProjection_runFrom (c : CoverState S k L) (u : List α)
    (h : ∀ a ≤ u.length, runFrom (cover M W L).step c (u.take a) ≠ none) :
    coverProjection M W L (runFrom (cover M W L).step c u) =
      runFrom M.step (coverProjection M W L c) u := by
  induction u generalizing c with
  | nil => rfl
  | cons x u ih =>
    have h1 : Cover.step M W L c x ≠ none := by simpa [cover] using h 1 (by simp)
    rw [runFrom_cons, runFrom_cons,
      ih _ (fun a ha => by simpa [cover] using h (a + 1) (by simp; omega))]
    exact congrArg (fun s => runFrom M.step s u) (coverProjection_step h1)

/-- A tuple that dominates a hole in its cover is a hole of the reader with the same
endpoints. -/
theorem cover_project_of_dom (hW : M.IsHole W) {U : Fin k → List α}
    (hU : Dominates (cover M W L) U W) : M.IsHole U ∧ ∀ i, M.endState U i = M.endState W i := by
  -- every cover state of `U` is a cover state of `W`
  have hvis : ∀ i a, a ≤ (U i).length →
      ∃ b ≤ (W i).length, (cover M W L).runPrefix U i a = (cover M W L).runPrefix W i b := by
    intro i a ha
    obtain ⟨b, hb, he⟩ :=
        mem_visitedStates.mp (hU.visitedStates_subset i (runPrefix_mem_visitedStates U i ha))
    exact ⟨b, hb, he.symm⟩
  have hnn : ∀ i a, a ≤ (U i).length → (cover M W L).runPrefix U i a ≠ none := by
    intro i a ha
    obtain ⟨b, hb, he⟩ := hvis i a ha
    rw [he, cover_runPrefix (hW.1 i) hb]
    exact cover_expect_ne_none i b
  have hproj : ∀ i a, a ≤ (U i).length →
      coverProjection M W L ((cover M W L).runPrefix U i a) = M.runPrefix U i a := by
    intro i a ha
    simp only [runPrefix]
    rw [coverProjection_runFrom _ _ (fun b hb => by
      rw [List.take_take]
      exact hnn i (min b a) (by omega)), coverProjection_start]
  have hstate : ∀ i a, a ≤ (U i).length → ∃ b ≤ (W i).length, M.runPrefix U i a =
      M.runPrefix W i b := by
    intro i a ha
    obtain ⟨b, hb, he⟩ := hvis i a ha
    exact ⟨b, hb, by rw [← hproj i a ha, he, cover_run hW i hb]⟩
  have hends : ∀ i, M.endState U i = M.endState W i := by
    intro i
    have h1 := hproj i _ le_rfl
    simp only [endState] at h1 ⊢
    rw [← h1, show (cover M W L).runPrefix U i (U i).length = (cover M W L).endState U i from rfl,
      hU.endState_eq i, show (cover M W L).endState W i =
          (cover M W L).runPrefix W i (W i).length from rfl,
      cover_run hW i le_rfl]
  refine ⟨⟨fun i => ⟨fun a ha => ?_, ?_⟩, fun i j pq hpq => ?_⟩, hends⟩
  · obtain ⟨b, hb, he⟩ := hstate i a ha
    rw [he]; exact (hW.1 i).1 b hb
  · rw [hends i]; exact (hW.1 i).2
  · obtain ⟨a, ha, b, hb, hp, rfl⟩ := mem_channel.mp hpq
    have hc := hU.channel_subset i j (pair_mem_channel ha hb hp)
    obtain ⟨a', ha', b', hb', hp', he⟩ := mem_channel.mp hc
    simp only [Prod.mk.injEq] at he
    have e1 : M.runPrefix U i a = M.runPrefix W i a' := by
      rw [← hproj i a ha, he.1, cover_run hW i ha']
    have e2 : M.runPrefix U j b = M.runPrefix W j b' := by
      rw [← hproj j b hb, he.2, cover_run hW j hb']
    simp only [e1, e2]
    exact hW.2 i j _ (pair_mem_channel ha' hb' hp')

/-- A fresh dominator of a hole in its cover is a hole of the reader with the same endpoints. -/
theorem cover_project (hW : M.IsHole W) {U : Fin k → List α}
    (hU : FreshDominates (cover M W L) U W) : M.IsHole U ∧ ∀ i, M.endState U i = M.endState W i :=
  cover_project_of_dom hW hU.1

/-! ## The small-hole theorem -/

section SmallHole

variable [Fintype α] [Fintype S]

omit [Fintype α] in
/-- A hole whose immortal rejected tails have length at most `L` gives a hole of total length
at most `freshTupleBound k (k · (N + L + 1) + 1)`: a fresh dominator of the hole in its
cover. -/
theorem exists_hole_totalLength_le_of_tails [Finite α] (M : StructuralReader α S k)
    {W : Fin k → List α}
    (hW : M.IsHole W) {L : ℕ}
    (hL : ∀ i, M.Immortal (M.endState W i) → M.rejectedTailLength W i ≤ L) :
    ∃ U, M.IsHole U ∧
      totalLength U ≤ Fresh.freshTupleBound k (k * (Fintype.card S + L + 1) + 1) := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨U, hU, hb⟩ := Fresh.exists_freshDominates_totalLength_le (cover_fresh hW hL)
  rw [cover_card] at hb
  exact ⟨U, (cover_project hW hU).1, hb⟩

/-- The small-hole bound for a reader over an alphabet of size `σ` with `k` starts and `N`
states: the fresh-tuple bound for the cover of a hole whose immortal rejected tails have
length at most `tailLengthBound σ k N`. -/
def smallHoleBound (σ k N : ℕ) : ℕ :=
  Fresh.freshTupleBound k (k * (N + Tail.tailLengthBound σ k N + 1) + 1)

/-- The small-hole theorem: a structural reader with `N` states and `k` starts over an alphabet
of size `σ` that has a hole has one of total length at most `smallHoleBound σ k N`. -/
theorem exists_small_hole (M : StructuralReader α S k) (h : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧ totalLength W ≤ smallHoleBound (Fintype.card α) k (Fintype.card S) := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨W', hW', hL⟩ := Tail.exists_hole_rejectedTailLength_le M hW
  exact exists_hole_totalLength_le_of_tails M hW' hL

/-- A reader has a hole exactly when it has one among the tuples of total length at most
`smallHoleBound σ k N`. -/
theorem exists_hole_iff_bounded (M : StructuralReader α S k) :
    (∃ W ∈ wordTuplesUpTo k (smallHoleBound (Fintype.card α) k (Fintype.card S)), M.IsHole W) ↔
      ∃ W, M.IsHole W := by
  constructor
  · rintro ⟨W, _, hW⟩; exact ⟨W, hW⟩
  · intro h
    obtain ⟨W, hW, hb⟩ := exists_small_hole M h
    exact ⟨W, mem_wordTuplesUpTo.mpr hb, hW⟩

/-- The existence of a hole is decidable: by the small-hole theorem it suffices to search the
tuples of total length at most `smallHoleBound σ k N`. -/
def decideHole (M : StructuralReader α S k) : Decidable (∃ W, M.IsHole W) :=
  decidable_of_iff _ (exists_hole_iff_bounded M)

end SmallHole

end DeciSigma1.Holes

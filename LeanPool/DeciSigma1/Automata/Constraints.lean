/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Automata.Basic
public import LeanPool.DeciSigma1.Constraints.Closure
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Run automata for flat constraints

For a flat constraint `Γ`, read with a covariant constructor, a configuration `(x, w)` is a
variable with a path, and the literals move configurations: `x ≤ y` copies `(x, w)` to `(y, w)`,
`f(a) ≤ x` pushes `(a i, w)` to `(x, i :: w)`, and `x ≤ f(a)` pops `(x, i :: w)` to `(a i, w)`
(`Move`). Two powerset automata over the child indices summarize the move derivations along a
path: the upper run `upperRun Γ x w` is the set of variables `b` such that `(x, w ++ σ)` reaches
`(b, σ)` by moves that do not touch `σ`, and the lower run `lowerRun Γ y w` the set of variables
`a` such that `(a, σ)` reaches `(y, w ++ σ)` in the same way (`upperRun_moves`, `lowerRun_moves`).
Every move derivation decomposes at a lowest point into an upper run and a lower run
(`lowest_point`). The runs are also the path judgments of the constraint (`lowerAt_iff_run`,
`upperAt_iff_run`).

The guarded product of two transition functions, which follows both runs while the pair of states
satisfies a guard, is the state space of the readers compiled from constraints.

## Main declarations

- `guardedPair`, `guardedStep`, `foldl_guardedStep`: guarded products of runs.
- `Config`, `Move`, `Moves`: configurations and move derivations.
- `upperStep`, `lowerStep`, `upper`, `lower`, `upperRun`, `lowerRun`: the run automata.
- `mem_upperRun_iff_moves`, `lowest_point`: runs as summaries of move derivations.
- `Constraints.lowerAt_iff_run`, `Constraints.upperAt_iff_run`: path judgments as runs.
-/

@[expose] public section


namespace DeciSigma1

open DeciSigma1.Constraints
namespace Automata

/-! ## Guarded products

The compiled readers run an upper and a lower automaton side by side and stop, in an absorbing
dead state, as soon as the pair of states fails a guard. -/

section Guarded

variable {α S T : Type}

/-- The pair `(s, t)` if it satisfies `good`, and the dead state `none` otherwise. -/
def guardedPair (good : S → T → Prop) [∀ s t, Decidable (good s t)] (s : S) (t : T) :
    Option (S × T) :=
  if good s t then some (s, t) else none

/-- One step of the product of the transition functions `f` and `g`, guarded by `good`; the
dead state `none` is absorbing. -/
def guardedStep (f : S → α → S) (g : T → α → T) (good : S → T → Prop)
    [∀ s t, Decidable (good s t)] : Option (S × T) → α → Option (S × T)
  | none, _ => none
  | some (s, t), a => guardedPair good (f s a) (g t a)

theorem forall_le_length_take_append_singleton {β : Type} (p : List β → Prop) (w : List β)
    (a : β) : (∀ j ≤ (w ++ [a]).length, p ((w ++ [a]).take j)) ↔
      (∀ j ≤ w.length, p (w.take j)) ∧ p (w ++ [a]) := by
  simp only [List.length_append, List.length_singleton]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · simpa [List.take_append_of_le_length hj] using h j (by omega)
    · have := h (w.length + 1) le_rfl
      rwa [List.take_of_length_le (by simp)] at this
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_or_ge w.length j with h3 | h3
    · rw [List.take_of_length_le (by simp; omega)]; exact h2
    · rw [List.take_append_of_le_length h3]; exact h1 j h3

variable (f : S → α → S) (g : T → α → T) (good : S → T → Prop) [∀ s t, Decidable (good s t)]

/-- The guarded product follows both runs as long as every prefix leads to a good pair, and
is dead afterward. -/
theorem foldl_guardedStep (s : S) (t : T) (w : List α) :
    w.foldl (guardedStep f g good) (guardedPair good s t) =
      if ∀ j ≤ w.length, good ((w.take j).foldl f s) ((w.take j).foldl g t) then
        some (w.foldl f s, w.foldl g t) else none := by
  induction w using List.reverseRecOn with
  | nil => simp [guardedPair]
  | append_singleton w a ih =>
    have key := forall_le_length_take_append_singleton
      (fun u => good (u.foldl f s) (u.foldl g t)) w a
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at key
    rw [List.foldl_append, ih]
    by_cases h : ∀ j ≤ w.length, good ((w.take j).foldl f s) ((w.take j).foldl g t)
    · by_cases h' : good (f (w.foldl f s) a) (g (w.foldl g t) a)
      · rw [ite_eq_left h, ite_eq_left (key.mpr ⟨h, h'⟩)]
        simp [guardedStep, guardedPair, h']
      · rw [ite_eq_left h, ite_eq_right (fun hk => h' (key.mp hk).2)]
        simp [guardedStep, guardedPair, h']
    · rw [ite_eq_right h, ite_eq_right (fun hk => h (key.mp hk).1)]
      rfl

theorem foldl_take_guardedStep_ne_none_iff (s : S) (t : T) {w : List α} {a : ℕ}
    (ha : a ≤ w.length) :
    (w.take a).foldl (guardedStep f g good) (guardedPair good s t) ≠ none ↔
      ∀ j ≤ a, good ((w.take j).foldl f s) ((w.take j).foldl g t) := by
  rw [foldl_guardedStep, List.length_take, Nat.min_eq_left ha]
  split_ifs with h
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    intro j hj
    simpa [List.take_take, Nat.min_eq_left hj] using h j hj
  · simp only [ne_eq, not_true_eq_false, false_iff]
    intro h'
    exact h fun j hj => by simpa [List.take_take, Nat.min_eq_left hj] using h' j hj

theorem foldl_guardedStep_eq_some (s : S) (t : T) {w : List α}
    (h : w.foldl (guardedStep f g good) (guardedPair good s t) ≠ none) :
    w.foldl (guardedStep f g good) (guardedPair good s t) = some (w.foldl f s, w.foldl g t) := by
  rw [foldl_guardedStep] at h ⊢
  split_ifs at h ⊢
  · rfl
  · exact absurd rfl h

end Guarded

/-! ## Configurations and moves -/

/-- A configuration `(x, w)`: the variable `x` with the path `w`. -/
abbrev Config (n : ℕ) (V : Type*) := V × List (Fin n)

/-- One move along a literal: `x ≤ y` copies `(x, w)` to `(y, w)`, `f(a) ≤ x` pushes `(a i, w)` to
`(x, i :: w)`, and `x ≤ f(a)` pops `(x, i :: w)` to `(a i, w)`. -/
inductive Move {n : ℕ} {V : Type*} (Γ : List (LitT n V)) : Config n V → Config n V → Prop
  | copy {u v w} : LitT.le u v ∈ Γ → Move Γ (u, w) (v, w)
  | push {a u w} (i : Fin n) : LitT.fLe a u ∈ Γ → Move Γ (a i, w) (u, i :: w)
  | pop {u a w} (i : Fin n) : LitT.leF u a ∈ Γ → Move Γ (u, i :: w) (a i, w)

/-- Derivations by moves. -/
abbrev Moves {n : ℕ} {V : Type*} (Γ : List (LitT n V)) : Config n V → Config n V → Prop :=
  Relation.ReflTransGen (Move Γ)

/-! ## The run automata -/

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem derivedPairs_refl (Γ : List (LitT n V)) (x : V) : (x, x) ∈ derivedPairs Γ :=
  (mem_derivedPairs Γ x x).mpr (.refl x)

theorem derivedPairs_trans {Γ : List (LitT n V)} {x y z : V}
    (h : (x, y) ∈ derivedPairs Γ) (h' : (y, z) ∈ derivedPairs Γ) : (x, z) ∈ derivedPairs Γ :=
  (mem_derivedPairs Γ x z).mpr
    (.trans ((mem_derivedPairs Γ x y).mp h) ((mem_derivedPairs Γ y z).mp h'))

/-- The variables derivably above `x`: the start state of the upper automaton. -/
def up (Γ : List (LitT n V)) (x : V) :
    Finset V := Finset.univ.filter fun y => (x, y) ∈ derivedPairs Γ
/-- The variables derivably below `y`: the start state of the lower automaton. -/
def down (Γ : List (LitT n V)) (y : V) :
    Finset V := Finset.univ.filter fun x => (x, y) ∈ derivedPairs Γ

/-- One step of the upper automaton: from the variables `P`, follow an upper constructor bound
`r ≤ f(b)` with `r ∈ P` to the child `b c`, and close upward. -/
def upperStep (Γ : List (LitT n V)) (P : Finset V) (c : Fin n) : Finset V :=
  Finset.univ.filter fun b => ∃ r ∈ P, ∃ p ∈ upperLits Γ, p.1 = r ∧ (p.2 c, b) ∈ derivedPairs Γ

/-- One step of the lower automaton: from the variables `Q`, follow a lower constructor bound
`f(a) ≤ r` with `r ∈ Q` to the child `a c`, and close downward. -/
def lowerStep (Γ : List (LitT n V)) (Q : Finset V) (c : Fin n) : Finset V :=
  Finset.univ.filter fun a => ∃ r ∈ Q, ∃ p ∈ lowerLits Γ, p.2 = r ∧ (a, p.1 c) ∈ derivedPairs Γ

/-- The upper automaton started at `x`. -/
def upper (Γ : List (LitT n V)) (x : V) : Semiautomaton (Fin n) (Finset V) :=
  ⟨up Γ x, upperStep Γ⟩
/-- The lower automaton started at `y`. -/
def lower (Γ : List (LitT n V)) (y : V) : Semiautomaton (Fin n) (Finset V) :=
  ⟨down Γ y, lowerStep Γ⟩
/-- The state of the upper automaton from `x` after reading `w`. -/
def upperRun (Γ : List (LitT n V)) (x : V) (w : List (Fin n)) : Finset V := (upper Γ x).run w
/-- The state of the lower automaton from `y` after reading `w`. -/
def lowerRun (Γ : List (LitT n V)) (y : V) (w : List (Fin n)) : Finset V := (lower Γ y).run w

@[simp] theorem mem_up {Γ : List (LitT n V)} {x y : V} :
    y ∈ up Γ x ↔ (x, y) ∈ derivedPairs Γ := by simp [up]
@[simp] theorem mem_down {Γ : List (LitT n V)} {x y : V} :
    x ∈ down Γ y ↔ (x, y) ∈ derivedPairs Γ := by simp [down]
@[simp] theorem mem_upperStep {Γ : List (LitT n V)} {S : Finset V} {c : Fin n} {b : V} :
    b ∈ upperStep Γ S c ↔ ∃ r ∈ S, ∃ bs, LitT.leF r bs ∈ Γ ∧
      ((bs c), b) ∈ derivedPairs Γ := by
  simp only [upperStep, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hr, ⟨u, bs⟩, hl, rfl, hd⟩
    exact ⟨u, hr, bs, (mem_upperLits Γ u bs).mp hl, hd⟩
  · rintro ⟨r, hr, bs, hl, hd⟩
    exact ⟨r, hr, (r, bs), (mem_upperLits Γ r bs).mpr hl, rfl, hd⟩
@[simp] theorem mem_lowerStep {Γ : List (LitT n V)} {S : Finset V} {c : Fin n} {a : V} :
    a ∈ lowerStep Γ S c ↔ ∃ r ∈ S, ∃ as, LitT.fLe as r ∈ Γ ∧
      (a, (as c)) ∈ derivedPairs Γ := by
  simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hr, ⟨as, u⟩, hl, rfl, hd⟩
    exact ⟨u, hr, as, (mem_lowerLits Γ as u).mp hl, hd⟩
  · rintro ⟨r, hr, as, hl, hd⟩
    exact ⟨r, hr, (as, r), (mem_lowerLits Γ as r).mpr hl, rfl, hd⟩
@[simp] theorem lowerRun_nil (Γ : List (LitT n V)) (x : V) : lowerRun Γ x [] = down Γ x := rfl
@[simp] theorem upperRun_snoc (Γ : List (LitT n V)) (x : V) (w : List (Fin n)) (c : Fin n) :
    upperRun Γ x (w ++ [c]) = upperStep Γ (upperRun Γ x w) c := by
  simp [upperRun, Semiautomaton.run, runFrom, List.foldl_append, upper]
@[simp] theorem lowerRun_snoc (Γ : List (LitT n V)) (x : V) (w : List (Fin n)) (c : Fin n) :
    lowerRun Γ x (w ++ [c]) = lowerStep Γ (lowerRun Γ x w) c := by
  simp [lowerRun, Semiautomaton.run, runFrom, List.foldl_append, lower]

@[simp] theorem upperStep_empty (Γ : List (LitT n V)) (c : Fin n) :
    upperStep Γ ∅ c = ∅ := by ext; simp

theorem upperRun_closed {Γ : List (LitT n V)} {x a b : V} {w : List (Fin n)}
    (ha : a ∈ upperRun Γ x w) (hab : (a, b) ∈ derivedPairs Γ) : b ∈ upperRun Γ x w := by
  cases w using List.reverseRecOn with
  | nil => exact mem_up.mpr (derivedPairs_trans (mem_up.mp ha) hab)
  | append_singleton w c =>
    rw [upperRun_snoc, mem_upperStep] at ha ⊢
    obtain ⟨r, hr, bs, hl, hd⟩ := ha
    exact ⟨r, hr, bs, hl, derivedPairs_trans hd hab⟩

theorem lowerRun_closed {Γ : List (LitT n V)} {y a b : V} {w : List (Fin n)}
    (ha : a ∈ lowerRun Γ y w) (hba : (b, a) ∈ derivedPairs Γ) : b ∈ lowerRun Γ y w := by
  cases w using List.reverseRecOn with
  | nil => exact mem_down.mpr (derivedPairs_trans hba (mem_down.mp ha))
  | append_singleton w c =>
    rw [lowerRun_snoc, mem_lowerStep] at ha ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := ha
    exact ⟨r, hr, as, hl, derivedPairs_trans hba hd⟩

/-- A derived inequality `a ≤ b` gives a move derivation from `(a, w)` to `(b, w)` for every path
`w`. -/
theorem derivedPairs_moves {Γ : List (LitT n V)} {a b : V} (h : (a, b) ∈ derivedPairs Γ)
    (w : List (Fin n)) : Moves Γ (a, w) (b, w) := by
  have hh := (mem_derivedPairs Γ a b).mp h
  clear h
  induction hh generalizing w with
  | refl => exact .refl
  | lit h => exact .single (.copy h)
  | trans _ _ ih₁ ih₂ => exact (ih₁ w).trans (ih₂ w)
  | decomp c hl _ hu ih => exact ((ih (c :: w)).head (.push c hl)).tail (.pop c hu)

/-- Every variable of an upper run is reached by moves above any suffix. -/
theorem upperRun_moves {Γ : List (LitT n V)} {x b : V} {β : List (Fin n)}
    (h : b ∈ upperRun Γ x β) (σ : List (Fin n)) : Moves Γ (x, β ++ σ) (b, σ) := by
  induction β using List.reverseRecOn generalizing b σ with
  | nil => exact derivedPairs_moves (mem_up.mp h) σ
  | append_singleton β c ih =>
    rw [upperRun_snoc, mem_upperStep] at h
    obtain ⟨r, hr, bs, hl, hd⟩ := h
    simpa [List.append_assoc] using
      ((ih hr (c :: σ)).tail (.pop c hl)).trans (derivedPairs_moves hd σ)

/-- Every variable of a lower run reaches its target by moves above any suffix. -/
theorem lowerRun_moves {Γ : List (LitT n V)} {y a : V} {γ : List (Fin n)}
    (h : a ∈ lowerRun Γ y γ) (σ : List (Fin n)) : Moves Γ (a, σ) (y, γ ++ σ) := by
  induction γ using List.reverseRecOn generalizing a σ with
  | nil => exact derivedPairs_moves (mem_down.mp h) σ
  | append_singleton γ c ih =>
    rw [lowerRun_snoc, mem_lowerStep] at h
    obtain ⟨r, hr, as, hl, hd⟩ := h
    simpa [List.append_assoc] using
      ((derivedPairs_moves hd σ).tail (.push c hl)).trans (ih hr (c :: σ))

/-- If `y ≤ z` is derived, the lower run of `y` is contained in that of `z`. -/
theorem lowerRun_target {Γ : List (LitT n V)} {y z a : V} {w : List (Fin n)}
    (hyz : (y, z) ∈ derivedPairs Γ) (h : a ∈ lowerRun Γ y w) : a ∈ lowerRun Γ z w := by
  induction w using List.reverseRecOn generalizing a with
  | nil => exact mem_down.mpr (derivedPairs_trans (mem_down.mp h) hyz)
  | append_singleton w c ih =>
    rw [lowerRun_snoc, mem_lowerStep] at h ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := h
    exact ⟨r, ih hr, as, hl, hd⟩

theorem lowerRun_push {Γ : List (LitT n V)} {as : Fin n → V} {y a : V} {w : List (Fin n)}
    (c : Fin n) (hl : LitT.fLe as y ∈ Γ) (h : a ∈ lowerRun Γ (as c) w) :
    a ∈ lowerRun Γ y (c :: w) := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    exact mem_lowerStep.mpr ⟨y, mem_down.mpr (derivedPairs_refl Γ y), as, hl, mem_down.mp h⟩
  | append_singleton w d ih =>
    rw [lowerRun_snoc, mem_lowerStep] at h
    change a ∈ lowerRun Γ y ((c :: w) ++ [d])
    rw [lowerRun_snoc, mem_lowerStep]
    obtain ⟨r, hr, bs, hb, hd⟩ := h
    exact ⟨r, ih hr, bs, hb, hd⟩

theorem lowerRun_pop {Γ : List (LitT n V)} {bs : Fin n → V} {y a : V} {w : List (Fin n)} (c : Fin n)
    (hu : LitT.leF y bs ∈ Γ) (h : a ∈ lowerRun Γ y (c :: w)) :
    a ∈ lowerRun Γ (bs c) w := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    obtain ⟨r, hr, as, hl, hd⟩ := mem_lowerStep.mp h
    exact mem_down.mpr (derivedPairs_trans hd ((mem_derivedPairs Γ _ _).mpr
      (.decomp c hl ((mem_derivedPairs Γ _ _).mp (mem_down.mp hr)) hu)))
  | append_singleton w d ih =>
    change a ∈ lowerRun Γ y ((c :: w) ++ [d]) at h
    rw [lowerRun_snoc, mem_lowerStep] at h ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := h
    exact ⟨r, ih hr, as, hl, hd⟩

/-- The common-suffix form of a lowest-point decomposition. -/
def Normal (Γ : List (LitT n V)) (x : V) (u : List (Fin n)) (y : V) (t : List (Fin n)) : Prop :=
  ∃ β γ σ v, u = β ++ σ ∧ t = γ ++ σ ∧ v ∈ upperRun Γ x β ∧ v ∈ lowerRun Γ y γ

theorem normal_step {Γ : List (LitT n V)} {x y z : V} {u t w : List (Fin n)}
    (h : Normal Γ x u y t) (hm : Move Γ (y, t) (z, w)) : Normal Γ x u z w := by
  obtain ⟨β, γ, σ, v, hu, ht, hp, hq⟩ := h
  cases hm with
  | copy hl =>
    exact ⟨β, γ, σ, v, hu, ht, hp, lowerRun_target ((mem_derivedPairs Γ _ _).mpr (.lit hl)) hq⟩
  | push c hl =>
    exact ⟨β, c :: γ, σ, v, hu, congrArg (List.cons c) ht, hp, lowerRun_push c hl hq⟩
  | @pop r as w c hl =>
    cases γ with
    | nil =>
      have hs : σ = c :: w := ht.symm
      refine ⟨β ++ [c], [], w, (as c), ?_, rfl, ?_, ?_⟩
      · simpa [hs, List.append_assoc] using hu
      · rw [upperRun_snoc, mem_upperStep]
        exact ⟨y, upperRun_closed hp (mem_down.mp hq), as, hl, derivedPairs_refl Γ _⟩
      · exact mem_down.mpr (derivedPairs_refl Γ _)
    | cons d γ =>
      have he := List.cons.inj ht
      obtain ⟨rfl, hw⟩ := he
      exact ⟨β, γ, σ, v, hu, hw, hp, lowerRun_pop c hl hq⟩

/-- Every move derivation has a lowest-point decomposition. -/
theorem moves_normal {Γ : List (LitT n V)} {a b : Config n V} (h : Moves Γ a b) :
    Normal Γ a.1 a.2 b.1 b.2 := by
  induction h with
  | refl => exact ⟨[], [], a.2, a.1, rfl, rfl,
      mem_up.mpr (derivedPairs_refl Γ _), mem_down.mpr (derivedPairs_refl Γ _)⟩
  | tail _ hm ih => exact normal_step ih hm

theorem normal_moves {Γ : List (LitT n V)} {x y : V} {u t : List (Fin n)}
    (h : Normal Γ x u y t) : Moves Γ (x, u) (y, t) := by
  obtain ⟨β, γ, σ, v, rfl, rfl, hp, hq⟩ := h
  exact (upperRun_moves hp σ).trans (lowerRun_moves hq σ)

/-- The upper run on `β` is the set of variables whose root is reached from `(x, β)` by moves. -/
theorem mem_upperRun_iff_moves {Γ : List (LitT n V)} {x b : V} (β : List (Fin n)) :
    b ∈ upperRun Γ x β ↔ Moves Γ (x, β) (b, []) := by
  constructor
  · intro h; simpa using upperRun_moves h []
  · intro h
    obtain ⟨β', γ, σ', v, he, hz, hp, hq⟩ := moves_normal h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hz.symm
    simp only [List.append_nil] at he
    subst β'
    exact upperRun_closed hp (mem_down.mp hq)

/-- A move derivation from `(x, u)` to `(y, t)` exists exactly when, for a common suffix
`u.drop s = t.drop e`, the upper run of `x` on `u.take s` meets the lower run of `y` on
`t.take e`. -/
theorem lowest_point {Γ : List (LitT n V)} {x y : V} {u t : List (Fin n)} :
    Moves Γ (x, u) (y, t) ↔ ∃ s ≤ u.length, ∃ e ≤ t.length,
      u.drop s = t.drop e ∧
      (upperRun Γ x (u.take s) ∩ lowerRun Γ y (t.take e)).Nonempty := by
  constructor
  · intro h
    obtain ⟨β, γ, σ, v, rfl, rfl, hp, hq⟩ := moves_normal h
    refine ⟨β.length, by simp, γ.length, by simp, ?_, ?_⟩
    · simp
    · simpa using
        (show (upperRun Γ x β ∩ lowerRun Γ y γ).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨hp, hq⟩⟩)
  · rintro ⟨s, _, e, _, he, v, hv⟩
    apply normal_moves
    exact ⟨u.take s, t.take e, u.drop s, v, (List.take_append_drop s u).symm,
      he ▸ (List.take_append_drop e t).symm, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩

end Automata
end DeciSigma1

namespace DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Lower path judgments are membership in the lower run. -/
theorem lowerAt_iff_run (Γ : List (LitT n V)) (π : List (Fin n)) (x y : V) :
    LowerAt Γ π x y ↔ x ∈ Automata.lowerRun Γ y π := by
  induction π using List.reverseRecOn generalizing x with
  | nil => simp [Automata.lowerRun, Automata.lower, Automata.Semiautomaton.run,
      runFrom, Automata.mem_down, mem_derivedPairs]
  | append_singleton π i ih =>
    rw [Automata.lowerRun_snoc, Automata.mem_lowerStep]
    constructor
    · intro h
      obtain ⟨r, hp, ht⟩ := h.factor
      cases ht with
      | cons hl hd ht =>
        exact ⟨_, Automata.lowerRun_closed ((ih _).mp hp) ((mem_derivedPairs Γ _ _).mpr hd),
          _, hl, (mem_derivedPairs Γ _ _).mpr (lowerAt_nil_iff.mp ht)⟩
    · rintro ⟨r, hr, a, hl, hd⟩
      have ht : LowerAt Γ [i] x r :=
        .cons hl (.refl _) (.nil ((mem_derivedPairs Γ _ _).mp hd))
      exact ht.comp ((ih _).mpr hr)

/-- Upper path judgments are membership in the upper run. -/
theorem upperAt_iff_run (Γ : List (LitT n V)) (π : List (Fin n)) (x y : V) :
    UpperAt Γ π x y ↔ y ∈ Automata.upperRun Γ x π := by
  induction π using List.reverseRecOn generalizing y with
  | nil => simp [Automata.upperRun, Automata.upper, Automata.Semiautomaton.run,
      runFrom, Automata.mem_up, mem_derivedPairs]
  | append_singleton π i ih =>
    rw [Automata.upperRun_snoc, Automata.mem_upperStep]
    constructor
    · intro h
      obtain ⟨r, hp, ht⟩ := h.factor
      cases ht with
      | cons hd hl ht =>
        exact ⟨_, Automata.upperRun_closed ((ih _).mp hp) ((mem_derivedPairs Γ _ _).mpr hd),
          _, hl, (mem_derivedPairs Γ _ _).mpr (upperAt_nil_iff.mp ht)⟩
    · rintro ⟨r, hr, a, hl, hd⟩
      have ht : UpperAt Γ [i] r y :=
        .cons (.refl _) hl (.nil ((mem_derivedPairs Γ _ _).mp hd))
      exact ((ih _).mpr hr).comp ht

end DeciSigma1.Constraints

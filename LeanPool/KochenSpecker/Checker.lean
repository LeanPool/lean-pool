/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

/- Lean Pool added documentation for the constraint fields. -/
module

public import Mathlib.Data.List.Basic

/-!
# A checked case-split refutation of Kochen–Specker colourings

A *system* is a list of pairs and a list of triads of natural-number labels. A *colouring* of a
system gives each label a truth value so that no pair has both labels `true` and every triad has
exactly one label `true`.

A `Refutation` is a binary tree of case splits. `refutes S ρ r` evaluates it under a partial
assignment `ρ`: `close` succeeds when `ρ` already violates some constraint (two `true`s on a pair
or a triad, or three `false`s on a triad), and `branch v t f` requires `t` to succeed with `v` set
`true` and `f` with `v` set `false`. `no_colouring_of_refutes` shows that a refutation accepted
from the empty assignment rules out every colouring. Refutations are generated outside Lean
(`scripts/peres33.py`) and checked here by the kernel; nothing computed outside Lean is trusted.

The method, a case-split tree over a list-based partial assignment checked with `decide`, is the
one used by M. Kernaghan's `lean-ks` (github.com/michaelkernaghan/contextuality), which the author
read before writing this file. This file was written separately: the constraints are explicit
pair and triad lists rather than an orthogonality test, a single `close` searches for any
violated constraint rather than naming one, and triads require exactly one `true`.
-/

@[expose] public section

namespace KochenSpecker

/-- A partial assignment of truth values to labels; the first entry for a label wins. -/
abbrev Partial := List (ℕ × Bool)

/-- The value a partial assignment gives a label, if any. -/
def valueOf : Partial → ℕ → Option Bool
  | [], _ => none
  | (w, b) :: ρ, v => if w = v then some b else valueOf ρ v

/-- Pairs and triads of labels. -/
structure Constraints where
  /-- Pairs that cannot both be true. -/
  pairs : List (ℕ × ℕ)
  /-- Triads in which exactly one label is true. -/
  triads : List (ℕ × ℕ × ℕ)

/-- `c` colours `S`: no pair is all `true`, and each triad has exactly one `true`. -/
def Colours (S : Constraints) (c : ℕ → Bool) : Prop :=
  (∀ p ∈ S.pairs, ¬ (c p.1 = true ∧ c p.2 = true)) ∧
  (∀ t ∈ S.triads, (c t.1 && !c t.2.1 && !c t.2.2) || (!c t.1 && c t.2.1 && !c t.2.2) ||
      (!c t.1 && !c t.2.1 && c t.2.2) = true)

/-- `c` extends the partial assignment `ρ`. -/
def Extends (c : ℕ → Bool) (ρ : Partial) : Prop := ∀ v b, valueOf ρ v = some b → c v = b

/-- The number of labels among three that `ρ` sets to `b`. -/
def countValue (ρ : Partial) (b : Bool) (t : ℕ × ℕ × ℕ) : ℕ :=
  (if valueOf ρ t.1 = some b then 1 else 0) + (if valueOf ρ t.2.1 = some b then 1 else 0) +
    (if valueOf ρ t.2.2 = some b then 1 else 0)

/-- `ρ` already violates a constraint of `S`. -/
def violated (S : Constraints) (ρ : Partial) : Bool :=
  S.pairs.any (fun p => valueOf ρ p.1 = some true ∧ valueOf ρ p.2 = some true) ||
    S.triads.any (fun t => 2 ≤ countValue ρ true t ∨ countValue ρ false t = 3)

/-- A case-split refutation. -/
inductive Refutation where
  | close
  | branch (v : ℕ) (t f : Refutation)

/-- Evaluate a refutation under a partial assignment. -/
def refutes (S : Constraints) : Partial → Refutation → Bool
  | ρ, .close => violated S ρ
  | ρ, .branch v t f => refutes S ((v, true) :: ρ) t && refutes S ((v, false) :: ρ) f

theorem Extends.cons {c : ℕ → Bool} {ρ : Partial} {v : ℕ} {b : Bool} (h : Extends c ρ)
    (hv : c v = b) : Extends c ((v, b) :: ρ) := by
  intro w b' hw
  simp only [valueOf] at hw
  split_ifs at hw with hvw
  · cases hw
    exact hvw ▸ hv
  · exact h w b' hw

/-- What `ρ` says about a label agrees with the colouring. -/
theorem valueOf_eq {c : ℕ → Bool} {ρ : Partial} (h : Extends c ρ) (v : ℕ) :
    valueOf ρ v = none ∨ valueOf ρ v = some (c v) := by
  rcases hl : valueOf ρ v with _ | b
  · exact Or.inl rfl
  · exact Or.inr (by rw [h v b hl])

/-- No constraint is violated by a partial assignment that a colouring extends. -/
theorem violated_eq_false {S : Constraints} {c : ℕ → Bool} {ρ : Partial} (hc : Colours S c)
    (h : Extends c ρ) : violated S ρ = false := by
  simp only [violated, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq]
  refine ⟨fun p hp ⟨h1, h2⟩ => hc.1 p hp ⟨h p.1 true h1, h p.2 true h2⟩, fun t ht => ?_⟩
  have h3 := hc.2 t ht
  rcases valueOf_eq h t.1 with e1 | e1 <;> rcases valueOf_eq h t.2.1 with e2 | e2 <;>
    rcases valueOf_eq h t.2.2 with e3 | e3 <;>
    · simp only [countValue, e1, e2, e3]
      cases hx : c t.1 <;> cases hy : c t.2.1 <;> cases hz : c t.2.2 <;> simp_all

/-- An accepted refutation leaves no colouring that extends `ρ`. -/
theorem not_extends_of_refutes (S : Constraints) {c : ℕ → Bool} (hc : Colours S c) :
    ∀ (cert : Refutation) (ρ : Partial), refutes S ρ cert = true → ¬ Extends c ρ
  | .close, ρ, hchk, h => by
    simp only [refutes] at hchk
    rw [violated_eq_false hc h] at hchk
    exact Bool.false_ne_true hchk
  | .branch v t f, ρ, hchk, h => by
    simp only [refutes, Bool.and_eq_true] at hchk
    cases hv : c v
    · exact not_extends_of_refutes S hc f _ hchk.2 (Extends.cons h hv)
    · exact not_extends_of_refutes S hc t _ hchk.1 (Extends.cons h hv)

/-- A refutation accepted from the empty assignment rules out every colouring. -/
theorem no_colouring_of_refutes (S : Constraints) (cert : Refutation)
    (h : refutes S [] cert = true) : ¬ ∃ c, Colours S c := by
  rintro ⟨c, hc⟩
  exact not_extends_of_refutes S hc cert [] h (fun _ _ hv => by simp [valueOf] at hv)

end KochenSpecker

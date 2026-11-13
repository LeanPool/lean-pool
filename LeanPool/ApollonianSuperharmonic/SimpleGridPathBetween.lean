/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: SimpleGridPathBetween]

/-!
# SimpleGridPathBetween

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A footprint graph $(V,E)$ is a simple nontrivial grid path from $x$ to $y$
when one list $p_0,\ldots,p_n$ without repeated vertices, with $n\geq1$,
simultaneously satisfies $p_0=x$, $p_n=y$, has vertex set exactly $V$, and
has edge set exactly the unordered pairs $\{p_j,p_{j+1}\}$.  Every
consecutive pair differs by one of $\pm1,\pm i$.
-/
def SimpleGridPathBetween (V : Set GaussianInt)
    (E : Set (Finset GaussianInt)) (x y : GaussianInt) : Prop :=
-- BODY
  ∃ p : List GaussianInt, p.Nodup ∧ 2 ≤ p.length ∧
    p.head? = some x ∧ p.getLast? = some y ∧
    V = (p.toFinset : Set GaussianInt) ∧
    (∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ →
        b = a + 1 ∨ b = a - 1 ∨
          b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) ∧
    ∀ e, e ∈ E ↔ ∃ a b : GaussianInt, ∃ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}

/-- Reversing a simple grid path preserves its vertices and undirected edges. -/
theorem SimpleGridPathBetween.reverse {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
    {x y : GaussianInt} (hp : SimpleGridPathBetween V E x y) : SimpleGridPathBetween V E y x := by
  classical
  rcases hp with ⟨p, hn, hl, hh, ht, hV, hs, he⟩
  have revstep : ∀ a b l₁ l₂, p.reverse = l₁ ++ a :: b :: l₂ →
      b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩ := by
    intro a b l₁ l₂ h
    have h' : p = l₂.reverse ++ b :: a :: l₁.reverse := by
      have := congrArg List.reverse h
      simpa [List.reverse_append, List.append_assoc] using this
    rcases hs b a _ _ h' with h | h | h | h
    · exact Or.inr (Or.inl (by rw [h]; simp))
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; simp)))
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; simp)))
  have revocc (q : List GaussianInt) (e : Finset GaussianInt)
      (ho : ∃ a b l₁ l₂, q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) :
      ∃ a b l₁ l₂, q.reverse = l₁ ++ a :: b :: l₂ ∧ e = {a, b} := by
    rcases ho with ⟨a, b, l₁, l₂, rfl, rfl⟩
    exact ⟨b, a, l₂.reverse, l₁.reverse,
      by simp [List.reverse_append, List.append_assoc], Finset.pair_comm _ _⟩
  refine ⟨p.reverse, List.nodup_reverse.mpr hn, by simpa using hl,
    by simpa using ht, by simpa using hh, by simpa using hV, revstep, ?_⟩
  intro e
  exact ⟨fun h => revocc p e ((he e).mp h), fun h =>
    (he e).mpr (by simpa using revocc p.reverse e h)⟩

end ApollonianSuperharmonic

end

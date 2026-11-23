/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import Mathlib.Data.Rat.Floor

/-!
# Finite denominator tuples and eventual greedy optimality

Authors of the mathematical results: Vjekoslav Kovač and Quanyu Tang.
List lengths count terms. A prefix of length `N` uses indices `0` through `N - 1`.
-/

@[expose] public section

namespace Egyptian

/-- The two ordering conventions for admissible denominator tuples. -/
inductive Convention where
  | weak
  | strict
  deriving DecidableEq, Repr

/-- The order relation on denominators in the chosen convention. -/
def Convention.rel : Convention → ℕ → ℕ → Prop
  | .weak => (· ≤ ·)
  | .strict => (· < ·)

/-- A rational unit fraction. Admissibility excludes zero denominators. -/
def unit (d : ℕ) : ℚ := 1 / (d : ℚ)

/-- The rational sum of the unit fractions in a finite denominator list. -/
def recipSum (ds : List ℕ) : ℚ := (ds.map unit).sum

/-- Ordered n-tuples with all denominators at least two and sum strictly below q. -/
def Admissible (σ : Convention) (q : ℚ) (n : ℕ) (ds : List ℕ) : Prop :=
  ds.length = n ∧ (∀ d ∈ ds, 2 ≤ d) ∧ ds.Pairwise σ.rel ∧ recipSum ds < q

/-- An attained maximum, expressed by comparison with every admissible rival. -/
def IsBest (σ : Convention) (q : ℚ) (n : ℕ) (ds : List ℕ) : Prop :=
  Admissible σ q n ds ∧ ∀ es, Admissible σ q n es → recipSum es ≤ recipSum ds

/-- The value R⁽σ⁾ₙ(q). Outside the domain of attained maxima the chosen default
is zero. The statement explicitly witnesses attainment at every occurrence of R. -/
noncomputable def bestValue (σ : Convention) (q : ℚ) (n : ℕ) : ℚ := by
  classical
  exact if h : ∃ ds, IsBest σ q n ds then recipSum h.choose else 0

/-- G(u) for a strict underapproximation (including the case of integral 1/u). -/
def greedyDen (u : ℚ) : ℕ := max 2 (⌊u⁻¹⌋₊ + 1)

/-- Greedy continuation with `lo` the smallest denominator allowed by the
preceding choice. Each selected term is subtracted before the next step. -/
def greedyFrom (σ : Convention) (u : ℚ) (lo : ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 =>
    let d := max lo (greedyDen u)
    let next := match σ with
      | .weak => d
      | .strict => d + 1
    d :: greedyFrom σ (u - unit d) next m

/-- The first `m` greedy choices for a fresh remainder, starting at denominator two. -/
def greedyTuple (σ : Convention) (u : ℚ) (m : ℕ) : List ℕ :=
  greedyFrom σ u 2 m

/-- Lean index k corresponds to paper index k+1. -/
def prefixTuple (a : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map a

/-- T₀ = T, T_{j+1} = Tⱼ(Tⱼ+1). -/
def unitIter (T : ℕ) : ℕ → ℕ
  | 0 => T
  | j + 1 => let s := unitIter T j; s * (s + 1)

/-- Theorem 1, including the single prefix that works at all later lengths. -/
def EventuallyGreedy : Prop :=
  ∀ (σ : Convention) (q : ℚ), 0 < q →
  ∃ (N : ℕ) (p : List ℕ), 1 ≤ N ∧ IsBest σ q N p ∧
    ∀ m : ℕ, 1 ≤ m →
      let u := q - bestValue σ q N
      let g := greedyTuple σ u m
      bestValue σ q (N + m) = bestValue σ q N + bestValue σ u m ∧
      IsBest σ u m g ∧
      (∀ ds, IsBest σ u m ds → ds = g) ∧
      IsBest σ q (N + m) (p ++ g)

end Egyptian

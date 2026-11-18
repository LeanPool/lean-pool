/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Data.Nat.Choose.Basic

/-!
# The binomial Ramsey bound, and a generic Pascal-recursive existence theorem

## Background: the classical bound

The Erdős–Szekeres proof of finite Ramsey-number existence is a double induction, showing that
any two-parameter family of "arrowing" statements `P n r s` (read: "every 2-colouring of a
size-`n` host finds a red witness of parameter `r` or a blue witness of parameter `s`") that
satisfies the handful of base cases and the one recursive-combination step every concrete Ramsey
formalisation ends up proving is automatically bounded by the binomial coefficient
`(r + s - 2).choose (r - 1)`. The graph-theoretic content, proving `P` satisfies that recursive
step for the actual 2-colour clique statement, is a separate, larger piece of
neighbourhood-counting combinatorics (a red/blue-degree pigeonhole argument) that is not part of
this file; see "Scope" below.

What is fully general, and is exactly what this file proves, is the induction skeleton itself,
abstracted away from any particular `P`. Any Pascal-recursive family, not just Ramsey numbers,
satisfying these hypotheses inherits the same binomial bound for free.

## Scope

This file does not reprove that the classical two-colour clique-Ramsey predicate itself satisfies
`le_binomialBound_of_pascalRecursive`'s hypotheses. In particular the recursive step, whose proof
needs a red/blue-degree pigeonhole argument over a host graph (not pure arithmetic), is proved
separately in `RamseyExistence.lean`, building on `RamseyProperty.lean`'s arrow semantics plus
mathlib's `SimpleGraph.degree`/`SimpleGraph.sum_degrees_eq_twice_card_edges` API. This file is pure
`Nat.choose` arithmetic with no graph theory and no dependency beyond
`Mathlib.Data.Nat.Choose.Basic`.

## Main declarations

* `Combinatorics.Ramsey.binomialBound r s`: the classical bound `(r + s - 2).choose (r - 1)`.
* `Combinatorics.Ramsey.binomialBound_succ_succ`: the shifted Pascal identity
  `binomialBound (r+2) (s+2) = binomialBound (r+1) (s+2) + binomialBound (r+2) (s+1)` that drives
  the induction below.
* `Combinatorics.Ramsey.le_binomialBound_of_pascalRecursive`: the generic theorem. Given a
  predicate `P : ℕ → ℕ → ℕ → Prop` satisfying the standard base cases and the standard recursive
  step, `P (binomialBound r s) r s` holds for every `r s`.

## References

* P. Erdős, G. Szekeres, *A combinatorial problem in geometry*, Compositio Math. 2 (1935), 463-470.

## Tags

ramsey theory, binomial coefficients, combinatorics
-/

@[expose] public section

namespace Combinatorics.Ramsey

/-- **The classical binomial Ramsey bound**, `(r + s - 2).choose (r - 1)`: the Erdős–Szekeres
upper bound that any Pascal-recursive two-parameter "arrowing" family satisfies. Pure `Nat`
arithmetic — no graph theory. -/
def binomialBound (r s : ℕ) : ℕ :=
  (r + s - 2).choose (r - 1)

@[simp]
theorem binomialBound_one_left (s : ℕ) : binomialBound 1 (s + 1) = 1 := by
  simp [binomialBound]

@[simp]
theorem binomialBound_one_right (r : ℕ) : binomialBound (r + 1) 1 = 1 := by
  simp [binomialBound]

/-- **The shifted Pascal identity.** `binomialBound` two steps up decomposes as the sum of the
two "one step up" values, i.e. Pascal's rule (`Nat.choose_succ_succ`) restated in the
`(r + s - 2).choose (r - 1)` shifted form the recursive existence theorem below needs. -/
theorem binomialBound_succ_succ (r s : ℕ) :
    binomialBound (r + 2) (s + 2) =
      binomialBound (r + 1) (s + 2) + binomialBound (r + 2) (s + 1) := by
  simp [binomialBound, show r + 2 + (s + 2) - 2 = r + s + 1 + 1 by omega,
    show r + 1 + (s + 2) - 2 = r + s + 1 by omega, show r + 2 + (s + 1) - 2 = r + s + 1 by omega,
    Nat.choose_succ_succ]

/-- **Positivity.** `binomialBound r s` is always positive: `r - 1 ≤ r + s - 2` whenever `s ≥ 1`,
so the binomial coefficient never vanishes for degenerate reasons on the arguments that matter
(`r ≥ 1`, `s ≥ 1`). -/
theorem binomialBound_pos {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) : 0 < binomialBound r s :=
  Nat.choose_pos (by omega)

/-- **The generic Pascal-recursive existence/upper-bound theorem.** Given a predicate
`P : ℕ → ℕ → ℕ → Prop` on (host size, red parameter, blue parameter) satisfying:

* `hRedZero`: the red parameter `0` is trivially satisfied at any host size;
* `hBlueZero`: the blue parameter `0` is trivially satisfied at any host size;
* `hOneRed`: host size `1` satisfies red parameter `1` against any blue parameter;
* `hOneBlue`: host size `1` satisfies blue parameter `1` against any red parameter;
* `hStep`: the recursive combination step — if a host of size `m` handles `(r, s + 1)` and a host
  of size `n` handles `(r + 1, s)`, then a host of size `m + n` (nonempty) handles `(r + 1, s + 1)`

then `P` holds at `binomialBound r s` for every `r s : ℕ`. This is the induction skeleton of the
classical Erdős–Szekeres Ramsey-number bound, abstracted away from any specific two-colour
"arrowing" predicate — any Pascal-recursive family inherits the same binomial bound.

Proved by strong induction on `r + s`: the five hypotheses are exactly the five cases `r = 0`,
`s = 0` (with `r ≥ 1`), `r = 1` (with `s ≥ 1`), `s = 1` (with `r ≥ 2`), and the recursive step
`r, s ≥ 2`, which combines the induction hypothesis at `(r - 1, s)` and at `(r, s - 1)` — both
strictly smaller in `r + s` — via `binomialBound_succ_succ`. -/
theorem le_binomialBound_of_pascalRecursive {P : ℕ → ℕ → ℕ → Prop}
    (hRedZero : ∀ n s, P n 0 s) (hBlueZero : ∀ n r, P n r 0)
    (hOneRed : ∀ s, P 1 1 s) (hOneBlue : ∀ r, P 1 r 1)
    (hStep : ∀ {m n r s : ℕ}, 0 < m + n → P m r (s + 1) → P n (r + 1) s →
      P (m + n) (r + 1) (s + 1)) :
    ∀ r s, P (binomialBound r s) r s
  | 0, s => hRedZero _ s
  | r + 1, 0 => hBlueZero _ (r + 1)
  | 1, s + 1 => by simpa using hOneRed (s + 1)
  | r + 2, 1 => by simpa using hOneBlue (r + 2)
  | r + 2, s + 2 => binomialBound_succ_succ r s ▸
      hStep ((binomialBound_pos (r := r + 1) (s := s + 2) (by omega) (by omega)).trans_le
        (Nat.le_add_right _ _))
        (le_binomialBound_of_pascalRecursive hRedZero hBlueZero hOneRed hOneBlue hStep _ _)
        (le_binomialBound_of_pascalRecursive hRedZero hBlueZero hOneRed hOneBlue hStep _ _)

/-! ### A worked example -/

/-- `binomialBound 3 3 = 6`: the classical bound on `R(3, 3)` computed directly from
`Nat.choose`. -/
theorem binomialBound_three_three : binomialBound 3 3 = 6 := by decide

end Combinatorics.Ramsey

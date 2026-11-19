/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.RamseyReservoir.RamseyBound
public import LeanPool.RamseyReservoir.Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Two-colour reservoirs and the Erdős–Szekeres bound

Colour the edges of a complete graph red (`G`) and blue (`Gᶜ`). A *two-colour reservoir* keeps a
red clique, a blue clique and a pool of vertices joined to every red-spine vertex in red and to
every blue-spine vertex in blue. A pool vertex `v` can be moved onto either spine: onto the red
spine (keeping its red neighbours) or onto the blue spine (keeping its blue neighbours). The two
retained pools partition the pool minus `v`.

This is the state machine behind the Erdős–Szekeres argument and the book algorithm of Campos,
Griffiths, Morris and Sahasrabudhe. With a threshold function `R : ℕ → ℕ → ℕ`, call a state
*winning* when its pool has at least `R (r - #red) (s - #blue)` vertices. If `R` satisfies Pascal's
inequality, some pivot from a winning state is again winning; following winning pivots reaches a
red `K_r` or a blue `K_s`. Any Pascal-superadditive function is therefore a Ramsey bound, and the
binomial coefficients give the Erdős–Szekeres bound.

## Main definitions

* `SimpleGraph.Bireservoir G`: a red clique, a blue clique and a common pool.
* `SimpleGraph.Bireservoir.redPivot`, `SimpleGraph.Bireservoir.bluePivot`: the two moves.
* `SimpleGraph.Bireservoir.IsWinning R r s`: the threshold potential is nonnegative.

## Main statements

* `SimpleGraph.Bireservoir.card_redPivot_pool_add_card_bluePivot_pool`: the two retained pools
  partition the pool minus the pivot.
* `SimpleGraph.Bireservoir.exists_of_ramseyBound`: a pool large enough for the missing cliques wins.
* `SimpleGraph.Bireservoir.IsWinning.exists_pivot`: from a winning state, a pivot keeps the state
  winning (the potential never runs out).
* `SimpleGraph.Bireservoir.IsWinning.exists_isNClique`: a winning state yields a red `K_r` or a blue
  `K_s`.
* `SimpleGraph.ramseyBound_of_pascal`, `SimpleGraph.ramseyNumber_le_of_isPascal`: every
  Pascal-superadditive threshold is a Ramsey bound, so it bounds FiniteRamsey's `ramseyNumber`.
* `SimpleGraph.isPascal_choose`, `SimpleGraph.ramseyBound_choose`: the binomial threshold is
  Pascal, hence **Erdős–Szekeres**, `R(r + 1, s + 1) ≤ C(r + s, r)`. This recovers, as one instance
  of the potential argument, the bound that FiniteRamsey proves by direct recursion
  (`SimpleGraph.ramsey_upper_bound`).
* `SimpleGraph.ramseyBound_four_pow`: `R(k + 1, k + 1) ≤ 4 ^ k`.
* `SimpleGraph.not_ramseyBound_five_three_three`, `SimpleGraph.ramseyNumber_three_three`:
  the five-cycle shows that `5` vertices do not suffice for `(3, 3)`, so
  `ramseyNumber ![3, 3] = 6`.

## References

* [P. Erdős, G. Szekeres, *A combinatorial problem in geometry*][ErdosSzekeres1935]
* [M. Campos, S. Griffiths, R. Morris, J. Sahasrabudhe, *An exponential improvement for diagonal
  Ramsey*][CamposGriffithsMorrisSahasrabudhe2026]
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A *two-colour reservoir*: a clique `red` of `G`, a clique `blue` of `Gᶜ`, and a pool joined to
`red` in `G` and to `blue` in `Gᶜ`. Since neither graph has loops, the pool is disjoint from both
spines (`SimpleGraph.Bireservoir.disjoint_red`, `SimpleGraph.Bireservoir.disjoint_blue`).

The red and blue spines are not required to be disjoint. States reached by pivots from `ofPool`
always have disjoint spines (a pivot moves a pool vertex, which lies on neither spine), but no
lemma here needs it, so the structure also describes states that no pivot walk reaches; for
example, with an empty pool, both spines can be the same single vertex. -/
structure Bireservoir where
  /-- The red spine, a clique of `G`. -/
  red : Finset V
  /-- The blue spine, a clique of `Gᶜ`. -/
  blue : Finset V
  /-- The common pool. -/
  pool : Finset V
  isClique_red : G.IsClique (red : Set V)
  isClique_blue : Gᶜ.IsClique (blue : Set V)
  adj_red : ∀ x ∈ red, ∀ y ∈ pool, G.Adj x y
  adj_blue : ∀ x ∈ blue, ∀ y ∈ pool, Gᶜ.Adj x y

namespace Bireservoir

variable {G}

/-- The two-colour reservoir with empty spines and pool `X`. -/
def ofPool (X : Finset V) : G.Bireservoir where
  red := ∅
  blue := ∅
  pool := X
  isClique_red := by simp
  isClique_blue := by simp
  adj_red := by simp
  adj_blue := by simp

/-- The starting state has an empty red spine. -/
@[simp] theorem ofPool_red (X : Finset V) : (ofPool (G := G) X).red = ∅ := rfl

/-- The starting state has an empty blue spine. -/
@[simp] theorem ofPool_blue (X : Finset V) : (ofPool (G := G) X).blue = ∅ := rfl

/-- The starting state's pool is the given set. -/
@[simp] theorem ofPool_pool (X : Finset V) : (ofPool (G := G) X).pool = X := rfl

variable (S : G.Bireservoir)

/-- The red half of a two-colour reservoir. -/
def toRed : G.Reservoir := ⟨S.red, S.pool, S.isClique_red, S.adj_red⟩

/-- The blue half of a two-colour reservoir, a reservoir of the complement. -/
def toBlue : Gᶜ.Reservoir := ⟨S.blue, S.pool, S.isClique_blue, S.adj_blue⟩

/-- The pool is disjoint from the red spine. -/
theorem disjoint_red : Disjoint S.red S.pool := S.toRed.disjoint

/-- The pool is disjoint from the blue spine. -/
theorem disjoint_blue : Disjoint S.blue S.pool := S.toBlue.disjoint

/-- The red reservoir's spine is the red clique. -/
@[simp] theorem toRed_spine : S.toRed.spine = S.red := rfl

/-- The red reservoir's pool is the common pool. -/
@[simp] theorem toRed_pool : S.toRed.pool = S.pool := rfl

/-- The blue reservoir's spine is the blue clique. -/
@[simp] theorem toBlue_spine : S.toBlue.spine = S.blue := rfl

/-- The blue reservoir's pool is the common pool. -/
@[simp] theorem toBlue_pool : S.toBlue.pool = S.pool := rfl

section Pivot

variable [DecidableEq V] [DecidableRel G.Adj] {v : V} (hv : v ∈ S.pool)

/-- Move `v` onto the red spine, keeping the pool vertices joined to `v` in red. -/
def redPivot : G.Bireservoir where
  red := (S.toRed.pivot v hv).spine
  blue := S.blue
  pool := (S.toRed.pivot v hv).pool
  isClique_red := (S.toRed.pivot v hv).isClique_spine
  isClique_blue := S.isClique_blue
  adj_red := (S.toRed.pivot v hv).adj
  adj_blue x hx y hy := S.adj_blue x hx y (S.toRed.pivot_pool_subset hv hy)

/-- Move `v` onto the blue spine, keeping the pool vertices joined to `v` in blue. -/
def bluePivot : G.Bireservoir where
  red := S.red
  blue := (S.toBlue.pivot v hv).spine
  pool := (S.toBlue.pivot v hv).pool
  isClique_red := S.isClique_red
  isClique_blue := (S.toBlue.pivot v hv).isClique_spine
  adj_red x hx y hy := S.adj_red x hx y (S.toBlue.pivot_pool_subset hv hy)
  adj_blue := (S.toBlue.pivot v hv).adj

/-- A red pivot adds the pivot vertex to the red clique. -/
@[simp] theorem redPivot_red : (S.redPivot hv).red = insert v S.red := rfl

/-- A red pivot keeps the blue clique. -/
@[simp] theorem redPivot_blue : (S.redPivot hv).blue = S.blue := rfl

/-- A red pivot keeps the pivot's red neighbours in the pool. -/
@[simp] theorem redPivot_pool : (S.redPivot hv).pool = {w ∈ S.pool | G.Adj v w} := rfl

/-- A blue pivot keeps the red clique. -/
@[simp] theorem bluePivot_red : (S.bluePivot hv).red = S.red := rfl

/-- A blue pivot adds the pivot vertex to the blue clique. -/
@[simp] theorem bluePivot_blue : (S.bluePivot hv).blue = insert v S.blue := rfl

/-- A blue pivot keeps the pivot's blue neighbours in the pool. -/
@[simp] theorem bluePivot_pool : (S.bluePivot hv).pool = {w ∈ S.pool | Gᶜ.Adj v w} := rfl

/-- A red pivot grows the red clique by one. -/
theorem card_redPivot_red : #(S.redPivot hv).red = #S.red + 1 :=
  S.toRed.card_pivot_spine hv

/-- A blue pivot grows the blue clique by one. -/
theorem card_bluePivot_blue : #(S.bluePivot hv).blue = #S.blue + 1 :=
  S.toBlue.card_pivot_spine hv

/-- **The two moves partition the pool.** Every pool vertex other than the pivot is kept by
exactly one of the two moves. -/
theorem card_redPivot_pool_add_card_bluePivot_pool :
    #(S.redPivot hv).pool + #(S.bluePivot hv).pool + 1 = #S.pool := by
  have h := card_filter_add_card_filter_not (s := S.pool) (G.Adj v)
  have hblue : {w ∈ S.pool | ¬G.Adj v w} = insert v {w ∈ S.pool | Gᶜ.Adj v w} := by
    ext w
    by_cases hw : w = v
    · subst hw; simp [hv]
    · simp [hw, compl_adj, Ne.symm hw]
  rw [hblue, card_insert_of_notMem (by simp)] at h
  simp only [redPivot_pool, bluePivot_pool]
  omega

/-- One of the two moves keeps at least half of the remaining pool. -/
theorem card_pool_le_two_mul_max :
    #S.pool ≤ 2 * max #(S.redPivot hv).pool #(S.bluePivot hv).pool + 1 := by
  have := S.card_redPivot_pool_add_card_bluePivot_pool hv
  omega

end Pivot

/-! ### Winning -/

/-- A clique of size at least `r` contains an `r`-clique. -/
theorem _root_.SimpleGraph.IsClique.exists_isNClique_subset {H : SimpleGraph V} {s : Finset V}
    (hs : H.IsClique (s : Set V)) {r : ℕ} (hr : r ≤ #s) : ∃ t ⊆ s, H.IsNClique r t := by
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq hr
  exact ⟨t, hts, ⟨hs.subset (by simpa using hts), ht⟩⟩

/-- **Large pools win.** If the pool has at least `n` vertices and `RamseyBound n (r - #red)
(s - #blue)`, then `G` has an `r`-clique or `Gᶜ` has an `s`-clique. -/
theorem exists_of_ramseyBound {n r s : ℕ} (h : RamseyBound n (r - #S.red) (s - #S.blue))
    (hn : n ≤ #S.pool) : (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t := by
  classical
  rcases h.exists_isNClique_subset G hn with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
  · have hu := S.toRed.isNClique_union hc ht
    obtain ⟨u, -, hu⟩ := hu.isClique.exists_isNClique_subset (r := r) (by
      rw [hu.card_eq, toRed_spine]; omega)
    exact .inl ⟨u, hu⟩
  · have hu := S.toBlue.isNClique_union hc ht
    obtain ⟨u, -, hu⟩ := hu.isClique.exists_isNClique_subset (r := s) (by
      rw [hu.card_eq, toBlue_spine]; omega)
    exact .inr ⟨u, hu⟩

/-- The state `S` is *winning* for the target `(r, s)` with threshold `R` when its pool has at
least `R (r - #red) (s - #blue)` vertices. -/
def IsWinning (R : ℕ → ℕ → ℕ) (r s : ℕ) : Prop :=
  R (r - #S.red) (s - #S.blue) ≤ #S.pool

/-- A threshold `R` satisfies *Pascal's inequality* if `R a (b + 1) + R (a + 1) b ≤
R (a + 1) (b + 1)` and `R (a + 1) (b + 1)` is positive. -/
def _root_.SimpleGraph.IsPascal (R : ℕ → ℕ → ℕ) : Prop :=
  ∀ a b, R a (b + 1) + R (a + 1) b ≤ R (a + 1) (b + 1) ∧ 0 < R (a + 1) (b + 1)

variable {S}

/-- **The potential never runs out.** From a winning state whose spines are both short of the
target, one of the two pivots at some pool vertex is again winning. -/
theorem IsWinning.exists_pivot [DecidableEq V] [DecidableRel G.Adj] {R : ℕ → ℕ → ℕ} {r s : ℕ}
    (hR : IsPascal R) (hS : S.IsWinning R r s) (hr : #S.red < r) (hs : #S.blue < s) :
    ∃ v, ∃ hv : v ∈ S.pool,
      (S.redPivot hv).IsWinning R r s ∨ (S.bluePivot hv).IsWinning R r s := by
  obtain ⟨a, ha⟩ : ∃ a, r - #S.red = a + 1 := ⟨r - #S.red - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, s - #S.blue = b + 1 := ⟨s - #S.blue - 1, by omega⟩
  unfold IsWinning at hS
  rw [ha, hb] at hS
  obtain ⟨hpas, hpos⟩ := hR a b
  obtain ⟨v, hv⟩ := card_pos.mp (hpos.trans_le hS)
  refine ⟨v, hv, ?_⟩
  have hpart := S.card_redPivot_pool_add_card_bluePivot_pool hv
  unfold IsWinning
  rw [card_redPivot_red, redPivot_blue, bluePivot_red, card_bluePivot_blue,
    show r - (#S.red + 1) = a by omega, show s - (#S.blue + 1) = b by omega, hb, ha]
  omega

/-- **Winning states win.** Following winning pivots from a winning state reaches a red `K_r` or a
blue `K_s`. -/
theorem IsWinning.exists_isNClique {R : ℕ → ℕ → ℕ} {r s : ℕ} (hR : IsPascal R)
    (hS : S.IsWinning R r s) : (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t := by
  classical
  induction hn : #S.pool using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hr : r ≤ #S.red
    · obtain ⟨t, -, ht⟩ := S.isClique_red.exists_isNClique_subset hr
      exact .inl ⟨t, ht⟩
    by_cases hs : s ≤ #S.blue
    · obtain ⟨t, -, ht⟩ := S.isClique_blue.exists_isNClique_subset hs
      exact .inr ⟨t, ht⟩
    obtain ⟨v, hv, h | h⟩ := hS.exists_pivot hR (by omega) (by omega)
    · refine ih _ ?_ h rfl
      have := S.card_redPivot_pool_add_card_bluePivot_pool hv
      omega
    · refine ih _ ?_ h rfl
      have := S.card_redPivot_pool_add_card_bluePivot_pool hv
      omega

end Bireservoir

/-! ### Ramsey bounds from the reservoir walk -/

/-- **Pascal thresholds are Ramsey bounds.** If `R` satisfies Pascal's inequality, then
`R r s` is a Ramsey bound for `(r, s)`. -/
theorem ramseyBound_of_pascal {R : ℕ → ℕ → ℕ} (hR : IsPascal R) (r s : ℕ) :
    RamseyBound (R r s) r s := fun G =>
  Bireservoir.IsWinning.exists_isNClique (S := Bireservoir.ofPool (G := G) univ) hR
    (by simp [Bireservoir.IsWinning])

/-- **Pascal thresholds bound the Ramsey number.** If `R` satisfies Pascal's inequality, then
FiniteRamsey's `ramseyNumber ![r, s]` is at most `R r s`. -/
theorem ramseyNumber_le_of_isPascal {R : ℕ → ℕ → ℕ} (hR : IsPascal R) (r s : ℕ) :
    ramseyNumber ![r, s] ≤ R r s :=
  ramseyBound_iff_ramseyNumber_le.mp (ramseyBound_of_pascal hR r s)

/-- The binomial threshold `C(a + b - 2, a - 1)`, extended by zero when `a = 0` or `b = 0`,
satisfies Pascal's inequality. -/
theorem isPascal_choose :
    IsPascal fun a b => if a = 0 ∨ b = 0 then 0 else (a + b - 2).choose (a - 1) := by
  intro a b
  refine ⟨?_, by simpa using Nat.choose_pos (by omega)⟩
  rcases a with _ | a <;> rcases b with _ | b
  · simp
  · simp
  · simp
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, or_self, ↓reduceIte,
      add_tsub_cancel_right]
    rw [show a + 1 + (b + 1 + 1) - 2 = a + b + 1 by omega,
      show a + 1 + 1 + (b + 1) - 2 = a + b + 1 by omega,
      show a + 1 + 1 + (b + 1 + 1) - 2 = a + b + 1 + 1 by omega]
    exact (Nat.choose_succ_succ' _ _).ge

/-- **Erdős–Szekeres.** `R(r + 1, s + 1) ≤ C(r + s, r)`, as the binomial instance of the Pascal
potential argument. FiniteRamsey proves the same bound by direct recursion as
`SimpleGraph.ramsey_upper_bound`; here it is a corollary of `ramseyBound_of_pascal`. -/
theorem ramseyBound_choose (r s : ℕ) : RamseyBound ((r + s).choose r) (r + 1) (s + 1) := by
  simpa [show r + 1 + (s + 1) - 2 = r + s by omega] using
    ramseyBound_of_pascal isPascal_choose (r + 1) (s + 1)

/-- The diagonal Erdős–Szekeres bound `R(k + 1, k + 1) ≤ 4 ^ k`. -/
theorem ramseyBound_four_pow (k : ℕ) : RamseyBound (4 ^ k) (k + 1) (k + 1) :=
  (ramseyBound_choose k k).mono (by rw [← two_mul]; exact Nat.centralBinom_le_four_pow k)

/-- `R(3, 3) ≤ 6`. -/
theorem ramseyBound_six_three_three : RamseyBound 6 3 3 := ramseyBound_choose 2 2

/-- `R(3, 3) > 5`: the five-cycle has no triangle and neither does its complement. -/
theorem not_ramseyBound_five_three_three : ¬RamseyBound 5 3 3 := by
  intro h
  have hfree : (cycleGraph 5).CliqueFree 3 ∧ (cycleGraph 5)ᶜ.CliqueFree 3 := by
    constructor <;>
    · intro t ht
      rw [is3Clique_iff] at ht
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
      revert a b c
      decide
  rcases h (cycleGraph 5) with ⟨t, ht⟩ | ⟨t, ht⟩
  exacts [hfree.1 t ht, hfree.2 t ht]

/-- **`R(3, 3) = 6`** for FiniteRamsey's Ramsey number. -/
theorem ramseyNumber_three_three : ramseyNumber ![3, 3] = 6 := by
  refine le_antisymm (ramseyBound_iff_ramseyNumber_le.mp ramseyBound_six_three_three) ?_
  by_contra! h
  exact not_ramseyBound_five_three_three (ramseyBound_iff_ramseyNumber_le.mpr (by omega))

end SimpleGraph

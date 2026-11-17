/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.DigraphTournament
import Mathlib.Tactic.IntervalCases

/-!
# Tournament Ramsey numbers

The tournament Ramsey number is the least `n` such that every tournament on `n` vertices contains
a transitive subtournament of a given order `k`. It is bounded above by the classical Erdős–Moser
doubling argument: a tournament on `2m` vertices, where `m` already forces a transitive
`(k + 1)`-subtournament, itself forces a transitive `(k + 2)`-subtournament, by pigeonholing on
which side of an arbitrary vertex `v` a majority of the other vertices falls.

## Main declarations

* `Digraph.ForcesTransitive n k`: every tournament, restricted to any `Finset` of at least `n`
  vertices, has a transitive sub-`Finset` of size exactly `k`.
* `Digraph.erdosMoserBound k`: the closed-form bound `2 ^ (k - 1)`.
* `Digraph.forcesTransitive_bound`: the classical Erdős–Moser doubling induction,
  `ForcesTransitive (erdosMoserBound k) k` for every `k ≥ 1`.
* `Digraph.exists_forcesTransitive`: unconditional existence, for every `k`, of a vertex count
  forcing a transitive `k`-subtournament, i.e. Ramsey's theorem for tournaments.
* `Digraph.tournamentRamseyNumber`: the tournament Ramsey number itself, via `Nat.find` on the
  existence theorem, with its defining spec/minimality/monotonicity lemmas.
* `Digraph.tournamentRamseyNumber_zero`/`_one`/`_two`/`_three`: the four smallest values,
  including the two genuine computations `tournamentRamseyNumber 2 = 2` and
  `tournamentRamseyNumber 3 = 4` (Erdős–Moser / Stearns).

## References

* R. Stearns, *The voting problem*, Amer. Math. Monthly 66 (1959), 761-763.
* P. Erdős, L. Moser, *On the representation of directed graphs as unions of orderings*, Magyar
  Tud. Akad. Mat. Kutató Int. Közl. 9 (1964), 125-132.

## Tags

ramsey theory, tournament, digraph
-/

@[expose] public section

namespace Digraph

/-! ## The existence induction -/

/-- `ForcesTransitive n k`: every tournament on an ambient vertex type, restricted to any
`Finset` `U` of at least `n` vertices, has a transitive sub-`Finset` of `U` of size exactly `k`.
Stated over an arbitrary `Finset U` of an arbitrary ambient type (rather than fixed to `Fin n`) so
the inductive step below can recurse on a smaller `Finset` of the *same* tournament, with no
re-indexing into a smaller `Fin m`.

`V` is `Type` rather than `Type*`: the whole induction stays within one ambient vertex type fixed
by the outermost quantifier (the recursive step never changes types, only takes smaller `Finset`s
of the same `V`), so universe polymorphism buys nothing here and instead leaves unresolved
universe metavariables at the induction's recursive call. -/
def ForcesTransitive (n k : Nat) : Prop :=
  ∀ {V : Type} {G : Digraph V}, G.IsTournament → ∀ U : Finset V, n ≤ U.card →
    ∃ S ⊆ U, S.card = k ∧ G.IsTransitiveOn (↑S : Set V)

/-- Base case `k = 0`: the empty set always works, for any `U` (in particular `n = 0`). -/
theorem forcesTransitive_zero : ForcesTransitive 0 0 :=
  fun _ U _ => ⟨∅, U.empty_subset, rfl, by simp⟩

/-- Base case `k = 1`: any single vertex of a nonempty `U` works, so `n = 1` suffices. -/
theorem forcesTransitive_one : ForcesTransitive 1 1 := fun hT U hU =>
  let ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  ⟨{v}, Finset.singleton_subset_iff.mpr hv, Finset.card_singleton v,
    by simpa using isTransitiveOn_singleton hT v⟩

/-- The classical Erdős–Moser bound: `erdosMoserBound k = 2 ^ (k - 1)` vertices force a transitive
`k`-subtournament, for `k ≥ 1`. -/
def erdosMoserBound (k : Nat) : Nat := 2 ^ (k - 1)

theorem erdosMoserBound_succ_succ (k : Nat) :
    erdosMoserBound (k + 2) = 2 * erdosMoserBound (k + 1) :=
  pow_succ' 2 k

theorem one_le_erdosMoserBound (k : Nat) : 1 ≤ erdosMoserBound k :=
  Nat.one_le_two_pow

/-- **The inductive step.** Doubling the vertex count lets us find one more vertex for the
transitive subtournament: split the ambient set (minus an arbitrary pivot `v`) into the vertices
`v` beats and the vertices that beat `v`; one side has at least `m` vertices, so the induction
hypothesis finds a transitive `(k + 1)`-subtournament there, and `v` extends it (at the bottom or
top respectively, since it is comparable with every member in the same direction). -/
theorem forcesTransitive_succ {m k : Nat} (hm : 1 ≤ m) (ih : ForcesTransitive m (k + 1)) :
    ForcesTransitive (2 * m) (k + 2) := by
  intro V G hT U hU
  classical
  obtain ⟨v, hvU⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  -- recurse on a side of `v` with at least `m` vertices; `v` then extends the transitive set
  have key (W : Finset V) (hW : W ⊆ U.erase v)
      (hside : (∀ u ∈ W, G.Adj u v) ∨ ∀ u ∈ W, G.Adj v u) (hbig : m ≤ W.card) :
      ∃ S ⊆ U, S.card = k + 2 ∧ G.IsTransitiveOn ↑S := by
    obtain ⟨S, hSW, hScard, hS⟩ := ih hT W hbig
    have hvS : v ∉ S := fun hv => (Finset.mem_erase.mp (hW (hSW hv))).1 rfl
    refine ⟨insert v S, Finset.insert_subset hvU ((hSW.trans hW).trans (Finset.erase_subset _ _)),
      by rw [Finset.card_insert_of_notMem hvS, hScard], ?_⟩
    rw [Finset.coe_insert]
    exact hS.insert_of_forall_adj hT
      (hside.imp (fun h u hu => h u (hSW hu)) fun h u hu => h u (hSW hu))
  let Uin := (U.erase v).filter (G.Adj · v)
  let Uout := (U.erase v).filter (¬G.Adj · v)
  have hsplit : Uin.card + Uout.card = (U.erase v).card :=
    Finset.card_filter_add_card_filter_not _
  rw [Finset.card_erase_of_mem hvU] at hsplit
  by_cases hin : m ≤ Uin.card
  · exact key Uin (Finset.filter_subset _ _) (.inl fun u hu => (Finset.mem_filter.mp hu).2) hin
  · refine key Uout (Finset.filter_subset _ _) (.inr fun u hu => ?_) (by omega)
    obtain ⟨hu, hnot⟩ := Finset.mem_filter.mp hu
    exact (hT.total_of_ne (Finset.ne_of_mem_erase hu)).resolve_left hnot



/-- `erdosMoserBound k` forces a transitive `k`-subtournament, for every `k ≥ 1`, by induction:
the base case is `forcesTransitive_one`, and the step is exactly `forcesTransitive_succ`. -/
theorem forcesTransitive_bound : ∀ k : Nat, ForcesTransitive (erdosMoserBound (k + 1)) (k + 1)
  | 0 => forcesTransitive_one
  | k + 1 => erdosMoserBound_succ_succ k ▸
      forcesTransitive_succ (one_le_erdosMoserBound (k + 1)) (forcesTransitive_bound k)

/-- Every `k` has *some* forcing bound: `n = 0` for `k = 0` (trivially, the empty set), and
`n = erdosMoserBound k` for `k ≥ 1`. -/
theorem exists_forcesTransitive : ∀ k : Nat, ∃ n : Nat, ForcesTransitive n k
  | 0 => ⟨0, forcesTransitive_zero⟩
  | k + 1 => ⟨erdosMoserBound (k + 1), forcesTransitive_bound k⟩

/-- Specialise a `ForcesTransitive` bound to the full vertex set of `Fin n`: every tournament on
`Fin n` itself has a transitive `k`-subtournament. -/
theorem forall_of_forcesTransitive {n k : Nat} (h : ForcesTransitive n k) :
    ∀ {G : Digraph (Fin n)}, G.IsTournament →
      ∃ S : Finset (Fin n), S.card = k ∧ G.IsTransitiveOn (↑S : Set (Fin n)) := fun hT =>
  let ⟨S, _, hS⟩ := h hT Finset.univ (by simp)
  ⟨S, hS⟩

/-- **The existence statement**: for every `k` there is an `n` such that every tournament on
`Fin n` has a transitive `k`-subtournament. -/
theorem exists_transitiveSub (k : Nat) :
    ∃ n : Nat, ∀ {G : Digraph (Fin n)}, G.IsTournament →
      ∃ S : Finset (Fin n), S.card = k ∧ G.IsTransitiveOn (↑S : Set (Fin n)) :=
  (exists_forcesTransitive k).imp fun _ => forall_of_forcesTransitive

/-- A cardinality obstruction: if `n < k`, no tournament on `Fin n` can guarantee a transitive
`k`-subtournament, since `Fin n` does not even have `k` vertices to draw one from. This gives the
easy half (`tournamentRamseyNumber k ≥ k`) of every tournament Ramsey number for free, only
needing `linearOrder` to inhabit a tournament on `Fin n` at all. -/
theorem not_forall_of_lt_card {k n : Nat} (hn : n < k) :
    ¬ ∀ {G : Digraph (Fin n)}, G.IsTournament →
        ∃ S : Finset (Fin n), S.card = k ∧ G.IsTransitiveOn (↑S : Set (Fin n)) := by
  intro hcon
  obtain ⟨S, hScard, -⟩ := hcon (isTournament_linearOrder n)
  have := hScard ▸ S.card_le_univ
  simp only [Fintype.card_fin] at this
  omega

/-! ## The tournament Ramsey number -/

open Classical in
/-- **The tournament Ramsey number** (Erdős–Moser / Stearns): the least `n` such that every
tournament on `Fin n` has a transitive subtournament of order `k`. -/
noncomputable def tournamentRamseyNumber (k : Nat) : Nat :=
  Nat.find (exists_transitiveSub k)

open Classical in
/-- Defining property: every tournament on `tournamentRamseyNumber k` vertices has a transitive
`k`-subtournament. -/
theorem tournamentRamseyNumber_spec (k : Nat) {G : Digraph (Fin (tournamentRamseyNumber k))}
    (hT : G.IsTournament) :
    ∃ S : Finset (Fin (tournamentRamseyNumber k)),
      S.card = k ∧ G.IsTransitiveOn (↑S : Set (Fin (tournamentRamseyNumber k))) :=
  Nat.find_spec (exists_transitiveSub k) hT

open Classical in
/-- Minimality: for `n < tournamentRamseyNumber k`, some tournament on `Fin n` has *no*
transitive `k`-subtournament. -/
theorem tournamentRamseyNumber_min {k n : Nat} (hn : n < tournamentRamseyNumber k) :
    ∃ G : Digraph (Fin n), G.IsTournament ∧
      ∀ S : Finset (Fin n), S.card = k → ¬ G.IsTransitiveOn (↑S : Set (Fin n)) := by
  by_contra! hcon
  exact Nat.find_min (exists_transitiveSub k) hn fun hT => hcon _ hT

open Classical in
/-- Upper-bound form of minimality: if some `n` already has the "every tournament has a
transitive `k`-subtournament" property, then `tournamentRamseyNumber k ≤ n`. -/
theorem tournamentRamseyNumber_le {k n : Nat}
    (h : ∀ {G : Digraph (Fin n)}, G.IsTournament →
      ∃ S : Finset (Fin n), S.card = k ∧ G.IsTransitiveOn (↑S : Set (Fin n))) :
    tournamentRamseyNumber k ≤ n :=
  Nat.find_min' (exists_transitiveSub k) h

/-- **Monotonicity.** Forcing a larger transitive subtournament needs at least as many vertices. -/
theorem tournamentRamseyNumber_mono {j k : Nat} (hjk : j ≤ k) :
    tournamentRamseyNumber j ≤ tournamentRamseyNumber k :=
  tournamentRamseyNumber_le fun hT =>
    let ⟨_, hScard, hS⟩ := tournamentRamseyNumber_spec k hT
    let ⟨S', hS'S, hS'card⟩ := Finset.exists_subset_card_eq (hjk.trans_eq hScard.symm)
    ⟨S', hS'card, hS.mono (Finset.coe_subset.mpr hS'S)⟩

theorem tournamentRamseyNumber_zero : tournamentRamseyNumber 0 = 0 :=
  le_antisymm (tournamentRamseyNumber_le (n := 0) (fun {_} _ => ⟨∅, rfl, by simp⟩)) (by omega)

open Classical in
theorem tournamentRamseyNumber_one : tournamentRamseyNumber 1 = 1 := by
  unfold tournamentRamseyNumber
  rw [Nat.find_eq_iff]
  refine ⟨forall_of_forcesTransitive forcesTransitive_one, fun n hn => ?_⟩
  exact not_forall_of_lt_card (k := 1) (n := n) (by omega)

open Classical in
theorem tournamentRamseyNumber_two : tournamentRamseyNumber 2 = 2 := by
  unfold tournamentRamseyNumber
  rw [Nat.find_eq_iff]
  refine ⟨forall_of_forcesTransitive (forcesTransitive_bound 1), fun n hn => ?_⟩
  exact not_forall_of_lt_card (k := 2) (n := n) (by omega)

/-- The `3`-cycle has no transitive triangle: `0` beats `1`, `1` beats `2`, but `0` does not
beat `2` (instead `2` beats `0`), so transitivity fails on the only size-`3` subset of `Fin 3`. -/
theorem not_cycle3_isTransitiveOn_univ :
    ¬ cycle3.IsTransitiveOn (Set.univ : Set (Fin 3)) := fun h =>
  absurd (h (Set.mem_univ 0) (Set.mem_univ 1) (Set.mem_univ 2) (by decide) (by decide)) (by decide)

/-- No tournament-Ramsey property at `n = 3`: the `3`-cycle is a counterexample, since its only
size-`3` `Finset` is all of `Fin 3`. -/
theorem not_forall_cycle3 :
    ¬ ∀ {G : Digraph (Fin 3)}, G.IsTournament →
        ∃ S : Finset (Fin 3), S.card = 3 ∧ G.IsTransitiveOn (↑S : Set (Fin 3)) := by
  intro hcon
  obtain ⟨S, hScard, hS⟩ := hcon isTournament_cycle3
  rw [Finset.eq_univ_of_card S (by simp [hScard]), Finset.coe_univ] at hS
  exact not_cycle3_isTransitiveOn_univ hS

open Classical in
theorem tournamentRamseyNumber_three : tournamentRamseyNumber 3 = 4 := by
  unfold tournamentRamseyNumber
  rw [Nat.find_eq_iff]
  refine ⟨forall_of_forcesTransitive (forcesTransitive_bound 2), fun n hn => ?_⟩
  interval_cases n <;> first | exact not_forall_of_lt_card (by omega) | exact not_forall_cycle3

/-! ### Worked example -/

/-- Concrete instance of the Erdős–Moser bound one step past `tournamentRamseyNumber_three`:
every tournament on `8` vertices contains a transitive `4`-subtournament. `erdosMoserBound 4 = 8`
is only an upper bound; this file does not decide whether `tournamentRamseyNumber 4` equals `8`. -/
theorem forcesTransitive_eight_four : ForcesTransitive 8 4 :=
  forcesTransitive_bound 3

end Digraph

/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Combinators
public import LeanPool.InteractionCombinators.Text.RenameMany

/-!
# General lemmas first proved in the review of the decomposition (page 85)

These lemmas were proved in `DecompositionCheck.lean` and `DecompositionReview.lean` and are used
by library files. They keep their names, including the namespaces `Comb.DecompositionCheck` and
`Comb.DecompositionReview`.

* `Comb.DecompositionCheck.termDecEq` — decidable equality of trees, and the instances that let
  `decide` compare nets of the combinators.
* `Equiv.sol_iff` — nets that are the same graph have the same solutions on their free ports
  (an invariant of `Equiv`, explained in `DecompositionReview.lean`).
* `Comb.DecompositionReview.pl`, `pr`, `pw` — the names of a rule written as trees.
* `Comb.DecompositionReview.equiv_wire_of_eq` — one wire substitution between two nets given as
  texts.

Contents, in the order of the file:

1. Definitions: decidable equality of trees: `termDecEq`, and the instances `DecidableEq sig.Sym`
   and `DecidableEq (Term sig ν)`.
2. Definitions and a lemma on the names of a rule: `pl`, `pr`, `pw`, the ports of the two cells
   and the internal wires; `equiv_wire_of_eq`, one wire substitution between two texts.
3. Solutions of a net: the definitions `Net.Solves` and `Net.Sol`, and the auxiliary lemmas
   `Net.solves_cons` and `Term.bind_subst_update`.
4. Main results: `Wire.sol_iff` and `Equiv.sol_iff`, nets that are the same graph have the same
   solutions on their free ports.
-/

@[expose] public section

-- ============================================================================================
-- 1. Definitions: decidable equality of trees
-- ============================================================================================

namespace INet.Comb.DecompositionCheck

open Term Rule

/-- Equality of trees is decidable when equality of symbols and of names is: compare the
symbols, then the subtrees. Only used to let `decide` compare nets in this file. -/
def termDecEq
    -- the symbols, with decidable equality
    {S : Signature}
    [DecidableEq S.Sym]
    -- the names, with decidable equality
    {ν : Type}
    [DecidableEq ν] :
    (t u : Term S ν) → Decidable (t = u)
  | .var x, .var y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | .var _, .app _ _ => isFalse fun e => by cases e
  | .app _ _, .var _ => isFalse fun e => by cases e
  | .app α ts, .app β us =>
    if h : α = β then by
      subst h
      exact
        haveI : ∀ i, Decidable (ts i = us i) := fun i => termDecEq (ts i) (us i)
        if h' : ∀ i, ts i = us i then isTrue (congrArg _ (funext h'))
        else isFalse fun e => by cases e; exact h' fun _ => rfl
    else isFalse fun e => by cases e; exact h rfl

-- the symbols of the combinators (`con`, `dup`, `era`) have decidable equality
instance : DecidableEq sig.Sym := inferInstanceAs (DecidableEq Comb)

-- the trees of the combinators over names with decidable equality have decidable equality
instance {ν : Type} [DecidableEq ν] : DecidableEq (Term sig ν) := termDecEq

end INet.Comb.DecompositionCheck

-- ============================================================================================
-- 2. Definitions and a lemma: the names of a rule, and one wire substitution
-- ============================================================================================

namespace INet.Comb.DecompositionReview

open Term Rule

/-- A port of the first cell. -/
abbrev pl
    -- the numbers of ports of the two cells, and of internal wires
    {a b m : ℕ}
    -- the port
    (i : Fin a) :
    Term sig (Fin a ⊕ Fin b ⊕ Fin m) :=
  .var (.inl i)

/-- A port of the second cell (in a side: a middle wire). -/
abbrev pr
    -- the numbers of ports of the two cells, and of internal wires
    {a b m : ℕ}
    -- the port
    (j : Fin b) :
    Term sig (Fin a ⊕ Fin b ⊕ Fin m) :=
  .var (.inr (.inl j))

/-- An internal wire. -/
abbrev pw
    -- the numbers of ports of the two cells, and of internal wires
    {a b m : ℕ}
    -- the wire
    (w : Fin m) :
    Term sig (Fin a ⊕ Fin b ⊕ Fin m) :=
  .var (.inr (.inr w))

/-- One wire substitution between two nets given as texts. -/
theorem equiv_wire_of_eq
    -- the names, with decidable equality, and the two nets
    {ν : Type}
    [DecidableEq ν]
    {N M : Net sig ν}
    -- the wire `x = t`, the equation `a = b` in which `x` occurs, and the rest of the net
    (x : ν)
    (t a b : Term sig ν)
    (Δ : Net sig ν)
    -- the net `x = t, a = b, Δ` is linear, and `x` occurs in `a = b`
    (hlin : Net.Linear (s(var x, t) ::ₘ s(a, b) ::ₘ Δ))
    (hx : x ∈ a.vars + b.vars)
    -- `N` is the net before the substitution, `M` the net after it
    (hN : N = s(var x, t) ::ₘ s(a, b) ::ₘ Δ)
    (hM : M = s(a.subst x t, b.subst x t) ::ₘ Δ) :
    -- the two nets are the same graph
    Equiv N M := by
  rw [hN, hM]
  exact (Wire.mk x t a b Δ hlin hx).equiv

end INet.Comb.DecompositionReview

-- ============================================================================================
-- 3. Solutions of a net
-- ============================================================================================

namespace INet

variable {S : Signature} {ν μ : Type}

open Term

/-- `s` solves the net `N`: the two sides of every equation become the same tree when each name
`x` is replaced by `s x`. -/
def Net.Solves
    -- the values of the names
    (s : ν → Term S μ)
    -- the net
    (N : Net S ν) :
    Prop :=
  ∀ e ∈ N, Sym2.lift ⟨fun u v => u.bind s = v.bind s, fun _ _ => propext eq_comm⟩ e

/-- A solution of `u = v` and of `N` is a solution of the net `u = v, N`. -/
theorem Net.solves_cons
    -- the values of the names, the equation `u = v` and the rest of the net
    {s : ν → Term S μ}
    {u v : Term S ν}
    {N : Net S ν} :
    -- `s` solves `u = v, N` exactly when it solves `u = v` and `N`
    Net.Solves s (s(u, v) ::ₘ N)
      ↔ u.bind s = v.bind s ∧ Net.Solves s N := by
  simp [Net.Solves]

variable [DecidableEq ν]

/-- Plugging into a substituted tree is plugging into the tree, with `x` sent to the image of the
tree substituted for it. -/
theorem Term.bind_subst_update
    -- the values of the names
    (s : ν → Term S μ)
    -- the tree `a`, in which the tree `t` is substituted for the name `x`
    (a : Term S ν)
    (x : ν)
    (t : Term S ν) :
    (a.subst x t).bind s = a.bind (Function.update s x (t.bind s)) := by
  unfold Term.subst
  rw [Term.bind_bind]
  refine Term.bind_congr fun y _ => ?_
  by_cases h : y = x
  · subst h; simp
  · simp [h]

/-- The values on the free ports of `N` that extend to a solution of `N`. -/
def Net.Sol
    -- the net
    (N : Net S ν)
    -- the values of the names
    (s : ν → Term S μ) :
    Prop :=
  ∃ s', Net.Solves s' N ∧ ∀ p, N.vars.count p = 1 → s' p = s p

-- ============================================================================================
-- 4. Main results: the solutions are an invariant of `Equiv`
-- ============================================================================================

/-- A wire substitution does not change the values on the free ports that extend to a solution:
the eliminated wire `x` takes the value of the tree plugged into it. -/
theorem Wire.sol_iff
    -- two nets, one obtained from the other by a wire substitution
    {N M : Net S ν}
    (h : Wire N M)
    -- the values on the free ports
    (s : ν → Term S μ) :
    -- they extend to a solution of `N` exactly when they extend to a solution of `M`
    N.Sol s ↔ M.Sol s := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hfree := (Wire.mk x t a b Δ hlin hx).free_iff
  have hc := hlin x
  have hx1 := Multiset.one_le_count_iff_mem.2 hx
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hc hx1
  have ht : x ∉ t.vars := fun h => by
    have := Multiset.one_le_count_iff_mem.2 h; omega
  have hΔ : x ∉ Δ.vars := fun h => by
    have := Multiset.one_le_count_iff_mem.2 h; omega
  constructor
  · rintro ⟨s', hs, hp⟩
    rw [Net.solves_cons, Net.solves_cons] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    have hu : Function.update s' x (t.bind s') = s' := by
      rw [Function.update_eq_self_iff]; exact h1.symm
    refine ⟨s', Net.solves_cons.2 ⟨?_, h3⟩, fun p hp1 => hp p ((hfree p).2 hp1)⟩
    rw [Term.bind_subst_update, Term.bind_subst_update, hu]
    exact h2
  · rintro ⟨s', hs, hp⟩
    rw [Net.solves_cons] at hs
    obtain ⟨h2, h3⟩ := hs
    set s'' := Function.update s' x (t.bind s')
    have hts : t.bind s'' = t.bind s' :=
      Term.bind_congr fun y hy => Function.update_of_ne (fun e => ht (by rw [← e]; exact hy)) _ _
    refine ⟨s'', ?_, fun p hp1 => ?_⟩
    · rw [Net.solves_cons, Net.solves_cons]
      refine ⟨by simp [s'', hts],
        by rwa [Term.bind_subst_update, Term.bind_subst_update] at h2, ?_⟩
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hv : ∀ y ∈ u.vars + v.vars, y ≠ x := fun y hy e => hΔ (e ▸ Multiset.mem_bind.2
          ⟨s(u, v), he, by simpa using hy⟩)
        have key := h3 _ he
        simp only [Sym2.lift_mk] at key ⊢
        rw [Term.bind_congr (g := s') fun y hy =>
            Function.update_of_ne (hv y (Multiset.mem_add.2 (Or.inl hy))) _ _,
          Term.bind_congr (f := s'') (g := s') fun y hy =>
            Function.update_of_ne (hv y (Multiset.mem_add.2 (Or.inr hy))) _ _]
        exact key
    · have hpx : p ≠ x := by
        rintro rfl
        simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
          Multiset.count_singleton_self] at hp1
        omega
      rw [show s'' p = s' p from Function.update_of_ne hpx _ _]
      exact hp p ((hfree p).1 hp1)

/-- Nets that are the same graph have the same solutions on their free ports. -/
theorem Equiv.sol_iff
    -- two nets that are the same graph
    {N M : Net S ν}
    (h : Equiv N M)
    -- the values on the free ports
    (s : ν → Term S μ) :
    -- they extend to a solution of `N` exactly when they extend to a solution of `M`
    N.Sol s ↔ M.Sol s := by
  induction h with
  | rel _ _ h => exact h.sol_iff s
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end INet

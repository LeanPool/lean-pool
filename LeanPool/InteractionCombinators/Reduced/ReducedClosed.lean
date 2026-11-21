/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduced.Vicious

/-!
# A reduced net with no free port is empty (page 80)

Lafont 1997, page 80: "By Proposition 2, a reduced net with no free port is necessarily empty."

The proof here does not go through Proposition 2. It is an induction on the number of equations
of the text. Take an equation of a nonempty, linear, reduced net with no free port.

* If both sides are cells, the equation is a cut.
* If one side is a name `x`, then `x` occurs twice, as there is no free port. If its other
  occurrence is in the other side `t`, the equation `x = t` is a vicious circle. Otherwise it is
  in another equation, and the wire substitution of `x` gives a net with one equation fewer,
  still nonempty. It is the same graph, so it is still linear and reduced, with no free port. By
  induction it is empty, which it is not.

A net with no cell, made of cycles of wires, is the second case: its wires are contracted one by
one until an equation `x = x` is left, a cyclic wire, which is a vicious circle of length 0.

Contents, in the order of the file:

1. Auxiliary lemmas: `Net.isReduced_zero`, the empty net is reduced;
   `Net.exists_wire_of_closed`, the step of the induction; `Net.eq_zero_of_closed_card`, the
   induction on the number of equations.
2. Main results: `Net.IsReduced.eq_zero_of_closed`, the statement of page 80; and its corollary
   `Net.IsReduced.cells_eq_zero_of_closed`, such a net has no cell, and neither has any net
   `Equiv` to it.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

namespace Net

-- ============================================================================================
-- 1. Auxiliary lemmas: the empty net, and the induction on the number of equations
-- ============================================================================================

/-- The empty net has no cut and no vicious circle (Lafont 1997, page 79). -/
theorem isReduced_zero :
    (0 : Net S ℕ).IsReduced := by
  refine ⟨fun hc => ?_, fun hv => ?_⟩
  · obtain ⟨a, b, xs, D, -, -, h⟩ := hc.chainCut
    cases xs with
    | nil => simp at h
    | cons y ys => simp at h
  · obtain ⟨K, D, ⟨x, y, t, C, -, -, rfl⟩, h⟩ := hv.chainVicious
    simp at h

/-- The step of the induction: in a linear net with no free port, an equation `x = t` that is
not a vicious circle is contracted by a wire substitution into a nonempty net with one equation
fewer (Lafont 1997, page 71: a wire is one edge of the graph). -/
theorem exists_wire_of_closed
    -- the net: an equation `x = t` and the rest `R`
    {x : ℕ}
    {t : Term S ℕ}
    {R : Net S ℕ}
    -- the net is linear and has no free port (no name occurs once)
    (hN : Net.Linear (s(var x, t) ::ₘ R))
    (hfree : ∀ y, (Net.vars (s(var x, t) ::ₘ R)).count y ≠ 1)
    -- the equation `x = t` is not a vicious circle: `x` does not occur in `t`
    (hx : x ∉ t.vars) :
    -- there is a net `M`
    ∃ M,
      -- obtained from the net by a wire substitution,
      Wire (s(var x, t) ::ₘ R) M ∧
      -- with fewer equations,
      Multiset.card M < Multiset.card (s(var x, t) ::ₘ R) ∧
      -- and not empty
      M ≠ 0 := by
  have h2 := hN x
  have h1 := hfree x
  have ht : t.vars.count x = 0 := Multiset.count_eq_zero.2 hx
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self, ht] at h1 h2
  have hR : x ∈ Net.vars R := Multiset.one_le_count_iff_mem.1 (by omega)
  obtain ⟨e, he, hxe⟩ := Multiset.mem_bind.1 hR
  obtain ⟨Δ, rfl⟩ := Multiset.exists_cons_of_mem he
  induction e using Sym2.ind with
  | _ a b =>
    refine ⟨_, Wire.mk x t a b Δ hN hxe, by simp, Multiset.cons_ne_zero⟩

/-- The induction on the number of equations behind `Net.IsReduced.eq_zero_of_closed`. -/
theorem eq_zero_of_closed_card :
    -- for every number `n` and every net `N` of `n` equations,
    ∀ (n : ℕ) (N : Net S ℕ),
      Multiset.card N = n →
      -- if `N` is linear and reduced,
      N.Linear →
      N.IsReduced →
      -- and has no free port (no name occurs once),
      (∀ x, N.vars.count x ≠ 1) →
      -- then `N` is empty
      N = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hN hR hfree
  by_contra h0
  obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero h0
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem he
  -- an equation with a name `x` on one side
  have wire : ∀ (x : ℕ) (t : Term S ℕ), e = s(var x, t) → False := by
    rintro x t rfl
    by_cases hx : x ∈ t.vars
    · exact hR.2 (hasVicious_of_mem hx (Multiset.mem_cons_self _ _))
    · obtain ⟨M, hW, hc, hM⟩ := exists_wire_of_closed hN hfree hx
      exact hM (ih _ (hn ▸ hc) M rfl hW.linear_right (hR.of_equiv hW.equiv)
        (fun y h1 => hfree y ((hW.free_iff y).2 h1)))
  induction e using Sym2.ind with
  | _ a b =>
    cases a with
    | var x => exact wire x b rfl
    | app α ts =>
      cases b with
      | var y => exact wire y (.app α ts) Sym2.eq_swap
      | app β us => exact hR.1 (hasCut_of_mem (Multiset.mem_cons_self _ _))

-- ============================================================================================
-- 2. Main results: a reduced net with no free port is empty
-- ============================================================================================

/-- **A reduced net with no free port is empty** (Lafont 1997, page 80: "a reduced net with no
free port is necessarily empty"). A linear net with no cut, no vicious circle and no name that
occurs once is the empty multiset of equations. -/
theorem IsReduced.eq_zero_of_closed
    -- the net: linear, reduced, with no free port (no name occurs once)
    {N : Net S ℕ}
    (hN : N.Linear)
    (hR : N.IsReduced)
    (hfree : ∀ x, N.vars.count x ≠ 1) :
    -- the net is empty
    N = 0 :=
  eq_zero_of_closed_card _ N rfl hN hR hfree

/-- **A reduced net with no free port has no cell** (Lafont 1997, page 80), and neither has any
net that is the same graph: wire substitutions create no cell (`Equiv.cells_eq`). -/
theorem IsReduced.cells_eq_zero_of_closed
    -- two nets; `N` is linear, reduced, with no free port (no name occurs once)
    {N M : Net S ℕ}
    (hN : N.Linear)
    (hR : N.IsReduced)
    (hfree : ∀ x, N.vars.count x ≠ 1)
    -- a net `M` that is the same graph as `N`
    (e : Equiv N M) :
    -- `M` has no cell
    M.cells = 0 := by
  rw [← e.cells_eq, hR.eq_zero_of_closed hN hfree]
  simp [Net.cells]

end Net

end INet

/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduced.Vicious

/-!
# A reduced net is trees plugged into a wiring, existence (Proposition 2, page 79)

Lafont 1997, Proposition 2, page 79: "Any reduced net with `n` free ports can be uniquely
decomposed as follows", the picture showing trees `t₁, …, tₙ` whose roots are the free ports and
whose leaves are joined by a wiring. This file proves the existence of the decomposition, on the
textual presentation, up to `Equiv`.

## The form on the text

`Net.IsTreesOnWiring N`: every equation of `N` is `x = t` with `x` a free port of `N` (a name that
occurs once). The tree `t` is the tree `tᵢ` hanging from the port `x`; it may be a single name, a
tree with no cell. The names that occur twice are then all leaves of these trees, and each of them
joins two leaves: they are the wiring.

### Cyclic wires

The wiring of the paper may in general contain cyclic wires (page 71). A reduced net has none: a
cyclic wire is an equation `x = x`, or a closed chain of names `x₀ = x₁, x₁ = x₂, …, xₖ = x₀`, and
either is a vicious circle of length 0 (page 79: "a cyclic wire can be considered as a vicious
circle of length 0"; `Net.HasVicious`, `Net.ChainVicious`). So the form does not need to allow
them, and it does not: its converse (`Net.IsTreesOnWiring.isReduced`) shows that every net in the
form is reduced, so no net the paper calls reduced is excluded up to `Equiv`, and no other net is
included.

## The proof

The paper chooses a principal path ending at a free port and removes its last cell. The proof
here is an induction on the number of equations, as in
`InteractionCombinators/Reduced/ReducedClosed.lean`. If an equation of a linear reduced net is
not hung from a free port, its two sides are not both cells (no cut), so one of them is a name
`x` that occurs twice. Its other occurrence is not in the other side `t` (no vicious circle), so
it is in another equation, and the wire substitution of `x` by `t` removes an equation and keeps
the graph, hence linearity and reducedness.

Contents, in the order of the file:

1. Definition: `Net.IsTreesOnWiring`, the form.
2. The converse: `Net.IsTreesOnWiring.eq_var_of_isCell`, `Net.IsTreesOnWiring.isReduced`, a net in
   the form is reduced.
3. Auxiliary lemmas, the induction on the number of equations: `Net.exists_wire_of_not_free` (the
   step), `Net.exists_treesOnWiring_card`.
4. Main results: `Net.IsReduced.exists_treesOnWiring`, **Proposition 2, existence**, and
   `Net.isReduced_iff_exists_treesOnWiring`, reduced is the form up to `Equiv`.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

namespace Net

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- **Trees plugged into a wiring**, on the text (Lafont 1997, Proposition 2, page 79): every
equation is `x = t` with `x` a free port, a name that occurs once in the net. The trees `t` hang
from the free ports; the names that occur twice are leaves, joined two by two: the wiring.
Cyclic wires are excluded, and need not be allowed: a cyclic wire is a vicious circle of length 0
(page 79), so a reduced net has none (see the module docstring). -/
def IsTreesOnWiring
    -- the net
    (N : Net S ℕ) :
    Prop :=
  -- every equation is `x = t`, with `x` a name that occurs once in `N`
  ∀ e ∈ N, ∃ (x : ℕ) (t : Term S ℕ), e = s(var x, t) ∧ N.vars.count x = 1

-- ============================================================================================
-- 2. The converse: a net in the form is reduced
-- ============================================================================================

/-- In a net in the form, an equation whose side `a` is a cell has a free port on its other
side. -/
theorem IsTreesOnWiring.eq_var_of_isCell
    -- a net in the form
    {N : Net S ℕ}
    (h : N.IsTreesOnWiring)
    -- an equation of `N` whose side `a` is a cell
    {a b : Term S ℕ}
    (hm : s(a, b) ∈ N)
    (ha : a.IsCell) :
    -- the other side `b` is a name `x` that occurs once in `N`
    ∃ x, b = var x ∧ N.vars.count x = 1 := by
  obtain ⟨x, t, he, hx⟩ := h _ hm
  rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact absurd ha (Cut.not_isCell_var x)
  · exact ⟨x, rfl, hx⟩

/-- **A net in the form is reduced** (Lafont 1997, page 79: trees on a wiring have no cut and
no vicious circle). This is the converse of `Net.IsReduced.exists_treesOnWiring`: the form is not
narrower than "reduced" up to `Equiv`. No linearity is needed. -/
theorem IsTreesOnWiring.isReduced
    -- a net in the form
    {N : Net S ℕ}
    (h : N.IsTreesOnWiring) :
    -- has no cut and no vicious circle
    N.IsReduced := by
  refine ⟨fun hc => ?_, fun hv => ?_⟩
  · obtain ⟨a, b, xs, D, ha, hb, hN⟩ := hc.chainCut
    cases xs with
    | nil =>
      have hm : s(a, b) ∈ N := by rw [hN]; simp
      obtain ⟨x, rfl, -⟩ := h.eq_var_of_isCell hm ha
      exact Cut.not_isCell_var x hb
    | cons y ys =>
      have hm : s(a, var y) ∈ N := by rw [hN]; simp
      obtain ⟨x, hx, h1⟩ := h.eq_var_of_isCell hm ha
      have hyx : y = x := by injection hx
      rw [← hyx] at h1
      have h2 := Cut.count_vars_chain b y a (y :: ys)
      rw [hN, Net.vars_add, Multiset.count_add] at h1
      simp only [List.count_cons_self] at h2
      omega
  · obtain ⟨K, D, ⟨x, y, t, C, hy, hC, rfl⟩, hN⟩ := hv.chainVicious
    have hcnt := Vicious.circle_count hy hC
    have hle : ∀ z, (Net.vars (s(var x, t) ::ₘ C)).count z ≤ N.vars.count z := fun z => by
      rw [hN, Net.vars_add, Multiset.count_add]
      omega
    have hm : s(var x, t) ∈ N := by rw [hN]; simp
    obtain ⟨x', t', he, h1⟩ := h _ hm
    rcases Sym2.eq_iff.1 he with ⟨hx, -⟩ | ⟨-, rfl⟩
    · cases hx
      have := hle x
      omega
    · have hyx : y = x' := by simpa using hy
      subst hyx
      have := hle y
      omega

-- ============================================================================================
-- 3. Auxiliary lemmas: the induction on the number of equations
-- ============================================================================================

/-- The step of the induction: in a linear net, an equation `x = t` whose name `x` is not a free
port and not a leaf of `t` is contracted by a wire substitution into a net with one equation
fewer (Lafont 1997, page 71: a wire is one edge of the graph). -/
theorem exists_wire_of_not_free
    -- the equation `x = t`
    {x : ℕ}
    {t : Term S ℕ}
    -- the rest of the net
    {R : Net S ℕ}
    -- the net is linear, `x` is not a free port, and `x` is not a leaf of `t`
    (hN : Net.Linear (s(var x, t) ::ₘ R))
    (h1 : (Net.vars (s(var x, t) ::ₘ R)).count x ≠ 1)
    (hx : x ∉ t.vars) :
    -- there is a net `M` such that
    ∃ M,
      -- the net becomes `M` by a wire substitution,
      Wire (s(var x, t) ::ₘ R) M ∧
      -- and `M` has fewer equations
      Multiset.card M < Multiset.card (s(var x, t) ::ₘ R) := by
  have h2 := hN x
  have ht : t.vars.count x = 0 := Multiset.count_eq_zero.2 hx
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self, ht] at h1 h2
  have hR : x ∈ Net.vars R := Multiset.one_le_count_iff_mem.1 (by omega)
  obtain ⟨e, he, hxe⟩ := Multiset.mem_bind.1 hR
  obtain ⟨Δ, rfl⟩ := Multiset.exists_cons_of_mem he
  induction e using Sym2.ind with
  | _ a b => exact ⟨_, Wire.mk x t a b Δ hN hxe, by simp⟩

/-- The induction on the number of equations behind `Net.IsReduced.exists_treesOnWiring`. -/
theorem exists_treesOnWiring_card :
    -- for every number `n` and every net `N` with `n` equations,
    ∀ (n : ℕ) (N : Net S ℕ), Multiset.card N = n →
      -- if `N` is linear and reduced,
      N.Linear → N.IsReduced →
      -- then `N` is the same graph as a net `M` in the form
      ∃ M, Equiv N M ∧ M.IsTreesOnWiring := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hN hR
  by_cases hF : N.IsTreesOnWiring
  · exact ⟨N, Equiv.refl N, hF⟩
  simp only [IsTreesOnWiring, not_forall, not_exists, not_and] at hF
  obtain ⟨e, he, hnot⟩ := hF
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem he
  -- an equation `x = t` whose name `x` is not a free port
  have wire : ∀ (x : ℕ) (t : Term S ℕ), e = s(var x, t) →
      ∃ M, Equiv (e ::ₘ R) M ∧ M.IsTreesOnWiring := by
    rintro x t rfl
    by_cases hx : x ∈ t.vars
    · exact absurd (hasVicious_of_mem hx (Multiset.mem_cons_self _ _)) hR.2
    · obtain ⟨M, hW, hc⟩ := exists_wire_of_not_free hN (hnot x t rfl) hx
      obtain ⟨M', hE, hM'⟩ := ih _ (hn ▸ hc) M rfl hW.linear_right (hR.of_equiv hW.equiv)
      exact ⟨M', hW.equiv.trans hE, hM'⟩
  induction e using Sym2.ind with
  | _ a b =>
    cases a with
    | var x => exact wire x b rfl
    | app α ts =>
      cases b with
      | var y => exact wire y (.app α ts) Sym2.eq_swap
      | app β us => exact absurd (hasCut_of_mem (Multiset.mem_cons_self _ _)) hR.1

-- ============================================================================================
-- 4. Main results: Proposition 2, existence
-- ============================================================================================

/-- **Proposition 2, existence** (Lafont 1997, page 79): "Any reduced net with `n` free ports can
be […] decomposed as follows": trees hanging from the free ports, their leaves joined by a wiring.
A linear net with no cut and no vicious circle is the same graph as a net each of whose equations
is `x = t` with `x` a free port (`Net.IsTreesOnWiring`). -/
theorem IsReduced.exists_treesOnWiring
    -- a linear reduced net
    {N : Net S ℕ}
    (hN : N.Linear)
    (hR : N.IsReduced) :
    -- there is a net `M` such that
    ∃ M,
      -- `N` is the same graph as `M`,
      Equiv N M ∧
      -- and `M` is trees plugged into a wiring
      M.IsTreesOnWiring :=
  exists_treesOnWiring_card _ N rfl hN hR

/-- **Reduced is trees on a wiring, up to wires** (Lafont 1997, Proposition 2, page 79). A
linear net is reduced if and only if it is the same graph as a net in the form
`Net.IsTreesOnWiring`. -/
theorem isReduced_iff_exists_treesOnWiring
    -- a linear net
    {N : Net S ℕ}
    (hN : N.Linear) :
    -- is reduced if and only if it is the same graph as a net in the form
    N.IsReduced ↔ ∃ M, Equiv N M ∧ M.IsTreesOnWiring :=
  ⟨IsReduced.exists_treesOnWiring hN,
    fun ⟨_, hE, hM⟩ => hM.isReduced.of_equiv hE.symm⟩

end Net

end INet

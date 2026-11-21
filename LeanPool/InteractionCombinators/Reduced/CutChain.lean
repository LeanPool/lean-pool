/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduced.Cut

/-!
# A translation reflects cuts (Proposition 3, page 80)

Lafont 1997, page 80, first point of the proof of Proposition 3: "if `Φ(N)` contains a cut, so
does `N`".

`Net.HasCut` speaks of every net equivalent to `N`, which is not a statement one can follow
through a translation. This file gives a description of a cut on the text itself: a chain of
wires written out,

  `a = x₁, x₁ = x₂, …, xₖ = b`   with `a` and `b` cells   (`Net.ChainCut`),

and shows that it is the same as a cut up to wires for a linear net (`Net.hasCut_iff_chainCut`).
The hard direction is that a wire substitution, in either direction, keeps a written chain
(`Cut.Wire.chainCut`, `Cut.Wire.chainCut_symm`): it shortens the chain, lengthens it, or plugs a
tree into one of its two cells.

The chain of `Φ(N)` is then followed back in `N` (`Cut.walk`): it starts at a cell of `N`, goes
through the same names, and ends at a cell of `N`, possibly before the end of the chain of `Φ(N)`.

Contents, in the order of the file:

1. Definitions: `Term.IsCell` (a tree whose root is a cell), `Cut.sub` (plugging a tree into one
   name of a net), `Cut.chain` (a chain of wires), `Net.ChainCut` (a cut written out on the
   text).
2. Auxiliary lemmas, cells and plugging: `not_isCell_var`, `isCell_subst`, `subst_var_self`,
   `subst_var_ne`, `sub_cons`, `sub_singleton`, `sub_add`, `sub_of_notMem`.
3. Auxiliary lemmas, chains of wires: `chain_nil`, `chain_cons`, `count_vars_chain`,
   `sub_chain`, `equiv_chain` (a chain is one wire), `ChainCut.add_right`, `chainCut_of_mem`,
   `ChainCut.hasCut` (a written cut of a linear net is a cut).
4. A wire substitution keeps a written cut: `mem_chain_var`, `chain_var_head`, `sub_contract`,
   `chain_insert`, `chain_replace_end`, `Wire.chainCut`, `chainCut_unsub`,
   `Wire.chainCut_symm`, `Equiv.chainCut_iff`.
5. A cut up to wires is a written cut: `HasCut.chainCut`, `hasCut_iff_chainCut`.
6. Auxiliary lemmas, following a chain back through a translation: `TermTr.isCell`,
   `TermTr.var_var`, `EqTr.inv`, `walk`.
7. Main result: `Translation.NetTr.hasCut_reflect`, a translation reflects cuts (first point of
   the proof of Proposition 3, page 80).
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- A tree whose root is the principal port of a cell. -/
def Term.IsCell
    -- the tree
    (t : Term S ℕ) :
    Prop :=
  -- there are a symbol `α` and trees `ts` on its auxiliary ports such that `t` is `α(ts)`
  ∃ α ts, t = Term.app α ts

namespace Cut

/-- Plug the tree `t` into the name `x`, in every equation of a net. -/
def sub
    -- the net
    (N : Net S ℕ)
    -- the name, and the tree plugged into it
    (x : ℕ)
    (t : Term S ℕ) :
    Net S ℕ :=
  N.map (Sym2.map fun r => r.subst x t)

/-- The chain of wires `a = x₁, x₁ = x₂, …, xₖ = b`; with no name, the equation `a = b`. -/
def chain
    -- the first end `a`
    (a : Term S ℕ) :
    -- the names `x₁, …, xₖ` of the links, and the last end `b`
    List ℕ → Term S ℕ → Net S ℕ
  | [], b => {s(a, b)}
  | y :: ys, b => s(a, var y) ::ₘ chain (var y) ys b

end Cut

open Cut

namespace Net

/-- A cut written out on the text: a chain of wires `a = x₁, x₁ = x₂, …, xₖ = b` between two
cells `a` and `b` (Lafont 1997, page 80). With no name it is an equation `a = b` between two
cells. -/
def ChainCut
    -- the net
    (N : Net S ℕ) :
    Prop :=
  -- there are two ends `a`, `b`, names `xs` and a rest `D` such that
  ∃ a b xs D,
    -- `a` is a cell,
    Term.IsCell a ∧
    -- `b` is a cell,
    Term.IsCell b ∧
    -- and `N` is the chain from `a` through `xs` to `b`, together with `D`
    N = chain a xs b + D

end Net

namespace Cut

-- ============================================================================================
-- 2. Auxiliary lemmas: cells and plugging a tree into one name
-- ============================================================================================

/-- A name is not a cell. -/
theorem not_isCell_var
    (y : ℕ) :
    ¬ (Term.var y : Term S ℕ).IsCell := by
  rintro ⟨α, ts, h⟩
  cases h

/-- Plugging a tree into a cell gives a cell. -/
theorem isCell_subst
    -- the cell
    {t : Term S ℕ}
    (h : t.IsCell)
    -- the name, and the tree plugged into it
    (x : ℕ)
    (u : Term S ℕ) :
    (t.subst x u).IsCell := by
  obtain ⟨α, ts, rfl⟩ := h
  exact ⟨α, _, rfl⟩

/-- Plugging `t` into the name `x` turns the tree `x` into `t`. -/
@[simp] theorem subst_var_self
    (x : ℕ)
    (t : Term S ℕ) :
    (Term.var x).subst x t = t := by
  simp [Term.subst]

/-- Plugging a tree into the name `x` leaves every other name alone. -/
theorem subst_var_ne
    -- two different names
    {x y : ℕ}
    (h : y ≠ x)
    -- the tree plugged into `x`
    (t : Term S ℕ) :
    (Term.var y : Term S ℕ).subst x t = Term.var y := by
  simp [Term.subst, h]

/-- Plugging a tree into a net with one more equation: it is plugged into both sides of the
equation and into the rest. -/
@[simp] theorem sub_cons
    -- the equation `a = b`
    (a b : Term S ℕ)
    -- the rest of the net
    (N : Net S ℕ)
    -- the name, and the tree plugged into it
    (x : ℕ)
    (t : Term S ℕ) :
    sub (s(a, b) ::ₘ N) x t = s(a.subst x t, b.subst x t) ::ₘ sub N x t := by
  simp [sub]

/-- Plugging a tree into a net of one equation. -/
@[simp] theorem sub_singleton
    -- the equation `a = b`
    (a b : Term S ℕ)
    -- the name, and the tree plugged into it
    (x : ℕ)
    (t : Term S ℕ) :
    sub ({s(a, b)} : Net S ℕ) x t = {s(a.subst x t, b.subst x t)} := by
  simp [sub]

/-- Plugging a tree into a sum of nets plugs it into each. -/
@[simp] theorem sub_add
    -- the two nets
    (N M : Net S ℕ)
    -- the name, and the tree plugged into it
    (x : ℕ)
    (t : Term S ℕ) :
    sub (N + M) x t = sub N x t + sub M x t := by
  simp [sub]

/-- Plugging a tree into a name that does not occur in the net changes nothing. -/
theorem sub_of_notMem
    -- the net and the name, which does not occur in it
    {N : Net S ℕ}
    {x : ℕ}
    -- the tree plugged into the name
    (t : Term S ℕ)
    (h : x ∉ N.vars) :
    sub N x t = N := by
  conv_rhs => rw [← Multiset.map_id N]
  refine Multiset.map_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab : x ∉ a.vars + b.vars := fun hx =>
      h (Multiset.mem_bind.2 ⟨_, he, by simpa using hx⟩)
    rw [Multiset.mem_add, not_or] at hab
    simp [Term.subst_of_notMem hab.1, Term.subst_of_notMem hab.2]

-- ============================================================================================
-- 3. Auxiliary lemmas: chains of wires
-- ============================================================================================

/-- A chain with no name is the equation between its two ends. -/
@[simp] theorem chain_nil
    -- the two ends
    (a b : Term S ℕ) :
    chain a [] b = {s(a, b)} :=
  rfl

/-- A chain whose first link is `y` is the equation `a = y` and the chain from `y`. -/
@[simp] theorem chain_cons
    -- the two ends
    (a b : Term S ℕ)
    -- the first link, and the others
    (y : ℕ)
    (ys : List ℕ) :
    chain a (y :: ys) b = s(a, var y) ::ₘ chain (var y) ys b :=
  rfl

/-- The names of a chain: those of its two ends, and each name of the list twice. -/
theorem count_vars_chain
    -- the last end
    (b : Term S ℕ)
    -- the name counted
    (z : ℕ) :
    -- for every first end `a` and names `xs`, the number of occurrences of `z` in the chain is
    -- its number in `a`, plus its number in `b`, plus twice its number in `xs`
    ∀ (a : Term S ℕ) (xs : List ℕ),
      (chain a xs b).vars.count z = a.vars.count z + b.vars.count z + 2 * xs.count z
  | a, [] => by simp
  | a, y :: ys => by
    rw [chain_cons, Net.vars_cons, Multiset.count_add, count_vars_chain b z (var y) ys]
    simp only [eqVars_mk, vars_var, Multiset.count_add, Multiset.count_singleton, List.count_cons,
      beq_iff_eq]
    split_ifs <;> omega

/-- Plugging a tree into a name that is not a link of the chain plugs it into the two ends. -/
theorem sub_chain
    -- the name, and the tree plugged into it
    {x : ℕ}
    {t : Term S ℕ}
    -- the last end
    (b : Term S ℕ) :
    -- for every first end `a` and names `xs` without `x`,
    ∀ (a : Term S ℕ) (xs : List ℕ), x ∉ xs →
      -- plugging `t` into `x` in the chain gives the chain between the two plugged ends
      sub (chain a xs b) x t = chain (a.subst x t) xs (b.subst x t)
  | a, [], _ => by simp
  | a, y :: ys, h => by
    have hy : y ≠ x := fun e => h (e ▸ List.mem_cons_self ..)
    have := sub_chain (t := t) b (var y) ys (fun hm => h (List.mem_cons_of_mem _ hm))
    rw [chain_cons, sub_cons, this, subst_var_ne hy, chain_cons]

/-- **A chain is one wire** (Lafont 1997, Section 1.1, page 71). In a linear net, the chain
`a = x₁, …, xₖ = b` is the same graph as the equation `a = b`. -/
theorem equiv_chain
    -- the last end
    (b : Term S ℕ) :
    -- for every first end `a`, names `xs` and rest `D` such that the chain with `D` is linear,
    ∀ (a : Term S ℕ) (xs : List ℕ) (D : Net S ℕ), (chain a xs b + D).Linear →
      -- the chain with `D` is the same graph as the equation `a = b` with `D`
      Equiv (chain a xs b + D) (s(a, b) ::ₘ D)
  | a, [], D, _ => Equiv.of_eq (by simp)
  | a, y :: ys, D, hlin => by
    have e : chain a (y :: ys) b + D = chain (var y) ys b + (s(a, var y) ::ₘ D) := by
      rw [chain_cons, Multiset.cons_add, Multiset.add_cons]
    rw [e] at hlin ⊢
    have E := equiv_chain b (var y) ys _ hlin
    have hlin' := E.linear hlin
    have hc := hlin' y
    simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at hc
    have ha : y ∉ a.vars := Multiset.count_eq_zero.1 (by omega)
    have W := Wire.mk y b a (var y) D hlin' (by simp)
    refine E.trans (W.equiv.trans (Equiv.of_eq ?_))
    rw [Term.subst_of_notMem ha, subst_var_self]

end Cut

namespace Net

/-- A written cut stays one when equations are added to the net. -/
theorem ChainCut.add_right
    -- the net, with a written cut
    {N : Net S ℕ}
    (h : N.ChainCut)
    -- the equations added
    (D' : Net S ℕ) :
    (N + D').ChainCut := by
  obtain ⟨a, b, xs, D, ha, hb, rfl⟩ := h
  exact ⟨a, b, xs, D + D', ha, hb, by rw [add_assoc]⟩

/-- An equation between two cells is a written cut. -/
theorem chainCut_of_mem
    -- the net
    {N : Net S ℕ}
    -- the two cells `α(ts)` and `β(us)`
    {α β : S.Sym}
    {ts : Fin (S.arity α) → Term S ℕ}
    {us : Fin (S.arity β) → Term S ℕ}
    -- the equation `α(ts) = β(us)` is in the net
    (h : s(Term.app α ts, Term.app β us) ∈ N) :
    N.ChainCut := by
  obtain ⟨D, rfl⟩ := Multiset.exists_cons_of_mem h
  exact ⟨_, _, [], D, ⟨α, ts, rfl⟩, ⟨β, us, rfl⟩, by simp⟩

/-- A written cut of a linear net is a cut (Lafont 1997, page 80): the chain is contracted to an
equation between the two cells (`Cut.equiv_chain`). -/
theorem ChainCut.hasCut
    -- the net, with a written cut, and linear
    {N : Net S ℕ}
    (h : N.ChainCut)
    (hN : N.Linear) :
    N.HasCut := by
  obtain ⟨a, b, xs, D, ⟨α, ts, rfl⟩, ⟨β, us, rfl⟩, rfl⟩ := h
  exact (hasCut_of_mem (Multiset.mem_cons_self _ _)).of_equiv (equiv_chain _ _ xs D hN).symm

end Net

namespace Cut

-- ============================================================================================
-- 4. A wire substitution keeps a written cut
-- ============================================================================================

/-- An equation `x = t` of a chain between two trees that are not the name `x` is a link: `x` is
one of the names of the chain. -/
theorem mem_chain_var
    -- the name `x` and the tree `t` of the equation
    {x : ℕ}
    {t b : Term S ℕ}
    -- the last end `b` of the chain is a cell
    (hb : b.IsCell) :
    -- for every first end `a` other than `x` and names `xs`,
    ∀ (a : Term S ℕ) (xs : List ℕ), a ≠ var x →
      -- if `x = t` is an equation of the chain, then `x` is one of the names
      s(var x, t) ∈ chain a xs b → x ∈ xs
  | a, [], ha, h => by
    rw [chain_nil, Multiset.mem_singleton] at h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact absurd h1.symm ha
    · exact (not_isCell_var x (h2 ▸ hb)).elim
  | a, y :: ys, ha, h => by
    rw [chain_cons, Multiset.mem_cons] at h
    by_cases hxy : x = y
    · exact hxy ▸ List.mem_cons_self ..
    rcases h with h | h
    · rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1.symm ha
      · cases h1; exact absurd rfl hxy
    · exact List.mem_cons_of_mem _
        (mem_chain_var hb (var y) ys (fun e => hxy (Term.var.inj e).symm) h)

/-- A chain that starts at the name `x`, with `x` nowhere else, starts with the equation `x = t`;
the rest of the chain makes a chain from any `a`, starting with `a = t`. -/
theorem chain_var_head
    -- the name `x`, the tree `t`, and the last end `b`, in which `x` does not occur
    {x : ℕ}
    {t b : Term S ℕ}
    (hb : x ∉ b.vars)
    -- the new first end
    (a : Term S ℕ) :
    -- for every list of names without `x`, and every rest `cs`,
    ∀ (ys : List ℕ) (cs : Net S ℕ), x ∉ ys →
      -- if the chain from `x` is `x = t` with `cs`,
      chain (var x) ys b = s(var x, t) ::ₘ cs →
        -- then the chain from `a` is `a = t` with `cs`,
        chain a ys b = s(a, t) ::ₘ cs ∧
        -- and `x` does not occur in `cs`
        x ∉ Net.vars cs
  | [], cs, _, h => by
    rw [chain_nil, Multiset.singleton_eq_cons_iff] at h
    obtain ⟨h1, rfl⟩ := h
    rcases Sym2.eq_iff.1 h1 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨by simp, by simp⟩
    · exact absurd (by simp) hb
  | z :: zs, cs, hx, h => by
    have hxz : x ≠ z := fun e => hx (e ▸ List.mem_cons_self ..)
    have hxzs : x ∉ zs := fun hm => hx (List.mem_cons_of_mem _ hm)
    have hnot : x ∉ Net.vars (chain (var z) zs b) := by
      intro hm
      have := Multiset.one_le_count_iff_mem.2 hm
      rw [count_vars_chain] at this
      simp [hxz, Multiset.count_eq_zero.2 hb,
        List.count_eq_zero.2 hxzs] at this
    rw [chain_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨h1, rfl⟩ | ⟨-, cs', h1, -⟩
    · rcases Sym2.eq_iff.1 h1 with ⟨-, rfl⟩ | ⟨-, h2⟩
      · exact ⟨rfl, hnot⟩
      · cases h2; exact absurd rfl hxz
    · exact absurd (h1 ▸ Multiset.mem_bind.2 ⟨_, Multiset.mem_cons_self _ _, by simp⟩) hnot

/-- **Contracting a link of a chain.** If `x = t` is a link of a chain whose name `x` occurs once
in the list and nowhere else, plugging `t` into `x` in the rest of the chain gives the chain
without `x`. -/
theorem sub_contract
    -- the name `x`, the tree `t`, and the last end `b`, in which `x` does not occur
    {x : ℕ}
    {t b : Term S ℕ}
    (hb : x ∉ b.vars) :
    -- for every first end `a` without `x`, names `xs` with `x` once, and rest `C`,
    ∀ (a : Term S ℕ) (xs : List ℕ) (C : Net S ℕ), x ∉ a.vars → xs.count x = 1 →
      -- if the chain is `x = t` with `C`, then plugging `t` into `x` in `C` gives the chain
      -- through `xs` without `x`
      chain a xs b = s(var x, t) ::ₘ C → sub C x t = chain a (xs.erase x) b
  | a, [], _, _, h1, _ => by simp at h1
  | a, y :: ys, C, ha, h1, h => by
    rw [chain_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨h2, rfl⟩ | ⟨-, cs, h2, rfl⟩
    · rcases Sym2.eq_iff.1 h2 with ⟨rfl, -⟩ | ⟨rfl, h3⟩
      · exact absurd (by simp) ha
      · cases h3
        have hys : x ∉ ys := by
          rw [List.count_cons_self] at h1
          exact List.count_eq_zero.1 (by omega)
        rw [sub_chain b (var x) ys hys, subst_var_self, Term.subst_of_notMem hb,
          List.erase_cons_head]
    · by_cases hyx : y = x
      · subst hyx
        have hys : y ∉ ys := by
          rw [List.count_cons_self] at h1
          exact List.count_eq_zero.1 (by omega)
        obtain ⟨e, hcs⟩ := chain_var_head hb a ys cs hys h2
        rw [sub_cons, sub_of_notMem t hcs, Term.subst_of_notMem ha, subst_var_self,
          List.erase_cons_head, e]
      · have h1' : ys.count x = 1 := by simpa [List.count_cons, hyx] using h1
        have IH := sub_contract hb (var y) ys cs (by simp [Ne.symm hyx]) h1' h2
        rw [sub_cons, IH, Term.subst_of_notMem ha, subst_var_ne hyx,
          List.erase_cons_tail (by simpa using hyx), chain_cons]

/-- **Inserting a link in a chain.** Replacing an equation `t = c` of a chain by `x = t, x = c`
gives a chain. -/
theorem chain_insert
    -- the new name `x`, and the two sides `t`, `c` of the equation replaced
    {x : ℕ}
    {t c : Term S ℕ}
    -- the last end
    (b : Term S ℕ) :
    -- for every first end `a`, names `xs` and rest `C`,
    ∀ (a : Term S ℕ) (xs : List ℕ) (C : Net S ℕ),
      -- if the chain is `t = c` with `C`,
      chain a xs b = s(t, c) ::ₘ C →
        -- then `x = t, x = c` with `C` is a chain from `a` to `b`, through some names `xs'`
        ∃ xs', s(var x, t) ::ₘ s(var x, c) ::ₘ C = chain a xs' b
  | a, [], C, h => by
    rw [chain_nil, Multiset.singleton_eq_cons_iff] at h
    obtain ⟨h1, rfl⟩ := h
    refine ⟨[x], ?_⟩
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [Sym2.eq_swap]
    · simp only [chain_cons, chain_nil]
      rw [Multiset.cons_swap, Sym2.eq_swap (a := var x) (b := a)]
      rfl
  | a, y :: ys, C, h => by
    rw [chain_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨h1, rfl⟩ | ⟨-, cs, h2, rfl⟩
    · refine ⟨x :: y :: ys, ?_⟩
      rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [chain_cons]
        rw [Sym2.eq_swap (a := var x) (b := a)]
      · simp only [chain_cons]
        rw [Multiset.cons_swap, Sym2.eq_swap (a := var x) (b := a)]
    · obtain ⟨xs', e⟩ := chain_insert b (var y) ys cs h2
      refine ⟨y :: xs', ?_⟩
      rw [chain_cons, ← e, Multiset.cons_swap (s(var x, c)), Multiset.cons_swap (s(var x, t))]

/-- **Changing a cell at an end of a chain.** If an equation `c = b₀` of a chain has a cell `c`
on one side, it is an end of the chain, and the cell can be replaced by any tree `a'`. The new
chain starts at `a` unless the old one started at the cell `c`. -/
theorem chain_replace_end
    -- the cell `c`, the tree `a'` that replaces it, and the other side `b₀` of its equation
    {c a' b₀ : Term S ℕ}
    (hc : c.IsCell) :
    -- for every two ends `a`, `b`, names `xs` and rest `C`,
    ∀ (a b : Term S ℕ) (xs : List ℕ) (C : Net S ℕ),
      -- if the chain is `c = b₀` with `C`,
      chain a xs b = s(c, b₀) ::ₘ C →
        -- then there are two new ends `a₁`, `b₁` such that
        ∃ a₁ b₁,
          -- `a' = b₀` with `C` is the chain from `a₁` through `xs` to `b₁`,
          s(a', b₀) ::ₘ C = chain a₁ xs b₁ ∧
          -- `a₁` is `a`, or it is `a'` and `a` was a cell,
          (a₁ = a ∨ (a₁ = a' ∧ a.IsCell)) ∧
          -- and `b₁` is `b` or `a'`
          (b₁ = b ∨ b₁ = a')
  | a, b, [], C, h => by
    rw [chain_nil, Multiset.singleton_eq_cons_iff] at h
    obtain ⟨h1, rfl⟩ := h
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨a', _, by simp, Or.inr ⟨rfl, hc⟩, Or.inl rfl⟩
    · exact ⟨_, a', by simp [Sym2.eq_swap], Or.inl rfl, Or.inr rfl⟩
  | a, b, y :: ys, C, h => by
    rw [chain_cons, Multiset.cons_eq_cons] at h
    rcases h with ⟨h1, rfl⟩ | ⟨-, cs, h2, rfl⟩
    · rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨a', b, rfl, Or.inr ⟨rfl, hc⟩, Or.inl rfl⟩
      · exact absurd hc (not_isCell_var y)
    · obtain ⟨a₂, b₂, e, ha₂, hb₂⟩ := chain_replace_end hc (var y) b ys cs h2
      have ha₂' : a₂ = var y := ha₂.resolve_right fun h => not_isCell_var y h.2
      subst ha₂'
      refine ⟨a, b₂, ?_, Or.inl rfl, hb₂⟩
      rw [Multiset.cons_swap, e, chain_cons]

/-- **A wire substitution keeps a written cut** (Lafont 1997, page 80). If the wire `x = t` is a
link of the chain, the chain gets shorter; otherwise `t` is plugged into the rest of the net and
the chain keeps its links. -/
theorem Wire.chainCut
    -- `M` is `N` with one wire contracted
    {N M : Net S ℕ}
    (h : Wire N M)
    -- `N` has a written cut
    (hc : N.ChainCut) :
    M.ChainCut := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hcx := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hcx
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have ht : x ∉ t.vars := Multiset.count_eq_zero.1 (by omega)
  have hΔ : x ∉ Net.vars Δ := Multiset.count_eq_zero.1 (by omega)
  have hM : s(a.subst x t, b.subst x t) ::ₘ Δ = sub (s(a, b) ::ₘ Δ) x t := by
    rw [sub_cons, sub_of_notMem t hΔ]
  rw [hM]
  obtain ⟨A, B, xs, D, hA, hB, hN⟩ := hc
  have hlin' := hlin x
  rw [hN, Net.vars_add, Multiset.count_add, count_vars_chain] at hlin'
  have hW : s(var x, t) ∈ chain A xs B + D := hN ▸ Multiset.mem_cons_self _ _
  rcases Multiset.mem_add.1 hW with hWc | hWD
  · obtain ⟨C, hC⟩ := Multiset.exists_cons_of_mem hWc
    rw [hC, Multiset.cons_add] at hN
    rw [(Multiset.cons_inj_right _).1 hN]
    have hxs : x ∈ xs := mem_chain_var hB A xs (fun e => not_isCell_var x (e ▸ hA)) hWc
    have h1 := List.count_pos_iff.2 hxs
    have hD : x ∉ Net.vars D := Multiset.count_eq_zero.1 (by omega)
    have hAx : x ∉ A.vars := Multiset.count_eq_zero.1 (by omega)
    have hBx : x ∉ B.vars := Multiset.count_eq_zero.1 (by omega)
    rw [sub_add, sub_of_notMem t hD, sub_contract hBx A xs C hAx (by omega) hC]
    exact ⟨A, B, _, D, hA, hB, rfl⟩
  · obtain ⟨D₁, rfl⟩ := Multiset.exists_cons_of_mem hWD
    rw [Multiset.add_cons] at hN
    rw [(Multiset.cons_inj_right _).1 hN]
    have hD1 : 1 ≤ (Net.vars (s(var x, t) ::ₘ D₁)).count x := by
      rw [Net.vars_cons, eqVars_mk, Multiset.count_add, Term.vars_var, Multiset.count_add,
        Multiset.count_singleton_self]
      omega
    have hxs : x ∉ xs := fun hm => by
      have := List.count_pos_iff.2 hm
      omega
    rw [sub_add, sub_chain B A xs hxs]
    exact ⟨_, _, xs, _, isCell_subst hA x t, isCell_subst hB x t, rfl⟩

/-- A wire substitution undone keeps a written cut, when `x` occurs in the left side `a` of the
equation it was plugged into. -/
theorem chainCut_unsub
    -- the wire `x = t`, the equation `a = b` into which `t` was plugged, with `x` in `a`
    {x : ℕ}
    {t a b : Term S ℕ}
    -- the rest of the net
    {Δ : Net S ℕ}
    (hxa : x ∈ a.vars)
    -- the net with `t` plugged into `a` has a written cut
    (hc : Net.ChainCut (s(a.subst x t, b) ::ₘ Δ)) :
    -- then so has the net with the wire
    Net.ChainCut (s(var x, t) ::ₘ s(a, b) ::ₘ Δ) := by
  obtain ⟨A, B, xs, D, hA, hB, hN⟩ := hc
  have hT : s(a.subst x t, b) ∈ chain A xs B + D := hN ▸ Multiset.mem_cons_self _ _
  rcases Multiset.mem_add.1 hT with hTc | hTD
  · obtain ⟨C, hC⟩ := Multiset.exists_cons_of_mem hTc
    rw [hC, Multiset.cons_add] at hN
    rw [(Multiset.cons_inj_right _).1 hN]
    cases a with
    | var y =>
      have hy : y = x := by simpa [eq_comm] using hxa
      subst hy
      rw [subst_var_self] at hC
      obtain ⟨xs', e⟩ := chain_insert (x := y) B A xs C hC
      refine ⟨A, B, xs', D, hA, hB, ?_⟩
      rw [← Multiset.cons_add, ← Multiset.cons_add, e]
    | app α ts =>
      obtain ⟨A₁, B₁, e, hA₁, hB₁⟩ :=
        chain_replace_end (a' := Term.app α ts) (isCell_subst ⟨α, ts, rfl⟩ x t) A B xs C hC
      refine ⟨A₁, B₁, xs, s(var x, t) ::ₘ D, ?_, ?_, ?_⟩
      · rcases hA₁ with rfl | ⟨rfl, -⟩
        · exact hA
        · exact ⟨α, ts, rfl⟩
      · rcases hB₁ with rfl | rfl
        · exact hB
        · exact ⟨α, ts, rfl⟩
      · rw [Multiset.add_cons, ← Multiset.cons_add, e]
  · obtain ⟨D₁, rfl⟩ := Multiset.exists_cons_of_mem hTD
    rw [Multiset.add_cons] at hN
    rw [(Multiset.cons_inj_right _).1 hN]
    refine ⟨A, B, xs, s(var x, t) ::ₘ s(a, b) ::ₘ D₁, hA, hB, ?_⟩
    rw [Multiset.add_cons, Multiset.add_cons]

/-- **A wire substitution undone keeps a written cut** (Lafont 1997, page 80). If `M` is `N` with
the wire `x = t` contracted and `M` has a written cut, so has `N`: the chain gets a new link `x`,
or one of its two cells is the cell into which `t` was plugged. -/
theorem Wire.chainCut_symm
    -- `M` is `N` with one wire contracted
    {N M : Net S ℕ}
    (h : Wire N M)
    -- `M` has a written cut
    (hc : M.ChainCut) :
    N.ChainCut := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hcx := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hcx
  rcases Multiset.mem_add.1 hx with hxa | hxb
  · have hb : x ∉ b.vars := by
      have := Multiset.one_le_count_iff_mem.2 hxa
      exact Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem hb] at hc
    exact chainCut_unsub hxa hc
  · have ha : x ∉ a.vars := by
      have := Multiset.one_le_count_iff_mem.2 hxb
      exact Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem ha, Sym2.eq_swap] at hc
    rw [Sym2.eq_swap (a := a)]
    exact chainCut_unsub hxb hc

/-- Equivalent nets have a written cut together. -/
theorem Equiv.chainCut_iff
    -- two texts of the same graph
    {N M : Net S ℕ}
    (h : Equiv N M) :
    N.ChainCut ↔ M.ChainCut := by
  induction h with
  | rel _ _ h => exact ⟨Wire.chainCut h, Wire.chainCut_symm h⟩
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end Cut

namespace Net

-- ============================================================================================
-- 5. A cut up to wires is a written cut
-- ============================================================================================

/-- A cut up to wires is written out in the net itself (Lafont 1997, page 80): a chain of wires
`a = x₁, …, xₖ = b` between two cells. No linearity is needed. -/
theorem HasCut.chainCut
    -- the net, with a cut up to wires
    {N : Net S ℕ}
    (h : N.HasCut) :
    N.ChainCut := by
  obtain ⟨N', hE, α, β, ts, us, hm⟩ := h
  exact (Cut.Equiv.chainCut_iff hE).2 (chainCut_of_mem hm)

/-- **A cut up to wires is a chain of wires** (Lafont 1997, page 80). For a linear net, a cut of
the graph is the same as a chain `a = x₁, x₁ = x₂, …, xₖ = b` between two cells `a`, `b` among the
equations of the net. -/
theorem hasCut_iff_chainCut
    -- the net, linear
    {N : Net S ℕ}
    (hN : N.Linear) :
    N.HasCut ↔ N.ChainCut :=
  ⟨HasCut.chainCut, fun h => h.hasCut hN⟩

end Net

namespace Cut

variable {Φ : Translation S S'}

-- ============================================================================================
-- 6. Auxiliary lemmas: following a chain back through a translation
-- ============================================================================================

/-- A tree that translates to a cell is a cell. -/
theorem TermTr.isCell
    -- `t'` translates `t`, and is a cell
    {t : Term S ℕ}
    {t' : Term S' ℕ}
    (h : Φ.TermTr t t')
    (h' : t'.IsCell) :
    t.IsCell := by
  cases h with
  | var x => exact absurd h' (not_isCell_var x)
  | app α ts ts' f _ => exact ⟨α, ts, rfl⟩

/-- A name that translates to the name `x` is `x`. -/
theorem TermTr.var_var
    {x y : ℕ}
    (h : Φ.TermTr (Term.var y) (Term.var x)) :
    y = x := by
  cases h
  rfl

/-- The equations that translate to `a' = b'` are the `a = b` with `a` translating to `a'` and
`b` to `b'`. -/
theorem EqTr.inv
    -- the equation `e`, which translates to `a' = b'`
    {e : Sym2 (Term S ℕ)}
    {a' b' : Term S' ℕ}
    (h : Φ.EqTr e s(a', b')) :
    -- there are two trees `a`, `b` such that
    ∃ a b,
      -- `e` is `a = b`,
      e = s(a, b) ∧
      -- `a` translates to `a'`,
      Φ.TermTr a a' ∧
      -- and `b` to `b'`
      Φ.TermTr b b' := by
  obtain ⟨a, b, c', d', rfl, he, ha, hb⟩ := h
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, b, rfl, ha, hb⟩
  · exact ⟨b, a, Sym2.eq_swap, hb, ha⟩

/-- **Following a chain back through a translation.** If the equations `C` translate a chain
`a' = x₁, …, xₖ = b'` whose end `b'` is a cell, then either `C` already has a written cut, or `C`
has a chain `a = x₁, …, xⱼ = y` with `a` translating `a'` and `y` a cell, `j ≤ k`.

Each link `xᵢ = xᵢ₊₁` of the translation comes from an equation `xᵢ = u` of `C` with `u`
translating to the name `xᵢ₊₁`. Either `u` is the name `xᵢ₊₁` and the chain goes on, or `u` is a
cell whose translation is a single wire from its root to an auxiliary port: then the chain of `C`
ends at the principal port of that cell. -/
theorem walk :
    -- for every chain `a' = x₁, …, xₖ = b'` of the target and every source net `C`,
    ∀ (xs : List ℕ) (a' b' : Term S' ℕ) (C : Net S ℕ),
      -- if the equations of `C` translate, one by one, the equations of the chain,
      Multiset.Rel Φ.EqTr C (chain a' xs b') →
      -- and `b'` is a cell,
      b'.IsCell →
        -- then `C` has a written cut,
        C.ChainCut ∨
        -- or there are a first end `a`, names `ys`, a last end `y` and a rest `D` such that
        ∃ a ys y D,
          -- `C` is the chain from `a` through `ys` to `y`, together with `D`,
          C = chain a ys y + D ∧
          -- `a` translates to `a'`,
          Φ.TermTr a a' ∧
          -- and `y` is a cell
          y.IsCell
  | [], a', b', C, h, hb' => by
    rw [chain_nil, ← Multiset.cons_zero, Multiset.rel_cons_right] at h
    obtain ⟨e, C₀, he, h0, rfl⟩ := h
    rw [Multiset.rel_zero_right] at h0
    subst h0
    obtain ⟨a, b, rfl, ha, hb⟩ := EqTr.inv he
    exact Or.inr ⟨a, [], b, 0, by simp, ha, TermTr.isCell hb hb'⟩
  | z :: zs, a', b', C, h, hb' => by
    rw [chain_cons, Multiset.rel_cons_right] at h
    obtain ⟨e, C₀, he, h0, rfl⟩ := h
    obtain ⟨a, y, rfl, ha, hy⟩ := EqTr.inv he
    cases y with
    | app γ vs =>
      exact Or.inr ⟨a, [], Term.app γ vs, C₀, by simp, ha, ⟨γ, vs, rfl⟩⟩
    | var w =>
      have hw := TermTr.var_var hy
      subst hw
      rcases walk zs (var w) b' C₀ h0 hb' with hcc | ⟨a₀, ys, y₀, D₀, rfl, ha₀, hy₀⟩
      · have := hcc.add_right {s(a, var w)}
        rw [add_comm, Multiset.singleton_add] at this
        exact Or.inl this
      · cases a₀ with
        | var v =>
          have hv := TermTr.var_var ha₀
          subst hv
          exact Or.inr ⟨a, v :: ys, y₀, D₀, by rw [chain_cons, Multiset.cons_add], ha, hy₀⟩
        | app γ vs =>
          refine Or.inl ⟨Term.app γ vs, y₀, ys, s(a, var w) ::ₘ D₀, ⟨γ, vs, rfl⟩, hy₀, ?_⟩
          rw [Multiset.add_cons]

end Cut

-- ============================================================================================
-- 7. Main result: a translation reflects cuts
-- ============================================================================================

/-- **A translation reflects cuts** (Lafont 1997, Proposition 3, first point of the proof,
page 80): if `N'` translates `N` and `N'` has a cut, so has `N`. No strictness is needed.

The cut of `N'` is a chain `a' = x₁, …, xₖ = b'` between two cells (`Net.hasCut_iff_chainCut`).
The internal wires of an instance join two leaves, so they are never links of the chain. The chain
is followed in `N` from the cell that translates to `a'` (`Cut.walk`): it goes through the same
names `x₁, x₂, …` and ends at the principal port of a cell of `N`. That cell is the one that
translates to `b'`, or an earlier one whose translation is a wire from its root to an auxiliary
port: the chain of `N'` passes through such a cell, the chain of `N` stops at it. -/
theorem Translation.NetTr.hasCut_reflect
    -- the translation
    {Φ : Translation S S'}
    -- the source net `N` and its translation `N'`
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Φ.NetTr N N')
    -- `N'` has a cut
    (hc : N'.HasCut) :
    N.HasCut := by
  refine Net.ChainCut.hasCut ?_ h.linear_source
  obtain ⟨A', B', xs, D', hA', hB', hN'⟩ := hc.chainCut
  have hrel := h.rel
  rw [hN'] at hrel
  obtain ⟨C, D, hC, -, rfl⟩ := Multiset.rel_add_right.1 hrel
  rcases Cut.walk xs A' B' C hC hB' with hcc | ⟨a, ys, y, D₀, rfl, ha, hy⟩
  · exact hcc.add_right D
  · exact ⟨a, y, ys, D₀ + D, Cut.TermTr.isCell ha hA', hy, add_assoc _ _ _⟩

end INet

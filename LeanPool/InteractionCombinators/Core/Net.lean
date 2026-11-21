/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Term
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Tactic.Abel

/-!
# Nets, linearity and equivalence up to wires

* `Net S ν` — a multiset of unordered equations between trees. An equation `t = u` plugs the root
  of `t` into the root of `u`.
* `Net.Linear` — every name occurs at most twice. A name occurring twice is an internal wire; a
  name occurring once is a free port.
* `Wire`, `Equiv` — two nets are the same graph when they differ by wire substitution: an equation
  `x = t` whose `x` has its other end elsewhere is the same as plugging `t` there. Interactions are
  not part of this equivalence. Renaming an internal wire is a special case.

Contents, in the order of the file:

1. Nets, their names and their cells: `Net`, `eqVars`, `eqCells`, `Net.cells`, `Net.vars`,
   `Net.bind`, `Net.vars_bind`.
2. Linearity and bounds on names: `Net.Linear`, `Net.Below`, `Term.Below`, the `below_` lemmas,
   `Net.Linear.add_fresh`.
3. Wire substitution and equivalence: `Wire`, `Equiv`.
4. One wire substitution: `Wire.count_vars`, `Wire.free_iff`, `Wire.cells_eq`,
   `Wire.linear_right`, `Wire.add_right`, `Wire.below`.
5. Equivalence: `Equiv.refl`, `Equiv.symm`, `Equiv.trans`, `Equiv.linear_iff`, `Equiv.free_iff`,
   `Equiv.cells_eq`.
-/

@[expose] public section

namespace INet

-- the signature, and the types of names, for the whole file
variable {S : Signature} {ν μ : Type}

-- ============================================================================================
-- 1. Nets, their names and their cells
-- ============================================================================================

/-- A net: a multiset of unordered equations between trees. -/
abbrev Net (S : Signature) (ν : Type) := Multiset (Sym2 (Term S ν))

/-- The names of an equation, with multiplicity. -/
def eqVars : Sym2 (Term S ν) → Multiset ν :=
  -- the names of both sides; the order of the sides does not matter
  Sym2.lift ⟨fun a b => a.vars + b.vars, fun _ _ => add_comm _ _⟩

/-- The names of the equation `a = b`: those of `a` and those of `b`. -/
@[simp] theorem eqVars_mk
    (a b : Term S ν) :
    eqVars s(a, b) = a.vars + b.vars :=
  rfl

/-- The cells of an equation, with multiplicity. -/
def eqCells : Sym2 (Term S ν) → Multiset S.Sym :=
  -- the cells of both sides; the order of the sides does not matter
  Sym2.lift ⟨fun a b => a.cells + b.cells, fun _ _ => add_comm _ _⟩

/-- The cells of the equation `a = b`: those of `a` and those of `b`. -/
@[simp] theorem eqCells_mk
    (a b : Term S ν) :
    eqCells s(a, b) = a.cells + b.cells :=
  rfl

namespace Net

/-- The cells of a net: the symbols occurring in it, with multiplicity. -/
def cells
    (N : Net S ν) :
    Multiset S.Sym :=
  N.bind eqCells

/-- The cells of a net with one more equation. -/
@[simp] theorem cells_cons
    -- the equation, and the rest of the net
    (e : Sym2 (Term S ν))
    (N : Net S ν) :
    cells (e ::ₘ N) = eqCells e + N.cells := by simp [cells]

/-- The names of a net, with multiplicity. -/
def vars
    (N : Net S ν) :
    Multiset ν :=
  N.bind eqVars

/-- The empty net has no name. -/
@[simp] theorem vars_zero : (0 : Net S ν).vars = 0 := by simp [vars]

/-- The names of a net with one more equation. -/
@[simp] theorem vars_cons
    -- the equation, and the rest of the net
    (e : Sym2 (Term S ν))
    (N : Net S ν) :
    vars (e ::ₘ N) = eqVars e + N.vars := by simp [vars]

/-- The names of a net of one equation. -/
@[simp] theorem vars_singleton
    (e : Sym2 (Term S ν)) :
    vars ({e} : Net S ν) = eqVars e := by
  simp [vars]

/-- The names of two nets put side by side. -/
@[simp] theorem vars_add
    (N M : Net S ν) :
    (N + M).vars = N.vars + M.vars := by simp [vars]

/-- Plug a tree into every name of the net. -/
def bind
    -- the tree to plug into each name
    (f : ν → Term S μ)
    -- the net plugged into
    (N : Net S ν) :
    Net S μ :=
  N.map (Sym2.map (Term.bind f))

/-- The names of a net after plugging: each name `x` is replaced by the names of `f x`. -/
theorem vars_bind
    -- the tree to plug into each name
    (f : ν → Term S μ)
    -- the net plugged into
    (N : Net S ν) :
    (N.bind f).vars = N.vars.bind fun x => (f x).vars := by
  unfold bind vars
  rw [Multiset.bind_map, Multiset.bind_assoc]
  congr 1
  funext e
  induction e using Sym2.ind with
  | _ a b => simp [Term.vars_bind, Multiset.add_bind]

-- ============================================================================================
-- 2. Linearity and bounds on names
-- ============================================================================================

/-- Every name occurs at most twice: once at each end of a wire, or once for a free port. -/
def Linear
    [DecidableEq ν]
    (N : Net S ν) :
    Prop :=
  ∀ x, N.vars.count x ≤ 2

/-- Every name of the net is below `k`: the names from `k` on are unused. -/
def Below
    -- the bound
    (k : ℕ)
    -- the net, with natural numbers as names
    (N : Net S ℕ) :
    Prop :=
  ∀ x ∈ N.vars, x < k

/-- A name at or above the bound of a net does not occur in it. -/
theorem Below.notMem
    -- a net with all its names below `k`
    {k x : ℕ}
    {N : Net S ℕ}
    (h : N.Below k)
    -- a name at or above `k`
    (hx : k ≤ x) :
    x ∉ N.vars :=
  fun hm => absurd (h x hm) (by omega)

/-- A bound on the names of a net can be raised. -/
theorem Below.mono
    -- a net with all its names below `k`
    {k m : ℕ}
    {N : Net S ℕ}
    (h : N.Below k)
    -- a larger bound
    (hkm : k ≤ m) :
    N.Below m :=
  fun x hx => (h x hx).trans_le hkm

end Net

/-- Every name of the tree is below `k`. -/
def Term.Below
    -- the bound
    (k : ℕ)
    -- the tree, with natural numbers as names
    (t : Term S ℕ) :
    Prop :=
  ∀ x ∈ t.vars, x < k

/-- A leaf is below `k` exactly when its name is. -/
@[simp] theorem Term.below_var
    {k x : ℕ} :
    (Term.var x : Term S ℕ).Below k ↔ x < k := by
  simp [Term.Below]

/-- A bound on the names of a tree can be raised. -/
theorem Term.Below.mono
    -- a tree with all its names below `k`
    {k m : ℕ}
    {t : Term S ℕ}
    (h : t.Below k)
    -- a larger bound
    (hkm : k ≤ m) :
    t.Below m :=
  fun x hx => (h x hx).trans_le hkm

namespace Net

/-- The empty net is below every bound. -/
@[simp] theorem below_zero
    {k : ℕ} :
    (0 : Net S ℕ).Below k := by simp [Below]

/-- A net with one more equation is below `k` exactly when both sides of the equation and the
rest of the net are. -/
@[simp] theorem below_cons
    {k : ℕ}
    -- the two sides of the equation, and the rest of the net
    {a b : Term S ℕ}
    {N : Net S ℕ} :
    Below k (s(a, b) ::ₘ N) ↔ a.Below k ∧ b.Below k ∧ N.Below k := by
  simp [Below, Term.Below, or_imp, forall_and, and_assoc]

/-- A net of one equation is below `k` exactly when both sides of the equation are. -/
@[simp] theorem below_singleton
    {k : ℕ}
    -- the two sides of the equation
    {a b : Term S ℕ} :
    Below k ({s(a, b)} : Net S ℕ) ↔ a.Below k ∧ b.Below k := by
  simp [Below, Term.Below, or_imp, forall_and]

/-- Two nets side by side are below `k` exactly when each of them is. -/
@[simp] theorem below_add
    {k : ℕ}
    {N M : Net S ℕ} :
    Below k (N + M) ↔ N.Below k ∧ M.Below k := by
  simp [Below, or_imp, forall_and]

/-- Linearity carried along an equality of nets. -/
theorem Linear.cast
    [DecidableEq ν]
    -- a linear net
    {N M : Net S ν}
    (h : N.Linear)
    -- a net equal to it
    (e : N = M) :
    M.Linear :=
  e ▸ h

/-- A bound on the names carried along an equality of nets. -/
theorem Below.cast
    -- a net with all its names below `k`
    {k : ℕ}
    {N M : Net S ℕ}
    (h : N.Below k)
    -- a net equal to it
    (e : N = M) :
    M.Below k :=
  e ▸ h

/-- Adding both ends of some new wires to a linear net keeps it linear. -/
theorem Linear.add_fresh
    [DecidableEq ν]
    -- the linear net one starts from, and the net one gets
    {N M : Net S ν}
    (hN : N.Linear)
    -- the new wires: pairwise distinct names, none of them used in `N`
    (F : Multiset ν)
    (hF : F.Nodup)
    (hfresh : ∀ x ∈ F, x ∉ N.vars)
    -- the names of `M` are those of `N` and the two ends of each new wire
    (hv : M.vars = N.vars + (F + F)) :
    M.Linear := by
  intro y
  rw [hv, Multiset.count_add, Multiset.count_add]
  by_cases hy : y ∈ F
  · have h0 : N.vars.count y = 0 := Multiset.count_eq_zero_of_notMem (hfresh y hy)
    have h1 := Multiset.nodup_iff_count_le_one.1 hF y
    omega
  · have := hN y
    simp only [Multiset.count_eq_zero_of_notMem hy, add_zero]
    exact this

end Net

-- ============================================================================================
-- 3. Wire substitution and equivalence
-- ============================================================================================

-- from here on, equality of names is decidable
variable [DecidableEq ν]

open Term in
/-- One wire substitution. The wire `x` has one end on the root of `t` and its other end inside
the equation `a = b`; plugging `t` there gives the same graph. Linearity of the net guarantees
that `x` occurs nowhere else. -/
inductive Wire : Net S ν → Net S ν → Prop
  | mk
      -- the wire, and the tree on one of its ends: the equation `x = t`
      (x : ν)
      (t : Term S ν)
      -- the equation `a = b` that holds the other end of the wire
      (a b : Term S ν)
      -- the rest of the net
      (Δ : Net S ν)
      -- the net one starts from is linear
      (hlin : Net.Linear (s(var x, t) ::ₘ s(a, b) ::ₘ Δ))
      -- the wire does have an end in `a = b`
      (hx : x ∈ a.vars + b.vars) :
      -- the equation `x = t` is removed, and `t` is plugged into `x` in `a = b`
      Wire (s(var x, t) ::ₘ s(a, b) ::ₘ Δ) (s(a.subst x t, b.subst x t) ::ₘ Δ)

/-- Nets that are the same graph, spelled differently. -/
def Equiv : Net S ν → Net S ν → Prop :=
  -- the equivalence relation generated by wire substitution
  Relation.EqvGen Wire

-- ============================================================================================
-- 4. One wire substitution
-- ============================================================================================

namespace Wire

-- the net before a wire substitution, and the net after
variable {N M : Net S ν}

/-- The net a wire substitution starts from is linear. -/
theorem linear_left
    (h : Wire N M) :
    N.Linear := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  exact hlin

/-- A wire substitution removes both ends of the wire and changes no other name. -/
theorem count_vars
    (h : Wire N M)
    -- the name that is counted
    (y : ν) :
    M.vars.count y ≤ N.vars.count y := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hxl
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have hone : a.vars.count x + b.vars.count x = 1 := by omega
  have key : a.vars.count x * t.vars.count y + b.vars.count x * t.vars.count y
      = t.vars.count y := by rw [← add_mul, hone, one_mul]
  simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, Term.count_vars_subst, Term.vars_var,
    Multiset.count_singleton]
  split_ifs <;> omega

/-- A wire substitution does not change which names are free ports. -/
theorem free_iff
    (h : Wire N M)
    -- the name that is counted
    (y : ν) :
    N.vars.count y = 1 ↔ M.vars.count y = 1 := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hxl
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have hone : a.vars.count x + b.vars.count x = 1 := by omega
  have key : a.vars.count x * t.vars.count y + b.vars.count x * t.vars.count y
      = t.vars.count y := by rw [← add_mul, hone, one_mul]
  simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, Term.count_vars_subst, Term.vars_var,
    Multiset.count_singleton]
  by_cases hy : y = x
  · subst hy
    simp only [ite_true]
    omega
  · simp only [hy, ite_false]
    omega

/-- A wire substitution creates and destroys no cell. -/
theorem cells_eq
    (h : Wire N M) :
    M.cells = N.cells := by
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hxl := hlin x
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hxl
  have hx1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hx
  rw [Multiset.count_add] at hx1
  have hone : a.vars.count x + b.vars.count x = 1 := by omega
  have key : a.vars.count x • t.cells + b.vars.count x • t.cells = t.cells := by
    rw [← add_nsmul, hone, one_nsmul]
  simp only [Net.cells_cons, eqCells_mk, Term.cells_subst, Term.cells_var, zero_add]
  calc a.cells + a.vars.count x • t.cells + (b.cells + b.vars.count x • t.cells) + Δ.cells
      = (a.vars.count x • t.cells + b.vars.count x • t.cells) + (a.cells + b.cells) + Δ.cells := by
        abel
    _ = t.cells + (a.cells + b.cells + Δ.cells) := by rw [key]; abel

/-- The net a wire substitution arrives at is linear. -/
theorem linear_right
    (h : Wire N M) :
    M.Linear :=
  fun y => (h.count_vars y).trans (h.linear_left y)

/-- A wire substitution brings no new name. -/
theorem mem_vars
    (h : Wire N M)
    -- a name of the net arrived at
    {y : ν}
    (hy : y ∈ M.vars) :
    y ∈ N.vars :=
  Multiset.one_le_count_iff_mem.1 ((Multiset.one_le_count_iff_mem.2 hy).trans (h.count_vars y))

/-- The two nets of a wire substitution are equivalent. -/
theorem equiv
    (h : Wire N M) :
    Equiv N M :=
  Relation.EqvGen.rel _ _ h

/-- A wire substitution can be done inside a larger net, as long as the larger net is linear. -/
theorem add_right
    (h : Wire N M)
    -- the rest of the net
    (Γ : Net S ν)
    -- the larger net one starts from is linear
    (hlin : (N + Γ).Linear) :
    Wire (N + Γ) (M + Γ) := by
  obtain ⟨x, t, a, b, Δ, -, hx⟩ := h
  have e : (s(Term.var x, t) ::ₘ s(a, b) ::ₘ Δ) + Γ = s(Term.var x, t) ::ₘ s(a, b) ::ₘ (Δ + Γ) := by
    simp only [Multiset.cons_add]
  have := Wire.mk x t a b (Δ + Γ) (e ▸ hlin) hx
  rw [e, Multiset.cons_add]
  exact this

/-- A wire substitution carried along equalities of nets. -/
theorem cast
    {N' M' : Net S ν}
    (h : Wire N M)
    -- a net equal to the one started from, and a net equal to the one arrived at
    (e : N = N')
    (e' : M = M') :
    Wire N' M' :=
  e ▸ e' ▸ h

end Wire

/-- A wire substitution keeps a bound on the names. -/
theorem Wire.below
    {k : ℕ}
    {N M : Net S ℕ}
    (h : Wire N M)
    -- the names of the net one starts from are below `k`
    (hN : N.Below k) :
    M.Below k :=
  fun x hx => hN x (h.mem_vars hx)

-- ============================================================================================
-- 5. Equivalence
-- ============================================================================================

namespace Equiv

-- three nets
variable {N M K : Net S ν}

/-- A net is equivalent to itself. -/
theorem refl
    (N : Net S ν) :
    Equiv N N :=
  Relation.EqvGen.refl _

/-- Equal nets are equivalent. -/
theorem of_eq
    (h : N = M) :
    Equiv N M :=
  h ▸ refl N

/-- Equivalence is symmetric. -/
theorem symm
    (h : Equiv N M) :
    Equiv M N :=
  Relation.EqvGen.symm _ _ h

/-- Equivalence is transitive. -/
theorem trans
    (h : Equiv N M)
    (h' : Equiv M K) :
    Equiv N K :=
  Relation.EqvGen.trans _ _ _ h h'

/-- Equivalent nets are linear together. -/
theorem linear_iff
    (h : Equiv N M) :
    N.Linear ↔ M.Linear := by
  induction h with
  | rel _ _ h => exact ⟨fun _ => h.linear_right, fun _ => h.linear_left⟩
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- A net equivalent to a linear net is linear. -/
theorem linear
    (h : Equiv N M)
    (hN : N.Linear) :
    M.Linear :=
  h.linear_iff.1 hN

/-- Equivalent nets have the same free ports. -/
theorem free_iff
    (h : Equiv N M)
    -- the name that is counted
    (y : ν) :
    N.vars.count y = 1 ↔ M.vars.count y = 1 := by
  induction h with
  | rel _ _ h => exact h.free_iff y
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- Equivalent nets have the same cells: the equivalence performs no interaction. -/
theorem cells_eq
    (h : Equiv N M) :
    N.cells = M.cells := by
  induction h with
  | rel _ _ h => exact h.cells_eq.symm
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end Equiv

end INet

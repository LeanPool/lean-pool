/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

/-!
# Trees over a signature

The textual presentation of interaction nets: a net is a set of equations between trees, and a
name stands for a wire, occurring once at each of its two ends.

* `Signature` — symbols with the number of their auxiliary ports.
* `Term S ν` — trees of cells whose leaves are names in `ν`.
* `Term.bind` — plug a tree into every leaf; `Term.subst` — plug a tree into one name.

Contents, in the order of the file:

1. Signatures and trees: `Signature`, `Term`.
2. Names, and plugging a tree into every leaf: `Term.vars`, `Term.bind`, `Term.vars_bind`.
3. Cells: `Term.cells`, `Term.cells_bind`.
4. Plugging a tree into one name: `Term.subst`, `Term.subst_of_notMem`,
   `Term.count_vars_subst`, `Term.cells_subst`.
-/

@[expose] public section

namespace INet

-- ============================================================================================
-- 1. Signatures and trees
-- ============================================================================================

/-- Symbols, each with the number of its auxiliary ports. Every cell also has one principal
port. -/
structure Signature where
  /-- The symbols. -/
  Sym : Type
  /-- The number of auxiliary ports of a symbol. -/
  arity : Sym → ℕ

/-- A tree of cells with leaves named in `ν`. The root of `app α ts` is the principal port of an
`α` cell whose `i`-th auxiliary port is plugged into the root of `ts i`. -/
inductive Term (S : Signature) (ν : Type) : Type
  -- a leaf: the end of the wire named `x`
  | var : ν → Term S ν
  -- a cell of symbol `α`, with one tree for each of its auxiliary ports
  | app : (α : S.Sym) → (Fin (S.arity α) → Term S ν) → Term S ν

namespace Term

-- the signature, and the types of names, for the whole file
variable {S : Signature} {ν μ : Type}

-- ============================================================================================
-- 2. Names, and plugging a tree into every leaf
-- ============================================================================================

/-- The leaves of a tree, with multiplicity. -/
def vars : Term S ν → Multiset ν
  -- a leaf is one name
  | var x => {x}
  -- a cell has the names of its subtrees
  | app _ ts => ∑ i, (ts i).vars

/-- Plug the tree `f x` into every leaf `x`. -/
def bind
    -- the tree to plug into each name
    (f : ν → Term S μ) :
    Term S ν → Term S μ
  -- a leaf is replaced by its tree
  | var x => f x
  -- a cell is kept, and the plugging is done in its subtrees
  | app α ts => app α fun i => (ts i).bind f

/-- The names of a leaf: the leaf itself. -/
@[simp] theorem vars_var
    (x : ν) :
    (var x : Term S ν).vars = {x} :=
  rfl

/-- The names of a cell: those of its subtrees. -/
@[simp] theorem vars_app
    -- the symbol of the cell, and the trees on its auxiliary ports
    (α : S.Sym)
    (ts : Fin (S.arity α) → Term S ν) :
    (app α ts).vars = ∑ i, (ts i).vars :=
  rfl

/-- Plugging into a leaf gives the tree chosen for its name. -/
@[simp] theorem bind_var
    -- the tree to plug into each name
    (f : ν → Term S μ)
    -- the leaf
    (x : ν) :
    (var x).bind f = f x :=
  rfl

/-- Plugging into a cell keeps the cell and plugs into its subtrees. -/
@[simp] theorem bind_app
    -- the tree to plug into each name
    (f : ν → Term S μ)
    -- the symbol of the cell, and the trees on its auxiliary ports
    (α : S.Sym)
    (ts : Fin (S.arity α) → Term S ν) :
    (app α ts).bind f = app α fun i => (ts i).bind f :=
  rfl

/-- `Multiset.bind` distributes over a finite sum of multisets. -/
theorem _root_.Multiset.sum_bind'
    {ι α β : Type}
    -- the finite sum: an index set and a multiset for each index
    (s : Finset ι)
    (f : ι → Multiset α)
    -- the function applied to every element
    (g : α → Multiset β) :
    (∑ i ∈ s, f i).bind g = ∑ i ∈ s, (f i).bind g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, Multiset.add_bind, ih]

/-- The names of a tree after plugging: each leaf `x` is replaced by the names of `f x`. -/
theorem vars_bind
    -- the tree to plug into each name
    (f : ν → Term S μ)
    -- the tree plugged into
    (t : Term S ν) :
    (t.bind f).vars = t.vars.bind fun x => (f x).vars := by
  induction t with
  | var x => simp
  | app α ts ih => simp [Multiset.sum_bind', ih]

-- ============================================================================================
-- 3. Cells
-- ============================================================================================

/-- The cells of a tree: the symbols occurring in it, with multiplicity. -/
def cells : Term S ν → Multiset S.Sym
  -- a leaf has no cell
  | var _ => 0
  -- the root cell, and the cells of the subtrees
  | app α ts => α ::ₘ ∑ i, (ts i).cells

/-- A leaf has no cell. -/
@[simp] theorem cells_var
    (x : ν) :
    (var x : Term S ν).cells = 0 :=
  rfl

/-- The cells of a tree with a cell at its root: that cell and the cells of the subtrees. -/
@[simp] theorem cells_app
    -- the symbol of the cell, and the trees on its auxiliary ports
    (α : S.Sym)
    (ts : Fin (S.arity α) → Term S ν) :
    (app α ts).cells = α ::ₘ ∑ i, (ts i).cells :=
  rfl

/-- The cells of a tree after plugging: its own cells, and for each leaf `x` the cells of
`f x`. -/
theorem cells_bind
    -- the tree to plug into each name
    (f : ν → Term S μ)
    -- the tree plugged into
    (t : Term S ν) :
    (t.bind f).cells = t.cells + t.vars.bind fun x => (f x).cells := by
  induction t with
  | var x => simp
  | app α ts ih =>
    simp only [bind_app, cells_app, vars_app, Multiset.sum_bind', ih, Finset.sum_add_distrib,
      Multiset.cons_add]

-- ============================================================================================
-- 4. Plugging a tree into one name
-- ============================================================================================

-- from here on, equality of names is decidable
variable [DecidableEq ν]

/-- Plug the tree `t` into the name `x`. -/
def subst
    -- the tree plugged into
    (r : Term S ν)
    -- the name that is replaced
    (x : ν)
    -- the tree that replaces it
    (t : Term S ν) :
    Term S ν :=
  r.bind fun y => if y = x then t else var y

/-- Plugging into a name that does not occur in the tree changes nothing. -/
theorem subst_of_notMem
    -- the name, the tree plugged into it, and the tree plugged into
    {x : ν}
    {t : Term S ν}
    {r : Term S ν}
    -- the name does not occur in `r`
    (h : x ∉ r.vars) :
    r.subst x t = r := by
  induction r with
  | var y =>
    have : y ≠ x := by simpa [eq_comm] using h
    simp [subst, this]
  | app α ts ih =>
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and, not_exists] at h
    simp only [subst, bind_app]
    congr 1
    funext i
    exact ih i (h i)

/-- The count of a name `y` in a multiset of names `m` after `t` is plugged into `x`: one copy of
the names of `t` for each occurrence of `x`, and the other names of `m` unchanged. -/
theorem count_bind_ite
    -- the multiset of names plugged into
    (m : Multiset ν)
    -- the name that is replaced, and the name that is counted
    (x y : ν)
    -- the tree that replaces `x`
    (t : Term S ν) :
    (m.bind fun z => (if z = x then t else var z : Term S ν).vars).count y =
      m.count x * t.vars.count y + if y = x then 0 else m.count y := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons z m ih =>
    rw [Multiset.cons_bind, Multiset.count_add, ih]
    by_cases hz : z = x
    · subst hz
      by_cases hy : y = z
      · subst hy; simp; ring
      · simp [hy]; ring
    · by_cases hy : y = x
      · subst hy; simp [hz, Ne.symm hz]
      · simp only [hz, ite_false, hy, vars_var, Multiset.count_singleton,
          Multiset.count_cons_of_ne (Ne.symm hz), Multiset.count_cons]
        split_ifs <;> omega

/-- The leaves of `r.subst x t`: every `x` is replaced by the leaves of `t`. -/
theorem count_vars_subst
    -- the tree plugged into
    (r : Term S ν)
    -- the name that is replaced, and the name that is counted
    (x y : ν)
    -- the tree that replaces `x`
    (t : Term S ν) :
    (r.subst x t).vars.count y =
      r.vars.count x * t.vars.count y + if y = x then 0 else r.vars.count y := by
  rw [subst, vars_bind]
  exact count_bind_ite _ _ _ _

/-- The cells brought by plugging `t` into `x` in a multiset of names `m`: one copy of the cells
of `t` for each occurrence of `x`. -/
theorem bind_ite_cells
    -- the multiset of names plugged into
    (m : Multiset ν)
    -- the name that is replaced
    (x : ν)
    -- the tree that replaces it
    (t : Term S ν) :
    (m.bind fun z => (if z = x then t else var z : Term S ν).cells) = m.count x • t.cells := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons z m ih =>
    rw [Multiset.cons_bind, ih]
    by_cases hz : z = x
    · subst hz; simp [add_nsmul, add_comm]
    · simp [hz, Multiset.count_cons_of_ne (Ne.symm hz)]

/-- Substitution adds one copy of the cells of `t` for each occurrence of `x`. -/
theorem cells_subst
    -- the tree plugged into
    (r : Term S ν)
    -- the name that is replaced
    (x : ν)
    -- the tree that replaces it
    (t : Term S ν) :
    (r.subst x t).cells = r.cells + r.vars.count x • t.cells := by
  rw [subst, cells_bind, bind_ite_cells]

end Term

end INet

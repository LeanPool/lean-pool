/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.WordRAM.AlgebraicSpec
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Specification: separator trees, fill, and elimination restricted to a pattern

The definitions behind the statements on nested dissection. This file imports only Mathlib and
`WordRAM/AlgebraicSpec.lean` (the operation-counting monad, itself Mathlib-only); the library
files import it, so their theorems are about exactly these constants.

## Contents

* Separator trees (`SepTree`) with the separator or leaf set at the root (`SepTree.own`), all
  their vertices (`SepTree.verts`), the boundary of a vertex set (`bdry`), the condition that a
  tree is a separator tree of a graph (`SepTree.IsDissection`), and the nested dissection order
  (`SepTree.order`: recursively the first part, the second part, then the separator).
* Conditions on all nodes (`SepTree.AllNodes`): parts of at most two thirds of the vertices
  (`SepTree.Shrinks`), separators and boundaries of at most `α √k` and `β √k` vertices at a node
  with `k` vertices (`SepTree.SqrtBound`).
* The filled graph of an elimination order (`fill`, through walks with low interior,
  `LowWalk`), and the later neighbours of a vertex (`laterNbrs`).
* In-place elimination steps (`elimStep`, `stage`; Gaussian elimination without pivoting when
  the pivots are nonzero, with the totalized inverse `0⁻¹ = 0` otherwise), and the same
  elimination restricted to the positions of a graph `H`, in the counting monad
  (`sparseStepCounted`, `sparseCounted`), with inversion charged one multiplication (`opInv`).
* Leading principal submatrices (`leading`) and the square of a graph (`PlanarSeparator.square`).

`LowWalk.trans` and `LowWalk.symm` are the only lemmas: the filled graph is a `SimpleGraph`, and
its adjacency must be shown symmetric.
-/

@[expose] public section

namespace NestedDissection

universe u v w

/-! ### Separator trees -/

/-- A separator tree: a leaf holding a vertex set, or a node holding a separator and two
subtrees for the two parts. -/
inductive SepTree (V : Type u) : Type u
  | leaf (s : Finset V) : SepTree V
  | node (s : Finset V) (a b : SepTree V) : SepTree V

section Bdry

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The boundary of `W`: the vertices outside `W` adjacent to a vertex of `W`. -/
def bdry (W : Finset V) : Finset V := {y | y ∉ W ∧ ∃ x ∈ W, G.Adj x y}

end Bdry

namespace SepTree

variable {V : Type u}

/-- The vertices numbered at the root of a subtree: the separator of a node, the whole set of a
leaf. -/
def own : SepTree V → Finset V
  | leaf s => s
  | node s _ _ => s

/-- `P` holds at every node of the tree. -/
def AllNodes (P : SepTree V → Prop) : SepTree V → Prop
  | leaf s => P (leaf s)
  | node s a b => P (node s a b) ∧ AllNodes P a ∧ AllNodes P b

variable [DecidableEq V]

/-- All vertices of a subtree. -/
def verts : SepTree V → Finset V
  | leaf s => s
  | node s a b => s ∪ a.verts ∪ b.verts

/-- `t` is a separator tree of `G`: at every node the separator and the two parts are pairwise
disjoint and no edge of `G` joins the two parts. -/
def IsDissection (G : SimpleGraph V) : SepTree V → Prop
  | leaf _ => True
  | node s a b => Disjoint s a.verts ∧ Disjoint s b.verts ∧ Disjoint a.verts b.verts ∧
      (∀ x ∈ a.verts, ∀ y ∈ b.verts, ¬ G.Adj x y) ∧ IsDissection G a ∧ IsDissection G b

/-- The parts of the root have at most two thirds of its vertices. -/
def Shrinks : SepTree V → Prop
  | leaf _ => True
  | node s a b => 3 * a.verts.card ≤ 2 * (node s a b).verts.card ∧
      3 * b.verts.card ≤ 2 * (node s a b).verts.card

/-- The separator bound `|own t| ≤ α √k` and the boundary bound `|bdry t| ≤ β √k` at the root
of `t`, where `k` is the number of vertices of `t`. -/
def SqrtBound [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (α β : ℝ) (t : SepTree V) :
    Prop :=
  (t.own.card : ℝ) ≤ α * √(t.verts.card) ∧ ((bdry G t.verts).card : ℝ) ≤ β * √(t.verts.card)

section Order

variable [LinearOrder V]

/-- The nested dissection order: recursively the first part, the second part, then the
separator (each separator and leaf set in increasing order of `V`). -/
def order : SepTree V → List V
  | leaf s => s.sort (· ≤ ·)
  | node s a b => order a ++ order b ++ s.sort (· ≤ ·)

end Order

end SepTree

/-! ### The filled graph -/

section Fill

variable {V : Type u} (G : SimpleGraph V) (r : V → ℕ)

/-- `LowWalk G r k u w`: there is a walk of positive length from `u` to `w` in `G` all of whose
interior vertices have rank `< k`. -/
inductive LowWalk (k : ℕ) : V → V → Prop
  | adj {u w : V} : G.Adj u w → LowWalk k u w
  | cons {u x w : V} : G.Adj u x → r x < k → LowWalk k x w → LowWalk k u w

namespace LowWalk

variable {G r} {k : ℕ} {u w : V}

theorem trans {x : V} (h₁ : LowWalk G r k u x) (hx : r x < k) (h₂ : LowWalk G r k x w) :
    LowWalk G r k u w := by
  induction h₁ with
  | adj h => exact .cons h hx h₂
  | cons h hy _ ih => exact .cons h hy (ih hx h₂)

theorem symm (h : LowWalk G r k u w) : LowWalk G r k w u := by
  induction h with
  | adj h => exact .adj h.symm
  | cons h hx _ ih => exact ih.trans hx (.adj h.symm)

end LowWalk

/-- The **filled graph** of `G` for the elimination order given by `r`: `u ≠ w` are adjacent
iff there is a walk from `u` to `w` whose interior vertices all have rank smaller than both
`r u` and `r w`. -/
def fill : SimpleGraph V where
  Adj u w := u ≠ w ∧ LowWalk G r (min (r u) (r w)) u w
  symm := ⟨fun u w h => ⟨h.1.symm, by rw [min_comm]; exact h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G r}

variable (r) in
/-- The neighbours of `v` in `H` that come later in the order `r`. -/
def laterNbrs [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) : Finset V :=
  {w | H.Adj v w ∧ r v < r w}

end Fill

/-! ### Elimination -/

section Elimination

open WordRAM.Algebraic Matrix

variable {K : Type u}

/-- Inversion, charged one multiplicative operation (the cost model `OpCount` records additive
and multiplicative operations; a division or inversion is counted with the latter). -/
def opInv [Inv K] (a : K) : Counted K := ⟨a⁻¹, OpCount.oneMul⟩

/-- The leading principal `k × k` submatrix. -/
def leading {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) K :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

variable [Field K]

/-- The in-place elimination step with pivot `k`: `M i j - M i k * (M k k)⁻¹ * M k j` for
`i, j > k`. The inverse is the field's, with `0⁻¹ = 0`, so at a zero pivot the step leaves `M`
unchanged. -/
def elimStep {n : ℕ} (k : Fin n) (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if k < i ∧ k < j then M i j - M i k * (M k k)⁻¹ * M k j else M i j

/-- `stage A k`: the matrix after the elimination steps with pivots `0, …, k - 1`; Gaussian
elimination without pivoting when these pivots are nonzero. -/
def stage {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => A
  | k + 1 => if h : k < n then elimStep ⟨k, h⟩ (stage A k) else stage A k

variable {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

/-- The elimination step with pivot `k` restricted to the positions `(i, j)` with `i` and `j`
later neighbours of `k` in `H`, in the counting monad: one inversion, one multiplication for
each multiplier, one multiplication and one subtraction for each updated entry. -/
def sparseStepCounted (k : Fin n) (M : Matrix (Fin n) (Fin n) K) :
    Counted (Matrix (Fin n) (Fin n) K) := do
  let p ← opInv (M k k)
  let l ← Counted.pi fun i : Fin n =>
    if i ∈ laterNbrs Fin.val H k then Op.mul (M i k) p else pure 0
  let S ← Counted.pi fun i : Fin n => Counted.pi fun j : Fin n =>
    if i ∈ laterNbrs Fin.val H k ∧ j ∈ laterNbrs Fin.val H k then do
      let t ← Op.mul (l i) (M k j)
      Op.sub (M i j) t
    else pure (M i j)
  pure (Matrix.of S)

/-- Restricted elimination in the counting monad: the first `k` steps. -/
def sparseCounted (A : Matrix (Fin n) (Fin n) K) : ℕ → Counted (Matrix (Fin n) (Fin n) K)
  | 0 => pure A
  | k + 1 => do
    let M ← sparseCounted A k
    if h : k < n then sparseStepCounted H ⟨k, h⟩ M else pure M

end Elimination

end NestedDissection

/-! ### Squares of graphs -/

namespace PlanarSeparator

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The square of a graph: distinct vertices at distance at most `2` are adjacent. -/
def square : SimpleGraph V where
  Adj i j := i ≠ j ∧ (G.Adj i j ∨ ∃ k, G.Adj i k ∧ G.Adj k j)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inl h.symm)
    fun ⟨k, h1, h2⟩ => Or.inr ⟨k, h2.symm, h1.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel (square G).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

end PlanarSeparator

end

/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Algebra.Word.CentralTable
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Prefix collection with a central scalar and two noncommuting letters

Central normalization moves the scalar letter to the beginning of each word.
A three-branch prefix tree then combines coefficients by following word paths,
and conversion back to rows discards zero coefficients. Evaluation retains the
order of the two ordinary letters and requires no commutativity of their algebra.

## Main definitions

* `Tree`: a coefficient tree with central, left, and right branches.
* `collect`: central normalization followed by prefix collection.

## Main results

* `eval_collectTree`, `eval_toTable`: semantics of the prefix representation.
* `eval_collect`: central normalization and collection preserve evaluation.
-/

@[expose] public section

namespace FQFP.CentralBinaryWordTable

/-- A prefix tree with coefficients at all words on the three-letter alphabet. -/
inductive Tree (R : Type*) where
  | zero
  | node (coeff : R) (central left right : Tree R)

variable {R : Type*}

/-- Add a coefficient by following the word's central or binary letter branches. -/
def insert [Zero R] [Add R] : List (Option (Fin 2)) → R → Tree R → Tree R
  | [], c, .zero => .node c .zero .zero .zero
  | [], c, .node d m l r => .node (c + d) m l r
  | none :: w, c, .zero => .node 0 (insert w c .zero) .zero .zero
  | none :: w, c, .node d m l r => .node d (insert w c m) l r
  | some a :: w, c, .zero =>
      if a = 0 then .node 0 .zero (insert w c .zero) .zero
      else .node 0 .zero .zero (insert w c .zero)
  | some a :: w, c, .node d m l r =>
      if a = 0 then .node d m (insert w c l) r
      else .node d m l (insert w c r)

/-- Collect a table's coefficients by their word paths, without normalization. -/
def collectTree [Zero R] [Add R] : CoeffWordTable.Table R (Option (Fin 2)) → Tree R
  | [] => .zero
  | p :: t => insert p.1 p.2 (collectTree t)

/-- Return all nonzero rows, in central-left-right prefix order. -/
def toTable [Zero R] [DecidableEq R] : Tree R → CoeffWordTable.Table R (Option (Fin 2))
  | .zero => []
  | .node c m l r =>
      (if c = 0 then [] else [([], c)]) ++
        (toTable m).map (fun p ↦ (none :: p.1, p.2)) ++
        (toTable l).map (fun p ↦ (some 0 :: p.1, p.2)) ++
        (toTable r).map (fun p ↦ (some 1 :: p.1, p.2))

/-- Normalize the central letter and collect coefficients with a prefix tree. -/
def collect [Zero R] [Add R] [DecidableEq R]
    (t : CoeffWordTable.Table R (Option (Fin 2))) : CoeffWordTable.Table R (Option (Fin 2)) :=
  toTable (collectTree (CentralWordTable.normalize t))

section Evaluation

variable {K A : Type*} [Semiring R] [CommSemiring K] [Semiring A] [Algebra K A]

/-- Horner evaluation of a coefficient tree through its coefficient homomorphism. -/
def eval (f : R →+* K) (letters : Option (Fin 2) → A) : Tree R → A
  | .zero => 0
  | .node c m l r =>
      f c • (1 : A) + letters none * eval f letters m +
        letters (some 0) * eval f letters l + letters (some 1) * eval f letters r

/-- Insertion adds exactly the weighted ordered word to the tree's evaluation. -/
theorem eval_insert (f : R →+* K) (letters : Option (Fin 2) → A)
    (w : List (Option (Fin 2))) (c : R) (t : Tree R) :
    eval f letters (insert w c t) = f c • (w.map letters).prod + eval f letters t := by
  induction w generalizing t with
  | nil => cases t <;> simp [insert, eval, map_add, add_smul, add_assoc]
  | cons a w ih =>
      cases a with
      | none =>
          cases t <;>
            simp [insert, eval, ih, mul_add, add_assoc, add_left_comm, add_comm]
      | some a =>
          fin_cases a <;> cases t <;>
            simp [insert, eval, ih, mul_add, add_assoc, add_left_comm, add_comm]

/-- Prefix collection preserves the evaluation of the unnormalized input table. -/
theorem eval_collectTree (f : R →+* K) (letters : Option (Fin 2) → A)
    (t : CoeffWordTable.Table R (Option (Fin 2))) :
    eval f letters (collectTree t) = CoeffWordTable.eval f letters t := by
  induction t with
  | nil => rfl
  | cons p t ih => rw [collectTree, eval_insert, CoeffWordTable.eval_cons, ih]

/-- Converting a tree to its nonzero rows preserves evaluation. -/
theorem eval_toTable [DecidableEq R] (f : R →+* K) (letters : Option (Fin 2) → A)
    (t : Tree R) : CoeffWordTable.eval f letters (toTable t) = eval f letters t := by
  induction t with
  | zero => rfl
  | node c m l r hm hl hr =>
      simp only [toTable, CoeffWordTable.eval_append, CoeffWordTable.eval_map_cons,
        hm, hl, hr, eval]
      by_cases hc : c = 0 <;>
        simp [hc, CoeffWordTable.eval_nil, CoeffWordTable.eval_singleton]

/-- Central normalization followed by prefix collection preserves ordered evaluation. -/
theorem eval_collect [DecidableEq R] (f : R →+* K) (p : K) (letters : Fin 2 → A)
    (t : CoeffWordTable.Table R (Option (Fin 2))) :
    CoeffWordTable.eval f (fun x ↦ match x with | none => p • (1 : A) | some i => letters i)
      (collect t) =
    CoeffWordTable.eval f (fun x ↦ match x with | none => p • (1 : A) | some i => letters i)
      t := by
  rw [collect, eval_toTable, eval_collectTree]
  convert CentralWordTable.eval_normalize f p letters t using 1 <;>
    congr 1 <;> funext x <;> cases x <;> rfl

end Evaluation

end FQFP.CentralBinaryWordTable

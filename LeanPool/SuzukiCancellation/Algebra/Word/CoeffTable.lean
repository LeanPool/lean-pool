/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Ordered word tables with scalar coefficients

A coefficient homomorphism interprets a finite word table in a scalar algebra.
This allows polynomial coefficients to be specialized at a parameter while the
letters retain their noncommutative multiplication order.

## Main definitions

* `Table`: finite lists of words and coefficients.
* `eval`: ordered evaluation through a scalar ring homomorphism.
* `mul`, `smul`, `collapse`: multiplication, scalar multiplication, and collection.

## Main results

* `eval_mul`, `eval_smul`, `eval_collapse`: semantics of the table operations.
* `eval_eq_zero_of_all`: a checked zero coefficient table evaluates to zero.
* `eval_flatMap_range`: evaluation of a finite family of tables is a finite sum.
-/

@[expose] public section

namespace FQFP.CoeffWordTable

/-- A finite table of ordered words with coefficients in `R`. -/
abbrev Table (R κ : Type*) := List (List κ × R)

variable {R K A κ : Type*}

section Operations

/-- The table representing one, with its coefficient on the empty word. -/
def unit [One R] : Table R κ := [([], 1)]

/-- Multiply tables by concatenating words and multiplying coefficients. -/
def mul [Mul R] (s t : Table R κ) : Table R κ :=
  s.flatMap fun p ↦ t.map fun q ↦ (p.1 ++ q.1, p.2 * q.2)

/-- Multiply every coefficient by `c`. -/
def smul [Mul R] (c : R) (t : Table R κ) : Table R κ :=
  t.map fun p ↦ (p.1, c * p.2)

/-- Merge one row into the first row with the same word. -/
def addRow [Add R] [DecidableEq κ] (p : List κ × R) : Table R κ → Table R κ
  | [] => [p]
  | q :: t => if q.1 = p.1 then (p.1, q.2 + p.2) :: t else q :: addRow p t

/-- Collect the rows of a table into an accumulator. -/
def collapseAux [Add R] [DecidableEq κ] : Table R κ → Table R κ → Table R κ
  | [], acc => acc
  | p :: t, acc => collapseAux t (addRow p acc)

/-- Collect equal words, retaining rows whose coefficient becomes zero. -/
def collapse [Add R] [DecidableEq κ] (t : Table R κ) : Table R κ := collapseAux t []

end Operations

section Evaluation

variable [Semiring R] [CommSemiring K] [Semiring A] [Algebra K A]

/-- Interpret the coefficients through `f` and multiply each word's letters in order. -/
def eval (f : R →+* K) (letters : κ → A) (t : Table R κ) : A :=
  (t.map fun p ↦ f p.2 • (p.1.map letters).prod).sum

/-- The empty table evaluates to zero. -/
lemma eval_nil (f : R →+* K) (letters : κ → A) : eval f letters ([] : Table R κ) = 0 := rfl

/-- Evaluation separates the first row from the remaining table. -/
lemma eval_cons (f : R →+* K) (letters : κ → A) (p : List κ × R) (t : Table R κ) :
    eval f letters (p :: t) = f p.2 • (p.1.map letters).prod + eval f letters t := rfl

/-- Evaluation of concatenated tables is the sum of their evaluations. -/
lemma eval_append (f : R →+* K) (letters : κ → A) (s t : Table R κ) :
    eval f letters (s ++ t) = eval f letters s + eval f letters t := by
  simp only [eval, List.map_append, List.sum_append]

/-- A singleton table evaluates to its weighted word. -/
lemma eval_singleton (f : R →+* K) (letters : κ → A) (p : List κ × R) :
    eval f letters [p] = f p.2 • (p.1.map letters).prod := by
  rw [eval_cons, eval_nil, add_zero]

/-- The empty-word unit table evaluates to one. -/
lemma eval_unit (f : R →+* K) (letters : κ → A) : eval f letters unit = 1 := by
  simp [unit, eval_singleton]

private lemma eval_mul_row (f : R →+* K) (letters : κ → A) (p : List κ × R)
    (t : Table R κ) :
    eval f letters (t.map fun q ↦ (p.1 ++ q.1, p.2 * q.2)) =
      (f p.2 • (p.1.map letters).prod) * eval f letters t := by
  induction t with
  | nil => simp [eval_nil]
  | cons q t ih =>
      simp only [List.map_cons, eval_cons, ih, mul_add, map_mul,
        List.map_append, List.prod_append, smul_mul_smul_comm]

/-- Prepending a letter to every word multiplies the evaluation on the left. -/
lemma eval_map_cons (f : R →+* K) (letters : κ → A) (a : κ) (t : Table R κ) :
    eval f letters (t.map fun p ↦ (a :: p.1, p.2)) = letters a * eval f letters t := by
  simpa using eval_mul_row f letters ([a], 1) t

/-- Evaluation preserves table multiplication without commuting the letters. -/
lemma eval_mul (f : R →+* K) (letters : κ → A) (s t : Table R κ) :
    eval f letters (mul s t) = eval f letters s * eval f letters t := by
  induction s with
  | nil => simp [mul, eval_nil]
  | cons p s ih =>
      change eval f letters (List.flatMap
        (fun p ↦ t.map fun q ↦ (p.1 ++ q.1, p.2 * q.2)) (p :: s)) = _
      rw [List.flatMap_cons, eval_append, eval_mul_row, eval_cons, add_mul]
      exact congrArg ((f p.2 • (p.1.map letters).prod) * eval f letters t + ·) ih

/-- Evaluation preserves scalar multiplication of the coefficients. -/
lemma eval_smul (f : R →+* K) (letters : κ → A) (c : R) (t : Table R κ) :
    eval f letters (smul c t) = f c • eval f letters t := by
  induction t with
  | nil => simp [smul, eval_nil]
  | cons p t ih =>
      change f (c * p.2) • (p.1.map letters).prod + eval f letters (smul c t) = _
      rw [map_mul, ih, eval_cons, smul_add, smul_smul]

/-- Adding a row preserves its contribution to the table evaluation. -/
lemma eval_addRow [DecidableEq κ] (f : R →+* K) (letters : κ → A)
    (p : List κ × R) (t : Table R κ) :
    eval f letters (addRow p t) = f p.2 • (p.1.map letters).prod + eval f letters t := by
  induction t with
  | nil => simp [addRow, eval_singleton, eval_nil]
  | cons q t ih =>
      rw [addRow]
      split_ifs with h
      · simp only [eval_cons, h, map_add, add_smul]
        ac_rfl
      · rw [eval_cons, ih, eval_cons]
        ac_rfl

/-- Collection into an accumulator preserves the sum of both evaluations. -/
lemma eval_collapseAux [DecidableEq κ] (f : R →+* K) (letters : κ → A)
    (t acc : Table R κ) :
    eval f letters (collapseAux t acc) = eval f letters t + eval f letters acc := by
  induction t generalizing acc with
  | nil => simp [collapseAux, eval_nil]
  | cons p t ih =>
      rw [collapseAux, ih, eval_addRow, eval_cons]
      ac_rfl

/-- Collecting equal words does not change evaluation. -/
lemma eval_collapse [DecidableEq κ] (f : R →+* K) (letters : κ → A) (t : Table R κ) :
    eval f letters (collapse t) = eval f letters t := by
  rw [collapse, eval_collapseAux, eval_nil, add_zero]

/-- A table with zero coefficients evaluates to zero. -/
lemma eval_eq_zero_of_rows (f : R →+* K) (letters : κ → A) (t : Table R κ)
    (h : ∀ p ∈ t, p.2 = 0) : eval f letters t = 0 := by
  induction t with
  | nil => rfl
  | cons p t ih =>
      rw [eval_cons, h p List.mem_cons_self, map_zero, zero_smul, zero_add]
      exact ih fun q hq ↦ h q (List.mem_cons_of_mem p hq)

/-- A Boolean zero-coefficient certificate implies zero evaluation. -/
lemma eval_eq_zero_of_all [BEq R] [LawfulBEq R]
    (f : R →+* K) (letters : κ → A) (t : Table R κ)
    (h : t.all (fun p ↦ p.2 == 0) = true) : eval f letters t = 0 :=
  eval_eq_zero_of_rows f letters t fun p hp ↦ by
    simpa only [beq_iff_eq] using List.all_eq_true.mp h p hp

/-- A finite family of tables evaluates to the corresponding finite sum. -/
lemma eval_flatMap {ι : Type*} (f : R →+* K) (letters : κ → A)
    (g : ι → Table R κ) (l : List ι) :
    eval f letters (l.flatMap g) = (l.map fun i ↦ eval f letters (g i)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [List.flatMap_cons, eval_append, ih, List.map_cons, List.sum_cons]

/-- A natural-number range of tables evaluates to the corresponding finite sum. -/
lemma eval_flatMap_range (f : R →+* K) (letters : κ → A)
    (g : ℕ → Table R κ) (n : ℕ) :
    eval f letters ((List.range n).flatMap g) = ∑ i ∈ Finset.range n, eval f letters (g i) := by
  induction n with
  | zero => simp [eval_nil]
  | succ n ih =>
      simp only [List.range_succ, List.flatMap_append, eval_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Finset.sum_range_succ, ih]

end Evaluation

end FQFP.CoeffWordTable

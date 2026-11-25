/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Algebra.Word.CoeffTable

/-!
# Collecting words with a central letter

An optional letter distinguishes a central scalar from ordinary noncommuting
letters. Moving the central letters to the beginning of each word preserves
evaluation and allows the existing word collector to combine equal terms.

## Main definitions

* `normalizeWord`: move all central letters to the beginning of a word.
* `normalize`: normalize each word in a coefficient table.
* `collect`: normalize and collect equal words.

## Main results

* `prod_map_eq_pow_smul`: separate a word's central scalar power.
* `eval_normalizeWord`, `eval_normalize`, `eval_collect`: evaluation is preserved.
-/

@[expose] public section

namespace FQFP.CentralWordTable

variable {R K A κ : Type*}

/-- Move all central letters to the beginning, preserving the other letters' order. -/
def normalizeWord [DecidableEq κ] (w : List (Option κ)) : List (Option κ) :=
  List.replicate (w.count none) none ++ (w.filterMap id).map some

/-- Normalize each word without changing its coefficient. -/
def normalize [DecidableEq κ] (t : CoeffWordTable.Table R (Option κ)) :
    CoeffWordTable.Table R (Option κ) :=
  t.map fun row ↦ (normalizeWord row.1, row.2)

/-- Move central letters to the beginning and collect equal words. -/
def collect [Add R] [DecidableEq κ] (t : CoeffWordTable.Table R (Option κ)) :
    CoeffWordTable.Table R (Option κ) := CoeffWordTable.collapse (normalize t)

section Evaluation

variable [CommSemiring K] [Semiring A] [Algebra K A] [DecidableEq κ]

/-- A word's central letters factor out as a scalar power without changing the other order. -/
lemma prod_map_eq_pow_smul (p : K) (letters : κ → A) (w : List (Option κ)) :
    (w.map (fun x ↦ match x with | none => p • (1 : A) | some i => letters i)).prod =
      p ^ w.count none • ((w.filterMap id).map letters).prod := by
  induction w with
  | nil => simp
  | cons x w ih =>
      cases x with
      | none =>
          simp only [List.map_cons, List.prod_cons, List.count_cons_self,
            List.filterMap_cons, id_eq, ih]
          rw [smul_mul_smul_comm, one_mul, pow_succ']
      | some i =>
          simp only [List.map_cons, List.prod_cons,
            List.count_cons_of_ne (by simp : some i ≠ (none : Option κ)),
            List.filterMap_cons, id_eq, ih]
          rw [mul_smul_comm]

/-- Moving central letters to the beginning preserves ordered word evaluation. -/
lemma eval_normalizeWord (p : K) (letters : κ → A) (w : List (Option κ)) :
    ((normalizeWord w).map
      (fun x ↦ match x with | none => p • (1 : A) | some i => letters i)).prod =
      (w.map (fun x ↦ match x with | none => p • (1 : A) | some i => letters i)).prod := by
  rw [prod_map_eq_pow_smul p letters w]
  simp [normalizeWord, List.map_map, Function.comp_def, smul_pow]

variable [Semiring R]

/-- Normalizing each word preserves the table's scalar-algebra evaluation. -/
lemma eval_normalize (f : R →+* K) (p : K) (letters : κ → A)
    (t : CoeffWordTable.Table R (Option κ)) :
    CoeffWordTable.eval f (fun x ↦ match x with | none => p • (1 : A) | some i => letters i)
      (normalize t) =
    CoeffWordTable.eval f (fun x ↦ match x with | none => p • (1 : A) | some i => letters i)
      t := by
  induction t with
  | nil => rfl
  | cons row t ih =>
      change f row.2 • ((normalizeWord row.1).map _).prod +
          CoeffWordTable.eval f _ (normalize t) = _
      rw [CoeffWordTable.eval_cons, eval_normalizeWord, ih]

/-- Collection after central normalization preserves evaluation. -/
lemma eval_collect (f : R →+* K) (p : K) (letters : κ → A)
    (t : CoeffWordTable.Table R (Option κ)) :
    CoeffWordTable.eval f (fun x ↦ match x with | none => p • (1 : A) | some i => letters i)
      (collect t) =
    CoeffWordTable.eval f (fun x ↦ match x with | none => p • (1 : A) | some i => letters i)
      t := by
  rw [collect, CoeffWordTable.eval_collapse, eval_normalize]

end Evaluation

end FQFP.CentralWordTable

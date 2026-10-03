/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalLoweringDerived

/-! NF weak partition development: NominalRenamingLemmas. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore

/-! Functoriality of nominal lowering under a de-Bruijn variable renaming.

This is the structural bridge needed by binder-permutation rules such as
Metamath `ax-7`: instead of proving a fresh equality for every generated
application, the certificate compiler can instantiate one kernel-checked
renaming theorem.
-/


/-- Extend a renaming under one de-Bruijn binder. -/
@[expose]
def underBinder (sigma : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sigma n + 1

/-- Apply a de-Bruijn renaming to a (possibly partially applied) term. -/
@[expose]
def renameTerm (sigma : Nat → Nat) : ∀ {l}, Fol.preterm LNF l → Fol.preterm LNF l
  | _, .var n => .var (sigma n)
  | _, .func f => .func f
  | _, .app t s => .app (renameTerm sigma t) (renameTerm sigma s)

/-- Apply a de-Bruijn renaming to a (possibly partially applied) formula. -/
@[expose]
def renameFormula (sigma : Nat → Nat) :
    ∀ {l}, @Fol.preformula LNF l → @Fol.preformula LNF l
  | _, .falsum => .falsum
  | _, .equal s t => .equal (renameTerm sigma s) (renameTerm sigma t)
  | _, .rel r => .rel r
  | _, .apprel p t => .apprel (renameFormula sigma p) (renameTerm sigma t)
  | _, .imp p q => .imp (renameFormula sigma p) (renameFormula sigma q)
  | _, .all p => .all (renameFormula (underBinder sigma) p)

@[expose]
def renameRho (sigma : Nat → Nat) (rho : Var → Nat) : Var → Nat := fun x => sigma (rho x)

@[simp]
theorem underBinder_zero (sigma : Nat → Nat) : underBinder sigma 0 = 0 :=
  rfl

@[simp]
theorem underBinder_succ (sigma : Nat → Nat) (n : Nat) :
    underBinder sigma (n + 1) = sigma n + 1 :=
  rfl

theorem renameRho_update (sigma : Nat → Nat) (rho : Var → Nat) (x : Var)
    (candidate : Nat) :
    renameRho sigma (updateRho rho x candidate) =
      updateRho (renameRho sigma rho) x (sigma candidate) :=
  by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [renameRho, updateRho]
  · simp [renameRho, updateRho, hy]

theorem renameRho_bind (sigma : Nat → Nat) (rho : Var → Nat) (x : Var) :
    renameRho (underBinder sigma) (bindRho rho x) = bindRho (renameRho sigma rho) x :=
  by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [renameRho, bindRho]
  · simp [renameRho, bindRho, underBinder, hy]

theorem renameRho_lift (sigma : Nat → Nat) (rho : Var → Nat) :
    renameRho (underBinder sigma) (liftRho rho) = liftRho (renameRho sigma rho) :=
  by
  funext y
  simp [renameRho, liftRho, underBinder]

mutual
  theorem lowerClassPred_rename (sigma : Nat → Nat) (rho : Var → Nat) (candidate : Nat)
      (A : Class) :
      lowerClassPred (renameRho sigma rho) (sigma candidate) A =
        renameFormula sigma (lowerClassPred rho candidate A) :=
    by
    cases A with
    | cv x => rfl
    | cab x p =>
      simp only [lowerClassPred]
      rw [← renameRho_update]
      exact lowerWff_rename sigma (updateRho rho x candidate) p
  theorem lowerWff_rename (sigma : Nat → Nat) (rho : Var → Nat) (p : Wff) :
      lowerWff (renameRho sigma rho) p = renameFormula sigma (lowerWff rho p) := by
    cases p with
    | falsum => rfl
    | imp p q =>
      simp only [lowerWff, renameFormula]
      rw [lowerWff_rename sigma rho p, lowerWff_rename sigma rho q]
    | all x p =>
      simp only [lowerWff, renameFormula]
      rw [← renameRho_bind]
      exact
        congrArg Fol.preformula.all
          (lowerWff_rename (underBinder sigma) (bindRho rho x) p)
    | objEq x y => rfl
    | objMem x y => rfl
    | classEq A B =>
      simp only [lowerWff, renameFormula, biimp, conj, neg]
      rw [← renameRho_lift]
      have hA :
        lowerClassPred (renameRho (underBinder sigma) (liftRho rho)) 0 A =
          renameFormula (underBinder sigma) (lowerClassPred (liftRho rho) 0 A) :=
        by simpa using (lowerClassPred_rename (underBinder sigma) (liftRho rho) 0 A)
      have hB :
        lowerClassPred (renameRho (underBinder sigma) (liftRho rho)) 0 B =
          renameFormula (underBinder sigma) (lowerClassPred (liftRho rho) 0 B) :=
        by simpa using (lowerClassPred_rename (underBinder sigma) (liftRho rho) 0 B)
      rw [hA, hB]
    | classMem A
      B =>
      simp only [lowerWff, renameFormula, ex, conj, neg, biimp]
      rw [← renameRho_lift sigma rho]
      rw [← renameRho_lift (underBinder sigma) (liftRho rho)]
      have hA :
        lowerClassPred
            (renameRho (underBinder (underBinder sigma)) (liftRho (liftRho rho))) 0 A =
          renameFormula (underBinder (underBinder sigma))
            (lowerClassPred (liftRho (liftRho rho)) 0 A) :=
        by
        simpa using
          (lowerClassPred_rename (underBinder (underBinder sigma)) (liftRho (liftRho rho)) 0 A)
      have hB :
        lowerClassPred (renameRho (underBinder sigma) (liftRho rho)) 0 B =
          renameFormula (underBinder sigma) (lowerClassPred (liftRho rho) 0 B) :=
        by simpa using (lowerClassPred_rename (underBinder sigma) (liftRho rho) 0 B)
      rw [hA, hB]
      simp [GenericLogicalHandlers.nfMem, renameFormula, renameTerm, underBinder]
end


end NFChoice.DirectNominalPrf.Nominal

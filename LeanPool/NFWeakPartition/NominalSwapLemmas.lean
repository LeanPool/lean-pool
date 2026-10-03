/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalRenamingLemmas

/-! NF weak partition development: NominalSwapLemmas. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore

/-! The concrete adjacent de-Bruijn permutation used by Metamath `ax-7`. -/


/-- Swap indices `depth` and `depth + 1`, fixing every other index. -/
@[expose]
def swapIndexAt (depth index : Nat) : Nat :=
  if index = depth then depth + 1 else if index = depth + 1 then depth else index

@[expose]
def liftIndexAt (index amount cutoff : Nat) : Nat :=
  if cutoff ≤ index then index + amount else index

@[expose]
def substIndexAt (index replacement target : Nat) : Nat :=
  if index < target then index
  else if target < index then index - 1 else replacement + target

@[simp]
theorem liftTermAt_var (index amount cutoff : Nat) :
    Fol.lift_term_at (&index : Fol.term LNF) amount cutoff =
      &(liftIndexAt index amount cutoff) :=
  by rfl

@[simp]
theorem substTerm_var_var (index replacement target : Nat) :
    Fol.subst_term (&index : Fol.term LNF) (&replacement) target =
      &(substIndexAt index replacement target) :=
  by
  simp [Fol.subst_term, Fol.subst_realize, substIndexAt]
  split_ifs <;> rfl

theorem swapIndexAt_numeric (depth index : Nat) :
    swapIndexAt depth index =
      substIndexAt
        (substIndexAt (liftIndexAt (liftIndexAt index 1 (depth + 2)) 1 (depth + 2)) 0
          (depth + 1))
        1 depth :=
  by
  simp [swapIndexAt, liftIndexAt, substIndexAt]
  split_ifs <;> omega

/-- Flypitch's lift/substitute presentation of the same term permutation. -/
@[expose]
def swapTermAt (depth : Nat) {l : Nat} (t : Fol.preterm LNF l) : Fol.preterm LNF l :=
  Fol.subst_term
    (Fol.subst_term (Fol.lift_term_at (Fol.lift_term_at t 1 (depth + 2)) 1 (depth + 2))
      (&0) (depth + 1))
    (&1) depth

/-- Flypitch's lift/substitute presentation of the same formula permutation. -/
@[expose]
def swapFormulaAt (depth : Nat) {l : Nat} (p : @Fol.preformula LNF l) :
    @Fol.preformula LNF l :=
  Fol.subst_formula
    (Fol.subst_formula
      (Fol.lift_formula_at (Fol.lift_formula_at p 1 (depth + 2)) 1 (depth + 2)) (&0)
      (depth + 1))
    (&1) depth

theorem underBinder_swapIndexAt (depth : Nat) :
    underBinder (swapIndexAt depth) = swapIndexAt (depth + 1) :=
  by
  funext index
  cases index with
  | zero => simp [underBinder, swapIndexAt]
  | succ index =>
    simp [underBinder, swapIndexAt]
    split_ifs <;> omega

theorem renameTerm_swapIndexAt (depth : Nat) :
    ∀ {l : Nat} (t : Fol.preterm LNF l),
      renameTerm (swapIndexAt depth) t = swapTermAt depth t :=
  by
  intro l t
  induction t with
  | var
    index =>
    simp only [renameTerm, swapTermAt, liftTermAt_var, substTerm_var_var]
    exact congrArg Fol.preterm.var (swapIndexAt_numeric depth index)
  | func f => rfl
  | app t s iht ihs => simp [renameTerm, swapTermAt, Fol.lift_term_at, iht, ihs]

theorem renameFormula_swapIndexAt :
    ∀ (depth : Nat) {l : Nat} (p : @Fol.preformula LNF l),
      renameFormula (swapIndexAt depth) p = swapFormulaAt depth p :=
  by
  intro depth l p
  induction p generalizing depth with
  | falsum => rfl
  | equal s t =>
    simp [renameFormula, swapFormulaAt, Fol.lift_formula_at, Fol.subst_formula,
      swapTermAt, renameTerm_swapIndexAt]
  | rel r => rfl
  | apprel p t ih =>
    simp [renameFormula, swapFormulaAt, Fol.lift_formula_at, Fol.subst_formula,
      swapTermAt, ih, renameTerm_swapIndexAt]
  | imp p q ihp ihq =>
    simp [renameFormula, swapFormulaAt, Fol.lift_formula_at, Fol.subst_formula, ihp, ihq]
  | all p ih =>
    rw [renameFormula]
    rw [underBinder_swapIndexAt]
    rw [ih (depth + 1)]
    simp [swapFormulaAt, Fol.lift_formula_at, Fol.subst_formula, Nat.add_assoc]

theorem renameFormula_swap01 (p : Fol.formula LNF) :
    renameFormula (swapIndexAt 0) p = GenericLogicalHandlers.swap01 p := by
  simpa [swapFormulaAt, GenericLogicalHandlers.swap01] using
    (renameFormula_swapIndexAt 0 p)

theorem renameRho_swap_bind_bind (rho : Var → Nat) (x y : Var) (hyx : y ≠ x) :
    renameRho (swapIndexAt 0) (bindRho (bindRho rho x) y) = bindRho (bindRho rho y) x :=
  by
  funext z
  by_cases hzx : z = x
  · subst z
    simp [renameRho, swapIndexAt, bindRho, Ne.symm hyx]
  · by_cases hzy : z = y
    · subst z
      simp [renameRho, swapIndexAt, bindRho, hyx]
    · simp [renameRho, swapIndexAt, bindRho, hzx, hzy]

theorem lowerWff_bind_swap (rho : Var → Nat) (x y : Var) (p : Wff) (hyx : y ≠ x) :
    lowerWff (bindRho (bindRho rho y) x) p =
      GenericLogicalHandlers.swap01 (lowerWff (bindRho (bindRho rho x) y) p) :=
  by
  calc
    lowerWff (bindRho (bindRho rho y) x) p =
        lowerWff (renameRho (swapIndexAt 0) (bindRho (bindRho rho x) y)) p :=
      by rw [renameRho_swap_bind_bind rho x y hyx]
    _ = renameFormula (swapIndexAt 0) (lowerWff (bindRho (bindRho rho x) y) p) :=
      (lowerWff_rename (swapIndexAt 0) (bindRho (bindRho rho x) y) p)
    _ = GenericLogicalHandlers.swap01 (lowerWff (bindRho (bindRho rho x) y) p) :=
      renameFormula_swap01 _

/-- Total kernel-checked nominal implementation of Metamath `ax-7`. -/
@[expose]
def ax7Structural (x y : Var) (p : Wff) :
    NPrf (.imp (.all x (.all y p)) (.all y (.all x p))) :=
  ax7 x y p (fun rho hyx => lowerWff_bind_swap rho x y p hyx)


end NFChoice.DirectNominalPrf.Nominal

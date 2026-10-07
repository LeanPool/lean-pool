/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalSwapLemmas

/-! NF weak partition development: NominalSubstitutionLemmas. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore

/-! Substitution naturality for nominal lowering.  This supplies the one-hole
template required by Flypitch's syntactic proof of Metamath `ax-11`.
-/


theorem underBinder_substIndexAt (replacement depth : Nat) :
    underBinder (fun index => substIndexAt index replacement depth) = fun index =>
      substIndexAt index replacement (depth + 1) :=
  by
  funext index
  cases index with
  | zero => simp [underBinder, substIndexAt]
  | succ index =>
    simp [underBinder, substIndexAt]
    split_ifs <;> omega

theorem renameTerm_substIndexAt (replacement depth : Nat) :
    ∀ {l : Nat} (t : Fol.preterm LNF l),
      renameTerm (fun index => substIndexAt index replacement depth) t =
        Fol.substTerm t (&replacement) depth :=
  by
  intro l t
  induction t with
  | var index => simp [renameTerm, substTerm_var_var]
  | func f => rfl
  | app t s iht ihs => simp [renameTerm, Fol.substTerm, iht, ihs]

theorem renameFormula_substIndexAt :
    ∀ (replacement depth : Nat) {l : Nat} (p : @Fol.preformula LNF l),
      renameFormula (fun index => substIndexAt index replacement depth) p =
        Fol.substFormula p (&replacement) depth :=
  by
  intro replacement depth l p
  induction p generalizing depth with
  | falsum => rfl
  | equal s t => simp [renameFormula, Fol.substFormula, renameTerm_substIndexAt]
  | rel r => rfl
  | apprel p t ih => simp [renameFormula, Fol.substFormula, ih, renameTerm_substIndexAt]
  | imp p q ihp ihq => simp [renameFormula, Fol.substFormula, ihp, ihq]
  | all p ih =>
    rw [renameFormula]
    rw [underBinder_substIndexAt]
    rw [ih (depth + 1)]
    rfl

theorem renameRho_subst_bind_lift (rho : Var → Nat) (x : Var) (replacement : Nat) :
    renameRho (fun index => substIndexAt index replacement 0) (bindRho (liftRho rho) x) =
      updateRho (liftRho rho) x replacement :=
  by
  funext y
  by_cases hy : y = x
  · subst y
    simp [renameRho, substIndexAt, bindRho, updateRho]
  · simp [renameRho, substIndexAt, bindRho, liftRho, updateRho, hy]

theorem lowerWff_template_subst (rho : Var → Nat) (x : Var) (replacement : Nat)
    (p : Wff) :
    (lowerWff (bindRho (liftRho rho) x) p) [(&replacement) // 0]f =
      lowerWff (updateRho (liftRho rho) x replacement) p :=
  by
  calc
    (lowerWff (bindRho (liftRho rho) x) p) [(&replacement) // 0]f =
        renameFormula (fun index => substIndexAt index replacement 0)
          (lowerWff (bindRho (liftRho rho) x) p) :=
      by
      symm
      exact renameFormula_substIndexAt replacement 0 _
    _ =
        lowerWff
          (renameRho (fun index => substIndexAt index replacement 0) (bindRho (liftRho rho) x))
          p :=
      by
      symm
      exact
        lowerWff_rename (fun index => substIndexAt index replacement 0)
          (bindRho (liftRho rho) x) p
    _ = lowerWff (updateRho (liftRho rho) x replacement) p := by
      rw [renameRho_subst_bind_lift]

theorem shiftRhoAt_bind_one (rho : Var → Nat) (x : Var) :
    shiftRhoAt (bindRho rho x) 1 = bindRho (liftRho rho) x :=
  by
  rw [show (1 : Nat) = 0 + 1 by rfl]
  rw [shiftRhoAt_bind]
  congr 1

theorem ax11Inst_lowerWff (rho : Var → Nat) (y : Var) (p : Wff) :
    GenericLogicalHandlers.ax11Inst (lowerWff (bindRho rho y) p) (&(rho y)) =
      lowerWff (liftRho rho) p :=
  by
  unfold GenericLogicalHandlers.ax11Inst
  rw [← lowerWff_shiftAt (bindRho rho y) 1 p]
  rw [shiftRhoAt_bind_one]
  have h := lowerWff_template_subst rho y (rho y + 1) p
  have hUpdate : updateRho (liftRho rho) y (rho y + 1) = liftRho rho :=
    by
    funext z
    by_cases hz : z = y
    · subst z
      simp [updateRho, liftRho]
    · simp [updateRho, hz]
  rw [hUpdate] at h
  simpa [Fol.liftTerm1, Fol.liftTermAt, liftIndexAt] using h

/-- Total kernel-checked nominal implementation of Metamath `ax-11`. -/
@[expose]
noncomputable def ax11Structural (x y : Var) (p : Wff) :
    NPrf (.imp (.objEq x y) (.imp (.all y p) (.all x (.imp (.objEq x y) p)))) :=
  ax11 x y p (fun rho => lowerWff (bindRho (liftRho rho) x) p)
    (fun rho _hyx => by
      calc
        GenericLogicalHandlers.ax11Inst (lowerWff (bindRho rho y) p) (&(rho y)) =
            lowerWff (liftRho rho) p :=
          ax11Inst_lowerWff rho y p
        _ = (lowerWff (bindRho (liftRho rho) x) p) [Fol.liftTerm1 (&(rho x)) // 0]f :=
          by
          symm
          have h := lowerWff_template_subst rho x (rho x + 1) p
          have hUpdate : updateRho (liftRho rho) x (rho x + 1) = liftRho rho :=
            by
            funext z
            by_cases hz : z = x
            · subst z
              simp [updateRho, liftRho]
            · simp [updateRho, hz]
          rw [hUpdate] at h
          simpa [Fol.liftTerm1, Fol.liftTermAt, liftIndexAt] using h)
    (fun rho _hyx => by
      have h := lowerWff_template_subst rho x 0 p
      rw [show updateRho (liftRho rho) x 0 = bindRho rho x from rfl] at h
      exact h)


end NFChoice.DirectNominalPrf.Nominal

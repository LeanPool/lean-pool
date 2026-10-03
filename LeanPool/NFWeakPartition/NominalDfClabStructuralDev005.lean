/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalDfClabProperSubstitutionCoreDev003
public import LeanPool.NFWeakPartition.NominalDefinitionLeafAdapterDev014

/-! NF weak partition development: NominalDfClabStructuralDev005. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.DfClabStructuralDev005

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005
open NFChoice.DirectCertificate.ClassBoundaryCoreDev006
open NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011
open NFChoice.DirectNominalPrf.Nominal.DefinitionLeafAdapterDev014
open NFChoice.DirectNominalPrf.Nominal.DfClabProperSubstitutionCoreDev003

abbrev Theory : Fol.SentTheory LNF :=
  LiteralHailperinNF

theorem renameRho_subst_bind (rho : Var → Nat) (x : Var) (replacement : Nat) :
    renameRho (fun index => substIndexAt index replacement 0) (bindRho rho x) =
      updateRho rho x replacement :=
  by
  funext y
  by_cases hy : y = x
  · subst y
    simp [renameRho, substIndexAt, bindRho, updateRho]
  · simp [renameRho, substIndexAt, bindRho, updateRho, hy]

theorem lowerWff_bound_subst (rho : Var → Nat) (x : Var) (replacement : Nat) (p : Wff) :
    (lowerWff (bindRho rho x) p) [(&replacement) // 0]f =
      lowerWff (updateRho rho x replacement) p :=
  by
  calc
    (lowerWff (bindRho rho x) p) [(&replacement) // 0]f =
        renameFormula (fun index => substIndexAt index replacement 0)
          (lowerWff (bindRho rho x) p) :=
      by
      symm
      exact renameFormula_substIndexAt replacement 0 _
    _ =
        lowerWff
          (renameRho (fun index => substIndexAt index replacement 0) (bindRho rho x)) p :=
      by
      symm
      exact
        lowerWff_rename (fun index => substIndexAt index replacement 0) (bindRho rho x) p
    _ = lowerWff (updateRho rho x replacement) p := by rw [renameRho_subst_bind]

theorem updateRho_self (rho : Var → Nat) (x : Var) : updateRho rho x (rho x) = rho :=
  by
  funext y
  by_cases hy : y = x
  · subst y
    simp [updateRho]
  · simp [updateRho, hy]

theorem updateRho_lift_zero_eq_bind (rho : Var → Nat) (x : Var) :
    updateRho (liftRho rho) x 0 = bindRho rho x :=
  by
  funext y
  by_cases hy : y = x
  · subst y
    simp [updateRho, bindRho]
  · simp [updateRho, bindRho, liftRho, hy]

theorem classPred_cv (rho : Var → Nat) (x : Var) :
    classPred rho (.cv x) = cvPred (&(rho x)) := by
  simp [classPred, lowerClassPred, cvPred, mem, liftRho, GenericLogicalHandlers.nfMem,
    Fol.lift_term1]

theorem classPred_cab (rho : Var → Nat) (x : Var) (p : Wff) :
    classPred rho (.cab x p) = lowerWff (bindRho rho x) p :=
  by
  unfold classPred
  rw [lowerClassPred, updateRho_lift_zero_eq_bind]

theorem lowerWff_sbDefiniens_ne (rho : Var → Nat) (x y : Var) (p : Wff) (hxy : x ≠ y) :
    lowerWff rho (sbDefiniens x y p) =
      properSubstRhs (lowerWff (bindRho rho y) p) (&(rho x)) (&(rho y)) :=
  by
  have hOriginal := lowerWff_bound_subst rho y (rho y) p
  rw [updateRho_self] at hOriginal
  simp only [sbDefiniens, Wff.conj, Wff.ex, Wff.neg, lowerWff]
  rw [← hOriginal]
  simp [properSubstRhs, bindRho, hxy, Fol.and', Fol.not', Fol.ex', Fol.lift_term1]

theorem lowerWff_sbDefiniens_same (rho : Var → Nat) (x : Var) (p : Wff) :
    lowerWff rho (sbDefiniens x x p) =
      coincidentSubstRhs (lowerWff (bindRho rho x) p) (&(rho x)) :=
  by
  have hOriginal := lowerWff_bound_subst rho x (rho x) p
  rw [updateRho_self] at hOriginal
  simp only [sbDefiniens, Wff.conj, Wff.ex, Wff.neg, lowerWff]
  rw [← hOriginal]
  simp [coincidentSubstRhs, bindRho, Fol.and', Fol.not', Fol.ex']

@[expose]
noncomputable def dfClabStructural (x y : Var) (p : Wff) : NPrf (dfClabGoal x y p) :=
  fun rho =>
  by
  change
    Theory.fst ⊢
      lowerWff rho (.classMem (.cv x) (.cab y p)) ⇔ lowerWff rho (sbDefiniens x y p)
  rw [lowerWff_classMem, classPred_cv, classPred_cab]
  by_cases hxy : x = y
  · subst y
    rw [lowerWff_sbDefiniens_same]
    exact
      Fol.biimp_trans (classMemCv (&(rho x)) (lowerWff (bindRho rho x) p))
        (coincidentSubstCore (lowerWff (bindRho rho x) p) (&(rho x)))
  · rw [lowerWff_sbDefiniens_ne rho x y p hxy]
    exact
      Fol.biimp_trans (classMemCv (&(rho x)) (lowerWff (bindRho rho y) p))
        (properSubstCore (lowerWff (bindRho rho y) p) (&(rho x)) (&(rho y)))


end NFChoice.DirectNominalPrf.Nominal.DfClabStructuralDev005

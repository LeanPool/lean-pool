/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.PartialTotalizationBridgeDev002

/-! NF weak partition development: BoundedNominalLoweringBridgeDev004. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.BoundedNominalLoweringBridgeDev004

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore

@[expose]
def finValRho {n : Nat} (rho : Var → Fin n) : Var → Nat := fun x => (rho x).val

theorem finVal_update {n : Nat} (rho : Var → Fin n) (x : Var) (value : Fin n) :
    finValRho (Function.update rho x value) = updateRho (finValRho rho) x value.val :=
  by
  funext y
  by_cases hyx : y = x <;> simp [finValRho, updateRho, Function.update, hyx]

theorem finVal_lift {n : Nat} (rho : Var → Fin n) :
    finValRho (NFChoice.SemanticCore.Lowering.liftRho rho) = liftRho (finValRho rho) :=
  by
  funext x
  simp [finValRho, NFChoice.SemanticCore.Lowering.liftRho, liftRho]

theorem finVal_bind {n : Nat} (rho : Var → Fin n) (x : Var) :
    finValRho (NFChoice.SemanticCore.Lowering.bindRho rho x) =
      bindRho (finValRho rho) x :=
  by
  funext y
  by_cases hyx : y = x <;>
    simp [finValRho, NFChoice.SemanticCore.Lowering.bindRho,
      NFChoice.SemanticCore.Lowering.liftRho, bindRho, Function.update, hyx]

mutual
  theorem lowerClassPred_toFlypitch {n : Nat} (rho : Var → Fin n) (candidate : Fin n)
      (A : Class) :
      lowerClassPred (finValRho rho) candidate.val A =
        ((NFChoice.SemanticCore.Lowering.lowerClassPred rho candidate A).toFlypitch).fst :=
    by
    cases A with
    | cv x => rfl
    | cab x
      p =>
      have ih := lowerWff_toFlypitch (Function.update rho x candidate) p
      simpa [lowerClassPred, NFChoice.SemanticCore.Lowering.lowerClassPred,
        finVal_update] using ih
  theorem lowerWff_toFlypitch {n : Nat} (rho : Var → Fin n) (p : Wff) :
      lowerWff (finValRho rho) p =
        ((NFChoice.SemanticCore.Lowering.lowerWff rho p).toFlypitch).fst :=
    by
    cases p with
    | falsum => rfl
    | imp p
      q =>
      simp only [lowerWff, NFChoice.SemanticCore.Lowering.lowerWff, Formula.toFlypitch,
        Fol.bounded_preformula.fst]
      rw [lowerWff_toFlypitch rho p, lowerWff_toFlypitch rho q]
    | all x
      p =>
      have ih := lowerWff_toFlypitch (NFChoice.SemanticCore.Lowering.bindRho rho x) p
      simpa [lowerWff, NFChoice.SemanticCore.Lowering.lowerWff, Formula.toFlypitch,
        finVal_bind] using congrArg Fol.preformula.all ih
    | objEq x y => rfl
    | objMem x y => rfl
    | classEq A
      B =>
      have ihA :=
        lowerClassPred_toFlypitch (NFChoice.SemanticCore.Lowering.liftRho rho) 0 A
      have ihB :=
        lowerClassPred_toFlypitch (NFChoice.SemanticCore.Lowering.liftRho rho) 0 B
      simpa [lowerWff, NFChoice.SemanticCore.Lowering.lowerWff, Formula.toFlypitch,
        Formula.biimp, Formula.conj, Formula.neg, biimp, conj, neg, finVal_lift,
        Fol.bounded_preformula.fst] using
        congrArg₂ (fun p q => Fol.preformula.all (biimp p q)) ihA ihB
    | classMem A
      B =>
      have ihA :=
        lowerClassPred_toFlypitch
          (NFChoice.SemanticCore.Lowering.liftRho (NFChoice.SemanticCore.Lowering.liftRho rho))
          0 A
      have ihB :=
        lowerClassPred_toFlypitch (NFChoice.SemanticCore.Lowering.liftRho rho) 0 B
      simp only [finVal_lift] at ihA ihB
      have ihA' :
        lowerClassPred (liftRho (liftRho (finValRho rho))) 0 A =
          ((NFChoice.SemanticCore.Lowering.lowerClassPred
                (NFChoice.SemanticCore.Lowering.liftRho
                  (NFChoice.SemanticCore.Lowering.liftRho rho)) 0 A).toFlypitch).fst :=
        by simpa using ihA
      have ihB' :
        lowerClassPred (liftRho (finValRho rho)) 0 B =
          ((NFChoice.SemanticCore.Lowering.lowerClassPred
                (NFChoice.SemanticCore.Lowering.liftRho rho) 0 B).toFlypitch).fst :=
        by simpa using ihB
      simp only [lowerWff, NFChoice.SemanticCore.Lowering.lowerWff]
      rw [ihA', ihB']
      rfl
end


end NFChoice.DirectNominalPrf.Nominal.BoundedNominalLoweringBridgeDev004

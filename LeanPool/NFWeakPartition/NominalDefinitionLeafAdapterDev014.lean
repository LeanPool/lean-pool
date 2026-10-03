/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalLoweringLemmas
public import LeanPool.NFWeakPartition.NominalClassHandlersDev011

/-! NF weak partition development: NominalDefinitionLeafAdapterDev014. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.DefinitionLeafAdapterDev014

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005
open NFChoice.DirectCertificate.ClassBoundaryCoreDev006
open NFChoice.DirectCertificate.ClassBoundaryRawHandlersDev010
open NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011

/-! Exporter-facing adapters for the three non-identity Metamath definitions.

The source replay has already checked every substituted `$d` pair.  These
lemmas turn the resulting `x ∉ A.fv` evidence into the exact de-Bruijn
lowering equalities expected by `dfCleqOfShift` and `dfClelOfShift`.
-/


theorem shiftRhoAt_lift_one (rho : Var → Nat) :
    shiftRhoAt (liftRho rho) 1 = liftRho (liftRho rho) :=
  by
  funext x
  simp [shiftRhoAt, liftRho, shiftIndexAt]

theorem classPred_double_lift (rho : Var → Nat) (A : Class) :
    lowerClassPred (liftRho (liftRho rho)) 0 A =
      Fol.lift_formula_at (classPred rho A) 1 1 :=
  by
  unfold classPred
  rw [← shiftRhoAt_lift_one]
  simpa [shiftIndexAt] using (lowerClassPred_shiftAt (liftRho rho) 0 1 A)

theorem classPred_bind_eq_lift_of_not_mem_fv (rho : Var → Nat) (x : Var) (A : Class)
    (hx : x ∉ A.fv) :
    lowerClassPred (liftRho (bindRho rho x)) 0 A =
      Fol.lift_formula_at (classPred rho A) 1 1 :=
  by
  unfold classPred
  calc
    lowerClassPred (liftRho (bindRho rho x)) 0 A =
        lowerClassPred (shiftRhoAt (liftRho rho) 1) 0 A :=
      by
      apply lowerClassPred_congr_fv
      intro y hy
      have hyx : y ≠ x := by
        intro h
        subst y
        exact hx hy
      simp [liftRho, bindRho, shiftRhoAt, shiftIndexAt, hyx]
    _ = Fol.lift_formula_at (lowerClassPred (liftRho rho) 0 A) 1 1 := by
      simpa [shiftIndexAt] using (lowerClassPred_shiftAt (liftRho rho) 0 1 A)

theorem classPred_bind_cv_self (rho : Var → Nat) (x : Var) :
    classPred (bindRho rho x) (.cv x) = cvPred (&0) := by
  simp [classPred, lowerClassPred, liftRho, bindRho, cvPred, mem,
    GenericLogicalHandlers.nfMem, Fol.lift_term1]

theorem lowerClassPred_bind_cv_self (rho : Var → Nat) (x : Var) :
    lowerClassPred (liftRho (bindRho rho x)) 0 (.cv x) = cvPred (&0) := by
  simpa [classPred] using classPred_bind_cv_self rho x

theorem lowerWff_classEq (rho : Var → Nat) (A B : Class) :
    lowerWff rho (.classEq A B) = classEq (classPred rho A) (classPred rho B) := by rfl

theorem lowerWff_classMem (rho : Var → Nat) (A B : Class) :
    lowerWff rho (.classMem A B) = classMem (classPred rho A) (classPred rho B) :=
  by
  rw [lowerWff, classMem, represents, classPred_double_lift]
  rfl

theorem lowerWff_bind_classMem_cv_of_not_mem_fv (rho : Var → Nat) (x : Var) (A : Class)
    (hx : x ∉ A.fv) :
    lowerWff (bindRho rho x) (.classMem (.cv x) A) = liftedClassMem (classPred rho A) :=
  by
  rw [lowerWff, liftedClassMem, classMem, represents, classPred_double_lift,
    classPred_bind_eq_lift_of_not_mem_fv rho x A hx, classPred_bind_cv_self]
  rfl

theorem lowerWff_bind_classEq_cv_of_not_mem_fv (rho : Var → Nat) (x : Var) (A : Class)
    (hx : x ∉ A.fv) :
    lowerWff (bindRho rho x) (.classEq (.cv x) A) =
      represents (&0) (Fol.lift_formula_at (classPred rho A) 1 1) :=
  by
  rw [lowerWff, represents, classPred_bind_eq_lift_of_not_mem_fv rho x A hx,
    lowerClassPred_bind_cv_self]
  rfl

/-- Direct adapter for the exact `df-cleq` source signature. -/
@[expose]
noncomputable def dfCleqOfDV (x y z : Var) (A B : Class)
    (hAxExt : NPrf
        (.imp (.all x (Wff.biimp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z))))
          (.classEq (.cv y) (.cv z))))
    (hxA : x ∉ A.fv) (hxB : x ∉ B.fv) : NPrf (dfCleqGoal x A B) :=
  dfCleqOfShift x y z A B hAxExt (fun rho => lowerWff_classEq rho A B)
    (fun rho => lowerWff_bind_classMem_cv_of_not_mem_fv rho x A hxA)
    (fun rho => lowerWff_bind_classMem_cv_of_not_mem_fv rho x B hxB)

/-- Direct adapter for the exact `df-clel` source signature. -/
@[expose]
noncomputable def dfClelOfDV (x : Var) (A B : Class) (hxA : x ∉ A.fv) (hxB : x ∉ B.fv) :
    NPrf (dfClelGoal x A B) :=
  dfClelOfShift x A B (fun rho => lowerWff_classMem rho A B)
    (fun rho => lowerWff_bind_classEq_cv_of_not_mem_fv rho x A hxA)
    (fun rho => lowerWff_bind_classMem_cv_of_not_mem_fv rho x B hxB)


end NFChoice.DirectNominalPrf.Nominal.DefinitionLeafAdapterDev014

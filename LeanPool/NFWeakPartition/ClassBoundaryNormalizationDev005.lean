/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalCertificate

/-! NF weak partition development: ClassBoundaryNormalizationDev005. -/


public section

namespace NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005

open scoped Fol
open NFChoice.Foundation

@[expose]
def mem (s t : Fol.term LNF) : Fol.formula LNF :=
  Fol.preformula.apprel (Fol.preformula.apprel (Fol.preformula.rel LNFRelation.mem) s) t

@[expose]
def cvPred (x : Fol.term LNF) : Fol.formula LNF :=
  mem (&0) (Fol.lift_term1 x)

@[expose]
def applyPred (P : Fol.formula LNF) (x : Fol.term LNF) : Fol.formula LNF :=
  P [x // 0]f

@[expose]
def represents (x : Fol.term LNF) (P : Fol.formula LNF) : Fol.formula LNF :=
  ∀'((mem (&0) (Fol.lift_term1 x)) ⇔ P)

theorem cvPredLiftForWitness (x : Fol.term LNF) :
    cvPred (Fol.lift_term1 x) = Fol.lift_formula_at (cvPred x) 1 1 :=
  by
  have hterm :
    Fol.lift_term1 (Fol.lift_term1 x) = Fol.lift_term_at (Fol.lift_term1 x) 1 1 := by
    simpa [Fol.lift_term1] using
      (Fol.lift_term_at2_small x 1 1 (m := 0) (m' := 0) (Nat.le_refl 0))
  have hformula := congrArg (fun t => mem (&0) t) hterm
  simpa [cvPred, mem, Fol.lift_formula_at, Fol.lift_term1, Fol.lift_term_at] using
    hformula

theorem representsWitnessSubst (x : Fol.term LNF) :
    (represents (&0) (Fol.lift_formula_at (cvPred x) 1 1)) [x // 0]f =
      represents x (cvPred x) :=
  by
  simp only [represents, Fol.subst_formula]
  congr 1
  rw [Fol.subst_formula_biimp]
  congr 1
  exact Fol.lift_at_subst_formula_eq (cvPred x) x 1

theorem classMemWitnessBodySubst (x : Fol.term LNF) (Q : Fol.formula LNF) :
    (represents (&0) (Fol.lift_formula_at (cvPred x) 1 1) ⊓' Q) [x // 0]f =
      represents x (cvPred x) ⊓' applyPred Q x :=
  by
  simp only [Fol.and', Fol.not', Fol.subst_formula]
  rw [representsWitnessSubst]
  rfl


end NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005

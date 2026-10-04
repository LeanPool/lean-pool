/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalLoweringDerived
public import LeanPool.NFWeakPartition.ClassBoundaryRawHandlersDev010

/-! NF weak partition development: NominalAtomicRecanonDev. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.AtomicRecanonDev

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005
open NFChoice.DirectCertificate.ClassBoundaryCoreDev006
open NFChoice.DirectCertificate.ClassBoundaryRawHandlersDev010

/-- Proof-translation construction identified upstream as `Theory`. -/
abbrev Theory : Fol.SentTheory LNF :=
  LiteralHailperinNF

/-! Atomic syntactic bridges for the two Metamath print ambiguities. -/


/-- Proof-translation construction identified upstream as `representsCvSelf`. -/
@[expose]
noncomputable def representsCvSelf (s : Fol.term LNF) :
    Theory.fst ⊢ represents s (cvPred s) :=
  by
  apply Fol.prf.allI
  exact Fol.biimpReflCertificate _ (mem (&0) (Fol.liftTerm1 s))

theorem representsCvTemplateSubst (s t : Fol.term LNF) :
    (represents (Fol.liftTerm1 s) (cvPred (&0))) [t // 0]f = represents s (cvPred t) :=
  by
  simp only [represents, mem, Nat.reduceAdd, Fol.liftTerm1, cvPred,
    Fol.liftTermAt.eq_1, Std.le_refl, ↓reduceIte, Nat.zero_add, Fol.substFormula,
    Fol.subst_formula_biimp, zero_lt_one, Fol.subst_term_var_lt, Fol.subst_term_var_eq,
    Fol.lift_term_def, Fol.preformula.all.injEq]
  have hDouble : (s ↑1) ↑1 = s ↑2 :=
    by
    change Fol.liftTermAt (Fol.liftTermAt s 1 0) 1 0 = Fol.liftTermAt s 2 0
    exact Fol.lift_term_at2_medium s 1 (n := 1) (m := 0) (m' := 0) (by omega) (by omega)
  rw [hDouble]
  rw [liftTwoSubstOne]

/-- Proof-translation construction identified upstream as `eqToRepresentsCv`. -/
@[expose]
noncomputable def eqToRepresentsCv (s t : Fol.term LNF) :
    Theory.fst ⊢ (s ≃ t) ⟹ represents s (cvPred t) :=
  by
  apply Fol.prf.impI
  apply Fol.prfSubst (represents (Fol.liftTerm1 s) (cvPred (&0))) (s := s) (t := t)
  · exact Fol.axm1
  · simpa [representsCvTemplateSubst] using
      (Fol.weakening (Set.subset_insert _ _) (representsCvSelf s))
  · exact representsCvTemplateSubst s t

/-- Proof-translation construction identified upstream as `objEqClassEqBiimp`. -/
@[expose]
noncomputable def objEqClassEqBiimp (s t : Fol.term LNF) :
    Theory.fst ⊢ (s ≃ t) ⇔ classEq (cvPred s) (cvPred t) :=
  by
  apply Fol.biimpI
  · have hImp :=
      Fol.weakening (Δ := insert (s ≃ t) Theory.fst) (Set.subset_insert _ _)
        (eqToRepresentsCv s t)
    have hRep := Fol.prf.impE (s ≃ t) hImp Fol.axm1
    simpa [classEq, represents, cvPred] using hRep
  · have hImp :=
      Fol.weakening (Δ := insert (classEq (cvPred s) (cvPred t)) Theory.fst)
        (Set.subset_insert _ _) (axExtAt s t)
    have hRep :
      insert (classEq (cvPred s) (cvPred t)) Theory.fst ⊢ represents s (cvPred t) := by
      exact
        (by
          simpa [classEq, represents, cvPred] using
            (Fol.axm1 :
              insert (classEq (cvPred s) (cvPred t)) Theory.fst ⊢
                classEq (cvPred s) (cvPred t)))
    exact Fol.prf.impE (represents s (cvPred t)) hImp hRep

/-- Proof-translation construction identified upstream as `objMemClassMemBiimp`. -/
@[expose]
noncomputable def objMemClassMemBiimp (s t : Fol.term LNF) :
    Theory.fst ⊢ mem s t ⇔ classMem (cvPred s) (cvPred t) := by
  exact
    biimpSymm
      (by
        simpa [applyPred, cvPred, mem, Fol.substFormula, Fol.lift_term1_subst_term,
          Fol.subst_term_var0] using (classMemCv s (cvPred t)))


end NFChoice.DirectNominalPrf.Nominal.AtomicRecanonDev

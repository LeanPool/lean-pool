/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalSubstitutionLemmas

/-! NF weak partition development: NominalDfClabProperSubstitutionCoreDev003. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.DfClabProperSubstitutionCoreDev003

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore

abbrev Theory : Fol.SentTheory LNF :=
  LiteralHailperinNF

@[expose]
def properSubstRhs (F : Fol.formula LNF) (replacement original : Fol.term LNF) :
    Fol.formula LNF :=
  ((original ≃ replacement) ⟹ F [original // 0]f) ⊓'
    ∃'(((&0) ≃ Fol.lift_term1 replacement) ⊓' F)

@[expose]
def coincidentSubstRhs (F : Fol.formula LNF) (source : Fol.term LNF) : Fol.formula LNF :=
  ((source ≃ source) ⟹ F [source // 0]f) ⊓' ∃'(((&0) ≃ (&0)) ⊓' F)

/-- Pure Flypitch proof of unrestricted proper substitution. -/
@[expose]
noncomputable def properSubstCore (F : Fol.formula LNF)
    (replacement original : Fol.term LNF) :
    Theory.fst ⊢ F [replacement // 0]f ⇔ properSubstRhs F replacement original :=
  by
  apply Fol.biimpI
  · let source := F [replacement // 0]f
    have hSource : insert source Theory.fst ⊢ source := Fol.axm1
    have hImp :
      insert source Theory.fst ⊢ (original ≃ replacement) ⟹ F [original // 0]f :=
      by
      apply Fol.prf.impI
      have hEq :
        insert (original ≃ replacement) (insert source Theory.fst) ⊢
          original ≃ replacement :=
        Fol.axm1
      have hSource' :
        insert (original ≃ replacement) (insert source Theory.fst) ⊢ source := Fol.axm2
      exact Fol.prf.subst₂ replacement original F (Fol.prf_symm hEq) hSource'
    have hEx : insert source Theory.fst ⊢ ∃'(((&0) ≃ Fol.lift_term1 replacement) ⊓' F) :=
      by
      apply Fol.exI replacement
      simpa [Fol.and', Fol.not', Fol.subst_formula, Fol.subst_formula_equal,
        Fol.lift_term1_subst_term, Fol.subst_term_var0] using
        (Fol.andI (Fol.prf.ref (insert source Theory.fst) replacement) hSource)
    exact Fol.andI hImp hEx
  · let rhs := properSubstRhs F replacement original
    have hRhs : insert rhs Theory.fst ⊢ rhs := Fol.axm1
    have hEx : insert rhs Theory.fst ⊢ ∃'(((&0) ≃ Fol.lift_term1 replacement) ⊓' F) :=
      Fol.andE2 ((original ≃ replacement) ⟹ F [original // 0]f) hRhs
    apply Fol.exE hEx
    let body := ((&0) ≃ Fol.lift_term1 replacement) ⊓' F
    have hBody : insert body (Fol.lift_formula1 '' insert rhs Theory.fst) ⊢ body :=
      Fol.axm1
    have hEq :
      insert body (Fol.lift_formula1 '' insert rhs Theory.fst) ⊢
        (&0) ≃ Fol.lift_term1 replacement :=
      Fol.andE1 F hBody
    have hF : insert body (Fol.lift_formula1 '' insert rhs Theory.fst) ⊢ F :=
      Fol.andE2 ((&0) ≃ Fol.lift_term1 replacement) hBody
    apply Fol.prf_subst (Fol.lift_formula_at F 1 1) hEq
    · simpa only [Fol.lift_subst_formula_cancel] using hF
    · exact Fol.lift_at_subst_formula_small0 F replacement 1 0

/-- Pure Flypitch proof for the captured/coincident source-name branch. -/
@[expose]
noncomputable def coincidentSubstCore (F : Fol.formula LNF) (sourceTerm : Fol.term LNF) :
    Theory.fst ⊢ F [sourceTerm // 0]f ⇔ coincidentSubstRhs F sourceTerm :=
  by
  apply Fol.biimpI
  · let source := F [sourceTerm // 0]f
    have hSource : insert source Theory.fst ⊢ source := Fol.axm1
    have hImp :
      insert source Theory.fst ⊢ (sourceTerm ≃ sourceTerm) ⟹ F [sourceTerm // 0]f :=
      by
      apply Fol.prf.impI
      exact Fol.weakening1 hSource
    have hEx : insert source Theory.fst ⊢ ∃'(((&0) ≃ (&0)) ⊓' F) :=
      by
      apply Fol.exI sourceTerm
      simpa [Fol.and', Fol.not', Fol.subst_formula, Fol.subst_formula_equal,
        Fol.subst_term_var0] using
        (Fol.andI (Fol.prf.ref (insert source Theory.fst) sourceTerm) hSource)
    exact Fol.andI hImp hEx
  · let rhs := coincidentSubstRhs F sourceTerm
    have hRhs : insert rhs Theory.fst ⊢ rhs := Fol.axm1
    have hImp :
      insert rhs Theory.fst ⊢ (sourceTerm ≃ sourceTerm) ⟹ F [sourceTerm // 0]f :=
      Fol.andE1 (∃'(((&0) ≃ (&0)) ⊓' F)) hRhs
    exact
      Fol.prf.impE (sourceTerm ≃ sourceTerm) hImp
        (Fol.prf.ref (insert rhs Theory.fst) sourceTerm)


end NFChoice.DirectNominalPrf.Nominal.DfClabProperSubstitutionCoreDev003

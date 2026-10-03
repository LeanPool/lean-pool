/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFCompactLeafGate
public import LeanPool.NFWeakPartition.DefinitionLeaves.Basic

/-! NF weak partition development: NFCompactLeafSemanticAdapters. -/


public section

namespace NFChoice.Compiler.NFCompactLeafSemanticAdapters

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax

/-- Semantic membership in the compact singleton constructor. -/
theorem holds_syn_csn {S : Fol.Structure LNF} (v : Var → S) (A : Class) (s : S) :
    Class.Holds S v (syn_csn A) s ↔ ∀ a : S, Mem S a s ↔ Class.Holds S v A a :=
  by
  let d := NFChoice.ReplaySupport.freshVar A.fv 0
  have hd : d ∉ A.fv := NFChoice.ReplaySupport.freshVar_not_mem A.fv 0
  simp only [syn_csn, Class.Holds, Wff.Holds, update_same]
  apply forall_congr'
  intro a
  exact iff_congr Iff.rfl (NFChoice.DefinitionLeaves.Class.holds_update_fresh A v hd s a)

/-- Semantic NAND law for the compact class intersection-complement primitive. -/
theorem holds_syn_cnin {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (A B : Class) (s : S) :
    Class.Holds S v (syn_cnin A B) s ↔ ¬(Class.Holds S v A s ∧ Class.Holds S v B s) :=
  by
  let d := NFChoice.ReplaySupport.freshVar (A.fv ∪ B.fv) 0
  have hdA : d ∉ A.fv :=
    NFChoice.ReplaySupport.freshVar_not_mem_of_subset (Finset.subset_union_left) 0
  have hdB : d ∉ B.fv :=
    NFChoice.ReplaySupport.freshVar_not_mem_of_subset (Finset.subset_union_right) 0
  change
    Wff.Holds S (update v d s) (syn_wnan (.classMem (.cv d) A) (.classMem (.cv d) B)) ↔ _
  rw [show
      syn_wnan (.classMem (.cv d) A) (.classMem (.cv d) B) =
        Wff.neg (Wff.conj (.classMem (.cv d) A) (.classMem (.cv d) B))
      by rfl]
  simp only [Wff.holds_neg, Wff.holds_conj]
  rw [NFChoice.DefinitionLeaves.SemanticBoundary.classMem_cv_iff_holds hExt (update v d s)
      d A]
  rw [NFChoice.DefinitionLeaves.SemanticBoundary.classMem_cv_iff_holds hExt (update v d s)
      d B]
  simp only [update_same]
  rw [NFChoice.DefinitionLeaves.Class.holds_update_fresh A v hdA s s]
  rw [NFChoice.DefinitionLeaves.Class.holds_update_fresh B v hdB s s]

theorem holds_syn_ccompl {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (A : Class) (s : S) : Class.Holds S v (syn_ccompl A) s ↔ ¬Class.Holds S v A s :=
  by
  rw [show syn_ccompl A = syn_cnin A A by rfl]
  rw [holds_syn_cnin hExt v A A s]
  tauto

theorem holds_syn_cun {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (A B : Class) (s : S) :
    Class.Holds S v (syn_cun A B) s ↔ Class.Holds S v A s ∨ Class.Holds S v B s :=
  by
  rw [show syn_cun A B = syn_cnin (syn_ccompl A) (syn_ccompl B) by rfl]
  rw [holds_syn_cnin hExt v (syn_ccompl A) (syn_ccompl B) s]
  rw [holds_syn_ccompl hExt v A s, holds_syn_ccompl hExt v B s]
  tauto

theorem holds_syn_cpr {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (A B : Class) (s : S) :
    Class.Holds S v (syn_cpr A B) s ↔
      (∀ a : S, Mem S a s ↔ Class.Holds S v A a) ∨
        (∀ a : S, Mem S a s ↔ Class.Holds S v B a) :=
  by
  rw [show syn_cpr A B = syn_cun (syn_csn A) (syn_csn B) by rfl]
  rw [holds_syn_cun hExt v (syn_csn A) (syn_csn B) s]
  rw [holds_syn_csn v A s, holds_syn_csn v B s]

/-- The compact ordered-pair constructor, stated without unfolding its syntax DAG. -/
theorem holds_syn_copk {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (A B : Class) (p : S) :
    Class.Holds S v (syn_copk A B) p ↔
      (∀ u : S, Mem S u p ↔ ∀ a : S, Mem S a u ↔ Class.Holds S v A a) ∨
        (∀ u : S, Mem S u p ↔ (∀ a : S, Mem S a u ↔ Class.Holds S v A a) ∨
              (∀ a : S, Mem S a u ↔ Class.Holds S v B a)) :=
  by
  rw [show syn_copk A B = syn_cpr (syn_csn A) (syn_cpr A B) by rfl]
  rw [holds_syn_cpr hExt v (syn_csn A) (syn_cpr A B) p]
  apply or_congr
  · apply forall_congr'
    intro u
    exact iff_congr Iff.rfl (holds_syn_csn v A u)
  · apply forall_congr'
    intro u
    exact iff_congr Iff.rfl (holds_syn_cpr hExt v A B u)

theorem formulaHolds_disj {S : Fol.Structure LNF} {n : Nat} {xs : DVec S n}
    {p q : Formula n} :
    NFChoice.SemanticCore.Lowering.FormulaHolds S xs (Formula.disj p q) ↔
      NFChoice.SemanticCore.Lowering.FormulaHolds S xs p ∨
        NFChoice.SemanticCore.Lowering.FormulaHolds S xs q :=
  by
  simp only [Formula.disj, Formula.neg, NFChoice.SemanticCore.Lowering.FormulaHolds]
  tauto

/-- Renaming a formula agrees with reindexing its bounded valuation. -/
theorem formulaHolds_renameVars {S : Fol.Structure LNF} {n m : Nat} (rho : Fin n → Fin m)
    (ys : DVec S m) (xs : DVec S n) (p : Formula n)
    (hlookup : ∀ i, NFChoice.SemanticCore.Lowering.lookup ys (rho i) =
          NFChoice.SemanticCore.Lowering.lookup xs i) :
    NFChoice.SemanticCore.Lowering.FormulaHolds S ys (Formula.renameVars rho p) ↔
      NFChoice.SemanticCore.Lowering.FormulaHolds S xs p :=
  by
  induction p generalizing m ys with
  | falsum => rfl
  | equal i
    j =>
    simp only [Formula.renameVars, NFChoice.SemanticCore.Lowering.FormulaHolds]
    rw [hlookup i, hlookup j]
  | mem i
    j =>
    simp only [Formula.renameVars, NFChoice.SemanticCore.Lowering.FormulaHolds]
    rw [hlookup i, hlookup j]
  | imp p q ihp
    ihq =>
    simp only [Formula.renameVars, NFChoice.SemanticCore.Lowering.FormulaHolds]
    exact Iff.imp (ihp rho ys xs hlookup) (ihq rho ys xs hlookup)
  | all p
    ih =>
    simp only [Formula.renameVars, NFChoice.SemanticCore.Lowering.FormulaHolds]
    apply forall_congr'
    intro a
    apply ih (Fin.cases 0 (fun i => Fin.succ (rho i))) (DVec.cons a ys) (DVec.cons a xs)
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [hlookup]

/-- `liftClassPredicate` merely inserts the represented set at index one. -/
theorem formulaHolds_liftClassPredicate {S : Fol.Structure LNF} {n : Nat} (xs : DVec S n)
    (candidate inserted : S) (p : Formula (n + 1)) :
    NFChoice.SemanticCore.Lowering.FormulaHolds S
        (DVec.cons candidate (DVec.cons inserted xs)) (Formula.liftClassPredicate p) ↔
      NFChoice.SemanticCore.Lowering.FormulaHolds S (DVec.cons candidate xs) p :=
  by
  apply formulaHolds_renameVars
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp []
  · simp []

theorem formulaHolds_eqCandidateToPredicate {S : Fol.Structure LNF} {n : Nat}
    (xs : DVec S n) (candidate : S) (p : Formula (n + 1)) :
    NFChoice.SemanticCore.Lowering.FormulaHolds S (DVec.cons candidate xs)
        (Formula.eqCandidateToPredicate p) ↔
      ∀ a : S,
        Mem S a candidate ↔
          NFChoice.SemanticCore.Lowering.FormulaHolds S (DVec.cons a xs) p :=
  by
  simp only [Formula.eqCandidateToPredicate, NFChoice.SemanticCore.Lowering.FormulaHolds,
    NFChoice.SemanticCore.Lowering.formulaHolds_biimp]
  apply forall_congr'
  intro a
  simp only [NFChoice.SemanticCore.Lowering.lookup_cons_zero, ]
  exact iff_congr Iff.rfl (formulaHolds_liftClassPredicate xs a candidate p)

/-- Direct model semantics of an exact literal class expression. -/
@[expose]
def LiteralClassSem {S : Fol.Structure LNF} {n : Nat} (xs : DVec S n) :
    LiteralClass n → S → Prop
  | .setVar i, a => Mem S a (NFChoice.SemanticCore.Lowering.lookup xs i)
  | .singleton A, a => ∀ z : S, Mem S z a ↔ LiteralClassSem xs A z
  | .unorderedPair A B, a =>
    (∀ z : S, Mem S z a ↔ LiteralClassSem xs A z) ∨
      (∀ z : S, Mem S z a ↔ LiteralClassSem xs B z)
  | .kPair A B, a =>
    (∀ u : S, Mem S u a ↔ ∀ z : S, Mem S z u ↔ LiteralClassSem xs A z) ∨
      (∀ u : S, Mem S u a ↔ (∀ z : S, Mem S z u ↔ LiteralClassSem xs A z) ∨
            (∀ z : S, Mem S z u ↔ LiteralClassSem xs B z))

/-- The exact literal membership formula denotes `LiteralClassSem`. -/
theorem formulaHolds_literalClass_membership {S : Fol.Structure LNF} {n : Nat}
    (xs : DVec S n) (A : LiteralClass n) (candidate : S) :
    NFChoice.SemanticCore.Lowering.FormulaHolds S (DVec.cons candidate xs)
        (LiteralClass.membership A) ↔
      LiteralClassSem xs A candidate :=
  by
  induction A generalizing candidate with
  | setVar i =>
    simp [LiteralClass.membership, LiteralClassSem,
      NFChoice.SemanticCore.Lowering.FormulaHolds]
  | singleton A ih =>
    simp only [LiteralClass.membership]
    rw [formulaHolds_eqCandidateToPredicate]
    simp only [LiteralClassSem]
    apply forall_congr'
    intro a
    exact iff_congr Iff.rfl (ih a)
  | unorderedPair A B ihA
    ihB =>
    simp only [LiteralClass.membership, formulaHolds_disj,
      formulaHolds_eqCandidateToPredicate, LiteralClassSem]
    apply or_congr
    · apply forall_congr'
      intro a
      exact iff_congr Iff.rfl (ihA a)
    · apply forall_congr'
      intro a
      exact iff_congr Iff.rfl (ihB a)
  | kPair A B ihA
    ihB =>
    simp only [LiteralClass.membership, formulaHolds_disj,
      formulaHolds_eqCandidateToPredicate, LiteralClassSem]
    apply or_congr
    · apply forall_congr'
      intro u
      apply iff_congr Iff.rfl
      apply forall_congr'
      intro a
      exact iff_congr Iff.rfl (ihA a)
    · apply forall_congr'
      intro u
      apply iff_congr Iff.rfl
      apply or_congr
      · apply forall_congr'
        intro a
        exact iff_congr Iff.rfl (ihA a)
      · apply forall_congr'
        intro a
        exact iff_congr Iff.rfl (ihB a)


end NFChoice.Compiler.NFCompactLeafSemanticAdapters

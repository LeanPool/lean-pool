/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFCompactLeafSemanticAdapters

/-! NF weak partition development: NFCompactLeafEndpoints. -/


public section

namespace NFChoice.Compiler.NFCompactLeafEndpoints

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.Lowering
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.NFCompactLeafSemanticAdapters

theorem formulaHolds_setEqClass {S : Fol.Structure LNF} {n : Nat} (xs : DVec S n)
    (r : Fin n) (A : LiteralClass n) :
    FormulaHolds S xs (LiteralClass.setEqClass r A) ↔
      ∀ z : S, Mem S z (lookup xs r) ↔ LiteralClassSem xs A z :=
  by
  simp only [LiteralClass.setEqClass, LiteralClass.classEq, FormulaHolds,
    formulaHolds_biimp]
  apply forall_congr'
  intro z
  rw [formulaHolds_literalClass_membership xs (.setVar r) z]
  rw [formulaHolds_literalClass_membership xs A z]
  rfl

theorem formulaHolds_classMemSet {S : Fol.Structure LNF} {n : Nat} (xs : DVec S n)
    (A : LiteralClass n) (r : Fin n) :
    FormulaHolds S xs (LiteralClass.classMemSet A r) ↔
      ∃ p : S, (∀ z : S, Mem S z p ↔ LiteralClassSem xs A z) ∧ Mem S p (lookup xs r) :=
  by
  simp only [LiteralClass.classMemSet, formulaHolds_ex, formulaHolds_conj]
  apply exists_congr
  intro p
  apply and_congr
  · rw [formulaHolds_eqCandidateToPredicate]
    apply forall_congr'
    intro z
    exact iff_congr Iff.rfl (formulaHolds_literalClass_membership xs A z)
  · simp [FormulaHolds]

theorem holds_syn_csn_literal {S : Fol.Structure LNF} {n : Nat} (v : Var → S)
    (xs : DVec S n) (A : Class) (LA : LiteralClass n)
    (hA : ∀ a : S, Class.Holds S v A a ↔ LiteralClassSem xs LA a) (s : S) :
    Class.Holds S v (synCsn A) s ↔ LiteralClassSem xs (.singleton LA) s :=
  by
  rw [holds_syn_csn v A s]
  simp only [LiteralClassSem]
  apply forall_congr'
  intro a
  exact iff_congr Iff.rfl (hA a)

theorem holds_syn_cpr_literal {S : Fol.Structure LNF} {n : Nat} (hExt : Extensional S)
    (v : Var → S) (xs : DVec S n) (A B : Class) (LA LB : LiteralClass n)
    (hA : ∀ a : S, Class.Holds S v A a ↔ LiteralClassSem xs LA a)
    (hB : ∀ a : S, Class.Holds S v B a ↔ LiteralClassSem xs LB a) (p : S) :
    Class.Holds S v (synCpr A B) p ↔ LiteralClassSem xs (.unorderedPair LA LB) p :=
  by
  rw [holds_syn_cpr hExt v A B p]
  simp only [LiteralClassSem]
  apply or_congr
  · apply forall_congr'
    intro a
    exact iff_congr Iff.rfl (hA a)
  · apply forall_congr'
    intro a
    exact iff_congr Iff.rfl (hB a)

theorem holds_syn_copk_literal {S : Fol.Structure LNF} {n : Nat} (hExt : Extensional S)
    (v : Var → S) (xs : DVec S n) (A B : Class) (LA LB : LiteralClass n)
    (hA : ∀ a : S, Class.Holds S v A a ↔ LiteralClassSem xs LA a)
    (hB : ∀ a : S, Class.Holds S v B a ↔ LiteralClassSem xs LB a) (p : S) :
    Class.Holds S v (synCopk A B) p ↔ LiteralClassSem xs (.kPair LA LB) p :=
  by
  rw [holds_syn_copk hExt v A B p]
  simp only [LiteralClassSem]
  apply or_congr
  · apply forall_congr'
    intro u
    apply iff_congr Iff.rfl
    apply forall_congr'
    intro a
    exact iff_congr Iff.rfl (hA a)
  · apply forall_congr'
    intro u
    apply iff_congr Iff.rfl
    apply or_congr
    · apply forall_congr'
      intro a
      exact iff_congr Iff.rfl (hA a)
    · apply forall_congr'
      intro a
      exact iff_congr Iff.rfl (hB a)

theorem holds_classEq_cv_literal {S : Fol.Structure LNF} {n : Nat} (v : Var → S)
    (xs : DVec S n) (x : Var) (r : Fin n) (A : Class) (LA : LiteralClass n)
    (hx : v x = lookup xs r)
    (hA : ∀ a : S, Class.Holds S v A a ↔ LiteralClassSem xs LA a) :
    Wff.Holds S v (.classEq (.cv x) A) ↔
      FormulaHolds S xs (LiteralClass.setEqClass r LA) :=
  by
  rw [formulaHolds_setEqClass]
  simp only [Wff.Holds, Class.Holds]
  apply forall_congr'
  intro a
  rw [hx]
  exact iff_congr Iff.rfl (hA a)

theorem holds_classMem_cv_literal {S : Fol.Structure LNF} {n : Nat} (v : Var → S)
    (xs : DVec S n) (x : Var) (r : Fin n) (A : Class) (LA : LiteralClass n)
    (hx : v x = lookup xs r)
    (hA : ∀ a : S, Class.Holds S v A a ↔ LiteralClassSem xs LA a) :
    Wff.Holds S v (.classMem A (.cv x)) ↔
      FormulaHolds S xs (LiteralClass.classMemSet LA r) :=
  by
  rw [formulaHolds_classMemSet]
  simp only [Wff.Holds, Class.Holds]
  apply exists_congr
  intro p
  apply and_congr
  · apply forall_congr'
    intro z
    exact iff_congr Iff.rfl (hA z)
  · rw [hx]

theorem holds_literalKPair {S : Fol.Structure LNF} {n : Nat} (hExt : Extensional S)
    (v : Var → S) (xs : DVec S n) (z w t : Var) (iz iw it : Fin n)
    (hz : v z = lookup xs iz) (hw : v w = lookup xs iw) (ht : v t = lookup xs it) :
    Wff.Holds S v (.classEq (.cv z) (synCopk (.cv w) (.cv t))) ↔
      FormulaHolds S xs (literalKPair iz iw it) :=
  by
  change
    Wff.Holds S v (.classEq (.cv z) (synCopk (.cv w) (.cv t))) ↔
      FormulaHolds S xs (LiteralClass.setEqClass iz (.kPair (.setVar iw) (.setVar it)))
  apply
    holds_classEq_cv_literal v xs z iz (synCopk (.cv w) (.cv t))
      (.kPair (.setVar iw) (.setVar it)) hz
  intro p
  apply holds_syn_copk_literal hExt v xs (.cv w) (.cv t) (.setVar iw) (.setVar it)
  · intro a
    simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S a) hw
  · intro a
    simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S a) ht

theorem holds_literalPairMem {S : Fol.Structure LNF} {n : Nat} (hExt : Extensional S)
    (v : Var → S) (xs : DVec S n) (a b r : Var) (ia ib ir : Fin n)
    (ha : v a = lookup xs ia) (hb : v b = lookup xs ib) (hr : v r = lookup xs ir) :
    Wff.Holds S v (.classMem (synCopk (.cv a) (.cv b)) (.cv r)) ↔
      FormulaHolds S xs (literalPairMem ia ib ir) :=
  by
  change
    Wff.Holds S v (.classMem (synCopk (.cv a) (.cv b)) (.cv r)) ↔
      FormulaHolds S xs (LiteralClass.classMemSet (.kPair (.setVar ia) (.setVar ib)) ir)
  apply
    holds_classMem_cv_literal v xs r ir (synCopk (.cv a) (.cv b))
      (.kPair (.setVar ia) (.setVar ib)) hr
  intro p
  apply holds_syn_copk_literal hExt v xs (.cv a) (.cv b) (.setVar ia) (.setVar ib)
  · intro z
    simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S z) ha
  · intro z
    simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S z) hb

theorem holds_literalSingletonPairMem {S : Fol.Structure LNF} {n : Nat}
    (hExt : Extensional S) (v : Var → S) (xs : DVec S n) (a b r : Var) (ia ib ir : Fin n)
    (ha : v a = lookup xs ia) (hb : v b = lookup xs ib) (hr : v r = lookup xs ir) :
    Wff.Holds S v (.classMem (synCopk (synCsn (.cv a)) (synCsn (.cv b))) (.cv r)) ↔
      FormulaHolds S xs (literalSingletonPairMem ia ib ir) :=
  by
  change
    Wff.Holds S v (.classMem (synCopk (synCsn (.cv a)) (synCsn (.cv b))) (.cv r)) ↔
      FormulaHolds S xs
        (LiteralClass.classMemSet
          (.kPair (.singleton (.setVar ia)) (.singleton (.setVar ib))) ir)
  apply
    holds_classMem_cv_literal v xs r ir (synCopk (synCsn (.cv a)) (synCsn (.cv b)))
      (.kPair (.singleton (.setVar ia)) (.singleton (.setVar ib))) hr
  intro p
  apply
    holds_syn_copk_literal hExt v xs (synCsn (.cv a)) (synCsn (.cv b))
      (.singleton (.setVar ia)) (.singleton (.setVar ib))
  · intro z
    apply holds_syn_csn_literal v xs (.cv a) (.setVar ia)
    intro u
    simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S u) ha
  · intro z
    apply holds_syn_csn_literal v xs (.cv b) (.setVar ib)
    intro u
    simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S u) hb

theorem holds_literalInsertedPairMem {S : Fol.Structure LNF} {n : Nat}
    (hExt : Extensional S) (v : Var → S) (xs : DVec S n) (z w t r : Var)
    (iz iw it ir : Fin n) (hz : v z = lookup xs iz) (hw : v w = lookup xs iw)
    (ht : v t = lookup xs it) (hr : v r = lookup xs ir) :
    Wff.Holds S v
        (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t))) (.cv r)) ↔
      FormulaHolds S xs (literalInsertedPairMem iz iw it ir) :=
  by
  change
    Wff.Holds S v
        (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t))) (.cv r)) ↔
      FormulaHolds S xs
        (LiteralClass.classMemSet (.kPair (.singleton (.singleton (.setVar iz)))
            (.kPair (.setVar iw) (.setVar it))) ir)
  apply
    holds_classMem_cv_literal v xs r ir
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
      (.kPair (.singleton (.singleton (.setVar iz))) (.kPair (.setVar iw) (.setVar it)))
      hr
  intro p
  apply
    holds_syn_copk_literal hExt v xs (synCsn (synCsn (.cv z)))
      (synCopk (.cv w) (.cv t)) (.singleton (.singleton (.setVar iz)))
      (.kPair (.setVar iw) (.setVar it))
  · intro q
    apply holds_syn_csn_literal v xs (synCsn (.cv z)) (.singleton (.setVar iz))
    intro u
    apply holds_syn_csn_literal v xs (.cv z) (.setVar iz)
    intro e
    simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S e) hz
  · intro q
    apply holds_syn_copk_literal hExt v xs (.cv w) (.cv t) (.setVar iw) (.setVar it)
    · intro e
      simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S e) hw
    · intro e
      simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S e) ht

theorem holds_literalPairSingletonSecondMem {S : Fol.Structure LNF} {n : Nat}
    (hExt : Extensional S) (v : Var → S) (xs : DVec S n) (a z r : Var) (ia iz ir : Fin n)
    (ha : v a = lookup xs ia) (hz : v z = lookup xs iz) (hr : v r = lookup xs ir) :
    Wff.Holds S v (.classMem (synCopk (.cv a) (synCsn (.cv z))) (.cv r)) ↔
      FormulaHolds S xs (literalPairSingletonSecondMem ia iz ir) :=
  by
  change
    Wff.Holds S v (.classMem (synCopk (.cv a) (synCsn (.cv z))) (.cv r)) ↔
      FormulaHolds S xs
        (LiteralClass.classMemSet (.kPair (.setVar ia) (.singleton (.setVar iz))) ir)
  apply
    holds_classMem_cv_literal v xs r ir (synCopk (.cv a) (synCsn (.cv z)))
      (.kPair (.setVar ia) (.singleton (.setVar iz))) hr
  intro p
  apply
    holds_syn_copk_literal hExt v xs (.cv a) (synCsn (.cv z)) (.setVar ia)
      (.singleton (.setVar iz))
  · intro e
    simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S e) ha
  · intro e
    apply holds_syn_csn_literal v xs (.cv z) (.setVar iz)
    intro u
    simpa [Class.Holds, LiteralClassSem] using congrArg (Mem S u) hz


end NFChoice.Compiler.NFCompactLeafEndpoints

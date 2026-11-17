/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelOrderSatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelIdealInterpretation

/-!
# Model Order Satisfaction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

def SetAutomorphism (I L F : ZFSet.{u}) : Prop :=
  TransitiveNameModel.FunctionGraph I I F ∧
  (∀ E ∈ I, ∃ D ∈ I, ZFSet.pair D E ∈ F) ∧
  (∀ D ∈ I, ∀ E ∈ I, ∀ D' ∈ I, ∀ E' ∈ I,
    ZFSet.pair D D' ∈ F → ZFSet.pair E E' ∈ F →
      (ZFSet.pair D E ∈ L ↔ ZFSet.pair D' E' ∈ L))

namespace Formula

def setIdeal (U L I : ℕ) : Formula := .conj (.subset I U)
  (.conj (.existsMem I (.equal 0 0))
    (.conj (allMem U (allMem (I+1) (imp (pairMem 1 0 (L+2)) (.member 1 (I+2)))))
      (allMem I (allMem (I+1) (.existsMem (I+2)
        (.conj (pairMem 2 0 (L+3)) (pairMem 1 0 (L+3))))))))

theorem eval_setIdeal (U L I : ℕ) (e : ℕ → ZFSet.{u}) :
    (setIdeal U L I).Eval e ↔ SetIdeal (e U) (e L) (e I) := by
  simp only [setIdeal,SetIdeal,Formula.Eval,eval_subset,eval_allMem,eval_imp,eval_pairMem,
    cons_zero,cons_succ,and_true]

def onto (d r f : ℕ) : Formula := allMem r (.existsMem (d+1) (pairMem 0 1 (f+2)))

theorem eval_onto (d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (onto d r f).Eval e ↔ ∀ y ∈ e r, ∃ x ∈ e d, ZFSet.pair x y ∈ e f := by
  simp only [onto,Formula.Eval,eval_allMem,eval_pairMem,cons_zero,cons_succ]

def surjection (d r f : ℕ) : Formula := .conj (functionGraph f d r) (onto d r f)

theorem eval_surjection (d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (surjection d r f).Eval e ↔ TransitiveNameModel.FunctionGraph (e d) (e r) (e f) ∧
      ∀ y ∈ e r, ∃ x ∈ e d, ZFSet.pair x y ∈ e f := by
  simp only [surjection,Formula.Eval,eval_functionGraph,eval_onto,TransitiveNameModel.FunctionGraph]

def setAutomorphism (I L F : ℕ) : Formula := .conj (functionGraph F I I)
  (.conj (onto I I F)
    (allMem I (allMem (I+1) (allMem (I+2) (allMem (I+3)
      (imp (pairMem 3 1 (F+4)) (imp (pairMem 2 0 (F+4))
        (iff (pairMem 3 2 (L+4)) (pairMem 1 0 (L+4))))))))))

theorem eval_setAutomorphism (I L F : ℕ) (e : ℕ → ZFSet.{u}) :
    (setAutomorphism I L F).Eval e ↔ SetAutomorphism (e I) (e L) (e F) := by
  simp only [setAutomorphism,SetAutomorphism,TransitiveNameModel.FunctionGraph,Formula.Eval,
    eval_functionGraph,eval_onto,eval_allMem,eval_imp,eval_iff,eval_pairMem,cons_zero,cons_succ]

theorem realize_setIdeal (M : ZFSet.{u}) (hM : Transitive M)
    (U L I : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (setIdeal U L I).Realize M e ↔ SetIdeal (e U) (e L) (e I) :=
  ((setIdeal U L I).absolute M hM e he).trans (eval_setIdeal U L I e)

theorem realize_setAutomorphism (M : ZFSet.{u}) (hM : Transitive M)
    (I L F : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (setAutomorphism I L F).Realize M e ↔ SetAutomorphism (e I) (e L) (e F) :=
  ((setAutomorphism I L F).absolute M hM e he).trans (eval_setAutomorphism I L F e)
end Formula

namespace LevySigma

def countable (o I : ℕ) : LevySigma := .existsSet (.bounded (.surjection (o+1) (I+1) 0))

theorem realize_countable (M : ZFSet.{u}) (hM : Transitive M)
    (o I : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (ho : e o = ZFSet.omega) :
    (countable o I).Realize M e ↔ InternallyCountable M (e I) := by
  simp only [countable,Realize,InternallyCountable]
  apply exists_congr; intro E
  apply and_congr_right; intro hE
  rw [(Formula.surjection (o+1) (I+1) 0).absolute M hM (cons E e)
    (by intro i; cases i <;> simp [cons,he,hE]),Formula.eval_surjection]
  simp only [cons_zero,cons_succ,ho]
end LevySigma

end TuringRigidity.BoundedSetTheory

end OAI

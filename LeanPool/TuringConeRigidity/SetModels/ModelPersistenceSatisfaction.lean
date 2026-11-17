/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelPersistenceSatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelOrderSatisfaction

/-!
# Model Persistence Satisfaction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- A countably enumerated larger ideal and an automorphism graph extending the original while
including `x`. -/
def SetExtensionWitness (o U L I F x J S E : ZFSet.{u}) : Prop :=
  SetIdeal U L J ∧
  (TransitiveNameModel.FunctionGraph o J E ∧ ∀ y ∈ J, ∃ n ∈ o, ZFSet.pair n y ∈ E) ∧
  SetAutomorphism J L S ∧ I ⊆ J ∧ x ∈ J ∧ F ⊆ S

/-- A set-coded automorphism admits a countably enumerated extension inside `M` containing
each degree-universe element. -/
def ModelPersistent (M U L I F : ZFSet.{u}) : Prop := SetAutomorphism I L F ∧
  ∀ x ∈ U, ∃ J ∈ M, ∃ S ∈ M, ∃ E ∈ M, SetExtensionWitness ZFSet.omega U L I F x J S E

namespace Formula

/-- Bounded formula expressing the data and inclusions of a set-coded persistence extension
witness. -/
def setExtensionWitness (o U L I F x J S E : ℕ) : Formula :=
  .conj (setIdeal U L J) (.conj (surjection o J E) (.conj (setAutomorphism J L S)
    (.conj (.subset I J) (.conj (.member x J) (.subset F S)))))

theorem eval_setExtensionWitness (o U L I F x J S E : ℕ) (e : ℕ → ZFSet.{u}) :
    (setExtensionWitness o U L I F x J S E).Eval e ↔
      SetExtensionWitness (e o) (e U) (e L) (e I) (e F) (e x) (e J) (e S) (e E) := by
  simp only [setExtensionWitness,SetExtensionWitness,Formula.Eval,eval_setIdeal,eval_surjection,
    eval_setAutomorphism,eval_subset]
end Formula

namespace LevySigma

/-- A Levy-sigma formula expressing the set-coded automorphism and all required persistence
extensions. -/
def persistent (o U L I F : ℕ) : LevySigma := .conj (.bounded (.setAutomorphism I L F))
  (.allMem U (.existsSet (.existsSet (.existsSet
    (.bounded (.setExtensionWitness (o+4) (U+4) (L+4) (I+4) (F+4) 3 2 1 0))))))

theorem realize_persistent (M : ZFSet.{u}) (hM : Transitive M)
    (o U L I F : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (ho : e o = ZFSet.omega) :
    (persistent o U L I F).Realize M e ↔ ModelPersistent M (e U) (e L) (e I) (e F) := by
  simp only [persistent,Realize,ModelPersistent]
  rw [Formula.realize_setAutomorphism M hM I L F e he]
  apply and_congr_right; intro _
  have hbody (x J S E : ZFSet.{u}) (hx : x ∈ M) (hJ : J ∈ M) (hS : S ∈ M) (hE : E ∈ M) :
      (Formula.setExtensionWitness (o+4) (U+4) (L+4) (I+4) (F+4) 3 2 1 0).Realize M
        (cons E (cons S (cons J (cons x e)))) ↔
      SetExtensionWitness ZFSet.omega (e U) (e L) (e I) (e F) x J S E := by
    rw [Formula.absolute _ M hM _ (by
      intro i
      rcases i with _ | i
      · exact hE
      rcases i with _ | i
      · exact hS
      rcases i with _ | i
      · exact hJ
      rcases i with _ | i
      · exact hx
      exact he i),Formula.eval_setExtensionWitness]
    simp only [cons_zero,cons_succ,ho]
  constructor
  · intro h x hx
    have hxM := hM _ (he U) _ hx
    obtain ⟨J,hJ,S,hS,E,hE,hb⟩ := h x hxM hx
    exact ⟨J,hJ,S,hS,E,hE,(hbody x J S E hxM hJ hS hE).mp hb⟩
  · intro h x hxM hx
    obtain ⟨J,hJ,S,hS,E,hE,hb⟩ := h x hx
    exact ⟨J,hJ,S,hS,E,hE,(hbody x J S E hxM hJ hS hE).mpr hb⟩
end LevySigma

end TuringRigidity.BoundedSetTheory

end OAI

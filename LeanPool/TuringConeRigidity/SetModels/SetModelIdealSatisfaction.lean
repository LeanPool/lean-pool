/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelIdealSatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelDegreeUniverse

/-!
# Set Model Ideal Satisfaction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions
universe u
noncomputable section
variable {M : ZFSet.{u}}

/-- Bounded formula expressing a nonempty lower directed subset of a coded degree order. -/
def idealFormula (i d l : ℕ) : Formula :=
  .conj (.subset i d) (.conj (.existsMem i (.equal 0 0))
    (.conj (.allMem i (.allMem (d+1) (.imp (.pairMem 0 1 (l+2)) (.member 0 (i+2)))))
      (.allMem i (.allMem (i+1) (.existsMem (i+2)
        (.conj (.pairMem 2 0 (l+3)) (.pairMem 1 0 (l+3))))))))

/-- A nonempty lower directed subset of the coded order on `d`. -/
def IsIdeal (a d l : ZFSet.{u}) : Prop :=
  a ⊆ d ∧ (∃ x, x ∈ a) ∧
    (∀ x ∈ a, ∀ y ∈ d, ZFSet.pair y x ∈ l → y ∈ a) ∧
    (∀ x ∈ a, ∀ y ∈ a, ∃ z ∈ a, ZFSet.pair x z ∈ l ∧ ZFSet.pair y z ∈ l)

@[simp] theorem eval_idealFormula (i d l : ℕ) (e : ℕ → ZFSet.{u}) :
    (idealFormula i d l).Eval e ↔ IsIdeal (e i) (e d) (e l) := by
  simp only [idealFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_imp,Formula.eval_pairMem,cons_zero,cons_succ,IsIdeal,and_true]

theorem order_code (C : Context M) {L : ZFSet.{u}}
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    {a b : Degree} (ha : degreeSet.{u} a ∈ M) (hb : degreeSet.{u} b ∈ M) :
    ZFSet.pair (degreeSet a) (degreeSet b) ∈ L ↔ a ≤ b := by
  obtain ⟨A,hA,rfl⟩ := represented_of_degreeSet_mem C ha
  obtain ⟨B,hB,rfl⟩ := represented_of_degreeSet_mem C hb
  exact hL A hA B hB

theorem ideal_satisfaction (C : Context M) {D L : ZFSet.{u}}
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hI : idealSet I ∈ M) : IsIdeal (idealSet I) D L := by
  have hm {a : Degree} (ha : a ∈ I.carrier) : degreeSet.{u} a ∈ M :=
    C.transitive _ hI _ ((mem_idealSet I _).mpr ⟨a,ha,rfl⟩)
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨A,hA,hAa⟩ := represented_of_degreeSet_mem C (hm ha)
    exact (hD _).mpr ⟨A,hA,by rw [hAa]⟩
  · obtain ⟨a,ha⟩ := I.nonempty
    exact ⟨degreeSet a,(mem_idealSet I _).mpr ⟨a,ha,rfl⟩⟩
  · intro x hx y hy hyx
    obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨B,hB,rfl⟩ := (hD y).mp hy
    obtain ⟨A,hA,rfl⟩ := represented_of_degreeSet_mem C (hm ha)
    have hba := (hL B hB A hA).mp hyx
    exact (mem_idealSet I _).mpr ⟨_,I.lower hba ha,rfl⟩
  · intro x hx y hy
    obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I y).mp hy
    have hc := I.join_mem ha hb
    refine ⟨degreeSet (a⊔b),(mem_idealSet I _).mpr ⟨_,hc,rfl⟩,
      (order_code C hL (hm ha) (hm hc)).mpr le_sup_left,
      (order_code C hL (hm hb) (hm hc)).mpr le_sup_right⟩

end
end TuringRigidity.SetModelSatisfaction

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelDegreeCodes.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticParameterFormula
public import LeanPool.TuringConeRigidity.SetModels.ModelRealOperations

/-!
# Model Degree Codes
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- The members of `R` that code oracles of the same Turing degree as `A`. -/
noncomputable def degreeCode (R : ZFSet.{u}) (A : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ B : Oracle, z = realCode B ∧ degree B = degree A) R

theorem degreeCode_subset (R : ZFSet.{u}) (A : Oracle) : degreeCode R A ⊆ R :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem realCode_mem_degreeCode (R : ZFSet.{u}) (A B : Oracle) :
    realCode B ∈ degreeCode R A ↔ realCode B ∈ R ∧ degree B = degree A := by
  rw [degreeCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨hB,C,he,hC⟩
    have hBC := realCode_injective he
    exact ⟨hB,hBC.symm ▸ hC⟩
  · rintro ⟨hB,hBA⟩; exact ⟨hB,B,rfl,hBA⟩

theorem degreeCode_equal (R : ZFSet.{u}) {A B : Oracle} (hA : realCode A ∈ R)
    : degreeCode R A = degreeCode R B ↔ degree A = degree B := by
  constructor
  · intro h
    have ha := (realCode_mem_degreeCode R A A).mpr ⟨hA,rfl⟩
    rw [h] at ha
    exact ((realCode_mem_degreeCode R B A).mp ha).2
  · intro h; unfold degreeCode; simp only [h]

/-- Degree-code closure under explicit axioms, without internal choice. -/
theorem internal_degreeCode_of_axioms (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
  (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ x ∈ R, ∃ B : Oracle, realCode B = x)
    {A : Oracle} (hA : A ∈ modelReals M) : degreeCode R A ∈ M := by
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hP hU hPow hS hω
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => realCode A)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    rcases i with _ | i
    · exact hz
    exact hA
  let D := ZFSet.sep (fun x => (Formula.twoOracles φ 1 2 3 0 4).Eval (cons x e)) R
  have hD : D ∈ M := sep_mem M hM hS _ e he hRM
  have hcode : degreeCode R A = D := by
    apply ZFSet.ext; intro x
    by_cases hx : x ∈ R
    · obtain ⟨B,rfl⟩ := hR x hx
      rw [realCode_mem_degreeCode,ZFSet.mem_sep]
      rw [hφ 1 2 3 0 4 (cons (realCode B) e) rfl hQ rfl B A rfl rfl]
    · simp only [degreeCode,D,ZFSet.mem_sep,hx,false_and]
  rw [hcode]
  exact hD


theorem internal_degreeCode (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ x ∈ R, ∃ B : Oracle, realCode B = x)
    {A : Oracle} (hA : A ∈ modelReals M) : degreeCode R A ∈ M := by
  exact internal_degreeCode_of_axioms M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) R hRM hR hA

theorem actual_degreeCode_membership (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ C : Oracle, realCode C ∈ R ↔ C ∈ modelReals M)
    {A : Oracle} (hA : A ∈ modelReals M) (B : Oracle) :
    realCode B ∈ degreeCode R A ↔ degree B = degree A := by
  rw [realCode_mem_degreeCode]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  exact (hR B).mpr (sourceT_real_lower M hM hT hA ((degree_eq_iff B A).mp h).1)

end TuringRigidity.BoundedSetTheory

end OAI

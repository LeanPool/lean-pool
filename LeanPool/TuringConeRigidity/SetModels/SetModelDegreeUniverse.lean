/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelDegreeUniverse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelCountableExtensions

/-!
# Set Model Degree Universe
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetPresentationDecoding SetDegreeDecoding UniformArithmetic
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem degree_universe (C : Context M) :
    ∃ D ∈ M, ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A) := by
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  refine ⟨quotientSet r E r,quotient_mem M C.transitive C.power C.separation hr hE hr,?_⟩
  intro x
  rw [mem_quotientSet]
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨A,hA,rfl⟩ := (hrc a).mp ha
    exact ⟨A,hA,hx.trans (class_eq_degreeSet M (lower_mem C) hrc hEc hA)⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨realSet A,(hrc _).mpr ⟨A,hA,rfl⟩,
      (class_eq_degreeSet M (lower_mem C) hrc hEc hA).symm⟩

theorem degree_order (C : Context M) :
    ∃ L ∈ M, ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B := by
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  obtain ⟨R,hR,hRc⟩ := internal_binary_relation C Reduces
    (reduces_arith (parameter_arith 0) (parameter_arith 1))
  refine ⟨actionGraph r E r R,
    action_mem M C.transitive C.pairing C.union C.power C.separation hr hE hr hR,?_⟩
  intro A hA B hB
  rw [mem_actionGraph]
  constructor
  · rintro ⟨x,hx,y,hy,hxy,he⟩
    obtain ⟨X,hX,rfl⟩ := (hrc x).mp hx
    obtain ⟨Y,hY,rfl⟩ := (hrc y).mp hy
    rw [class_eq_degreeSet M (lower_mem C) hrc hEc hX,
      class_eq_degreeSet M (lower_mem C) hrc hEc hY] at he
    obtain ⟨ha,hb⟩ := ZFSet.pair_inj.mp he
    have ha' := degreeSet_injective ha
    have hb' := degreeSet_injective hb
    have hab := (hRc X hX Y hY).mp hxy
    exact ((degree_eq_iff A X).mp ha').1.trans
      (hab.trans ((degree_eq_iff B Y).mp hb').2)
  · intro hab
    refine ⟨realSet A,(hrc _).mpr ⟨A,hA,rfl⟩,realSet B,(hrc _).mpr ⟨B,hB,rfl⟩,
      (hRc A hA B hB).mpr hab,?_⟩
    rw [class_eq_degreeSet M (lower_mem C) hrc hEc hA,
      class_eq_degreeSet M (lower_mem C) hrc hEc hB]

theorem represented_of_degreeSet_mem (C : Context M) {a : Degree}
    (ha : degreeSet.{u} a ∈ M) : ∃ A ∈ reals M, degree A = a := by
  obtain ⟨A,rfl⟩ := degree_surjective a
  exact ⟨A,C.transitive _ ha _ ((real_mem_degreeSet A _).mpr rfl),rfl⟩

end
end TuringRigidity.SetModelSatisfaction

end OAI

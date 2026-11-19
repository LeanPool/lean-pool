/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConePullbackProgram.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.Representation.OwnProgramValue
public import LeanPool.TuringConeRigidity.TuringConeExtensionBounds

/-!
# The inverse-join graph and oracle-program semantics

The map represented here is x |-> rho.symm (a join x), not an automorphism.
Its native graph lets the general forcing/program lemmas apply without an
incorrect bijectivity assumption. Pointwise arithmetic output witnesses follow
from the previously checked inverse bound; uniform program selection is separate.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePullbackProgram

open TransitiveNameModel BoundedSetTheory PersistentRestrictions SetDegreeDecoding
open ConePersistence OracleJump RelativeConstructible GenericIdentity

noncomputable section
universe u

/-- Apply the inverse cone isomorphism to the join of the base with the ideal element. -/
def inverseAt {I : CountableIdeal} {a : Degree} (ρ : I ≃o Cone I a) (x : I) : I :=
  ρ.symm ⟨a ⊔ x.val, I.join_mem (ConePresentation.base_mem ρ) x.property, le_sup_left⟩

theorem inverseAt_prescribed {I : CountableIdeal} {a : Degree}
    (e : Degree ≃o Set.Ici a) (ρ : I ≃o Cone I a)
    (he : ConePersistence.RestrictsTo e I ρ) (x : I) :
    (inverseAt ρ x).val = ConeRigidity.pullback e x.val := by
  apply e.injective
  apply Subtype.ext
  have hv : (ρ (inverseAt ρ x)).val = a ⊔ x.val :=
    congrArg Subtype.val (ρ.apply_symm_apply _)
  exact (he (inverseAt ρ x)).trans (hv.trans (ConeRigidity.apply_pullback_val e x.val).symm)

/-- The set-coded graph of the ideal cone isomorphism's join-based pullback. -/
def pullbackGraph {I : CountableIdeal} {a : Degree} (ρ : I ≃o Cone I a) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x : I,
    z = ZFSet.pair (degreeSet x.val) (degreeSet (inverseAt ρ x).val))
      (ZFSet.prod (idealSet I) (idealSet I))

@[simp] theorem mem_pullbackGraph {I : CountableIdeal} {a : Degree}
    (ρ : I ≃o Cone I a) (z : ZFSet.{u}) :
    z ∈ pullbackGraph ρ ↔ ∃ x : I,
      z = ZFSet.pair (degreeSet x.val) (degreeSet (inverseAt ρ x).val) := by
  rw [pullbackGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨x, rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr
      ⟨(mem_idealSet I _).mpr ⟨x.val, x.property, rfl⟩,
        (mem_idealSet I _).mpr ⟨(inverseAt ρ x).val, (inverseAt ρ x).property, rfl⟩⟩,
      ⟨x, rfl⟩⟩

/-- The output relation used by the existing general forcing compiler. -/
def Output (E f : ZFSet.{0}) (A X : Oracle) : Prop :=
  ∃ u ∈ degreeUniverse (groundReals E), ∃ v ∈ degreeUniverse (groundReals E),
    realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f

theorem output_of_degree {I : CountableIdeal} {a : Degree} (ρ : I ≃o Cone I a)
    (E : ZFSet.{0}) (hD : degreeUniverse (groundReals E) = idealSet I)
    (A X : Oracle) (hA : degree A ∈ I.carrier)
    (hX : degree X = (inverseAt ρ ⟨degree A, hA⟩).val) :
    Output E (pullbackGraph ρ) A X := by
  refine ⟨degreeSet (degree A), ?_, degreeSet (inverseAt ρ ⟨degree A, hA⟩).val,
    ?_, (real_mem_degreeSet A _).mpr rfl, (real_mem_degreeSet X _).mpr hX,
    (mem_pullbackGraph ρ _).mpr ⟨⟨degree A, hA⟩, rfl⟩⟩
  · rw [hD]
    exact (mem_idealSet I _).mpr ⟨degree A, hA, rfl⟩
  · rw [hD]
    exact (mem_idealSet I _).mpr
      ⟨(inverseAt ρ ⟨degree A, hA⟩).val, (inverseAt ρ ⟨degree A, hA⟩).property, rfl⟩

theorem output_action {I : CountableIdeal} {a : Degree} (ρ : I ≃o Cone I a)
    (E : ZFSet.{0}) (A X : Oracle) (h : Output E (pullbackGraph ρ) A X) :
    ∃ hA : degree A ∈ I.carrier, degree X = (inverseAt ρ ⟨degree A, hA⟩).val := by
  obtain ⟨u, _, v, _, hAu, hXv, hpair⟩ := h
  obtain ⟨x, he⟩ := (mem_pullbackGraph ρ _).mp hpair
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
  have ha : degree A = x.val := (real_mem_degreeSet A x.val).mp hAu
  have hA : degree A ∈ I.carrier := ha.symm ▸ x.property
  have hx : (⟨degree A, hA⟩ : I) = x := Subtype.ext ha
  exact ⟨hA, by rw [hx]; exact (real_mem_degreeSet X _).mp hXv⟩

/-- The arithmetic witness at one input is supplied by the cone bound,
not assumed to be a uniform computation. -/
theorem output_of_extension {I J : CountableIdeal} {a : Degree}
    (ρ : I ≃o Cone I a) (σ : J ≃o Cone J a)
    (hIJ : I.carrier ⊆ J.carrier) (he : ConePersistence.Extends hIJ ρ σ)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (B : Oracle) (hB : degree B = (ρ ⟨degree (jump FixedArithmetic.zero), hz⟩).val)
    (E : ZFSet.{0}) (hD : degreeUniverse (groundReals E) = idealSet J)
    (A : Oracle) (hA : degree A ∈ J.carrier) :
    ∃ X : Oracle, Reduces X (iterate (join A B) 5) ∧
      Output E (pullbackGraph σ) A X := by
  obtain ⟨X, hX, hb⟩ :=
    ConeExtensionBounds.inverse_bound_of_extension ρ σ hIJ he hz B hB A hA
  exact ⟨X, hb, output_of_degree σ E hD A X hA hX⟩

/-- A compiled program whose output lies in the native inverse graph has
exactly the intended degree. No automorphism hypothesis on that graph is used. -/
theorem own_program_action {I : CountableIdeal} {a : Degree} (ρ : I ≃o Cone I a)
    (E : ZFSet.{0}) (p : OracleCode) (B A : Oracle)
    (h : OwnProgramAt E (pullbackGraph ρ) p B A) :
    ∃ hA : degree A ∈ I.carrier,
      degree (value p B A) = (inverseAt ρ ⟨degree A, hA⟩).val :=
  output_action ρ E A (value p B A) h.2

theorem own_program_prescribed {I : CountableIdeal} {a : Degree}
    (e : Degree ≃o Set.Ici a) (ρ : I ≃o Cone I a)
    (he : ConePersistence.RestrictsTo e I ρ)
    (E : ZFSet.{0}) (p : OracleCode) (B A : Oracle)
    (h : OwnProgramAt E (pullbackGraph ρ) p B A) :
    Total p B A ∧ degree (value p B A) = ConeRigidity.pullback e (degree A) := by
  obtain ⟨hA, hv⟩ := own_program_action ρ E p B A h
  exact ⟨h.1, hv.trans (inverseAt_prescribed e ρ he _)⟩

end
end OAI.TuringRigidity.ConePullbackProgram

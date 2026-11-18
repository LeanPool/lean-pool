/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePullbackProgram.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeDegreeIdeal
public import LeanPool.TuringConeRigidity.TuringConePullbackProgram
public import LeanPool.TuringConeRigidity.TuringTwoConeLocality

/-!
# The joined inverse of a two-cone map as a native relation

The target base belongs to the ambient ideal explicitly. The joined inverse
is a total map on that ordinary ideal with values in its source cone; it is
not assumed injective. Its graph uses the existing relation-only oracle
compiler. When the partial map restricts a global map, all outputs agree with
that same global map, and the fixed fifth-jump bound supplies its witnesses.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePullbackProgram

open TransitiveNameModel BoundedSetTheory PersistentRestrictions SetDegreeDecoding
open OracleJump RelativeConstructible GenericIdentity ElementaryModel
open ConePersistence (Cone)
open ConePullbackProgram (Output)
open TwoConeLocality (forwardAnchor)

universe u
noncomputable section

/-- Apply the inverse cone isomorphism to the join of the target base with the ideal element. -/
def inverseAt {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hb : b ∈ I.carrier) (x : I) : Cone I a :=
  ρ.symm ⟨b ⊔ x.val, I.join_mem hb x.property, le_sup_left⟩

theorem inverseAt_prescribed {I : CountableIdeal} {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (ρ : Cone I a ≃o Cone I b)
    (hb : b ∈ I.carrier) (he : TwoConePersistence.RestrictsTo e I ρ) (x : I) :
    (inverseAt ρ hb x).val = TwoConeRigidity.pullback e x.val := by
  have hinput : ConeRigidity.coneJoin a (inverseAt ρ hb x).val =
      (⟨(inverseAt ρ hb x).val, (inverseAt ρ hb x).property.2⟩ : Set.Ici a) :=
    Subtype.ext (sup_eq_right.mpr (inverseAt ρ hb x).property.2)
  have hv : (ρ (inverseAt ρ hb x)).val = b ⊔ x.val :=
    congrArg Subtype.val (ρ.apply_symm_apply _)
  have hm : e ⟨(inverseAt ρ hb x).val, (inverseAt ρ hb x).property.2⟩ =
      ConeRigidity.coneJoin b x.val := by
    apply Subtype.ext
    have hh := (he (inverseAt ρ hb x)).trans hv
    change (e (ConeRigidity.coneJoin a (inverseAt ρ hb x).val)).val = b ⊔ x.val at hh
    rw [hinput] at hh
    exact hh
  have hh := congrArg (fun z => (e.symm z).val) hm
  simpa only [TwoConeRigidity.pullback, TwoConeRigidity.imageJoin, e.symm_apply_apply] using hh

/-- The set-coded graph on the whole ideal of the join-based pullback into the source cone. -/
def pullbackGraph {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hb : b ∈ I.carrier) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x : I,
    z = ZFSet.pair (degreeSet x.val) (degreeSet (inverseAt ρ hb x).val))
      (ZFSet.prod (idealSet I) (idealSet I))

@[simp] theorem mem_pullbackGraph {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hb : b ∈ I.carrier) (z : ZFSet.{u}) :
    z ∈ pullbackGraph ρ hb ↔ ∃ x : I,
      z = ZFSet.pair (degreeSet x.val) (degreeSet (inverseAt ρ hb x).val) := by
  rw [pullbackGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨x, rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr
      ⟨(mem_idealSet I _).mpr ⟨x.val, x.property, rfl⟩,
        (mem_idealSet I _).mpr ⟨(inverseAt ρ hb x).val, (inverseAt ρ hb x).property.1, rfl⟩⟩,
      ⟨x, rfl⟩⟩

theorem output_of_degree {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hb : b ∈ I.carrier)
    (E : ZFSet.{0}) (hD : degreeUniverse (groundReals E) = idealSet I)
    (A X : Oracle) (hA : degree A ∈ I.carrier)
    (hX : degree X = (inverseAt ρ hb ⟨degree A, hA⟩).val) :
    Output E (pullbackGraph ρ hb) A X := by
  refine ⟨degreeSet (degree A), ?_, degreeSet (inverseAt ρ hb ⟨degree A, hA⟩).val,
    ?_, (real_mem_degreeSet A _).mpr rfl, (real_mem_degreeSet X _).mpr hX,
    (mem_pullbackGraph ρ hb _).mpr ⟨⟨degree A, hA⟩, rfl⟩⟩
  · rw [hD]
    exact (mem_idealSet I _).mpr ⟨degree A, hA, rfl⟩
  · rw [hD]
    exact (mem_idealSet I _).mpr
      ⟨(inverseAt ρ hb ⟨degree A, hA⟩).val,
        (inverseAt ρ hb ⟨degree A, hA⟩).property.1, rfl⟩

theorem output_action {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hb : b ∈ I.carrier)
    (E : ZFSet.{0}) (A X : Oracle) (h : Output E (pullbackGraph ρ hb) A X) :
    ∃ hA : degree A ∈ I.carrier, degree X = (inverseAt ρ hb ⟨degree A, hA⟩).val := by
  obtain ⟨u, _, v, _, hAu, hXv, hpair⟩ := h
  obtain ⟨x, he⟩ := (mem_pullbackGraph ρ hb _).mp hpair
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
  have ha : degree A = x.val := (real_mem_degreeSet A x.val).mp hAu
  have hA : degree A ∈ I.carrier := ha.symm ▸ x.property
  have hx : (⟨degree A, hA⟩ : I) = x := Subtype.ext ha
  exact ⟨hA, by rw [hx]; exact (real_mem_degreeSet X _).mp hXv⟩

/-- The old parameter represents e(a'); there is no uniformity claim about
reduction indices in this pointwise output theorem. -/
theorem model_outputs_of_restriction {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (E : ZFSet.{0}) [Countable (Conditions E)] (hE : Transitive E) (hTE : SourceT E)
    (ρ : Cone (modelIdeal E hE hTE) a ≃o Cone (modelIdeal E hE hTE) b)
    (hb : b ∈ (modelIdeal E hE hTE).carrier)
    (he : TwoConePersistence.RestrictsTo e (modelIdeal E hE hTE) ρ)
    (R : Oracle) (hR : degree R = forwardAnchor e) :
    ∀ A ∈ modelReals E, ∃ X : Oracle,
      Reduces X (iterate (join A R) 5) ∧ Output E (pullbackGraph ρ hb) A X := by
  intro A hA
  let x : modelIdeal E hE hTE := ⟨degree A, ⟨A, hA, rfl⟩⟩
  obtain ⟨X, hX⟩ := degree_surjective (inverseAt ρ hb x).val
  have hglobal := hX.trans (inverseAt_prescribed e ρ hb he x)
  exact ⟨X, TwoConeLocality.pullback_reduces_fifth_jump e R hR X A hglobal,
    output_of_degree ρ hb E (ground_degreeUniverse_eq_idealSet E hE hTE)
      A X x.property hX⟩

/-- Program correctness is for the prescribed original global map, not
an unrelated extension of a smaller partial map. -/
theorem own_program_prescribed {I : CountableIdeal} {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (ρ : Cone I a ≃o Cone I b)
    (hb : b ∈ I.carrier) (he : TwoConePersistence.RestrictsTo e I ρ)
    (E : ZFSet.{0}) (p : OracleCode) (P A : Oracle)
    (h : OwnProgramAt E (pullbackGraph ρ hb) p P A) :
    Total p P A ∧ degree (value p P A) = TwoConeRigidity.pullback e (degree A) := by
  obtain ⟨hA, hv⟩ := output_action ρ hb E A (value p P A) h.2
  exact ⟨h.1, hv.trans (inverseAt_prescribed e ρ hb he _)⟩

end
end OAI.TuringRigidity.TwoConePullbackProgram

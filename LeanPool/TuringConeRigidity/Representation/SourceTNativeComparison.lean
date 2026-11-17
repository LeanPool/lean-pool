/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTNativeComparison.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTNativeAbsoluteness
public import LeanPool.TuringConeRigidity.SetModels.SetModelGraphPresentation

/-!
# Source TNative Comparison
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetModelSyntax SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions PersistentPresentation PersistentCountability
universe u
noncomputable section

theorem native_persistence_absolute (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {D L : ZFSet.{u}} (hDM : D ∈ M) (hLM : L ∈ M)
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) ↔ Persistent I ρ := by
  obtain ⟨A,hAM,hA⟩ := sourceT_countable_presentation M hM hT I hI hct
  have hRM := internal_graph_presentation (sourceContext M hM hT) hA hAM hI ρ hρ
  exact sourceT_native_persistence_iff M hM hT hDM hLM hD hL I hI hct ρ hρ hA hAM hRM
    (fun n => by simp [graphOracle]) hz

def SetMoved (f i : ZFSet.{u}) : Prop := ∃ x ∈ i, ∃ y ∈ i, ZFSet.pair x y ∈ f ∧ x ≠ y

theorem setMoved_iff (I : CountableIdeal) (ρ : I ≃o I) :
    SetMoved (automorphismSet.{u} ρ) (idealSet I) ↔ ∃ x : I, ρ x ≠ x := by
  constructor
  · rintro ⟨x,hx,y,hy,hxy,hne⟩
    obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I y).mp hy
    have hab := (action_code ρ ⟨a,ha⟩ ⟨b,hb⟩).mp hxy
    refine ⟨⟨a,ha⟩,fun he => hne ?_⟩
    exact congrArg (fun x : I => degreeSet.{u} x.val) (he.symm.trans hab)
  · rintro ⟨a,ha⟩
    exact ⟨degreeSet a.val,(mem_idealSet I _).mpr ⟨_,a.property,rfl⟩,
      degreeSet (ρ a).val,(mem_idealSet I _).mpr ⟨_,(ρ a).property,rfl⟩,
      (action_code ρ a (ρ a)).mpr rfl,
      fun he => ha (Subtype.ext (degreeSet_injective he).symm)⟩

def NativeNonidentity (M D L i : ZFSet.{u}) : Prop :=
  ∃ f ∈ M, IsAction f i L ∧ SetMoved f i ∧
    persistenceFormula.Realize M (cons D (cons L (cons i (cons f (fun _ => ZFSet.omega)))))

theorem native_nonidentity_absolute (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {D L : ZFSet.{u}} (hDM : D ∈ M) (hLM : L ∈ M)
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    NativeNonidentity M D L (idealSet I) ↔ ∃ ρ : I ≃o I, Persistent I ρ ∧ ∃ x : I, ρ x ≠ x := by
  let C := sourceContext M hM hT
  constructor
  · rintro ⟨f,hf,ha,hm,hp⟩
    obtain ⟨ρ,rfl⟩ := decode_action C hL I hI ha
    exact ⟨ρ,(native_persistence_absolute M hM hT hDM hLM hD hL I hI hct ρ hf hz).mp hp,
      (setMoved_iff I ρ).mp hm⟩
  · rintro ⟨ρ,hp,hm⟩
    have hρ := persistent_mem_of_countable C (sourceT_internalChoice M hM hT) I hI hct ρ hp hz
    exact ⟨automorphismSet ρ,hρ,action_satisfaction C hL hI ρ,(setMoved_iff I ρ).mpr hm,
      (native_persistence_absolute M hM hT hDM hLM hD hL I hI hct ρ hρ hz).mpr hp⟩

end
end TuringRigidity.ArithmeticTree

end OAI

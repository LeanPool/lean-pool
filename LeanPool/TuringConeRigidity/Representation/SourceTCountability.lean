/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTCountability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTTreeAbsoluteness
public import LeanPool.TuringConeRigidity.SetModels.SetModelPersistentSatisfaction

/-!
# Source TCountability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetModelCountability SetModelSyntax SetDegreeDecoding
open PersistentPresentation PersistentRestrictions SetModelSatisfaction
universe u
noncomputable section

theorem sourceT_internalChoice (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    SetModelCountability.InternalChoice M := by
  intro a ha hne
  obtain ⟨f,hf,hfg⟩ := hT.choice a ha (fun x hx => by
    obtain ⟨y,_,hy⟩ := hne x (hM a ha x hx) hx
    exact ⟨y,hy⟩)
  have hu := union_mem M hM hT.union ha
  have he : ∀ i, cons f (cons a (fun _ => ZFSet.sUnion a)) i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [hf,ha,hu]
  refine ⟨f,hf,((choiceFormula 0 1 2).absolute M hM _ he).mpr ?_⟩
  rw [eval_choiceFormula]
  change SetModelCountability.FunctionGraph f a (ZFSet.sUnion a) ∧ ∀ x ∈ a, ∃ y ∈ x, ZFSet.pair x
    y ∈ f
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,y,hy,heq⟩ := hfg.1 z hz
    exact ⟨x,hx,y,ZFSet.mem_sUnion.mpr ⟨x,hx,hy⟩,heq⟩
  · intro x hx
    obtain ⟨y,hy,hxy,_⟩ := hfg.2 x hx
    exact ⟨y,ZFSet.mem_sUnion.mpr ⟨x,hx,hy⟩,hxy,
      fun z _ hxz => hfg.functional hxz hxy⟩
  · intro x hx
    obtain ⟨y,hy,hxy,_⟩ := hfg.2 x hx
    exact ⟨y,hy,hxy⟩

theorem sourceT_countable_presentation (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I)) :
    ∃ A ∈ reals M, Presented I A :=
  countable_presentation (sourceContext M hM hT) (sourceT_internalChoice M hM hT) I hI hct

theorem sourceT_native_persistence (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    ∃ D ∈ M, ∃ L ∈ M,
      (∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A)) ∧
      (∀ A ∈ reals M, ∀ B ∈ reals M,
        ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B) ∧
      automorphismSet ρ ∈ M ∧
      persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
        (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) :=
  source_4_2_5_transitive (sourceContext M hM hT) (sourceT_internalChoice M hM hT) I hI hct ρ hρ hz

end
end TuringRigidity.ArithmeticTree

end OAI

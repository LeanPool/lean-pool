/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTNativeAbsoluteness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTCountability
public import LeanPool.TuringConeRigidity.SetModels.SetModelPersistenceDecoding

/-!
# Source TNative Absoluteness
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetModelSyntax SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions PersistentPresentation PersistentCountability
open NumericalAutomorphism NumericalIdeal NumericalExtension
universe u
noncomputable section

theorem native_internal_matrix {M : ZFSet.{u}} (C : Context M)
    {D L : ZFSet.{u}} (hDM : D ∈ M) (hLM : L ∈ M)
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    {A R : Oracle} (hA : Presented I A)
    (hR : ∀ n, R n = true ↔ Graph ρ hA n)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hp : persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega)))))) :
    ∀ H ∈ reals M, Matrix (parameters A R H) 0 := by
  intro H hHM hcode hincl
  let J := decode H hcode
  have hJ : Presented J H := decoded_presentation H hcode
  have hIJ : I.carrier ⊆ J.carrier := (includes_iff hA hJ).mp hincl
  let K₀ := JumpIdeal.generated (degree H)
  let B := JumpIdealPresentation.presentation H
  have hB : Presented K₀ B := JumpIdealPresentation.presents H
  have hBM : B ∈ reals M := (realClosure C).presentation hHM
  obtain ⟨K,hIK,τ,hBK,he⟩ := decode_persistence_extension C hDM hLM hD hL I hI ρ hρ hp hBM
  have hK₀K : K₀.carrier ⊆ K.carrier := by
    intro x hx
    obtain ⟨n,rfl⟩ := (hB x).mp hx
    exact K.lower (CodingExtraction.column_projection_reduces B n) hBK
  have hJK₀ : J.carrier ⊆ K₀.carrier := by
    intro x hx
    obtain ⟨n,rfl⟩ := (hJ x).mp hx
    exact K₀.lower (CodingExtraction.column_projection_reduces H n) (JumpIdeal.includes _)
  have hJK : J.carrier ⊆ K.carrier := fun x hx => hK₀K (hJK₀ hx)
  obtain ⟨σ,hσ,_,hr⟩ := PersistentRestrictionCode.restriction ρ τ hIK he hz hIJ hJK
    (decoded_closed H hcode) hJ hK₀K
  obtain ⟨e,hg⟩ := graph_program hJ σ hr
  refine ⟨e,(PersistenceCriterion.action_congr hg).mpr (action_of_automorphism hJ σ),?_⟩
  intro i j n m hr hp hin
  exact ((compatible_iff hA hJ hIJ ρ σ).mpr hσ) i j n m ((hR _).mp hr) ((hg _).mp hp) hin

theorem sourceT_native_persistence_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {D L : ZFSet.{u}} (hDM : D ∈ M) (hLM : L ∈ M)
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    {A R : Oracle} (hA : Presented I A) (hAM : A ∈ reals M) (hRM : R ∈ reals M)
    (hR : ∀ n, R n = true ↔ Graph ρ hA n)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) ↔ Persistent I ρ := by
  let C := sourceContext M hM hT
  constructor
  · intro hp
    have hi := native_internal_matrix C hDM hLM hD hL I hI ρ hρ hA hR hz hp
    have he := (sourceT_piOneOne_matrix M hM hT matrix_arith A R hAM hRM 0).mp hi
    exact (ArithmeticPersistence.persistent_iff hA ρ hz hR).mpr he
  · intro hp
    exact persistent_satisfaction C (sourceT_internalChoice M hM hT) hDM hLM hD hL I hI hct ρ hp hz

end
end TuringRigidity.ArithmeticTree

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelPersistenceDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelActionDecoding

/-!
# Set Model Persistence Decoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section

theorem decode_persistence_extension {M : ZFSet.{u}} (C : Context M)
    {D L : ZFSet.{u}} (hDM : D ∈ M) (hLM : L ∈ M)
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hp : persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))))
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (σ : J ≃o J),
      degree X ∈ J.carrier ∧ Extends hIJ ρ σ := by
  have hxD : degreeSet.{u} (degree X) ∈ D := (hD _).mpr ⟨X,hX,rfl⟩
  have hxM := C.transitive _ hDM _ hxD
  rw [persistenceFormula,InternalFormula.realize_allMem] at hp
  obtain ⟨a,ha,f,hf,c,hc,hmat⟩ := hp _ hxM hxD
  let e := cons c (cons f (cons a (cons (degreeSet (degree X)) (cons D (cons L
    (cons (idealSet I) (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))))))
  have heM : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|_|_|_|i <;> simp [e,hc,hf,ha,hxM,hDM,hLM,hI,hρ,C.omega_mem]
  have hm := (persistenceMatrix.absolute M C.transitive e heM).mp hmat
  simp only [persistenceMatrix,Formula.Eval,eval_idealFormula,eval_ontoFormula,
    eval_actionFormula,Formula.eval_subset,cons_zero,cons_succ,e] at hm
  obtain ⟨hideal,honto,hact,hsub,hfsub,hxa⟩ := hm
  have hct : InternallyCountable M a := by
    have hec : ∀ i, cons c (cons ZFSet.omega (fun _ => a)) i ∈ M := by
      intro i
      rcases i with _|_|i <;> simp [hc,C.omega_mem,ha]
    exact ⟨c,hc,((ontoFormula 0 1 2).absolute M C.transitive _ hec).mpr
      ((eval_ontoFormula 0 1 2 _).mpr honto)⟩
  obtain ⟨J,rfl⟩ := decode_ideal C hD hL ha hideal hct
  obtain ⟨σ,rfl⟩ := decode_action C hL J ha hact
  have hIJ := ideal_subset_iff.mp hsub
  refine ⟨J,hIJ,σ,?_,(extends_sets_iff hIJ ρ σ).mp hfsub⟩
  obtain ⟨a,ha,he⟩ := (mem_idealSet J _).mp hxa
  exact (degreeSet_injective he).symm ▸ ha

end
end TuringRigidity.SetModelSatisfaction

end OAI

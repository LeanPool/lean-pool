/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativePersistentDescent.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.WeakRealDescent
public import LeanPool.TuringConeRigidity.Constructibility.RelativeDegreeIdeal

/-!
# Relative Persistent Descent
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions
universe u

theorem persistent_modelIdeal_graph_mem_relativeModel (M : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT)
    (hρ : Persistent (modelIdeal M hM hT) ρ) :
    automorphismSet ρ ∈ relativeModel M (groundReals M) := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have hRN : R ∈ N := (mem_relativeModel M R R hM hT hR).mpr
    (parameter_in_relativeModel M R hM hT)
  have hreal (x : ZFSet.{u}) (hx : x ∈ R) : ∃ B : Oracle, SetModelReals.realSet B = x :=
    ⟨decodeReal x,realCode_decodeReal ((mem_groundReals M x).mp hx).2⟩
  have hIR (d : Degree) : d ∈ (modelIdeal M hM hT).carrier ↔
      ∃ B : Oracle, SetModelReals.realSet B ∈ R ∧ degree B = d := by
    change (∃ B ∈ modelReals M, degree B = d) ↔ _
    exact exists_congr (fun B => and_congr (realCode_mem_groundReals M B).symm Iff.rfl)
  have hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ (modelIdeal M hM hT).carrier :=
    ⟨_,sourceT_real_jump M hM hT (sourceT_zero_real M hM hT),rfl⟩
  exact FullSetForcing.persistent_graph_mem_of_real_family N M
    (relativeModel_transitive M R hM) (relativeModel_pairing M R hM hT hR)
    (relativeModel_union M R hM hT hR) (relativeModel_power_set M R hM hT hR)
    (relativeModel_sigma_separation M R hM hT hR)
    (relativeModel_sigma_replacement M R hM hT hR)
    (ground_relativeModel_infinity M hM hT) (relativeModel_subset M R)
    hRN hreal (modelIdeal M hM hT) (ground_idealSet_mem_relativeModel M hM hT)
    hIR ρ hρ hz

theorem persistent_modelIdeal_graph_in_relativeL (M : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT)
    (hρ : Persistent (modelIdeal M hM hT) ρ) :
    InRelativeL (groundReals M) (automorphismSet ρ) :=
  relativeModel_external M _ (persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hρ)

end TuringRigidity.RelativeConstructible

end OAI

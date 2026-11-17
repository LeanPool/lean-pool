/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeConstructibleExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeForcingDescent
public import LeanPool.TuringConeRigidity.Constructibility.RelativeDegreeIdeal
public import LeanPool.TuringConeRigidity.Constructibility.RelativeConstruction
public import LeanPool.TuringConeRigidity.Constructibility.RelativeSigmaSchemas

/-!
# Persistent cone extensions in the relative constructible model

A persistent cone map on all degrees of a countable transitive SourceT model
has its entire graph in that model's relative L(R). This follows from collapse
and descent, not an assumption that the graph is constructible. Persistent
partial maps consequently extend to all model degrees with an internal graph.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeConstructibleExtension

open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions ConePersistence ConeSetGraphs RelativeConstructible
open OracleJump

universe u

/-- The graph lies in the relative constructible model over the old reals. -/
theorem persistent_modelIdeal_graph_mem_relativeModel (M : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    {a : Degree} (ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a)
    (hρ : ConePersistence.Persistent (modelIdeal M hM hT) ρ) :
    coneGraph ρ ∈ relativeModel M (groundReals M) := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have hRN : R ∈ N := (mem_relativeModel M R R hM hT hR).mpr
    (parameter_in_relativeModel M R hM hT)
  have hreal (x : ZFSet.{u}) (hx : x ∈ R) :
      ∃ B : Oracle, SetModelReals.realSet B = x :=
    ⟨decodeReal x, realCode_decodeReal ((mem_groundReals M x).mp hx).2⟩
  have hIR (d : Degree) : d ∈ (modelIdeal M hM hT).carrier ↔
      ∃ B : Oracle, SetModelReals.realSet B ∈ R ∧ degree B = d := by
    change (∃ B ∈ modelReals M, degree B = d) ↔ _
    exact exists_congr (fun B => and_congr (realCode_mem_groundReals M B).symm Iff.rfl)
  have hza : degreeJump a ∈ (modelIdeal M hM hT).carrier :=
    modelIdeal_jump M hM hT a (ConePresentation.base_mem ρ)
  exact ConeForcingDescent.persistent_graph_mem_of_real_family N M
    (relativeModel_transitive M R hM) (relativeModel_pairing M R hM hT hR)
    (relativeModel_union M R hM hT hR) (relativeModel_power_set M R hM hT hR)
    (relativeModel_sigma_separation M R hM hT hR)
    (relativeModel_sigma_replacement M R hM hT hR)
    (ground_relativeModel_infinity M hM hT) (relativeModel_subset M R)
    hRN hreal (modelIdeal M hM hT) (ground_idealSet_mem_relativeModel M hM hT)
    hIR ρ hρ hza

theorem persistent_modelIdeal_graph_in_relativeL (M : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    {a : Degree} (ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a)
    (hρ : ConePersistence.Persistent (modelIdeal M hM hT) ρ) :
    InRelativeL (groundReals M) (coneGraph ρ) :=
  relativeModel_external M _ (persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hρ)

/-- Extend to the entire model ideal, preserve persistence, and prove that the
full graph belongs to relative L(R). The initial graph need not be given as
an element of the model. -/
theorem persistent_extension_in_relativeModel (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) {a : Degree} (ρ : I ≃o Cone I a)
    (hρ : ConePersistence.Persistent I ρ) (hza : degreeJump a ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a,
      ConePersistence.Extends hIM ρ σ ∧
      ConePersistence.Persistent (modelIdeal M hM hT) σ ∧
      coneGraph σ ∈ relativeModel M (groundReals M) := by
  obtain ⟨σ, he, hσ⟩ := ConePersistentExtension.persistent_extension
    I (modelIdeal M hM hT) ρ hρ hza hIM (modelIdeal_jump M hM hT)
  exact ⟨σ, he, hσ, persistent_modelIdeal_graph_mem_relativeModel M hM hT σ hσ⟩

theorem persistent_extension_in_model (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) {a : Degree} (ρ : I ≃o Cone I a)
    (hρ : ConePersistence.Persistent I ρ) (hza : degreeJump a ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a,
      ConePersistence.Extends hIM ρ σ ∧
      ConePersistence.Persistent (modelIdeal M hM hT) σ ∧ coneGraph σ ∈ M := by
  obtain ⟨σ, he, hσ, hmem⟩ := persistent_extension_in_relativeModel M hM hT I ρ hρ hza hIM
  exact ⟨σ, he, hσ, relativeModel_subset M _ hmem⟩

/-- Reuse the general finite-construction coding for the new cone graph. -/
theorem persistent_graph_construction (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {a : Degree} (ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a)
    (hρ : ConePersistence.Persistent (modelIdeal M hM hT) ρ) :
    ∃ t : Construction.{u}, ∃ P : Oracle, P ∈ modelReals M ∧
      t.Indexed M ∧ t.Certified (groundReals M) P ∧
      t.value (groundReals M) P = coneGraph ρ :=
  construction_of_relativeModel M hM hT _
    (persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hρ)

theorem persistent_extension_construction (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) {a : Degree} (ρ : I ≃o Cone I a)
    (hρ : ConePersistence.Persistent I ρ) (hza : degreeJump a ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a,
      ConePersistence.Extends hIM ρ σ ∧
      ConePersistence.Persistent (modelIdeal M hM hT) σ ∧
      ∃ t : Construction.{u}, ∃ P : Oracle, P ∈ modelReals M ∧
        t.Indexed M ∧ t.Certified (groundReals M) P ∧
        t.value (groundReals M) P = coneGraph σ := by
  obtain ⟨σ, he, hσ, hm⟩ := persistent_extension_in_relativeModel M hM hT I ρ hρ hza hIM
  exact ⟨σ, he, hσ, construction_of_relativeModel M hM hT _ hm⟩

end OAI.TuringRigidity.ConeConstructibleExtension

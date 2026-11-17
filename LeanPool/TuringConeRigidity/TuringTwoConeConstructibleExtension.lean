/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeConstructibleExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeForcingDescent
public import LeanPool.TuringConeRigidity.Constructibility.RelativeDegreeIdeal
public import LeanPool.TuringConeRigidity.Constructibility.ConstructionDefinition

/-!
# Persistent two-cone graphs in relative L(R)

Collapse and descent place the entire graph in the relative constructible
model, without assuming the graph was already internal. Both bases are named
members of the model ideal; unlike the one-cone case, an isomorphism between
two possibly empty intersections alone does not establish those memberships.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeConstructibleExtension

open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions TwoConeSetGraphs RelativeConstructible OracleJump
open ConePersistence (Cone)

universe u

/-- The complete persistent graph belongs to relative L over the model reals. -/
theorem persistent_modelIdeal_graph_mem_relativeModel (M : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    {a b : Degree}
    (ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b)
    (hρ : TwoConePersistence.Persistent (modelIdeal M hM hT) ρ)
    (ha : a ∈ (modelIdeal M hM hT).carrier)
    (hb : b ∈ (modelIdeal M hM hT).carrier) :
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
  exact TwoConeForcingDescent.persistent_graph_mem_of_real_family N M
    (relativeModel_transitive M R hM) (relativeModel_pairing M R hM hT hR)
    (relativeModel_union M R hM hT hR) (relativeModel_power_set M R hM hT hR)
    (relativeModel_sigma_separation M R hM hT hR)
    (relativeModel_sigma_replacement M R hM hT hR)
    (ground_relativeModel_infinity M hM hT) (relativeModel_subset M R)
    hRN hreal (modelIdeal M hM hT) (ground_idealSet_mem_relativeModel M hM hT)
    hIR ρ hρ (modelIdeal_jump M hM hT a ha) (modelIdeal_jump M hM hT b hb)

theorem persistent_modelIdeal_graph_in_relativeL (M : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    {a b : Degree}
    (ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b)
    (hρ : TwoConePersistence.Persistent (modelIdeal M hM hT) ρ)
    (ha : a ∈ (modelIdeal M hM hT).carrier)
    (hb : b ∈ (modelIdeal M hM hT).carrier) :
    InRelativeL (groundReals M) (coneGraph ρ) :=
  relativeModel_external M _
    (persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hρ ha hb)

/-- Extend to both cones of the whole model ideal, preserving persistence.
No prior internality of the initial graph is required. -/
theorem persistent_extension_in_relativeModel (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) {a b : Degree} (ρ : Cone I a ≃o Cone I b)
    (hρ : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b,
      TwoConePersistence.Extends hIM ρ σ ∧
      TwoConePersistence.Persistent (modelIdeal M hM hT) σ ∧
      coneGraph σ ∈ relativeModel M (groundReals M) := by
  obtain ⟨σ, he, hσ⟩ := TwoConePersistentExtension.persistent_extension
    I (modelIdeal M hM hT) ρ hρ hza hzb hIM (modelIdeal_jump M hM hT)
  exact ⟨σ, he, hσ, persistent_modelIdeal_graph_mem_relativeModel M hM hT σ hσ
    (hIM (I.lower (degree_le_jump a) hza)) (hIM (I.lower (degree_le_jump b) hzb))⟩

theorem persistent_extension_in_model (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) {a b : Degree} (ρ : Cone I a ≃o Cone I b)
    (hρ : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b,
      TwoConePersistence.Extends hIM ρ σ ∧
      TwoConePersistence.Persistent (modelIdeal M hM hT) σ ∧ coneGraph σ ∈ M := by
  obtain ⟨σ, he, hσ, hmem⟩ :=
    persistent_extension_in_relativeModel M hM hT I ρ hρ hza hzb hIM
  exact ⟨σ, he, hσ, relativeModel_subset M _ hmem⟩

/-- The general finite-construction coding applies to this precise graph. -/
theorem persistent_graph_construction (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {a b : Degree}
    (ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b)
    (hρ : TwoConePersistence.Persistent (modelIdeal M hM hT) ρ)
    (ha : a ∈ (modelIdeal M hM hT).carrier)
    (hb : b ∈ (modelIdeal M hM hT).carrier) :
    ∃ t : Construction.{u}, ∃ P : Oracle, P ∈ modelReals M ∧
      t.Indexed M ∧ t.Certified (groundReals M) P ∧
      t.value (groundReals M) P = coneGraph ρ :=
  construction_of_relativeModel M hM hT _
    (persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hρ ha hb)

theorem persistent_extension_construction (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) {a b : Degree} (ρ : Cone I a ≃o Cone I b)
    (hρ : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b,
      TwoConePersistence.Extends hIM ρ σ ∧
      TwoConePersistence.Persistent (modelIdeal M hM hT) σ ∧
      ∃ t : Construction.{u}, ∃ P : Oracle, P ∈ modelReals M ∧
        t.Indexed M ∧ t.Certified (groundReals M) P ∧
        t.value (groundReals M) P = coneGraph σ := by
  obtain ⟨σ, he, hσ, hm⟩ :=
    persistent_extension_in_relativeModel M hM hT I ρ hρ hza hzb hIM
  exact ⟨σ, he, hσ, construction_of_relativeModel M hM hT _ hm⟩

end OAI.TuringRigidity.TwoConeConstructibleExtension

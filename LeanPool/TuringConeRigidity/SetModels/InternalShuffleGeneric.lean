/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalShuffleGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalShuffleSets
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFilters

/-!
# Internal Shuffle Generic
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing
open ShuffleRequirements FiniteShuffleCertificate
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem groundGeneric_shuffle (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : Oracle) (hG : AtomicForcing.GroundGeneric M (pushFilter (realFilter G)))
    (Y : Oracle) :
    AtomicForcing.GroundGeneric M (pushFilter (realFilter (GenericCoding.code Y G))) := by
  apply (groundGeneric_iff M _).mpr
  intro D hD hd
  obtain ⟨p,hp,hstar⟩ := (groundGeneric_iff M _).mp hG (shuffleStar D)
    (shuffleStar_mem M hM hT D hD) (shuffleStar_dense D hd)
  rw [pull_push] at hp
  have hc := (wordCode_mem_shuffleStar D p.word).mp hstar
  obtain ⟨t,⟨r,hr,hrt⟩,htransfer⟩ := certificate_transfer (shuffleOpen D) p.word hc Y
  refine ⟨⟨r⟩,?_,hr⟩
  rw [pull_push]
  exact realizes_mono hrt (htransfer G hp)

theorem shuffleStar_internal_dense (D : ZFSet.{0})
    (hD : Dense {p : Conditions conditions | label conditions p ∈ D}) :
    Dense {p : Conditions conditions | label conditions p ∈ shuffleStar D} := by
  apply (dense_pull_iff _).mp
  have hd := (dense_pull_iff _).mpr hD
  have hl (p : Condition) : label conditions (conditionEquiv p) = wordCode p.word :=
    label_encodeCondition p
  simp only [Set.mem_ofPred_eq,hl] at hd ⊢
  exact shuffleStar_dense D hd

end TuringRigidity.InternalCohen

end OAI

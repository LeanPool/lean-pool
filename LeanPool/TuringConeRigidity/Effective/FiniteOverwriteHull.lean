/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteOverwriteHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GroundPrefixOverwrite

/-!
# Finite Overwrite Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FiniteOverwriteHull
open TransitiveNameModel BoundedSetTheory RealGeneratedModel FiniteOverwrite
open CountableForcing InternalCohen CohenBorelForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem contains_iff_of_degree (M N : ZFSet.{0}) (A B : Oracle)
    (he : degree A = degree B) : Contains M (realCode A) N ↔ Contains M (realCode B) N := by
  obtain ⟨hAB,hBA⟩ := (degree_eq_iff A B).mp he
  constructor
  · rintro ⟨hN,hT,hMN,hA⟩
    exact ⟨hN,hT,hMN,sourceT_real_lower N hN hT hA hBA⟩
  · rintro ⟨hN,hT,hMN,hB⟩
    exact ⟨hN,hT,hMN,sourceT_real_lower N hN hT hB hAB⟩

theorem hull_eq_of_degree (M : ZFSet.{0}) (A B : Oracle)
    (he : degree A = degree B) : RealGeneratedModel.hull M (realCode A) = RealGeneratedModel.hull
      M (realCode B) := by
  classical
  have hc := fun N => contains_iff_of_degree M N A B he
  by_cases hA : ∃ N, Contains M (realCode A) N
  · have hB : ∃ N, Contains M (realCode B) N :=
      ⟨hA.choose,(hc _).mp hA.choose_spec⟩
    apply ZFSet.ext
    intro z
    rw [mem_hull M _ z hA,mem_hull M _ z hB]
    exact ⟨fun h N hN => h N ((hc N).mpr hN),fun h N hN => h N ((hc N).mp hN)⟩
  · have hB : ¬ ∃ N, Contains M (realCode B) N := fun h =>
      hA ⟨h.choose,(hc _).mpr h.choose_spec⟩
    simp only [RealGeneratedModel.hull,dite_eq_right hA,dite_eq_right hB]

theorem overwrite_hull (M : ZFSet.{0}) (s : List Bool) (A : Oracle) :
    RealGeneratedModel.hull M (realCode (overwrite s A)) = RealGeneratedModel.hull M (realCode A) :=
  hull_eq_of_degree M _ _ (degree_overwrite s A)

theorem overwrite_extension (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A)))
    (s : List Bool) :
    genericExtensionSet M conditions (pushFilter (realFilter (overwrite s A))).carrier =
      genericExtensionSet M conditions (pushFilter (realFilter A)).carrier := by
  exact prefix_extension_eq_of_hull M hM hT _ _
    (GroundPrefixOverwrite.overwrite_generic M hM hT A hA s) hA (overwrite_hull M s A)

end TuringRigidity.FiniteOverwriteHull

end OAI

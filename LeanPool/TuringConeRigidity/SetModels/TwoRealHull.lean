/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/TwoRealHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.OriginalRealCohenFactorization
public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnRealName

/-!
# Two Real Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.TwoRealHull
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RealGeneratedModel CohenColumnRealName InternalCountableOrdinals
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem contains_join_iff (M : ZFSet.{0}) (X Y : Oracle)
    (hN : Contains M (realCode X) (RealGeneratedModel.hull M (realCode X))) (W : ZFSet.{0}) :
    Contains M (realCode (join X Y)) W ↔
      Contains (RealGeneratedModel.hull M (realCode X)) (realCode Y) W := by
  constructor
  · rintro ⟨hW,hTW,hMW,hXY⟩
    have hX := sourceT_real_lower W hW hTW hXY (reduces_join_left X Y)
    have hY := sourceT_real_lower W hW hTW hXY (reduces_join_right X Y)
    refine ⟨hW,hTW,?_,hY⟩
    intro z hz
    exact ((mem_hull M (realCode X) z ⟨_,hN⟩).mp hz) W ⟨hW,hTW,hMW,hX⟩
  · rintro ⟨hW,hTW,hNW,hY⟩
    exact ⟨hW,hTW,fun z hz => hNW (hN.2.2.1 hz),
      sourceT_real_join W hW hTW (hNW hN.2.2.2) hY⟩

theorem hull_join (M : ZFSet.{0}) (X Y : Oracle)
    (hN : Contains M (realCode X) (RealGeneratedModel.hull M (realCode X)))
    (hJ : Contains M (realCode (join X Y)) (RealGeneratedModel.hull M (realCode (join X Y)))) :
    RealGeneratedModel.hull (RealGeneratedModel.hull M (realCode X)) (realCode Y) =
      RealGeneratedModel.hull M (realCode (join X Y)) := by
  apply hull_eq_of_least _ _ _ ((contains_join_iff M X Y hN _).mp hJ)
  intro W hW z hz
  exact ((mem_hull M (realCode (join X Y)) z ⟨_,hJ⟩).mp hz) W
    ((contains_join_iff M X Y hN W).mpr hW)

theorem joined_factorization (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X Y : Oracle)
    (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) :
    let N := RealGeneratedModel.hull M (realCode X)
    let H := RealGeneratedModel.hull N (realCode Y)
    Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧
      ∃ U : GenericFilter (Conditions (poset K)), GroundGeneric H U ∧
        genericExtensionSet H (poset K) U.carrier = genericExtensionSet M (poset K) G.carrier := by
  dsimp only
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (CohenGroundPoset.conditions_mem M _ hM hT
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
        hK.2.1 (sourceT_omega_mem M hM hT))) G hG
  obtain ⟨hN,_,_,_⟩ := OriginalRealCohenFactorization.real_factorization M K hM hT hK
    G hG (realCode X) hX (realCode_subset X)
  obtain ⟨hJ,U,hU,hUE⟩ := OriginalRealCohenFactorization.real_factorization M K hM hT hK
    G hG (realCode (join X Y)) (sourceT_real_join _ hE hTE hX hY) (realCode_subset _)
  have hNJ := (contains_join_iff M X Y hN _).mp hJ
  have he := hull_join M X Y hN hJ
  rw [←he] at hNJ hU hUE
  exact ⟨hN,hNJ,U,hU,hUE⟩

end TuringRigidity.TwoRealHull

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GroundIteratedTriple.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticIteratedJoin
public import LeanPool.TuringConeRigidity.Representation.GroundArithmeticGeneric
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenValue
public import LeanPool.TuringConeRigidity.Representation.RealGeneratedModel
public import LeanPool.TuringConeRigidity.SetModels.RegularTreeExtension

/-!
# Ground Iterated Triple
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.GroundIteratedTriple
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open InternalCohen CohenBorelForcing UniformArithmetic
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem generic_triple_of_arithmetic (M : ZFSet.{0})
    (O : Oracles) (hO : ∀ i, realCode (O i) ∈ M)
    (Y L R : Oracle) (hY : ArithmeticPrefixForcing.Generic O Y)
    (hN : RealGeneratedModel.Contains M (realCode Y) (RealGeneratedModel.hull M (realCode Y)))
    (hL : GroundGeneric (RealGeneratedModel.hull M (realCode Y)) (pushFilter (realFilter L)))
    (hR : GroundGeneric (genericExtensionSet (RealGeneratedModel.hull M (realCode Y)) conditions
      (pushFilter (realFilter L)).carrier) (pushFilter (realFilter R))) :
    ArithmeticPrefixForcing.Generic O (join Y (join L R)) := by
  let N := RealGeneratedModel.hull M (realCode Y)
  let OY : Oracles := fun i => if i = 0 then Y else O (i - 1)
  have hOY : ∀ i, realCode (OY i) ∈ N := by
    intro i
    dsimp only [OY]
    split
    · exact hN.2.2.2
    · exact hN.2.2.1 (hO _)
  obtain ⟨hF,hTF,hNF,_⟩ := RegularTreeExtension.extension_properties N conditions hN.1 hN.2.1
    (conditions_mem N hN.1 hN.2.1) (pushFilter (realFilter L)) hL
  have hLF : realCode L ∈ genericExtensionSet N conditions (pushFilter (realFilter L)).carrier :=
    (mem_extensionSet _ _ _ _).mpr ⟨realName,realName_internal N hN.1 hN.2.1,val_realName L⟩
  have hOL : ∀ i, realCode ((fun i => if i = 0 then L else OY (i - 1)) i) ∈
      genericExtensionSet N conditions (pushFilter (realFilter L)).carrier := by
    intro i
    dsimp only
    split
    · exact hLF
    · exact hNF (hOY _)
  have hLa := GroundArithmeticGeneric.ground_arithmetic N hN.1 hN.2.1 OY hOY L hL
  have hRa := GroundArithmeticGeneric.ground_arithmetic _ hF hTF _ hOL R hR
  exact ArithmeticIteratedJoin.generic_join O Y (join L R) hY
    (ArithmeticIteratedJoin.generic_join OY L R hLa hRa)

theorem generic_triple (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (O : Oracles) (hO : ∀ i, realCode (O i) ∈ M)
    (Y L R : Oracle) (hY : GroundGeneric M (pushFilter (realFilter Y)))
    (hN : RealGeneratedModel.Contains M (realCode Y) (RealGeneratedModel.hull M (realCode Y)))
    (hL : GroundGeneric (RealGeneratedModel.hull M (realCode Y)) (pushFilter (realFilter L)))
    (hR : GroundGeneric (genericExtensionSet (RealGeneratedModel.hull M (realCode Y)) conditions
      (pushFilter (realFilter L)).carrier) (pushFilter (realFilter R))) :
    ArithmeticPrefixForcing.Generic O (join Y (join L R)) :=
  generic_triple_of_arithmetic M O hO Y L R
    (GroundArithmeticGeneric.ground_arithmetic M hM hT O hO Y hY) hN hL hR

theorem triple_join (Y L R : Oracle) : GenericTruth.triple (join Y (join L R)) = (Y,L,R) := by
  rw [GenericSourceTransfer.triple_join]
  have hl : PairGenericSelection.column false (join L R) = L := by
    funext n; simp [PairGenericSelection.column]
  have hr : PairGenericSelection.column true (join L R) = R := by
    funext n; simp [PairGenericSelection.column]
  rw [hl,hr]

end TuringRigidity.GroundIteratedTriple

end OAI

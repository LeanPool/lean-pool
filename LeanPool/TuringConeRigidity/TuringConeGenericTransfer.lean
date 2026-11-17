/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeGenericTransfer.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeSourceIdentity
public import LeanPool.TuringConeRigidity.Representation.RealHullPrescribedTruth

/-!
# Transferring inverse representation from columns to arithmetic generics

All three generic coordinates are chosen as in the original proof. The
minimal-pair calculation is instead made over A join Y, where A represents
the cone base and belongs to the parameter model. The arithmetic source
equation itself is unchanged, so its generic truth-transfer theorem is reused.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeGenericTransfer

open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals UniformArithmetic RelativeConstructible
open GenericIdentity ConeProgramGlobalization

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- The generic triple can satisfy the stronger common-lower-bound identity
over any fixed real already in the parameter model. -/
theorem exists_relative_prefix_triple (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X A : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hA : realCode A ∈ RealGeneratedModel.hull M (realCode X))
    (O : Oracles) (hO : ∀ i, realCode (O i) ∈ RealGeneratedModel.hull M (realCode X))
    (s : List Bool) : ∃ Y L R : Oracle,
      (∀ B ∈ ({Y, L, R} : Set Oracle),
        realCode B ∈ genericExtensionSet M (poset K) G.carrier ∧
        GroundGeneric (RealGeneratedModel.hull M (realCode X))
          (InternalCohen.pushFilter (CohenBorelForcing.realFilter B))) ∧
      GenericCoding.InfiniteOdd L ∧ GenericCoding.InfiniteOdd R ∧
      PrincipalIntersection (join A Y) (join (join A Y) L) (join (join A Y) R) ∧
      ArithmeticPrefixForcing.Generic O (join Y (join L R)) ∧
      ShuffleRequirements.Realizes s (join Y (join L R)) := by
  exact RealHullGenericTriple.exists_generic_prefix_triple_of_base M K hM hT hK G hG X hX
    (fun Y => join A Y)
    (fun _ H hH => sourceT_real_join H hH.1 hH.2.1 (hH.2.2.1 hA) hH.2.2.2) O hO s

/-- Correctness on all column realizations of one extension implies
correctness on its arithmetic-generic real inputs, not merely its columns. -/
theorem real_hull_prescribed_transfer {a : Degree} (e : Degree ≃o Set.Ici a)
    (M K i : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (hi : i ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X A : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hA : degree A = a) (hAN : realCode A ∈ RealGeneratedModel.hull M (realCode X))
    (p : OracleCode) (P : Oracle)
    (hP : realCode P ∈ RealGeneratedModel.hull M (realCode X))
    (hsem : ∀ H : GenericFilter (Conditions (poset K)),
      GroundGeneric (RealGeneratedModel.hull M (realCode X)) H →
      genericExtensionSet (RealGeneratedModel.hull M (realCode X)) (poset K) H.carrier =
        genericExtensionSet M (poset K) G.carrier →
      ∀ Y : Oracle, (realName K i).val H.carrier = realCode Y →
        RepresentsInverseAt e p P Y) :
    (∀ H : Oracle, ArithmeticPrefixForcing.Generic (fun _ => P) H →
      SourceEquation p P (GenericTruth.triple H)) ∧
    ∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
      ArithmeticPrefixForcing.Generic (fun _ => P) Y → RepresentsInverseAt e p P Y := by
  have h := real_hull_prescribed_transfer_of_source M K i hM hT hK hi G hG X hX p P hP
    (RepresentsInverseAt e p P) (fun Y => join A Y)
    (fun _ H hH => sourceT_real_join H hH.1 hH.2.1 (hH.2.2.1 hAN) hH.2.2.2)
    (fun Y L R => ConeSourceIdentity.source_equation_iff e p P A Y L R hA) hsem
  exact ⟨h.2.1,h.2.2.2⟩

end OAI.TuringRigidity.ConeGenericTransfer

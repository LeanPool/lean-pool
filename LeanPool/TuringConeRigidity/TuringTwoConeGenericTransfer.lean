/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeGenericTransfer.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeSourceIdentity
public import LeanPool.TuringConeRigidity.Representation.RealHullPrescribedTruth

/-!
# Transfer from Cohen columns to arithmetic-generic inputs

The general triple construction is reused with an oracle for the target base.
The two-cone source equation transports its relative principal intersection,
including ordinary lower bounds outside the source cone. Correctness is always
for the prescribed original map, not just an unspecified map in an extension.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeGenericTransfer

open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals UniformArithmetic RelativeConstructible
open GenericIdentity TwoConeProgramGlobalization

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Correctness on realizations of one Cohen column implies correctness on
all sufficiently arithmetic-generic inputs of the same extension. -/
theorem real_hull_prescribed_transfer {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (M K i : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (hi : i ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X B : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hB : degree B = b) (hBN : realCode B ∈ RealGeneratedModel.hull M (realCode X))
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
    (RepresentsInverseAt e p P) (fun Y => join B Y)
    (fun _ H hH => sourceT_real_join H hH.1 hH.2.1 (hH.2.2.1 hBN) hH.2.2.2)
    (fun Y L R => TwoConeSourceIdentity.source_equation_iff e p P B Y L R hB) hsem
  exact ⟨h.2.1,h.2.2.2⟩

end OAI.TuringRigidity.TwoConeGenericTransfer

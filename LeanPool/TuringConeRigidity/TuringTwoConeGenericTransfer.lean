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
public import LeanPool.TuringConeRigidity.TuringConeGenericTransfer

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
  let N := RealGeneratedModel.hull M (realCode X)
  have hrep : ∀ Y : Oracle,
      ColumnRealizesExtension N K i (genericExtensionSet M (poset K) G.carrier) Y →
      RepresentsInverseAt e p P Y := by
    rintro Y ⟨H, hH, he, hY⟩
    exact hsem H hH he Y hY
  have hordinary : ∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
      GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter Y)) →
      RepresentsInverseAt e p P Y := fun Y hYE hY => hrep Y
    (real_hull_generic_column_realizes M K i hM hT hK hi G hG X Y hX hYE hY)
  have hshuffle : ∀ Y L : Oracle,
      realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
      realCode L ∈ genericExtensionSet M (poset K) G.carrier →
      GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) →
      RepresentsInverseAt e p P (GenericCoding.code Y L) := fun Y L hYE hLE hL => hrep _
    (real_hull_shuffled_column_realizes M K i hM hT hK hi G hG X Y L hX hYE hLE hL)
  have hd : ∀ s : List Bool, ∃ H : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => P) H ∧
      ShuffleRequirements.Realizes s H ∧ SourceEquation p P (GenericTruth.triple H) := by
    intro s
    obtain ⟨Y, L, R, hbase, hL, hR, hI, hg, hs⟩ := ConeGenericTransfer.exists_relative_prefix_triple
      M K hM hT hK G hG X B hX hBN (fun _ => P) (fun _ => hP) s
    have hy := hbase Y (by simp)
    have hl := hbase L (by simp)
    have hr := hbase R (by simp)
    refine ⟨join Y (join L R), hg, hs, ?_⟩
    rw [GroundIteratedTriple.triple_join]
    exact (TwoConeSourceIdentity.source_equation_iff e p P B Y L R hB
      (hordinary L hl.1 hl.2) (hordinary R hr.1 hr.2)
      (hshuffle Y L hy.1 hl.1 hl.2) (hshuffle Y R hy.1 hr.1 hr.2) hL hR hI).mpr
        (hordinary Y hy.1 hy.2)
  have ht := ArithmeticSourceTruth.source_equation_of_dense p P hd
  refine ⟨ht, ?_⟩
  intro Y hYE hY
  obtain ⟨hN, hH, L, R, hLE, hRE, hL, hR⟩ :=
    RealHullIteration.exists_iterated_pair M K hM hT hK G hG X Y hX hYE
  let H := RealGeneratedModel.hull N (realCode Y)
  obtain ⟨_, _, hHF, _⟩ := RegularTreeExtension.extension_properties H InternalCohen.conditions
    hH.1 hH.2.1 (InternalCohen.conditions_mem H hH.1 hH.2.1)
    (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) hL
  have hLN : GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) :=
    fun D hD hd => hL D (hH.2.2.1 hD) hd
  have hRN : GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) :=
    fun D hD hd => hR D (hHF (hH.2.2.1 hD)) hd
  have hBY : join B Y ∈ modelReals H :=
    sourceT_real_join H hH.1 hH.2.1 (hH.2.2.1 hBN) hH.2.2.2
  have hI := IteratedGenericCommonIdeal.ideal_of_iterated_generics H hH.1 hH.2.1
    (join B Y) hBY L R hL hR
  have heq := ht (join Y (join L R))
    (GroundIteratedTriple.generic_triple_of_arithmetic N (fun _ => P) (fun _ => hP)
      Y L R hY hH hL hR)
  rw [GroundIteratedTriple.triple_join] at heq
  exact (TwoConeSourceIdentity.source_equation_iff e p P B Y L R hB
    (hordinary L hLE hLN) (hordinary R hRE hRN)
    (hshuffle Y L hYE hLE hLN) (hshuffle Y R hYE hRE hRN)
    (InternalCohen.groundGeneric_infiniteOdd N hN.1 hN.2.1 L hLN)
    (InternalCohen.groundGeneric_infiniteOdd N hN.1 hN.2.1 R hRN) hI).mp heq

end OAI.TuringRigidity.TwoConeGenericTransfer

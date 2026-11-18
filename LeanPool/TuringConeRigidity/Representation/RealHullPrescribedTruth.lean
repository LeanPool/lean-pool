/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/RealHullPrescribedTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
The source-parametric proof also shares upstream RequestProject/TuringConeGenericTransfer.lean
and TuringTwoConeGenericTransfer.lean (Bjørn Kjos-Hanssen, Apache-2.0).
-/

module

public import LeanPool.TuringConeRigidity.Representation.RealHullGenericTriple
public import LeanPool.TuringConeRigidity.Representation.RealHullColumnRealization
public import LeanPool.TuringConeRigidity.Computability.ArithmeticFiniteTruthTransfer

/-!
# Real Hull Prescribed Truth
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals GenericIdentity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Transfer any represented predicate whose source identity holds at its chosen hull base. -/
theorem real_hull_prescribed_transfer_of_source (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (p : OracleCode) (P : Oracle)
    (hP : realCode P ∈ RealGeneratedModel.hull M (realCode X))
    (Rep : Oracle → Prop)
    (F : Oracle → Oracle)
    (hF : ∀ (Y : Oracle) (H : ZFSet.{0}),
      RealGeneratedModel.Contains (RealGeneratedModel.hull M (realCode X)) (realCode Y) H →
      F Y ∈ modelReals H)
    (hsource : ∀ Y L R : Oracle,
      Rep L → Rep R → Rep (GenericCoding.code Y L) → Rep (GenericCoding.code Y R) →
      GenericCoding.InfiniteOdd L → GenericCoding.InfiniteOdd R →
      PrincipalIntersection (F Y) (join (F Y) L) (join (F Y) R) →
      (SourceEquation p P (Y,L,R) ↔ Rep Y))
    (hsem : ∀ H : GenericFilter (Conditions (poset K)),
      GroundGeneric (RealGeneratedModel.hull M (realCode X)) H →
      genericExtensionSet (RealGeneratedModel.hull M (realCode X)) (poset K) H.carrier =
        genericExtensionSet M (poset K) G.carrier →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → Rep A) :
    (∀ s : List Bool, ∃ H : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => P) H ∧
      ShuffleRequirements.Realizes s H ∧ SourceEquation p P (GenericTruth.triple H)) ∧
    (∀ H : Oracle, ArithmeticPrefixForcing.Generic (fun _ => P) H →
      SourceEquation p P (GenericTruth.triple H)) ∧
    (∃ D : ArithmeticPrefixForcing.PrefixPredicate, ArithmeticPrefixForcing.ArithmeticPrefix D ∧
      (∀ n, FiniteShuffle.DenseOpen (D (fun _ => P) n)) ∧
      ∀ H : Oracle, ShuffleRequirements.GenericFor (D (fun _ => P)) H →
        SourceEquation p P (GenericTruth.triple H)) ∧
    ∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
      ArithmeticPrefixForcing.Generic (fun _ => P) Y → Rep Y := by
  let N := RealGeneratedModel.hull M (realCode X)
  have hrep : ∀ A : Oracle,
      ColumnRealizesExtension N K a (genericExtensionSet M (poset K) G.carrier) A →
      Rep A := by
    rintro A ⟨H,hH,he,hA⟩
    exact hsem H hH he A hA
  have hordinary : ∀ A : Oracle, realCode A ∈ genericExtensionSet M (poset K) G.carrier →
      GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter A)) →
      Rep A := fun A hAE hA => hrep A
    (real_hull_generic_column_realizes M K a hM hT hK ha G hG X A hX hAE hA)
  have hshuffle : ∀ Y L : Oracle,
      realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
      realCode L ∈ genericExtensionSet M (poset K) G.carrier →
      GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) →
      Rep (GenericCoding.code Y L) := fun Y L hYE hLE hL => hrep _
    (real_hull_shuffled_column_realizes M K a hM hT hK ha G hG X Y L hX hYE hLE hL)
  have hd : ∀ s : List Bool, ∃ H : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => P) H ∧
      ShuffleRequirements.Realizes s H ∧ SourceEquation p P (GenericTruth.triple H) := by
    intro s
    obtain ⟨Y,L,R,hbase,hL,hR,hi,hg,hs⟩ :=
      RealHullGenericTriple.exists_generic_prefix_triple_of_base
      M K hM hT hK G hG X hX F hF (fun _ => P) (fun _ => hP) s
    have hy := hbase Y (by simp)
    have hl := hbase L (by simp)
    have hr := hbase R (by simp)
    refine ⟨join Y (join L R),hg,hs,?_⟩
    rw [GroundIteratedTriple.triple_join]
    exact (hsource Y L R (hordinary L hl.1 hl.2) (hordinary R hr.1 hr.2)
      (hshuffle Y L hy.1 hl.1 hl.2) (hshuffle Y R hy.1 hr.1 hr.2) hL hR hi).mpr
        (hordinary Y hy.1 hy.2)
  have ht := ArithmeticSourceTruth.source_equation_of_dense p P hd
  refine ⟨hd,ht,ArithmeticFiniteTruthTransfer.source_equation_finite_family p P hd,?_⟩
  intro Y hYE hY
  obtain ⟨hN,hH,L,R,hLE,hRE,hL,hR⟩ :=
    RealHullIteration.exists_iterated_pair M K hM hT hK G hG X Y hX hYE
  let H := RealGeneratedModel.hull N (realCode Y)
  obtain ⟨_,_,hHF,_⟩ := RegularTreeExtension.extension_properties H InternalCohen.conditions
    hH.1 hH.2.1 (InternalCohen.conditions_mem H hH.1 hH.2.1)
    (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) hL
  have hLN : GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) :=
    fun D hD hd => hL D (hH.2.2.1 hD) hd
  have hRN : GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) :=
    fun D hD hd => hR D (hHF (hH.2.2.1 hD)) hd
  have hi := IteratedGenericCommonIdeal.ideal_of_iterated_generics H hH.1 hH.2.1
    (F Y) (hF Y H hH) L R hL hR
  have heq := ht (join Y (join L R))
    (GroundIteratedTriple.generic_triple_of_arithmetic N (fun _ => P) (fun _ => hP)
      Y L R hY hH hL hR)
  rw [GroundIteratedTriple.triple_join] at heq
  exact (hsource Y L R (hordinary L hLE hLN) (hordinary R hRE hRN)
    (hshuffle Y L hYE hLE hLN) (hshuffle Y R hYE hRE hRN)
    (InternalCohen.groundGeneric_infiniteOdd N hN.1 hN.2.1 L hLN)
    (InternalCohen.groundGeneric_infiniteOdd N hN.1 hN.2.1 R hRN) hi).mp heq

theorem real_hull_prescribed_transfer (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (π : Degree ≃o Degree) (p : OracleCode) (P : Oracle)
    (hP : realCode P ∈ RealGeneratedModel.hull M (realCode X))
    (hsem : ∀ H : GenericFilter (Conditions (poset K)),
      GroundGeneric (RealGeneratedModel.hull M (realCode X)) H →
      genericExtensionSet (RealGeneratedModel.hull M (realCode X)) (poset K) H.carrier =
        genericExtensionSet M (poset K) G.carrier →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → RepresentsAt π p P A) :
    (∀ s : List Bool, ∃ H : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => P) H ∧
      ShuffleRequirements.Realizes s H ∧ SourceEquation p P (GenericTruth.triple H)) ∧
    (∀ H : Oracle, ArithmeticPrefixForcing.Generic (fun _ => P) H →
      SourceEquation p P (GenericTruth.triple H)) ∧
    (∃ D : ArithmeticPrefixForcing.PrefixPredicate, ArithmeticPrefixForcing.ArithmeticPrefix D ∧
      (∀ n, FiniteShuffle.DenseOpen (D (fun _ => P) n)) ∧
      ∀ H : Oracle, ShuffleRequirements.GenericFor (D (fun _ => P)) H →
        SourceEquation p P (GenericTruth.triple H)) ∧
    ∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
      ArithmeticPrefixForcing.Generic (fun _ => P) Y → RepresentsAt π p P Y := by
  exact real_hull_prescribed_transfer_of_source M K a hM hT hK ha G hG X hX p P hP
    (RepresentsAt π p P) id (fun _ _ hH => hH.2.2.2)
    (fun Y L R => source_5_5_iff π p P Y L R) hsem
end TuringRigidity.RelativeConstructible

end OAI

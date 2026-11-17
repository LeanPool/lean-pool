/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericFiberIdeal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GenericFactor
public import LeanPool.TuringConeRigidity.Representation.CommonIdealSelection

/-!
# Generic Fiber Ideal
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericFactor
open FiniteShuffle ShuffleRequirements PairGenericSelection Set

def IdealFiber (D : ℕ → List Bool → Prop)
    (Y : {Y : Oracle // GenericFor (FirstFamily D) Y}) (n t : ℕ) : Prop :=
  if n % 2 = 0 then CommonIdeal.family Y.val (n/2) t
  else Fiber D Y.val (n/2) (BorelGeneric.word t)

theorem idealFiber_dense (D : ℕ → List Bool → Prop)
    (Y : {Y : Oracle // GenericFor (FirstFamily D) Y}) (n s : ℕ) :
    ∃ t, BorelGeneric.Ext s t ∧ IdealFiber D Y n t := by
  unfold IdealFiber
  split
  · exact CommonIdeal.family_dense Y.val _ s
  · exact coded_dense _ (fiber_denseOpen D Y.val Y.property _) s

theorem idealFiber_measurable (D : ℕ → List Bool → Prop) (n t : ℕ) :
    MeasurableSet {Y | IdealFiber D Y n t} := by
  unfold IdealFiber
  split
  · exact (CommonIdeal.family_measurable _ _).preimage measurable_subtype_coe
  · exact (fiber_isOpen D _ _).measurableSet.preimage measurable_subtype_coe

theorem borel_joint_ideal_selection (D E : ℕ → List Bool → Prop)
    (hD : ∀ n, DenseOpen (D n)) (hE : ∀ n, DenseOpen (E n)) :
    (∀ n, DenseOpen (FirstFamily D n)) ∧
    ∃ Z : {Y : Oracle // GenericFor (FirstFamily D) Y} → Oracle, Measurable Z ∧
      (∀ Y, GenericFor D (join Y.val (Z Y))) ∧
      (∀ Y b, GenericFor E (column b (Z Y)) ∧ GenericCoding.InfiniteOdd (column b (Z Y)) ∧
        ∀ X, GenericFor E (GenericCoding.code X (column b (Z Y)))) ∧
      ∀ Y a, a ≤ degree Y.val ↔
        a ≤ degree (join Y.val (column false (Z Y))) ∧
        a ≤ degree (join Y.val (column true (Z Y))) := by
  obtain ⟨Z,hZ,hgen,hR⟩ := borel_pair_selection E hE (IdealFiber D)
    (idealFiber_dense D) (idealFiber_measurable D)
  refine ⟨firstFamily_denseOpen D hD,Z,hZ,?_,hgen,?_⟩
  · intro Y
    apply join_generic
    intro n
    obtain ⟨t,ht,hZt⟩ := hR Y (2*n+1)
    refine ⟨BorelGeneric.word t,?_,(realizes_iff_meets _ _).mpr hZt⟩
    simpa [IdealFiber,Nat.add_div] using ht
  · intro Y a
    apply CommonIdeal.ideal_of_family Y.val (Z Y) _ a
    intro n
    obtain ⟨t,ht,hZt⟩ := hR Y (2*n)
    exact ⟨t,by simpa [IdealFiber] using ht,hZt⟩

end TuringRigidity.GenericFactor

end OAI

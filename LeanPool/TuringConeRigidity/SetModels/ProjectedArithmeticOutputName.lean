/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ProjectedArithmeticOutputName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenProjectedNameLift
public import LeanPool.TuringConeRigidity.SetModels.ExtensionArithmeticRepresentative
public import LeanPool.TuringConeRigidity.Representation.SourceTTreeAbsoluteness
public import LeanPool.TuringConeRigidity.SetModels.SetModelJoin

/-!
# Projected Arithmetic Output Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ProjectedArithmeticOutputName
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open PersistentRestrictions ExtensionArithmeticRepresentative OracleJump
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem representative_in_model (N : ZFSet.{0}) (hN : Transitive N) (hTN : SourceT N)
    (I J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
    (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (A R : Oracle) (hA : degree A ∈ J.carrier)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero), hz⟩).val)
    (hAN : A ∈ modelReals N) (hRN : R ∈ modelReals N) :
    ∃ X : Oracle, X ∈ modelReals N ∧ degree X = (σ ⟨degree A,hA⟩).val ∧
      Reduces X (iterate (join A R) 5) ∧ ∃ e : OracleCode,
        OracleCode.eval (oracleFunction (iterate (join A R) 5)) e = oracleFunction X := by
  obtain ⟨X,hX,hred,hcode⟩ := extension_literal_join_program I J hIJ ρ σ he hz A R hA hR
  have hj : join A R ∈ SetModelReals.reals N := SetModelArithmetic.join_mem N hN
    hTN.pairing hTN.union hTN.powerSet hTN.separation.finitePrefix.bounded hTN.infinity hAN hRN
  have hi (n : ℕ) : iterate (join A R) n ∈ SetModelReals.reals N := by
    induction n with
    | zero => exact hj
    | succ n ih => exact SetModelSyntax.jump_mem (ArithmeticTree.sourceContext N hN hTN) ih
  exact ⟨X,SetModelSyntax.lower_mem (ArithmeticTree.sourceContext N hN hTN) (hi 5) hred,
    hX,hred,hcode⟩

theorem projected_output_name (M C B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (I J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
    (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (A R : Oracle) (hA : degree A ∈ J.carrier)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero), hz⟩).val)
    (hAN : A ∈ modelReals (genericExtensionSet M (conditions B) (projected C B hBC G).carrier))
    (hRN : R ∈ modelReals (genericExtensionSet M (conditions B) (projected C B hBC G).carrier)) :
    ∃ X : Oracle, degree X = (σ ⟨degree A,hA⟩).val ∧
      Reduces X (iterate (join A R) 5) ∧
      (∃ e : OracleCode, OracleCode.eval (oracleFunction (iterate (join A R) 5)) e =
        oracleFunction X) ∧
      ∃ y : Name (Conditions (conditions C)), y.encode (label (conditions C)) ∈ M ∧
        y.val G.carrier = realCode X ∧
        ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
          (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
          ∀ H : GenericFilter (Conditions (conditions C)),
            y.val (AutomorphismName.mapFilter a H).carrier = y.val H.carrier := by
  let H := projected C B hBC G
  let N := genericExtensionSet M (conditions B) H.carrier
  have hH : GroundGeneric M H := projected_groundGeneric M C B hM hT hC hB hBC G hG
  have hc := conditions_mem M B hM hT hB
  have hN := genericExtensionSet_transitive M (conditions B) hM H.carrier
  obtain ⟨p,hp⟩ := H.nonempty
  have hTN := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair _) H hH (H.upper le_top hp)
  obtain ⟨X,hXN,hX,hred,hcode⟩ :=
    representative_in_model N hN hTN I J hIJ ρ σ he hz A R hA hR hAN hRN
  have hxN : realCode X ∈ (N : Set ZFSet.{0}) := hXN
  rw [genericExtensionSet_coe] at hxN
  obtain ⟨τ,hτ,hτv⟩ := hxN
  obtain ⟨y,hy,hyv,hinv⟩ := CohenProjectedNameLift.lift_projected_real_name M C B
    hM hT hC hB hBC τ hτ
  refine ⟨X,hX,hred,hcode,y,hy,?_,hinv⟩
  exact (hyv G hG (by rw [hτv]; exact realCode_subset X)).trans hτv

end TuringRigidity.ProjectedArithmeticOutputName

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelPersistence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelGraphImage
public import LeanPool.TuringConeRigidity.SetModels.SetDegreeDecoding
public import LeanPool.TuringConeRigidity.Constructibility.PersistenceRealClosure

/-!
# Set Model Persistence
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelPersistence
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding SetModelReals
open SetDegreeDecoding SetModelSequences SetModelColumns EncodedForcing
open PersistentRestrictions PersistentPresentation PersistentCountability
universe u
noncomputable section

theorem graphImage_action {I : CountableIdeal} {A G : Oracle}
    (hA : Presented I A) (ρ : I ≃o I) (hG : ∀ v, G v = true ↔ Graph ρ hA v)
    (n m : ℕ) :
    ZFSet.pair (realSet.{u} (columns A n)) (realSet (columns A m)) ∈ graphImage A G ↔
      (ρ (entry hA n)).val = degree (columns A m) := by
  rw [mem_graphImage]
  constructor
  · rintro ⟨i,j,hGij,hpair⟩
    obtain ⟨hi,hj⟩ := ZFSet.pair_inj.mp hpair
    have hi' := realSet_injective hi
    have hj' := realSet_injective hj
    have he : entry hA n = entry hA i := Subtype.ext (congrArg degree hi')
    have hh := (hG (Nat.pair i j)).mp hGij
    simpa only [PersistentPresentation.Graph,Nat.unpair_pair,he,hj'] using hh
  · intro h
    refine ⟨n,m,(hG _).mpr ?_,rfl⟩
    simpa only [PersistentPresentation.Graph,Nat.unpair_pair] using h

theorem persistent_decoding (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hC : PersistenceRealClosure.Closed (reals M))
    {p E : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p) (hEM : E ∈ M)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    idealSet I ∈ M ∧ automorphismSet ρ ∈ M := by
  obtain ⟨r,hr,hrdef⟩ := internal_reals M hM hPow hS hI
  have hcols : ∀ n, columns A n ∈ reals M :=
    fun n => hC.lower hAM (CodingExtraction.column_projection_reduces A n)
  have hseq := columns_mem M hM hP hU hPow hS hI hC.lower hp hpdef hAM
  have ha := columnRange_mem M hM hPow hS hI hcols hseq
  have hi := quotient_mem M hM hPow hS hr hEM ha
  have hieq := quotient_eq_idealSet M hC.lower hrdef hE hA (mem_columnRange A) hcols
  refine ⟨hieq ▸ hi,?_⟩
  let G := graphOracle hA ρ
  have hGM : G ∈ reals M := PersistenceRealClosure.graph_mem hC hA hAM ρ hρ hz
  have hG : ∀ v, G v = true ↔ Graph ρ hA v := fun v => by simp [G,graphOracle]
  have hR := graphImage_mem M hM hP hU hPow hS hI hp hpdef hseq ha hGM
  have hm := action_mem M hM hP hU hPow hS hr hEM ha hR
  have heq := action_eq_automorphismSet M hC.lower hrdef hE hA ρ
    (mem_columnRange A) hcols (graphImage_action hA ρ hG)
  exact heq ▸ hm

theorem persistent_extension_sets (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hC : PersistenceRealClosure.Closed (reals M))
    {p E : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p) (hEM : E ∈ M)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : J ≃o J) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ Extends hIJ ρ σ ∧ Persistent J σ ∧
      idealSet J ∈ M ∧ automorphismSet σ ∈ M := by
  let B := join A X
  let J := JumpIdeal.generated (degree B)
  let H := JumpIdealPresentation.presentation B
  have hH : Presented J H := JumpIdealPresentation.presents B
  have hHM : H ∈ reals M := hC.presentation (hC.join hAM hX)
  have hIJ : I.carrier ⊆ J.carrier := by
    intro y hy
    obtain ⟨n,rfl⟩ := (hA y).mp hy
    exact J.lower ((CodingExtraction.column_projection_reduces A n).trans
      (reduces_join_left A X)) (JumpIdeal.includes _)
  have hXJ : degree X ∈ J.carrier := J.lower (reduces_join_right A X) (JumpIdeal.includes _)
  obtain ⟨σ,he,hσ⟩ := PersistentExtension.source_4_1_10 I J ρ hρ hz hIJ (JumpIdeal.closed _)
  have hsets := persistent_decoding M hM hP hU hPow hS hI hC hp hpdef hEM hE
    hH hHM σ hσ (hIJ hz)
  exact ⟨J,σ,hIJ,hXJ,he,hσ,hsets⟩

end
end TuringRigidity.SetModelPersistence

end OAI

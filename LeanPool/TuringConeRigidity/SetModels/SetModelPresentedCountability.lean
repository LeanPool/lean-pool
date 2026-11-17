/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelPresentedCountability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelCountablePresentation

/-!
# Set Model Presented Countability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelArithmetic
open SetPresentationDecoding SetDegreeDecoding SetModelSequences SetModelColumns SetModelSyntax
open PersistentRestrictions PersistentPresentation EncodedForcing
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem ideal_mem_of_presentation (C : Context M) {I : CountableIdeal} {A : Oracle}
    (hA : Presented I A) (hAM : A ∈ reals M) : idealSet I ∈ M := by
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  have hcols : ∀ n, columns A n ∈ reals M :=
    fun n => lower_mem C hAM (CodingExtraction.column_projection_reduces A n)
  have hs := columns_mem M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) C.pairing_mem pairingSet_code hAM
  have ha := columnRange_mem M C.transitive C.power C.separation C.infinity hcols hs
  have hi := quotient_mem M C.transitive C.power C.separation hr hE ha
  have he := quotient_eq_idealSet M (lower_mem C) hrc hEc hA (mem_columnRange A) hcols
  exact he ▸ hi

def degreeSequence (A : Oracle) : ZFSet.{u} :=
  ZFSet.range (fun n : ℕ => ZFSet.pair (natSet n) (degreeSet (degree (columns A n))))

@[simp] theorem mem_degreeSequence (A : Oracle) (z : ZFSet.{u}) :
    z ∈ degreeSequence A ↔ ∃ n, z = ZFSet.pair (natSet n) (degreeSet (degree (columns A n))) := by
  rw [degreeSequence,ZFSet.mem_range]
  exact exists_congr (fun n => eq_comm)

@[simp] theorem pair_mem_degreeSequence (A : Oracle) (n : ℕ) (x : ZFSet.{u}) :
    ZFSet.pair (natSet n) x ∈ degreeSequence A ↔ x = degreeSet (degree (columns A n)) := by
  rw [mem_degreeSequence]
  constructor
  · rintro ⟨m,he⟩
    obtain ⟨hn,hx⟩ := ZFSet.pair_inj.mp he
    exact natSet_injective hn ▸ hx
  · intro h
    exact ⟨n,by rw [h]⟩

def degreeSequenceFormula : Formula :=
  .existsMem 1 (.existsMem 3 (.existsMem 6
    (.conj (.orderedPair 3 2 0) (.conj (.pairMem 2 1 6) (classFormula 0 1 5 8)))))

theorem degreeSequence_mem (C : Context M) {I : CountableIdeal} {A : Oracle}
    (hA : Presented I A) (hAM : A ∈ reals M) : degreeSequence.{u} A ∈ M := by
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  have hcols : ∀ n, columns A n ∈ reals M :=
    fun n => lower_mem C hAM (CodingExtraction.column_projection_reduces A n)
  have hs := columns_mem M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) C.pairing_mem pairingSet_code hAM
  have hi := ideal_mem_of_presentation C hA hAM
  let e := cons ZFSet.omega (cons r (cons (sequenceSet (columns A)) (cons (idealSet I) (fun _ =>
    E))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp [e,C.omega_mem,hr,hs,hi,hE]
  have hp := sep_mem M C.transitive C.separation degreeSequenceFormula e he
    (C.prod_mem C.omega_mem hi)
  have eq : ZFSet.sep (fun z => degreeSequenceFormula.Eval (cons z e))
      (ZFSet.prod ZFSet.omega (idealSet I)) = degreeSequence A := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,degreeSequenceFormula,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_pairMem,eval_classFormula,cons_zero,cons_succ,e,mem_degreeSequence]
    constructor
    · rintro ⟨_,n,hn,x,hx,c,hc,hz,hnx,hcx⟩
      obtain ⟨k,rfl⟩ := (mem_omega n).mp hn
      have hx' := (pair_mem_sequenceSet _ _ _).mp hnx
      have hc' : c = degreeSet (degree (columns A k)) := by
        rw [hcx,hx']
        exact class_eq_degreeSet M (lower_mem C) hrc hEc (hcols k)
      exact ⟨k,by rw [hz,hc']⟩
    · rintro ⟨n,rfl⟩
      have hn : natSet.{u} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
      have hdn : degreeSet (degree (columns A n)) ∈ idealSet I :=
        (mem_idealSet I _).mpr ⟨_,(hA _).mpr ⟨n,rfl⟩,rfl⟩
      refine ⟨ZFSet.pair_mem_prod.mpr ⟨hn,hdn⟩,natSet n,hn,realSet (columns A n),
        (hrc _).mpr ⟨_,hcols n,rfl⟩,_,hdn,rfl,(pair_mem_sequenceSet _ _ _).mpr rfl,?_⟩
      exact (class_eq_degreeSet M (lower_mem C) hrc hEc (hcols n)).symm
  exact eq ▸ hp

theorem countable_of_presentation (C : Context M) {I : CountableIdeal} {A : Oracle}
    (hA : Presented I A) (hAM : A ∈ reals M) : InternallyCountable M (idealSet I) := by
  have hs := degreeSequence_mem C hA hAM
  have hi := ideal_mem_of_presentation C hA hAM
  let e := cons (degreeSequence A) (cons ZFSet.omega (fun _ => idealSet I))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,hs,C.omega_mem,hi]
  refine ⟨degreeSequence A,hs,((ontoFormula 0 1 2).absolute M C.transitive e he).mpr ?_⟩
  rw [eval_ontoFormula]
  change FunctionGraph (degreeSequence A) ZFSet.omega (idealSet I) ∧ _
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨n,rfl⟩ := (mem_degreeSequence A z).mp hz
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,_,
      (mem_idealSet I _).mpr ⟨_,(hA _).mpr ⟨n,rfl⟩,rfl⟩,rfl⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    refine ⟨_,(mem_idealSet I _).mpr ⟨_,(hA _).mpr ⟨n,rfl⟩,rfl⟩,
      (pair_mem_degreeSequence _ _ _).mpr rfl,?_⟩
    intro z hz hnz
    exact (pair_mem_degreeSequence _ _ _).mp hnz
  · intro y hy
    obtain ⟨a,ha,rfl⟩ := (mem_idealSet I y).mp hy
    obtain ⟨n,hn⟩ := (hA a).mp ha
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,(pair_mem_degreeSequence _ _ _).mpr
      (congrArg degreeSet hn.symm)⟩

end
end TuringRigidity.SetModelCountability

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelIdealInterpretation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelDegreeOrder
public import LeanPool.TuringConeRigidity.SetModels.CountableSetReal
public import LeanPool.TuringConeRigidity.SetModels.PresentedDegreeEmbedding

/-!
# Model Ideal Interpretation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing PersistentRestrictions PersistentPresentation
universe u

def SetIdeal (U L I : ZFSet.{u}) : Prop := I ⊆ U ∧ (∃ D, D ∈ I) ∧
  (∀ D ∈ U, ∀ E ∈ I, ZFSet.pair D E ∈ L → D ∈ I) ∧
  (∀ D ∈ I, ∀ E ∈ I, ∃ F ∈ I, ZFSet.pair D F ∈ L ∧ ZFSet.pair E F ∈ L)

theorem degreeCode_mem_presentationSet (R : ZFSet.{u}) (H : Oracle)
    (hc : ∀ n, realCode (columns H n) ∈ R) (A : Oracle) :
    degreeCode R A ∈ presentationSet R H ↔ ∃ n, degree (columns H n) = degree A := by
  rw [mem_presentationSet]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,(degreeCode_equal R (hc n)).mp hn.symm⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,((degreeCode_equal R (hc n)).mpr hn).symm⟩

theorem presentationSet_ideal (R : ZFSet.{u}) {J : CountableIdeal} {H : Oracle}
    (hH : Presented J H) (hc : ∀ n, realCode (columns H n) ∈ R) :
    SetIdeal (degreeUniverse R) (degreeOrder R) (presentationSet R H) := by
  have hmem (A : Oracle) : degreeCode R A ∈ presentationSet R H ↔ degree A ∈ J.carrier :=
    (degreeCode_mem_presentationSet R H hc A).trans (hH (degree A)).symm
  refine ⟨?_,⟨degreeCode R (columns H 0),(mem_presentationSet _ _ _).mpr ⟨0,rfl⟩⟩,?_,?_⟩
  · intro D hD
    obtain ⟨n,rfl⟩ := (mem_presentationSet R H D).mp hD
    exact (mem_degreeUniverse _ _).mpr ⟨columns H n,hc n,rfl⟩
  · intro D hD E hE hle
    obtain ⟨A,hA,rfl⟩ := (mem_degreeUniverse R D).mp hD
    obtain ⟨n,rfl⟩ := (mem_presentationSet R H E).mp hE
    exact (hmem A).mpr (J.lower ((degreeOrder_actual R hA (hc n)).mp hle) (entry hH n).property)
  · intro D hD E hE
    obtain ⟨n,rfl⟩ := (mem_presentationSet R H D).mp hD
    obtain ⟨m,rfl⟩ := (mem_presentationSet R H E).mp hE
    obtain ⟨k,hk⟩ := (hH _).mp (J.join_mem (entry hH n).property (entry hH m).property)
    refine ⟨degreeCode R (columns H k),(mem_presentationSet _ _ _).mpr ⟨k,rfl⟩,?_,?_⟩
    · apply (degreeOrder_actual R (hc n) (hc k)).mpr
      rw [hk]; exact le_sup_left
    · apply (degreeOrder_actual R (hc m) (hc k)).mpr
      rw [hk]; exact le_sup_right

theorem sourceT_countable_ideal_presentation (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M)
    (hRd : ∀ w ∈ R, ∃ A : Oracle, realCode A = w)
    {I : ZFSet.{u}} (hIM : I ∈ M)
    (hI : SetIdeal (degreeUniverse R) (degreeOrder R) I) (hcount : InternallyCountable M I) :
    ∃ J : CountableIdeal, ∃ H ∈ modelReals M, Presented J H ∧ presentationSet R H = I := by
  obtain ⟨H,hHM,hHI⟩ := internal_countable_degree_presentation M hM hT R hRd hIM hI.1 hcount
  have hc : ∀ n, realCode (columns H n) ∈ R :=
    fun n => (hR _).mpr (sourceT_real_column M hM hT hHM n)
  let C : Set Degree := Set.range (fun n => degree (columns H n))
  have hmem (A : Oracle) : degreeCode R A ∈ I ↔ degree A ∈ C := by
    rw [←hHI,degreeCode_mem_presentationSet R H hc]
    rfl
  have hlower : ∀ {a b : Degree}, a ≤ b → b ∈ C → a ∈ C := by
    intro a b hab hb
    obtain ⟨n,rfl⟩ := hb
    obtain ⟨A,rfl⟩ := degree_surjective a
    have hA : realCode A ∈ R := (hR A).mpr
      (sourceT_real_lower M hM hT (sourceT_real_column M hM hT hHM n) hab)
    exact (hmem A).mp (hI.2.2.1 (degreeCode R A) ((mem_degreeUniverse _ _).mpr ⟨A,hA,rfl⟩)
      (degreeCode R (columns H n)) ((hmem _).mpr ⟨n,rfl⟩)
      ((degreeOrder_actual R hA (hc n)).mpr hab))
  have hjoin : ∀ {a b : Degree}, a ∈ C → b ∈ C → a ⊔ b ∈ C := by
    intro a b ha hb
    obtain ⟨n,rfl⟩ := ha
    obtain ⟨m,rfl⟩ := hb
    obtain ⟨D,hD,hn,hm⟩ := hI.2.2.2 _ ((hmem _).mpr ⟨n,rfl⟩) _ ((hmem _).mpr ⟨m,rfl⟩)
    obtain ⟨k,hk⟩ := (mem_presentationSet R H D).mp (hHI.symm ▸ hD)
    rw [hk] at hn hm
    exact hlower (sup_le ((degreeOrder_actual R (hc n) (hc k)).mp hn)
      ((degreeOrder_actual R (hc m) (hc k)).mp hm)) ⟨k,rfl⟩
  let J : CountableIdeal := ⟨C,⟨degree (columns H 0),0,rfl⟩,Set.countable_range _,@hlower,@hjoin⟩
  exact ⟨J,H,hHM,fun _ => Iff.rfl,hHI⟩

theorem presentedDegreeCode_order (R : ZFSet.{u}) {J : CountableIdeal} {H : Oracle}
    (hH : Presented J H) (hc : ∀ n, realCode (columns H n) ∈ R) (x y : J) :
    ZFSet.pair (presentedDegreeCode R hH x) (presentedDegreeCode R hH y) ∈ degreeOrder R ↔ x ≤ y
      := by
  unfold presentedDegreeCode
  rw [degreeOrder_actual R (hc _) (hc _)]
  rw [Classical.choose_spec ((hH x.val).mp x.property),Classical.choose_spec ((hH y.val).mp
    y.property)]
  rfl

end TuringRigidity.BoundedSetTheory

end OAI

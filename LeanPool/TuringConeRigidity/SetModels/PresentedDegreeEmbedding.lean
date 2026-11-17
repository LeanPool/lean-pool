/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/PresentedDegreeEmbedding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.PresentationGraphSet
public import LeanPool.TuringConeRigidity.Constructibility.PersistentPresentation

/-!
# Presented Degree Embedding
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open EncodedForcing PersistentRestrictions PersistentPresentation
universe u

noncomputable def presentedDegreeCode (R : ZFSet.{u}) {I : CountableIdeal} {H : Oracle}
    (hH : Presented I H) (x : I) : ZFSet.{u} :=
  degreeCode R (columns H (Classical.choose ((hH x.val).mp x.property)))

theorem presentedDegreeCode_entry (R : ZFSet.{u}) {I : CountableIdeal} {H : Oracle}
    (hH : Presented I H) (hc : ∀ n, realCode (columns H n) ∈ R) (n : ℕ) :
    presentedDegreeCode R hH (entry hH n) = degreeCode R (columns H n) := by
  apply (degreeCode_equal R (hc _)).mpr
  exact Classical.choose_spec ((hH (entry hH n).val).mp (entry hH n).property)

theorem presentedDegreeCode_injective (R : ZFSet.{u}) {I : CountableIdeal} {H : Oracle}
    (hH : Presented I H) (hc : ∀ n, realCode (columns H n) ∈ R) :
    Function.Injective (presentedDegreeCode R hH) := by
  intro x y hxy
  apply Subtype.ext
  have h := (degreeCode_equal R (hc (Classical.choose ((hH x.val).mp x.property)))).mp hxy
  exact (Classical.choose_spec ((hH x.val).mp x.property)).symm.trans
    (h.trans (Classical.choose_spec ((hH y.val).mp y.property)))

theorem presentedDegreeCode_mem (R : ZFSet.{u}) {I : CountableIdeal} {H : Oracle}
    (hH : Presented I H) (x : I) : presentedDegreeCode R hH x ∈ presentationSet R H :=
  (mem_presentationSet R H _).mpr ⟨_,rfl⟩

theorem presentedDegreeCode_onto (R : ZFSet.{u}) {I : CountableIdeal} {H : Oracle}
    (hH : Presented I H) (hc : ∀ n, realCode (columns H n) ∈ R) :
    ∀ D ∈ presentationSet R H, ∃ x : I, presentedDegreeCode R hH x = D := by
  intro D hD
  obtain ⟨n,rfl⟩ := (mem_presentationSet R H D).mp hD
  exact ⟨entry hH n,presentedDegreeCode_entry R hH hc n⟩

theorem presentationGraph_actual (R : ZFSet.{u}) {I : CountableIdeal} {H S : Oracle}
    (hH : Presented I H) (hc : ∀ n, realCode (columns H n) ∈ R)
    (ρ : I ≃o I) (hS : ∀ v, S v = true ↔ Graph ρ hH v) (x y : I) :
    ZFSet.pair (presentedDegreeCode R hH x) (presentedDegreeCode R hH y) ∈ presentationGraph R H S
      ↔ ρ x = y := by
  rw [mem_presentationGraph]
  constructor
  · rintro ⟨i,j,hp,hs⟩
    obtain ⟨hx,hy⟩ := ZFSet.pair_inj.mp hp
    have hxi : x = entry hH i := presentedDegreeCode_injective R hH hc
      (hx.trans (presentedDegreeCode_entry R hH hc i).symm)
    have hyj : y = entry hH j := presentedDegreeCode_injective R hH hc
      (hy.trans (presentedDegreeCode_entry R hH hc j).symm)
    rw [hxi,hyj]
    apply Subtype.ext
    simpa only [PersistentPresentation.Graph,entry,Nat.unpair_pair] using (hS (Nat.pair i j)).mp hs
  · intro hxy
    obtain ⟨i,hi⟩ := (hH x.val).mp x.property
    obtain ⟨j,hj⟩ := (hH y.val).mp y.property
    have hxi : entry hH i = x := Subtype.ext hi
    have hyj : entry hH j = y := Subtype.ext hj
    refine ⟨i,j,?_,(hS (Nat.pair i j)).mpr ?_⟩
    · rw [←hxi,←hyj,presentedDegreeCode_entry R hH hc i,presentedDegreeCode_entry R hH hc j]
    · change (ρ (entry hH (Nat.unpair (Nat.pair i j)).1)).val = degree (columns H (Nat.unpair
      (Nat.pair i j)).2)
      simp only [Nat.unpair_pair]
      rw [hxi,hxy,hj]

end TuringRigidity.BoundedSetTheory

end OAI

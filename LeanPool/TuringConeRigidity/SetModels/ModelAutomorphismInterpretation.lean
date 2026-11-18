/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelAutomorphismInterpretation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelOrderSatisfaction
public import LeanPool.TuringConeRigidity.SetModels.ModelPersistentGraph

/-!
# Model Automorphism Interpretation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing PersistentRestrictions PersistentPresentation
open NumericalIdeal NumericalAutomorphism NumericalExtension
universe u

theorem presentationGraph_automorphism (R : ZFSet.{u}) {J : CountableIdeal} {H S : Oracle}
    (hH : Presented J H) (hc : ∀ n, realCode (columns H n) ∈ R)
    (ρ : J ≃o J) (hS : ∀ v, S v = true ↔ Graph ρ hH v) :
    SetAutomorphism (presentationSet R H) (degreeOrder R) (presentationGraph R H S) := by
  refine ⟨presentationGraph_function R hH hc ρ hS,presentationGraph_onto R hH hc ρ hS,?_⟩
  intro D hD E hE D' hD' E' hE' hDD hEE
  obtain ⟨x,rfl⟩ := presentedDegreeCode_onto R hH hc D hD
  obtain ⟨y,rfl⟩ := presentedDegreeCode_onto R hH hc E hE
  obtain ⟨x',rfl⟩ := presentedDegreeCode_onto R hH hc D' hD'
  obtain ⟨y',rfl⟩ := presentedDegreeCode_onto R hH hc E' hE'
  have hx := (presentationGraph_actual R hH hc ρ hS x x').mp hDD
  have hy := (presentationGraph_actual R hH hc ρ hS y y').mp hEE
  rw [presentedDegreeCode_order R hH hc,presentedDegreeCode_order R hH hc,←hx,←hy]
  exact ρ.le_iff_le.symm

theorem presentationGraph_action (R : ZFSet.{u}) {J : CountableIdeal} {H S : Oracle}
    (hH : Presented J H) (hc : ∀ n, realCode (columns H n) ∈ R)
    (hS : Action H (fun v => S v = true)) :
    SetAutomorphism (presentationSet R H) (degreeOrder R) (presentationGraph R H S) := by
  obtain ⟨ρ,hρ⟩ := reconstruct hH hS
  exact presentationGraph_automorphism R hH hc ρ hρ

theorem presentationSet_subset_of_includes (R : ZFSet.{u}) {A H : Oracle}
    (hA : ∀ n, realCode (columns A n) ∈ R) (hin : Includes A H) :
    presentationSet R A ⊆ presentationSet R H := by
  intro D hD
  obtain ⟨n,rfl⟩ := (mem_presentationSet R A D).mp hD
  obtain ⟨m,hm⟩ := hin n
  exact (mem_presentationSet R H _).mpr ⟨m,(degreeCode_equal R (hA n)).mpr hm⟩

theorem presentationGraph_subset_of_compatible (R : ZFSet.{u}) {A H S T : Oracle}
    (hA : ∀ n, realCode (columns A n) ∈ R)
    (hin : Includes A H) (ha : Action H (fun v => T v = true))
    (hc : Compatible A H (fun v => S v = true) (fun v => T v = true)) :
    presentationGraph R A S ⊆ presentationGraph R H T := by
  intro z hz
  obtain ⟨i,j,rfl,hij⟩ := (mem_presentationGraph R A S z).mp hz
  obtain ⟨n,hin⟩ := hin i
  obtain ⟨m,hm⟩ := ha.total n
  have hjm := hc i j n m hij hm hin
  exact (mem_presentationGraph R H T _).mpr ⟨n,m,by
    rw [(degreeCode_equal R (hA i)).mpr hin,(degreeCode_equal R (hA j)).mpr hjm],hm⟩

theorem presentationGraph_unique (R : ZFSet.{u}) {J : CountableIdeal} {H S : Oracle}
    (hH : Presented J H) (hc : ∀ n, realCode (columns H n) ∈ R)
    (ρ : J ≃o J) (hS : ∀ v, S v = true ↔ Graph ρ hH v)
    (F : ZFSet.{u}) (hf : F ⊆ ZFSet.prod (presentationSet R H) (presentationSet R H))
    (hF : ∀ x y : J, ZFSet.pair (presentedDegreeCode R hH x) (presentedDegreeCode R hH y) ∈ F ↔ ρ
      x = y) :
    F = presentationGraph R H S := by
  apply ZFSet.ext; intro z
  by_cases hz : z ∈ ZFSet.prod (presentationSet R H) (presentationSet R H)
  · obtain ⟨D,hD,E,hE,rfl⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨x,rfl⟩ := presentedDegreeCode_onto R hH hc D hD
    obtain ⟨y,rfl⟩ := presentedDegreeCode_onto R hH hc E hE
    exact (hF x y).trans (presentationGraph_actual R hH hc ρ hS x y).symm
  · exact ⟨fun h => False.elim (hz (hf h)),fun h => False.elim (hz (ZFSet.mem_sep.mp h).1)⟩

end TuringRigidity.BoundedSetTheory

end OAI

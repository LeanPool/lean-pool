/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SetAutomorphismReconstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalAutomorphism
public import LeanPool.TuringConeRigidity.SetModels.ModelOrderSatisfaction

/-!
# Set Automorphism Reconstruction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing PersistentRestrictions PersistentPresentation
open NumericalAutomorphism
universe u

/-- The Boolean oracle coding membership in the set-coded degree action graph. -/
noncomputable def setGraphReal (R H F : ZFSet.{u}) : Oracle := fun v => by
  classical
  exact decide (ZFSet.pair (degreeCode R (columns (decodeReal H) (Nat.unpair v).1))
    (degreeCode R (columns (decodeReal H) (Nat.unpair v).2)) ∈ F)

theorem setGraphReal_bit (R F : ZFSet.{u}) (H : Oracle) (n m : ℕ) :
    setGraphReal R (realCode H) F (Nat.pair n m) = true ↔
      ZFSet.pair (degreeCode R (columns H n)) (degreeCode R (columns H m)) ∈ F := by
  classical
  simp [setGraphReal,decodeReal_realCode]

theorem setGraphReal_action (R : ZFSet.{u}) {H : Oracle}
    (hc : ∀ n, realCode (columns H n) ∈ R)
    (F : ZFSet.{u}) (hF : SetAutomorphism (presentationSet R H) (degreeOrder R) F) :
    Action H (fun v => setGraphReal R (realCode H) F v = true) := by
  have hi (n : ℕ) : degreeCode R (columns H n) ∈ presentationSet R H :=
    (mem_presentationSet _ _ _).mpr ⟨n,rfl⟩
  constructor
  · intro n
    obtain ⟨D,hD,hn,_⟩ := hF.1.2 _ (hi n)
    obtain ⟨m,rfl⟩ := (mem_presentationSet _ _ _).mp hD
    exact ⟨m,(setGraphReal_bit R F H n m).mpr hn⟩
  · intro m
    obtain ⟨D,hD,hm⟩ := hF.2.1 _ (hi m)
    obtain ⟨n,rfl⟩ := (mem_presentationSet _ _ _).mp hD
    exact ⟨n,(setGraphReal_bit R F H n m).mpr hm⟩
  · intro n m n' m' hnm hn'm'
    have h := hF.2.2 _ (hi n) _ (hi n') _ (hi m) _ (hi m')
      ((setGraphReal_bit R F H n m).mp hnm) ((setGraphReal_bit R F H n' m').mp hn'm')
    rwa [degreeOrder_actual R (hc n) (hc n'),degreeOrder_actual R (hc m) (hc m')] at h
  · intro n m m' hnm hmm
    apply (setGraphReal_bit R F H n m').mpr
    rw [←(degreeCode_equal R (hc m)).mpr hmm]
    exact (setGraphReal_bit R F H n m).mp hnm

theorem setGraphReal_decodes (R : ZFSet.{u}) (H : Oracle) (F : ZFSet.{u})
    (hF : F ⊆ ZFSet.prod (presentationSet R H) (presentationSet R H)) :
    presentationGraph R H (setGraphReal R (realCode H) F) = F := by
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨n,m,rfl,hnm⟩ := (mem_presentationGraph _ _ _ _).mp hz
    exact (setGraphReal_bit R F H n m).mp hnm
  · intro hz
    obtain ⟨D,hD,E,hE,rfl⟩ := ZFSet.mem_prod.mp (hF hz)
    obtain ⟨n,rfl⟩ := (mem_presentationSet _ _ _).mp hD
    obtain ⟨m,rfl⟩ := (mem_presentationSet _ _ _).mp hE
    exact (mem_presentationGraph _ _ _ _).mpr ⟨n,m,rfl,(setGraphReal_bit R F H n m).mpr hz⟩

theorem setAutomorphism_reconstruct (R : ZFSet.{u}) {J : CountableIdeal} {H : Oracle}
    (hH : Presented J H) (hc : ∀ n, realCode (columns H n) ∈ R)
    (F : ZFSet.{u}) (hF : SetAutomorphism (presentationSet R H) (degreeOrder R) F) :
    ∃ ρ : J ≃o J, ∀ x y : J,
      ZFSet.pair (presentedDegreeCode R hH x) (presentedDegreeCode R hH y) ∈ F ↔ ρ x = y := by
  obtain ⟨ρ,hρ⟩ := reconstruct hH (setGraphReal_action R hc F hF)
  refine ⟨ρ,?_⟩
  have he := setGraphReal_decodes R H F (fun z hz => ZFSet.mem_prod.mpr (hF.1.1 z hz))
  intro x y
  rw [←he]
  exact presentationGraph_actual R hH hc ρ hρ x y

end TuringRigidity.BoundedSetTheory

end OAI

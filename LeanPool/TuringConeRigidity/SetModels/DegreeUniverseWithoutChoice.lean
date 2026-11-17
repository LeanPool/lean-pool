/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/DegreeUniverseWithoutChoice.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelDegreeUniverse

/-!
# Degree Universe Without Choice
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem internal_degreeCode_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
  (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ x ∈ R, ∃ B : Oracle, realCode B = x)
    {A : Oracle} (hA : A ∈ modelReals M) : degreeCode R A ∈ M := by
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hP hU hPow hS hω
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => realCode A)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    rcases i with _ | i
    · exact hz
    exact hA
  let D := ZFSet.sep (fun x => (Formula.twoOracles φ 1 2 3 0 4).Eval (cons x e)) R
  have hD : D ∈ M := sep_mem M hM hS _ e he hRM
  have hcode : degreeCode R A = D := by
    apply ZFSet.ext; intro x
    by_cases hx : x ∈ R
    · obtain ⟨B,rfl⟩ := hR x hx
      rw [realCode_mem_degreeCode,ZFSet.mem_sep]
      rw [hφ 1 2 3 0 4 (cons (realCode B) e) rfl hQ rfl B A rfl rfl]
    · simp only [degreeCode,D,ZFSet.mem_sep,hx,false_and]
  rw [hcode]
  exact hD

theorem internal_degreeUniverse_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing
  M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ w ∈ R, ∃ B : Oracle, realCode B = w) : degreeUniverse R ∈ M := by
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hP hU hPow hS hω
  obtain ⟨P,hPM,hPdef⟩ := internal_power M hM hPow hRM
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  have hsub : degreeUniverse R ⊆ P := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := (mem_degreeUniverse R D).mp hD
    exact (hPdef _).mpr ⟨internal_degreeCode_without_choice M hM hP hU hPow hS hω R hRM hR (hM _
      hRM _ hA),
      degreeCode_subset R A⟩
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => R)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    rcases i with _ | i
    · exact hz
    exact hRM
  have hs := sep_mem M hM hS (Formula.degreeUniverseMember φ 1 2 3 4 0) e he hPM
  have heq : ZFSet.sep (fun D => (Formula.degreeUniverseMember φ 1 2 3 4 0).Eval (cons D e)) P =
      degreeUniverse R := by
    apply ZFSet.ext; intro D
    rw [ZFSet.mem_sep,Formula.degreeUniverseMember_spec hφ 1 2 3 4 0 (cons D e) rfl hQ rfl hR]
    exact ⟨And.right,fun h => ⟨hsub h,h⟩⟩
  exact heq ▸ hs

end TuringRigidity.BoundedSetTheory

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelDegreeUniverse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.DegreeSetFormula

/-!
# Model Degree Universe
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def degreeUniverse (R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun D => ∃ A : Oracle, realCode A ∈ R ∧ D = degreeCode R A) (ZFSet.powerset R)

theorem mem_degreeUniverse (R D : ZFSet.{u}) :
    D ∈ degreeUniverse R ↔ ∃ A : Oracle, realCode A ∈ R ∧ D = degreeCode R A := by
  rw [degreeUniverse,ZFSet.mem_sep]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  obtain ⟨A,_,rfl⟩ := h
  exact ZFSet.mem_powerset.mpr (degreeCode_subset R A)

theorem degreeUniverse_nonempty_member (R D : ZFSet.{u}) (hD : D ∈ degreeUniverse R) :
    ∃ A : Oracle, realCode A ∈ D ∧ D = degreeCode R A := by
  obtain ⟨A,hA,rfl⟩ := (mem_degreeUniverse R D).mp hD
  exact ⟨A,(realCode_mem_degreeCode R A A).mpr ⟨hA,rfl⟩,rfl⟩

namespace Formula
def degreeUniverseMember (φ : Formula) (o Q z R D : ℕ) : Formula :=
  .existsMem R (degreeSet φ (o+1) (Q+1) (z+1) (R+1) 0 (D+1))

theorem degreeUniverseMember_spec {φ : Formula} (hφ : DegreeEqualityFormula.{u} φ)
    (o Q z R D : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w) :
    (degreeUniverseMember φ o Q z R D).Eval e ↔ e D ∈ degreeUniverse (e R) := by
  simp only [degreeUniverseMember,Formula.Eval]
  rw [mem_degreeUniverse]
  constructor
  · rintro ⟨w,hw,hd⟩
    obtain ⟨A,rfl⟩ := hR w hw
    exact ⟨A,hw,(degreeSet_spec hφ (o+1) (Q+1) (z+1) (R+1) 0 (D+1)
      (cons (realCode A) e) ho hQ hz hR A rfl).mp hd⟩
  · rintro ⟨A,hA,hd⟩
    exact ⟨realCode A,hA,(degreeSet_spec hφ (o+1) (Q+1) (z+1) (R+1) 0 (D+1)
      (cons (realCode A) e) ho hQ hz hR A rfl).mpr hd⟩
end Formula

theorem internal_degreeUniverse (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ w ∈ R, ∃ B : Oracle, realCode B = w) : degreeUniverse R ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet
    hS hω
  obtain ⟨P,hPM,hP⟩ := internal_power M hM hT.powerSet hRM
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  have hsub : degreeUniverse R ⊆ P := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := (mem_degreeUniverse R D).mp hD
    exact (hP _).mpr ⟨internal_degreeCode M hM hT R hRM hR (hM _ hRM _ hA),
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

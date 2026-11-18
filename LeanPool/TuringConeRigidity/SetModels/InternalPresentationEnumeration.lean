/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalPresentationEnumeration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.PresentationEnumeration

/-!
# Internal Presentation Enumeration
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing
universe u

theorem internal_presentationEnumeration (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M)
    (hRd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    {H : Oracle} (hH : H ∈ modelReals M) : presentationEnumeration R H ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet
    hS hω
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  have hφ' : DegreeEqualityFormula.{u} φ := hφ
  have hc : ∀ n, realCode (columns H n) ∈ R :=
    fun n => (hR _).mpr (sourceT_real_column M hM hT hH n)
  let I := presentationSet R H
  have hIM : I ∈ M := internal_presentationSet M hM hT R hRM hR hRd hH
  have hsub : presentationEnumeration R H ⊆ ZFSet.prod ZFSet.omega I := by
    intro z hz
    exact ZFSet.mem_prod.mpr ((presentationEnumeration_function R H).1 z hz)
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (cons R (cons (realCode H) (fun _ => I)))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    rcases i with _ | i
    · exact hz
    rcases i with _ | i
    · exact hRM
    rcases i with _ | i
    · exact hH
    exact hIM
  let E := ZFSet.sep (fun z => (Formula.enumerationMember φ 1 2 3 4 5 6 0).Eval (cons z e))
    (ZFSet.prod ZFSet.omega I)
  have hEM : E ∈ M := sep_mem M hM hS _ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hIM)
  have hE : E = presentationEnumeration R H := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,Formula.enumerationMember_spec hφ' 1 2 3 4 5 6 0 (cons z e) rfl hQ rfl hRd H
      rfl hc rfl]
    exact ⟨And.right,fun h => ⟨hsub h,h⟩⟩
  rw [←hE]
  exact hEM

theorem internal_presentation_countable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M)
    (hRd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    {H : Oracle} (hH : H ∈ modelReals M) :
    presentationSet R H ∈ M ∧ ∃ E ∈ M,
      TransitiveNameModel.FunctionGraph ZFSet.omega (presentationSet R H) E ∧
      ∀ D ∈ presentationSet R H, ∃ x ∈ ZFSet.omega, ZFSet.pair x D ∈ E :=
  ⟨internal_presentationSet M hM hT R hRM hR hRd hH,
    presentationEnumeration R H,internal_presentationEnumeration M hM hT R hRM hR hRd hH,
    presentationEnumeration_function R H,presentationEnumeration_onto R H⟩

end TuringRigidity.BoundedSetTheory

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/PresentationGraphSet.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalPresentationEnumeration

/-!
# Presentation Graph Set
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing
universe u

/-- The relation on presented degree classes selected by the paired bits of `S`. -/
noncomputable def presentationGraph (R : ZFSet.{u}) (H S : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i j, z = ZFSet.pair (degreeCode R (columns H i)) (degreeCode R (columns H
    j)) ∧
    S (Nat.pair i j) = true) (ZFSet.prod (presentationSet R H) (presentationSet R H))

theorem mem_presentationGraph (R : ZFSet.{u}) (H S : Oracle) (z : ZFSet.{u}) :
    z ∈ presentationGraph R H S ↔ ∃ i j,
      z = ZFSet.pair (degreeCode R (columns H i)) (degreeCode R (columns H j)) ∧ S (Nat.pair i j)
        = true := by
  rw [presentationGraph,ZFSet.mem_sep]
  refine ⟨And.right,?_⟩
  rintro ⟨i,j,rfl,hs⟩
  exact ⟨ZFSet.mem_prod.mpr ⟨_,(mem_presentationSet R H _).mpr ⟨i,rfl⟩,
    _,(mem_presentationSet R H _).mpr ⟨j,rfl⟩,rfl⟩,i,j,rfl,hs⟩

namespace Formula
/-- Bounded formula describing membership in the relation graph on presented degree classes. -/
def presentationGraphMember : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 6 (.existsMem 7
    (.conj (.orderedPair 4 3 2) (.conj (.pairMem 1 3 6)
      (.conj (.pairMem 0 2 6) (columnBit 8 9 1 7 0)))))))

theorem presentationGraphMember_spec (R Q : ZFSet.{u})
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ Q)
    (H S : Oracle) (z : ZFSet.{u}) :
    presentationGraphMember.Eval (cons z (cons (presentationSet R H) (cons
      (presentationEnumeration R H)
      (cons (realCode S) (cons ZFSet.omega (fun _ => Q)))))) ↔ z ∈ presentationGraph R H S := by
  let e := cons z (cons (presentationSet R H) (cons (presentationEnumeration R H)
      (cons (realCode S) (cons ZFSet.omega (fun _ => Q)))))
  have hb (D F : ZFSet.{u}) (i j : ℕ) := columnBit_spec 8 9 1 7 0
    (cons (natSet j) (cons (natSet i) (cons F (cons D e)))) rfl hQ S rfl i j rfl rfl
  simp only [presentationGraphMember,Formula.Eval,eval_orderedPair,eval_pairMem,cons_zero,cons_succ]
  rw [mem_presentationGraph]
  constructor
  · rintro ⟨D,_,F,_,i,hi,j,hj,hz,hiD,hjF,hs⟩
    obtain ⟨i,rfl⟩ := (mem_omega i).mp hi
    obtain ⟨j,rfl⟩ := (mem_omega j).mp hj
    have hd := (presentationEnumeration_pair R H i D).mp hiD
    have hf := (presentationEnumeration_pair R H j F).mp hjF
    exact ⟨i,j,by simpa only [hd,hf] using hz,(hb D F i j).mp hs⟩
  · rintro ⟨i,j,hz,hs⟩
    refine ⟨_,(mem_presentationSet R H _).mpr ⟨i,rfl⟩,
      _,(mem_presentationSet R H _).mpr ⟨j,rfl⟩,
      natSet i,(mem_omega _).mpr ⟨i,rfl⟩,natSet j,(mem_omega _).mpr ⟨j,rfl⟩,hz,
      (presentationEnumeration_pair R H i _).mpr rfl,(presentationEnumeration_pair R H j _).mpr
        rfl,?_⟩
    exact (hb _ _ i j).mpr hs
end Formula

theorem internal_presentationGraph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M)
    (hRd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    {H S : Oracle} (hH : H ∈ modelReals M) (hSM : S ∈ modelReals M) : presentationGraph R H S ∈ M
      := by
  have hSep := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet
    hSep hω
  have hIM := internal_presentationSet M hM hT R hRM hR hRd hH
  have hEM := internal_presentationEnumeration M hM hT R hRM hR hRd hH
  let e := cons (presentationSet R H) (cons (presentationEnumeration R H)
      (cons (realCode S) (cons ZFSet.omega (fun _ => Q))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hIM
    rcases i with _ | i
    · exact hEM
    rcases i with _ | i
    · exact hSM
    rcases i with _ | i
    · exact hω
    exact hQM
  let B := ZFSet.sep (fun z => Formula.presentationGraphMember.Eval (cons z e))
    (ZFSet.prod (presentationSet R H) (presentationSet R H))
  have hBM : B ∈ M := sep_mem M hM hSep _ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hSep hIM hIM)
  have hB : B = presentationGraph R H S := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,Formula.presentationGraphMember_spec R Q hQ H S z]
    exact ⟨And.right,fun h => ⟨(ZFSet.mem_sep.mp h).1,h⟩⟩
  rw [←hB]
  exact hBM

end TuringRigidity.BoundedSetTheory

end OAI

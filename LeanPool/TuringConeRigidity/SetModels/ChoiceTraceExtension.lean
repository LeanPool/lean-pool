/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ChoiceTraceExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ChoiceTraceFormula

/-!
# Choice Trace Extension
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace InternalWellOrder

theorem adjoin_prior (f i x k y : ZFSet.{u}) (hk : k ∈ i) :
    ZFSet.pair k y ∈ f ∪ ({ZFSet.pair i x} : ZFSet.{u}) ↔ ZFSet.pair k y ∈ f := by
  rw [ZFSet.mem_union,ZFSet.mem_singleton]
  constructor
  · rintro (h|h)
    · exact h
    · obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp h
      exact False.elim ((lt_irrefl _) (ZFSet.rank_lt_of_mem hk))
  · exact Or.inl

theorem Trace.adjoin {α a q s f i x r : ZFSet.{u}} (hf : Trace α a q s f)
    (hi : i ∈ α) (hit : Transitive i) (hx : x ∈ a) (hr : r ∈ q)
    (hrem : Remaining a f i r) (hrx : ZFSet.pair r x ∈ s)
    (hprev : ∀ j ∈ i, ∃ y ∈ a, ZFSet.pair j y ∈ f)
    (hdom : ∀ j y, ZFSet.pair j y ∈ f → j ∈ i) :
    Trace α a q s (f ∪ ({ZFSet.pair i x} : ZFSet.{u})) := by
  refine ⟨?_,?_,?_⟩
  · intro z hz
    rcases ZFSet.mem_union.mp hz with hz|hz
    · exact hf.shape z hz
    · obtain rfl := ZFSet.mem_singleton.mp hz
      exact ⟨i,hi,x,hx,rfl⟩
  · intro j hj y hy hjy k hkj
    rcases ZFSet.mem_union.mp hjy with hjy|hjy
    · obtain ⟨z,hz,hkz⟩ := hf.initial j hj y hy hjy k hkj
      exact ⟨z,hz,ZFSet.mem_union.mpr (Or.inl hkz)⟩
    · have he := ZFSet.mem_singleton.mp hjy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      obtain ⟨z,hz,hkz⟩ := hprev k hkj
      exact ⟨z,hz,ZFSet.mem_union.mpr (Or.inl hkz)⟩
  · intro j hj y hy hjy
    rcases ZFSet.mem_union.mp hjy with hjy|hjy
    · obtain ⟨b,hb,hbrem,hby⟩ := hf.choice j hj y hy hjy
      refine ⟨b,hb,⟨hbrem.1,?_⟩,hby⟩
      intro z hz
      rw [hbrem.2 z hz]
      apply not_congr
      apply exists_congr; intro k
      apply and_congr_right; intro hkj
      exact (adjoin_prior f i x k z (hit j (hdom j y hjy) k hkj)).symm
    · have he := ZFSet.mem_singleton.mp hjy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      refine ⟨r,hr,⟨hrem.1,?_⟩,hrx⟩
      intro z hz
      rw [hrem.2 z hz]
      apply not_congr
      apply exists_congr; intro k
      apply and_congr_right; intro hki
      exact (adjoin_prior f j y k z hki).symm

theorem Trace.domain_before {α a q s f i : ZFSet.{u}} (hα : α.IsOrdinal)
    (hf : Trace α a q s f) (hi : i ∈ α) (hmissing : ¬ ∃ x ∈ a, ZFSet.pair i x ∈ f)
    (j y : ZFSet.{u}) (hjy : ZFSet.pair j y ∈ f) : j ∈ i := by
  have hj := (hf.pair_mem hjy).1
  have hy := (hf.pair_mem hjy).2
  rcases (hα.mem hj).mem_trichotomous (hα.mem hi) with hji|he|hij
  · exact hji
  · subst j; exact False.elim (hmissing ⟨y,hy,hjy⟩)
  · exact False.elim (hmissing (hf.initial j hj y hy hjy i hij))

theorem FunctionGraph.exists_presentation {d r f : ZFSet.{u}} (hf :
  TransitiveNameModel.FunctionGraph d r f) :
    ∃ j : ZFSet.{u} → ZFSet.{u}, Presents d f j ∧ ∀ x ∈ d, j x ∈ r := by
  classical
  let j := fun x => if hx : x ∈ d then (hf.2 x hx).choose else ∅
  have hj (x : ZFSet.{u}) (hx : x ∈ d) : j x ∈ r ∧ ZFSet.pair x (j x) ∈ f := by
    simp only [j,dite_eq_left hx]
    exact ⟨(hf.2 x hx).choose_spec.1,(hf.2 x hx).choose_spec.2.1⟩
  refine ⟨j,?_,fun x hx => (hj x hx).1⟩
  intro z
  constructor
  · intro hz
    obtain ⟨x,hx,y,_,rfl⟩ := hf.1 z hz
    exact ⟨x,hx,congrArg (ZFSet.pair x) (hf.functional hx hz (hj x hx).2)⟩
  · rintro ⟨x,hx,rfl⟩
    exact (hj x hx).2

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCountableMap.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRelationSelection

/-!
# Internal Countable Map
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCountableMap
open TransitiveNameModel BoundedSetTheory

noncomputable def composite (A B C f g : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod A C).sep (fun z => ∃ x ∈ A, ∃ y ∈ C,
    z = ZFSet.pair x y ∧ ∃ t ∈ B, ZFSet.pair x t ∈ f ∧ ZFSet.pair t y ∈ g)

theorem pair_composite (A B C f g x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ composite A B C f g ↔
      x ∈ A ∧ y ∈ C ∧ ∃ t ∈ B, ZFSet.pair x t ∈ f ∧ ZFSet.pair t y ∈ g := by
  simp only [composite,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',hx,y',hy,he,ht⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,ht⟩
  · rintro ⟨hx,hy,ht⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,ht⟩

theorem composite_mem (M A B C f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hC : C ∈ M) (hf : f ∈ M) (hg : g ∈ M) :
    composite A B C f g ∈ M := by
  let e := cons A (cons C (cons B (cons f (fun _ => g))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact hA
    · exact hC
    · exact hB
    · exact hf
    · exact hg
  simpa only [composite,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.conj (.pairMem 2 0 7) (.pairMem 0 1 8)))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hC)

theorem composite_function (A B C f g : ZFSet.{0})
    (hf : FunctionGraph A B f) (hg : FunctionGraph B C g) :
    FunctionGraph A C (composite A B C f g) := by
  constructor
  · intro z hz
    exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    obtain ⟨t,ht,hxt,_⟩ := hf.2 x hx
    obtain ⟨y,hy,hty,_⟩ := hg.2 t ht
    refine ⟨y,hy,(pair_composite A B C f g x y).mpr ⟨hx,hy,t,ht,hxt,hty⟩,?_⟩
    intro y' _ hxy'
    obtain ⟨_,_,t',_,hxt',hty'⟩ := (pair_composite A B C f g x y').mp hxy'
    have he := hf.functional hx hxt' hxt
    exact hg.functional ht (he ▸ hty') hty

theorem countable_of_surjection (M A B g : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hgM : g ∈ M)
    (hg : FunctionGraph A B g) (honto : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ g)
    (hct : InternallyCountable M A) : InternallyCountable M B := by
  obtain ⟨f,hfM,hf,hfOnto⟩ := hct
  refine ⟨composite ZFSet.omega A B f g,
    composite_mem M _ A B f g hM hT (sourceT_omega_mem M hM hT) hA hB hfM hgM,
    composite_function _ A B f g hf hg,?_⟩
  intro y hy
  obtain ⟨x,hx,hxy⟩ := honto y hy
  obtain ⟨n,hn,hnx⟩ := hfOnto x hx
  exact ⟨n,hn,(pair_composite _ A B f g n y).mpr ⟨hn,hy,x,hx,hnx,hxy⟩⟩

end TuringRigidity.InternalCountableMap

end OAI

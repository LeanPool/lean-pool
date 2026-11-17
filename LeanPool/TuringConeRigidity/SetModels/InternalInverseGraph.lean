/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalInverseGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableMap

/-!
# Internal Inverse Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalInverseGraph
open TransitiveNameModel BoundedSetTheory

/-- Transpose the set-coded graph from `A` to `B` to obtain its inverse relation. -/
noncomputable def inverse (A B f : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod B A).sep (fun z => ∃ y ∈ B, ∃ x ∈ A,
    z = ZFSet.pair y x ∧ ZFSet.pair x y ∈ f)

theorem pair_inverse (A B f y x : ZFSet.{0}) :
    ZFSet.pair y x ∈ inverse A B f ↔ y ∈ B ∧ x ∈ A ∧ ZFSet.pair x y ∈ f := by
  simp only [inverse,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y',hy,x',hx,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hy,hx,h⟩
  · rintro ⟨hy,hx,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hy,hx⟩,y,hy,x,hx,rfl,h⟩

theorem inverse_mem (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hf : f ∈ M) : inverse A B f ∈ M := by
  let e := cons B (cons A (fun _ => f))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hB
    · exact hA
    · exact hf
  simpa only [inverse,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (.pairMem 0 1 5)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hB hA)

theorem inverse_function (A B f : ZFSet.{0})
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) :
    FunctionGraph B A (inverse A B f) := by
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := hs y hy
    refine ⟨x,hx,(pair_inverse A B f y x).mpr ⟨hy,hx,hxy⟩,?_⟩
    intro x' hx' hyx'
    exact hi x' hx' x hx y hy ((pair_inverse A B f y x').mp hyx').2.2 hxy

theorem inverse_onto (A B f : ZFSet.{0}) (hf : FunctionGraph A B f) :
    ∀ x ∈ A, ∃ y ∈ B, ZFSet.pair y x ∈ inverse A B f := by
  intro x hx
  obtain ⟨y,hy,hxy,_⟩ := hf.2 x hx
  exact ⟨y,hy,(pair_inverse A B f y x).mpr ⟨hy,hx,hxy⟩⟩

theorem countable_of_bijection (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hfM : f ∈ M) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f)
    (hct : InternallyCountable M B) : InternallyCountable M A :=
  InternalCountableMap.countable_of_surjection M B A (inverse A B f) hM hT hB hA
    (inverse_mem M A B f hM hT hA hB hfM) (inverse_function A B f hi hs)
    (inverse_onto A B f hf) hct

end TuringRigidity.InternalInverseGraph

end OAI

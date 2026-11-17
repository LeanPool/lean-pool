/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalGraphEquiv.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalInverseGraph

/-!
# Internal Graph Equiv
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalGraphEquiv
open TransitiveNameModel BoundedSetTheory

noncomputable def graphMap (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (x : Conditions A) : Conditions B :=
  equivShrink B ⟨(hf.2 (label A x) (label_mem A x)).choose,
    (hf.2 (label A x) (label_mem A x)).choose_spec.1⟩

theorem graphMap_spec (A B f : ZFSet.{0}) (hf : FunctionGraph A B f) (x : Conditions A) :
    ZFSet.pair (label A x) (label B (graphMap A B f hf x)) ∈ f := by
  simpa only [graphMap,label,Equiv.symm_apply_apply] using
    (hf.2 (label A x) (label_mem A x)).choose_spec.2.1

theorem graphMap_bijective (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) : Function.Bijective (graphMap A B f hf) := by
  constructor
  · intro x x' he
    apply label_injective A
    exact hi _ (label_mem A x) _ (label_mem A x') _ (label_mem B (graphMap A B f hf x))
      (graphMap_spec A B f hf x) (he.symm ▸ graphMap_spec A B f hf x')
  · intro y
    obtain ⟨x,hx,hxy⟩ := hs (label B y) (label_mem B y)
    obtain ⟨x,rfl⟩ := label_surjective A hx
    exact ⟨x,label_injective B (hf.functional (label_mem A x) (graphMap_spec A B f hf x) hxy)⟩

noncomputable def graphEquiv (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) : Conditions A ≃ Conditions B :=
  Equiv.ofBijective (graphMap A B f hf) (graphMap_bijective A B f hf hi hs)

theorem graphEquiv_spec (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) (x : Conditions A) (y : Conditions B) :
    ZFSet.pair (label A x) (label B y) ∈ f ↔ y = graphEquiv A B f hf hi hs x := by
  exact ⟨fun h => label_injective B (hf.functional (label_mem A x) h (graphMap_spec A B f hf x)),
    fun h => h.symm ▸ graphMap_spec A B f hf x⟩

end TuringRigidity.InternalGraphEquiv

end OAI

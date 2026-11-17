/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/AmbientDegreeSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.FullNativePersistence
public import LeanPool.TuringConeRigidity.Representation.NativeModelCompatibility
public import LeanPool.TuringConeRigidity.SetModels.ModelDegreeOrder

/-!
# Ambient Degree Syntax
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

noncomputable def definedSet (s : ℕ) (p : Formula) : SentenceForm :=
  all (SentenceForm.iff (.member 0 (s+1)) (fromBounded p))

theorem definedSet_spec (M : ZFSet.{u}) (hM : Transitive M)
    (s : ℕ) (p : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (definedSet s p).Sat (M : Set ZFSet) e ↔
      ∀ x ∈ M, x ∈ e s ↔ p.Eval (cons x e) := by
  simp only [definedSet,sat_all,sat_iff,Sat,cons_zero,cons_succ,bounded_sat]
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  exact iff_congr Iff.rfl (Formula.absolute p M hM _
    (by
      intro i
      cases i
      · exact hx
      · exact he _))

noncomputable def ownPower (a s : ℕ) : SentenceForm :=
  definedSet s (.subset 0 (a+1))

theorem ownPower_spec (M : ZFSet.{u}) (hM : Transitive M)
    (a s : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (ownPower a s).Sat (M : Set ZFSet) e ↔
      ∀ x, x ∈ e s ↔ x ∈ M ∧ x ⊆ e a := by
  rw [ownPower,definedSet_spec M hM s _ e he]
  simp only [Formula.eval_subset,cons_zero,cons_succ]
  constructor
  · intro h x
    exact ⟨fun hx => ⟨hM _ (he s) _ hx,(h x (hM _ (he s) _ hx)).mp hx⟩,
      fun hx => (h x hx.1).mpr hx.2⟩
  · intro h x hx
    exact (h x).trans (and_iff_right hx)

def productMember (a b x : ℕ) : Formula :=
  .existsMem a (.existsMem (b+1) (.orderedPair (x+2) 1 0))

theorem productMember_spec (a b x : ℕ) (e : ℕ → ZFSet.{u}) :
    (productMember a b x).Eval e ↔ e x ∈ ZFSet.prod (e a) (e b) := by
  simp only [productMember,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,ZFSet.mem_prod]

theorem definedSet_unique (M : ZFSet.{u}) (hM : Transitive M)
    (s : ℕ) (p : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (S : ZFSet.{u}) (hS : S ∈ M)
    (hs : ∀ x ∈ M, p.Eval (cons x e) ↔ x ∈ S) :
    (definedSet s p).Sat (M : Set ZFSet) e ↔ e s = S := by
  rw [definedSet_spec M hM s p e he]
  constructor
  · intro h
    apply ZFSet.ext; intro x
    exact ⟨fun hx => (hs x (hM _ (he s) _ hx)).mp ((h x (hM _ (he s) _ hx)).mp hx),
      fun hx => (h x (hM _ hS _ hx)).mpr ((hs x (hM _ hS _ hx)).mpr hx)⟩
  · intro h x hx; rw [h]; exact (hs x hx).symm

end TuringRigidity.FullSetForcing

end OAI

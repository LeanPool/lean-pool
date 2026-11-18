/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaTransitiveWitness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaHull

/-!
# Sigma Transitive Witness
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

theorem transitive_upward (φ : SigmaFormula) {d D : ZFSet.{u}} (hd : Transitive d) (hD :
  Transitive D)
    (hsub : d ⊆ D) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ d) :
    φ.Realize d e → φ.Realize D e := by
  induction φ generalizing e with
  | bounded φ =>
    intro h
    exact (φ.absolute D hD e (fun i => hsub (he i))).mpr ((φ.absolute d hd e he).mp h)
  | existsSet φ ih =>
    rintro ⟨x,hx,hφ⟩
    exact ⟨x,hsub hx,ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx]) hφ⟩

theorem internal_transitive_witness (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) {t : ZFSet.{u}} (ht : t ∈ M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ t) (φ : SigmaFormula) (hφ : φ.Realize M e) :
    ∃ d ∈ M, Transitive d ∧ t ⊆ d ∧ φ.Realize d e := by
  obtain ⟨xs,hlen,hxs,hmat⟩ := (φ.realize_iff_prefix M e).mp hφ
  have hω := omega_mem M hM hS hI
  have h0 := hM _ hω _ ZFSet.omega_zero
  let s := t ∪ FiniteTuple.elements xs
  have hs : s ∈ M := binary_union_mem M hM hP hU ht (FiniteTuple.elements_mem M hM hP hU h0 xs hxs)
  obtain ⟨d,hdM,hd,hsd⟩ := internal_transitive_container M hM hP hU hS hR hI hs
  have hsD : s ⊆ d := fun y hy => hd s hsd y hy
  have htD : t ⊆ d := fun y hy => hsD (ZFSet.mem_union.mpr (Or.inl hy))
  have hxsD : ∀ y ∈ xs, y ∈ d := fun y hy =>
    hsD (ZFSet.mem_union.mpr (Or.inr ((FiniteTuple.mem_elements y xs).mpr hy)))
  have heM := fun i => hM t ht _ (he i)
  have heD := fun i => htD (he i)
  refine ⟨d,hdM,hd,htD,(φ.realize_iff_prefix d e).mpr ⟨xs,hlen,hxsD,?_⟩⟩
  exact (φ.matrix.absolute d hd _ (feed_mem xs e d hxsD heD)).mpr
    ((φ.matrix.absolute M hM _ (feed_mem xs e M hxs heM)).mp hmat)
end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI

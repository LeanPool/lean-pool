/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaCollection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformSigmaHull
public import LeanPool.TuringConeRigidity.Syntax.BoundedSupport

/-!
# Sigma Collection
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

def scope : SigmaFormula → ℕ
  | .bounded φ => φ.scope
  | .existsSet φ => φ.scope-1

theorem realize_congr (φ : SigmaFormula) (d : ZFSet.{u}) (e f : ℕ → ZFSet.{u})
    (h : ∀ i, i < φ.scope → e i = f i) : φ.Realize d e ↔ φ.Realize d f := by
  induction φ generalizing e f with
  | bounded φ => exact φ.realize_congr d e f h
  | existsSet φ ih =>
    simp only [Realize]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply ih; intro j hj
    cases j with
    | zero => rfl
    | succ j => exact h j (by change j < φ.scope-1; omega)
end SigmaFormula

theorem internal_sigma_request_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ W ∈ M, ∀ x ∈ a, (∃ y ∈ M, φ.Realize M (cons y (cons x e))) →
      ∃ y ∈ W, φ.Realize M (cons y (cons x e)) := by
  have hω := omega_mem M hM hS.bounded hI
  let ee := cons a (cons ZFSet.omega e)
  have hee : ∀ i, ee i ∈ M := by
    intro i
    rcases i with _ | i
    · exact ha
    rcases i with _ | i
    · exact hω
    exact he i
  obtain ⟨t,ht,htt,hat,hentries⟩ := BoundedForcing.finite_container M hM hP hU hS.bounded hR hI
    ee hee (φ.scope+2)
  have hωt : ZFSet.omega.{u} ∈ t := hentries 1 (by omega)
  have h0t : (∅ : ZFSet.{u}) ∈ t := htt _ hωt _ ZFSet.omega_zero
  let e' := fun i => if i < φ.scope then e i else ∅
  have he' : ∀ i, e' i ∈ t := by
    intro i; dsimp [e']; split_ifs with hi
    · exact hentries (i+2) (by omega)
    · exact h0t
  have congr (x y : ZFSet.{u}) : φ.Realize M (cons y (cons x e)) ↔
      φ.Realize M (cons y (cons x e')) := by
    apply φ.realize_congr; intro i hi
    rcases i with _ | i
    · rfl
    rcases i with _ | i
    · rfl
    exact (ite_eq_left (show i < φ.scope by omega)).symm
  obtain ⟨W,hW,hbound⟩ := FiniteTuple.internal_uniform_sigma_witness_bound M t hM hP hU hPow hS hR
    hI hAC ht htt h0t
  refine ⟨W,hW,?_⟩
  intro x hx hy
  have henv : ∀ i, cons x e' i ∈ t := by
    intro i; cases i with
    | zero => exact htt a hat x hx
    | succ i => exact he' i
  obtain ⟨z,hz,hφ⟩ := hbound (cons x e') henv φ (by
    obtain ⟨y,hy,hφ⟩ := hy
    exact ⟨y,hy,(congr x y).mp hφ⟩)
  exact ⟨z,hz,(congr x z).mpr hφ⟩

def SigmaCollection (M : ZFSet.{u}) : Prop :=
  ∀ (φ : SigmaFormula) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) → ∀ a ∈ M,
    (∀ x ∈ a, ∃ y ∈ M, φ.Realize M (cons y (cons x e))) →
      ∃ W ∈ M, ∀ x ∈ a, ∃ y ∈ W, φ.Realize M (cons y (cons x e))

theorem sigma_collection (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) :
    SigmaCollection M := by
  intro φ e he a ha htotal
  obtain ⟨W,hW,hbound⟩ := internal_sigma_request_bound M hM hP hU hPow hS hR hI hAC φ e he ha
  exact ⟨W,hW,fun x hx => hbound x hx (htotal x hx)⟩

end TuringRigidity.BoundedSetTheory

end OAI

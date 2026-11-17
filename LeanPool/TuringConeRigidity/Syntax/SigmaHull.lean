/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.FragmentHull

/-!
# Sigma Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

def matrix : SigmaFormula → Formula
  | .bounded φ => φ
  | .existsSet φ => matrix φ

def prefixLength : SigmaFormula → ℕ
  | .bounded _ => 0
  | .existsSet φ => prefixLength φ+1

def feed : List ZFSet.{u} → (ℕ → ZFSet.{u}) → (ℕ → ZFSet.{u})
  | [],e => e
  | x::xs,e => feed xs (cons x e)

theorem feed_mem (xs : List ZFSet.{u}) (e : ℕ → ZFSet.{u}) (d : ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ d) (he : ∀ i, e i ∈ d) : ∀ i, feed xs e i ∈ d := by
  induction xs generalizing e with
  | nil => exact he
  | cons x xs ih =>
    have he' : ∀ i, cons x e i ∈ d := by
      intro i; cases i with
      | zero => exact hxs x List.mem_cons_self
      | succ i => exact he i
    exact ih (cons x e) (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) he'

theorem realize_iff_prefix (φ : SigmaFormula) (d : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    φ.Realize d e ↔ ∃ xs : List ZFSet.{u}, xs.length = φ.prefixLength ∧
      (∀ x ∈ xs, x ∈ d) ∧ φ.matrix.Realize d (feed xs e) := by
  induction φ generalizing e with
  | bounded φ =>
    constructor
    · intro h; exact ⟨[],rfl,by simp,h⟩
    · rintro ⟨xs,hlen,_,hφ⟩
      have heq : xs = [] := List.length_eq_zero_iff.mp hlen
      subst xs; exact hφ
  | existsSet φ ih =>
    constructor
    · rintro ⟨x,hx,hφ⟩
      obtain ⟨xs,hlen,hxs,hmat⟩ := (ih (cons x e)).mp hφ
      refine ⟨x::xs,congrArg Nat.succ hlen,?_,hmat⟩
      intro y hy; rcases List.mem_cons.mp hy with rfl|hy
      · exact hx
      · exact hxs y hy
    · rintro ⟨xs,hlen,hxs,hmat⟩
      cases xs with
      | nil => simp [prefixLength] at hlen
      | cons x xs =>
        refine ⟨x,hxs x List.mem_cons_self,(ih (cons x e)).mpr ?_⟩
        exact ⟨xs,Nat.succ.inj hlen,fun y hy => hxs y (List.mem_cons_of_mem _ hy),hmat⟩
end SigmaFormula
namespace FiniteTuple

noncomputable def elements : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x::xs => ({x} : ZFSet.{u}) ∪ elements xs

theorem mem_elements (x : ZFSet.{u}) (xs : List ZFSet.{u}) : x ∈ elements xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [elements]
  | cons y xs ih => simp only [elements,ZFSet.mem_union,ZFSet.mem_singleton,ih,List.mem_cons]

theorem elements_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ M) : elements xs ∈ M := by
  induction xs with
  | nil => exact h0
  | cons x xs ih =>
    exact binary_union_mem M hM hP hU
      (singleton_mem M hM hP (hxs x List.mem_cons_self))
      (ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)))

theorem internal_sigma_witness_hull (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {t x : ZFSet.{u}} (ht : t ∈ M) (hx : x ∈ M) (φ : SigmaFormula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ t) (hφ : φ.Realize M (cons x e)) :
    ∃ h ∈ M, t ⊆ h ∧ x ∈ h ∧ RelationCollapse.StructureExtensional h ∧
      φ.Realize h (cons x e) := by
  obtain ⟨xs,hlen,hxs,hmat⟩ := (φ.realize_iff_prefix M (cons x e)).mp hφ
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ (omega_mem M hM hS hI) _ ZFSet.omega_zero
  let s := t ∪ elements (x::xs)
  have hs : s ∈ M := binary_union_mem M hM hP hU ht
    (elements_mem M hM hP hU h0 (x::xs) (by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hxs y hy))
  have hts : t ⊆ s := fun _ hy => ZFSet.mem_union.mpr (Or.inl hy)
  have hxsS : ∀ y ∈ x::xs, y ∈ s :=
    fun y hy => ZFSet.mem_union.mpr (Or.inr ((mem_elements y (x::xs)).mpr hy))
  obtain ⟨d,hd,hdt,hsd⟩ := internal_transitive_container M hM hP hU hS hR hI hs
  have hsd' : s ⊆ d := fun y hy => hdt _ hsd y hy
  have henvS : ∀ i, cons x e i ∈ s := by
    intro i; cases i with
    | zero => exact hxsS x List.mem_cons_self
    | succ i => exact hts (he i)
  have hfeedS := SigmaFormula.feed_mem xs (cons x e) s
    (fun y hy => hxsS y (List.mem_cons_of_mem _ hy)) henvS
  have hfeedM : ∀ i, SigmaFormula.feed xs (cons x e) i ∈ M := fun i => hM s hs _ (hfeedS i)
  have hfeedD : ∀ i, SigmaFormula.feed xs (cons x e) i ∈ d := fun i => hsd' (hfeedS i)
  have hmatD : φ.matrix.Realize d (SigmaFormula.feed xs (cons x e)) :=
    (φ.matrix.absolute d hdt _ hfeedD).mpr ((φ.matrix.absolute M hM _ hfeedM).mp hmat)
  obtain ⟨h,hh,hsh,_,hext,htransfer⟩ :=
    internal_fragment_hull M hM hP hU hPow hS hR hI hAC hd hs hdt hsd' φ.matrix
  refine ⟨h,hh,fun y hy => hsh (hts hy),hsh (hxsS x List.mem_cons_self),hext,?_⟩
  apply (φ.realize_iff_prefix h (cons x e)).mpr
  exact ⟨xs,hlen,fun y hy => hsh (hxsS y (List.mem_cons_of_mem _ hy)),
    (htransfer _ (fun i => hsh (hfeedS i))).mpr hmatD⟩

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI

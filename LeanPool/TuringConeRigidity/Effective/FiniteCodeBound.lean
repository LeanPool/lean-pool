/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteCodeBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteExtensionCode

/-!
# Finite Code Bound
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTuple

/-- Finite codes generated from elements of `t`, the empty set, and unordered pairing. -/
inductive FiniteCode (t : ZFSet.{u}) : ZFSet.{u} → Prop
  | atom (x : ZFSet.{u}) (hx : x ∈ t) : FiniteCode t x
  | empty : FiniteCode t ∅
  | pair {x y : ZFSet.{u}} : FiniteCode t x → FiniteCode t y → FiniteCode t {x,y}

theorem FiniteCode.orderedPair {t x y : ZFSet.{u}} (hx : FiniteCode t x) (hy : FiniteCode t y) :
    FiniteCode t (ZFSet.pair x y) := by
  have hs : FiniteCode t ({x} : ZFSet.{u}) := by simpa using hx.pair hx
  exact hs.pair (hx.pair hy)

theorem FiniteCode.mem_model (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (h0 : (∅ : ZFSet.{u}) ∈ M) {t x : ZFSet.{u}} (ht : t ∈ M) (hx : FiniteCode t x) : x ∈ M := by
  induction hx with
  | atom x hx => exact hM t ht x hx
  | empty => exact h0
  | pair _ _ ihx ihy => exact pair_mem M hM hP ihx ihy

theorem transitive_union {a b : ZFSet.{u}} (ha : Transitive a) (hb : Transitive b) :
    Transitive (a ∪ b) := by
  intro x hx y hy
  rcases ZFSet.mem_union.mp hx with hx|hx
  · exact ZFSet.mem_union.mpr (Or.inl (ha x hx y hy))
  · exact ZFSet.mem_union.mpr (Or.inr (hb x hx y hy))

theorem transitive_adjoin {a z : ZFSet.{u}} (ha : Transitive a) (hz : z ⊆ a) :
    Transitive (a ∪ ({z} : ZFSet.{u})) := by
  intro x hx y hy
  rcases ZFSet.mem_union.mp hx with hx|hx
  · exact ZFSet.mem_union.mpr (Or.inl (ha x hx y hy))
  · obtain rfl := ZFSet.mem_singleton.mp hx
    exact ZFSet.mem_union.mpr (Or.inl (hz hy))

theorem FiniteCode.finite_transitive_extension (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (h0 : (∅ : ZFSet.{u}) ∈ M)
    {t x : ZFSet.{u}} (ht : t ∈ M) (htt : Transitive t) (hx : FiniteCode t x) :
    ∃ xs : List ZFSet.{u}, (∀ y ∈ xs, y ∈ M) ∧ x ∈ t ∪ elements xs ∧
      Transitive (t ∪ elements xs) := by
  induction hx with
  | atom x hx =>
    refine ⟨[],by simp,?_,?_⟩
    · exact ZFSet.mem_union.mpr (Or.inl hx)
    · have heq : t ∪ elements [] = t := by
        apply ZFSet.ext; intro z; simp [ZFSet.mem_union,elements]
      exact heq.symm ▸ htt
  | empty =>
    refine ⟨[∅],?_,?_,?_⟩
    · intro y hy; obtain rfl := List.mem_singleton.mp hy; exact h0
    · exact ZFSet.mem_union.mpr (Or.inr ((mem_elements _ _).mpr List.mem_cons_self))
    · have heq : t ∪ elements [∅] = t ∪ ({∅} : ZFSet.{u}) := by
        apply ZFSet.ext; intro z; simp [ZFSet.mem_union,elements]
      rw [heq]
      exact transitive_adjoin htt (by simp)
  | @pair x y hx hy ihx ihy =>
    obtain ⟨xs,hxs,hxxs,htxs⟩ := ihx
    obtain ⟨ys,hys,hyys,htys⟩ := ihy
    let zs := xs ++ ys
    have hb : t ∪ elements zs = (t ∪ elements xs) ∪ (t ∪ elements ys) := by
      apply ZFSet.ext; intro z
      simp only [ZFSet.mem_union,mem_elements,List.mem_append,zs]
      tauto
    have hbt : Transitive (t ∪ elements zs) := hb.symm ▸ transitive_union htxs htys
    have hxb : x ∈ t ∪ elements zs := hb.symm ▸ ZFSet.mem_union.mpr (Or.inl hxxs)
    have hyb : y ∈ t ∪ elements zs := hb.symm ▸ ZFSet.mem_union.mpr (Or.inr hyys)
    have hp : ({x,y} : ZFSet.{u}) ⊆ t ∪ elements zs := by
      intro z hz; rcases ZFSet.mem_pair.mp hz with rfl|rfl
      · exact hxb
      · exact hyb
    refine ⟨({x,y} : ZFSet.{u}) :: zs,?_,?_,?_⟩
    · intro z hz; rcases List.mem_cons.mp hz with rfl|hz
      · exact pair_mem M hM hP (hx.mem_model M hM hP h0 ht) (hy.mem_model M hM hP h0 ht)
      · rcases List.mem_append.mp hz with hz|hz
        · exact hxs z hz
        · exact hys z hz
    · exact ZFSet.mem_union.mpr (Or.inr ((mem_elements _ _).mpr List.mem_cons_self))
    · have heq : t ∪ elements (({x,y} : ZFSet.{u})::zs) =
          (t ∪ elements zs) ∪ ({({x,y} : ZFSet.{u})} : ZFSet.{u}) := by
        apply ZFSet.ext; intro z
        simp only [ZFSet.mem_union,mem_elements,List.mem_cons,ZFSet.mem_singleton]
        tauto
      rw [heq]
      exact transitive_adjoin hbt hp

theorem internal_finite_code_bound (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (ht : t ∈ M) (htt : Transitive t) :
    ∃ K ∈ M, ∀ x, FiniteCode t x → x ∈ K := by
  have hω := omega_mem M hM hS.bounded hI
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ hω _ ZFSet.omega_zero
  have hk := indexSpace_mem M hM hP hU hPow hS.bounded hω ht
  obtain ⟨K,hK,hbound⟩ := internal_small_transitive_bound M (indexSpace t) hM hP hU hPow hS hR hk
  refine ⟨K,hK,?_⟩
  intro x hx
  obtain ⟨xs,hxs,hxD,hDT⟩ := hx.finite_transitive_extension M hM hP h0 ht htt
  have hD := binary_union_mem M hM hP hU ht (elements_mem M hM hP hU h0 xs hxs)
  obtain ⟨f,hf,hfg⟩ := internal_finite_extension_injection M hM hP hU hPow hS.bounded hR hω ht xs
    hxs
  exact hbound _ hD hDT f hf (finiteIndex t xs) hfg
    (fun y _ => finiteIndex_mem t xs y) (finiteIndex_injective t xs) hxD

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI

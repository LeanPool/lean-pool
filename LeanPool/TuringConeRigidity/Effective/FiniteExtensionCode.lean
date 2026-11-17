/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteExtensionCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SigmaHull

/-!
# Finite Extension Code
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTuple

/-- The tagged union of the atom set and the natural-number indices. -/
noncomputable def indexSpace (t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod {natSet 0} t ∪ ZFSet.prod {natSet 1} ZFSet.omega

/-- Use a tagged atom when `x` belongs to `t`; otherwise use its tagged `List.idxOf` index in
`xs`. -/
noncomputable def finiteIndex (t : ZFSet.{u}) (xs : List ZFSet.{u}) (x : ZFSet.{u}) : ZFSet.{u} :=
  by
  classical
  exact if x ∈ t then ZFSet.pair (natSet 0) x else ZFSet.pair (natSet 1) (natSet (xs.idxOf x))

theorem indexSpace_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hω : ZFSet.omega.{u} ∈ M) {t : ZFSet.{u}} (ht : t ∈ M) : indexSpace t ∈ M := by
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact binary_union_mem M hM hP hU
    (product_mem M hM hP hU hPow hS (singleton_mem M hM hP (hn 0)) ht)
    (product_mem M hM hP hU hPow hS (singleton_mem M hM hP (hn 1)) hω)

theorem finiteIndex_mem (t : ZFSet.{u}) (xs : List ZFSet.{u}) (x : ZFSet.{u}) :
    finiteIndex t xs x ∈ indexSpace t := by
  classical
  unfold finiteIndex
  by_cases hx : x ∈ t
  · rw [ite_eq_left hx]
    exact ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_prod.mpr
      ⟨_,ZFSet.mem_singleton.mpr rfl,x,hx,rfl⟩))
  · rw [ite_eq_right hx]
    exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_prod.mpr
      ⟨_,ZFSet.mem_singleton.mpr rfl,_,(mem_omega _).mpr ⟨xs.idxOf x,rfl⟩,rfl⟩))

theorem finiteIndex_injective (t : ZFSet.{u}) (xs : List ZFSet.{u})
    (x : ZFSet.{u}) (hx : x ∈ t ∪ elements xs) (y : ZFSet.{u}) (_hy : y ∈ t ∪ elements xs)
    (he : finiteIndex t xs x = finiteIndex t xs y) : x = y := by
  classical
  unfold finiteIndex at he
  by_cases hxt : x ∈ t <;> by_cases hyt : y ∈ t
  · rw [ite_eq_left hxt,ite_eq_left hyt] at he
    exact (ZFSet.pair_inj.mp he).2
  · rw [ite_eq_left hxt,ite_eq_right hyt] at he
    have hf := natSet_injective (ZFSet.pair_inj.mp he).1
    omega
  · rw [ite_eq_right hxt,ite_eq_left hyt] at he
    have hf := natSet_injective (ZFSet.pair_inj.mp he).1
    omega
  · rw [ite_eq_right hxt,ite_eq_right hyt] at he
    have hidx := natSet_injective (ZFSet.pair_inj.mp he).2
    have hxl : x ∈ xs := (mem_elements x xs).mp ((ZFSet.mem_union.mp hx).resolve_left hxt)
    exact (List.idxOf_inj hxl).mp hidx

theorem internal_finite_extension_injection (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hω : ZFSet.omega.{u} ∈ M)
    {t : ZFSet.{u}} (ht : t ∈ M) (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ M) :
    ∃ f ∈ M, Presents (t ∪ elements xs) f (finiteIndex t xs) := by
  classical
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  have hk := indexSpace_mem M hM hP hU hPow hS hω ht
  let j := finiteIndex t xs
  have hj (x : ZFSet.{u}) : j x ∈ M := hM _ hk _ (finiteIndex_mem t xs x)
  let φ : Formula := .existsMem 2 (.conj (.orderedPair 1 2 0) (.orderedPair 0 4 2))
  let e := cons (indexSpace t) (fun _ => natSet 0)
  have he : ∀ i, e i ∈ M := by intro i; cases i with
    | zero => exact hk
    | succ => exact hn 0
  obtain ⟨b,hb,hbdef⟩ := replacement_image M hM hR (.bounded φ) e he ht
    (fun x => ZFSet.pair x (ZFSet.pair (natSet 0) x))
    (fun x hx => orderedPair_mem M hM hP (hM t ht x hx)
      (orderedPair_mem M hM hP (hn 0) (hM t ht x hx))) (by
      intro x hx y hy
      change φ.Realize M (cons y (cons x e)) ↔ _
      rw [Formula.absolute _ M hM _ (by
        intro i
        rcases i with _ | i
        · exact hy
        rcases i with _ | i
        · exact hM t ht x hx
        exact he i)]
      simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
      constructor
      · rintro ⟨v,_,hy,rfl⟩; exact hy
      · intro hy
        have hjx := finiteIndex_mem t xs x
        rw [finiteIndex,ite_eq_left hx] at hjx
        exact ⟨_,hjx,hy,rfl⟩)
  let f := b ∪ elements (xs.map (fun x => ZFSet.pair x (j x)))
  have hf : f ∈ M := binary_union_mem M hM hP hU hb
    (elements_mem M hM hP hU (hn 0) _ (by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
      exact orderedPair_mem M hM hP (hxs x hx) (hj x)))
  refine ⟨f,hf,?_⟩
  intro z
  change z ∈ b ∪ elements (xs.map (fun x => ZFSet.pair x (j x))) ↔ _
  rw [ZFSet.mem_union,hbdef,mem_elements,List.mem_map]
  constructor
  · rintro (⟨x,hx,rfl⟩|⟨x,hx,rfl⟩)
    · refine ⟨x,ZFSet.mem_union.mpr (Or.inl hx),?_⟩
      simp only [finiteIndex,ite_eq_left hx]
    · exact ⟨x,ZFSet.mem_union.mpr (Or.inr ((mem_elements x xs).mpr hx)),rfl⟩
  · rintro ⟨x,hx,rfl⟩
    rcases ZFSet.mem_union.mp hx with hx|hx
    · apply Or.inl
      exact ⟨x,hx,by simp only [finiteIndex,ite_eq_left hx]⟩
    · exact Or.inr ⟨x,(mem_elements x xs).mp hx,rfl⟩

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI

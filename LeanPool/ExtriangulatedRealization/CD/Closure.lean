/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Subcategory
public import LeanPool.ExtriangulatedRealization.Categories.Mat

/-!
# Closure properties of `C_J` and smallness of `C(D)` (Corollary 2.4)

`C_J` is closed under isomorphisms, finite direct sums and extensions: the middle term of a
realization has `ρ`-image an extension of good representations, hence good. `C(D)` is
essentially small: every object is isomorphic to one indexed by some `Fin n`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

attribute [local instance] HasExt.standard

/-- The middle term of a realization between objects with labels in `J` has labels in `J`. -/
lemma labelsIn_of_realizes {J : Set I} {A B C : CD D} {δ : (cdData D).Ext C A} {x : A ⟶ B}
    {y : B ⟶ C} (h : (cdData D).Realizes δ x y) (hA : labelsIn D J A) (hC : labelsIn D J C) :
    labelsIn D J B := by
  obtain ⟨w, ⟨hS, -⟩, -⟩ := h
  let E := objIdx D A ∪ objIdx D C
  refine labelsIn_of_isGood D E (fun e he => ?_) ?_
  · rcases Finset.mem_union.mp he with h | h
    exacts [mem_of_mem_objIdx D hA h, mem_of_mem_objIdx D hC h]
  · exact IsGood.of_shortExact E hS (isGood_rho D E A (labelIn_objIdx D A Finset.subset_union_left))
      (isGood_rho D E C (labelIn_objIdx D C Finset.subset_union_right))

/-- `C_J` is extension-closed. -/
lemma subcatJ_isExtensionClosed (J : Set I) : (cdData D).IsExtensionClosed (subcatJ D J) := by
  intro A B C δ x y h hA hC
  exact labelsIn_of_realizes D h hA hC

/-- `C_J` is closed under binary direct sums. -/
lemma labelsIn_biprod {J : Set I} {A C : CD D} (hA : labelsIn D J A) (hC : labelsIn D J C) :
    labelsIn D J (A ⊞ C) := by
  let E := objIdx D A ∪ objIdx D C
  refine labelsIn_of_isGood D E (fun e he => ?_) ?_
  · rcases Finset.mem_union.mp he with h | h
    exacts [mem_of_mem_objIdx D hA h, mem_of_mem_objIdx D hC h]
  · let := preservesBinaryBiproduct_of_preservesBiproduct (rho D) A C
    exact IsGood.of_iso ((rho D).mapBiprod A C).symm (IsGood.biprod
      (isGood_rho D E A (labelIn_objIdx D A Finset.subset_union_left))
      (isGood_rho D E C (labelIn_objIdx D C Finset.subset_union_right)))

/-! ### Smallness -/

instance essentiallySmall_CD : EssentiallySmall.{u} (CD D) := by
  rw [essentiallySmall_iff]
  refine ⟨?_, inferInstance⟩
  let f : (Σ n : ℕ, Fin n → IndCat D) → Skeleton (CD D) :=
    fun p => toSkeleton (⟨Fin p.1, p.2⟩ : CD D)
  refine small_of_surjective (f := f) fun s => ?_
  let M : CD D := s.out
  let e := Fintype.equivFin M.ι
  refine ⟨⟨_, fun j => M.X (e.symm j)⟩, ?_⟩
  change toSkeleton _ = s
  rw [← Quotient.out_eq s]
  exact Quotient.sound ⟨(Mat_.isoReindex M e).symm⟩

end ExtriangulatedRealization

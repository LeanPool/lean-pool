/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.Compact

/-!
# Gluing two compatible homeomorphisms

The comparison of caps in XII (3.1), page 245, glues a map of the
original surface to a map of the added disc. Agreement on their
intersection gives continuity. The intersection condition gives
injectivity, and the two target pieces give surjectivity.
-/

public section

namespace GraphMinor.GM12

open Set Topology

/-- Compatible homeomorphisms of two closed pieces glue to a
homeomorphism of compact Hausdorff spaces. -/
theorem exists_homeomorph_of_two_closed_pieces
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [CompactSpace S] [T2Space T]
    {A B : Set S} {A' B' : Set T} (hA : IsClosed A) (hB : IsClosed B)
    (hcover : A ∪ B = univ) (hcover' : A' ∪ B' = univ)
    (f : A ≃ₜ A') (g : B ≃ₜ B')
    (hcross : ∀ x : A, (f x).val ∈ B' ↔ x.val ∈ B)
    (hagree : ∀ (x : A) (hx : x.val ∈ B), (f x).val = (g ⟨x.val, hx⟩).val) :
    ∃ H : S ≃ₜ T, (∀ x : A, H x.val = (f x).val) ∧
      ∀ x : B, H x.val = (g x).val := by
  classical
  have hmem : ∀ x, x ∈ A ∨ x ∈ B := by
    intro x
    change x ∈ A ∪ B
    rw [hcover]
    trivial
  let F : S → T := fun x => if hx : x ∈ A then (f ⟨x, hx⟩).val
    else (g ⟨x, (hmem x).resolve_left hx⟩).val
  have hFA : ∀ x : A, F x.val = (f x).val := fun x => by simp only [F, dite_eq_left x.property]
  have hFB : ∀ x : B, F x.val = (g x).val := by
    intro x
    by_cases hx : x.val ∈ A
    · exact (hFA ⟨x.val, hx⟩).trans (hagree ⟨x.val, hx⟩ x.property)
    · simp only [F, dite_eq_right hx]
  have hFcA : ContinuousOn F A := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : A => F x.val)
    have heq : (fun x : A => F x.val) = fun x => (f x).val := funext hFA
    rw [heq]
    exact continuous_subtype_val.comp f.continuous
  have hFcB : ContinuousOn F B := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : B => F x.val)
    have heq : (fun x : B => F x.val) = fun x => (g x).val := funext hFB
    rw [heq]
    exact continuous_subtype_val.comp g.continuous
  have hFc : Continuous F := by
    have hc := hFcA.union_of_isClosed hFcB hA hB
    rw [hcover] at hc
    exact continuousOn_univ.mp hc
  have hinjA : ∀ (x : A) (y : S), F x.val = F y → x.val = y := by
    intro x y he
    by_cases hy : y ∈ A
    · rw [hFA x, hFA ⟨y, hy⟩] at he
      exact congrArg Subtype.val (f.injective (Subtype.ext he))
    · have hyB := (hmem y).resolve_left hy
      rw [hFA x, hFB ⟨y, hyB⟩] at he
      have hxB := (hcross x).mp (he ▸ (g ⟨y, hyB⟩).property)
      have hg : (g ⟨x.val, hxB⟩).val = (g ⟨y, hyB⟩).val :=
        (hagree x hxB).symm.trans he
      exact congrArg Subtype.val (g.injective (Subtype.ext hg))
  have hi : Function.Injective F := by
    intro x y he
    by_cases hx : x ∈ A
    · exact hinjA ⟨x, hx⟩ y he
    · by_cases hy : y ∈ A
      · exact (hinjA ⟨y, hy⟩ x he.symm).symm
      · rw [hFB ⟨x, (hmem x).resolve_left hx⟩, hFB ⟨y, (hmem y).resolve_left hy⟩] at he
        exact congrArg Subtype.val (g.injective (Subtype.ext he))
  have hs : Function.Surjective F := by
    intro y
    have hy : y ∈ A' ∪ B' := hcover'.symm ▸ mem_univ y
    rcases hy with hy | hy
    · refine ⟨(f.symm ⟨y, hy⟩).val, ?_⟩
      rw [hFA]
      exact congrArg Subtype.val (f.apply_symm_apply ⟨y, hy⟩)
    · refine ⟨(g.symm ⟨y, hy⟩).val, ?_⟩
      rw [hFB]
      exact congrArg Subtype.val (g.apply_symm_apply ⟨y, hy⟩)
  exact ⟨hFc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hi, hs⟩), hFA, hFB⟩

end GraphMinor.GM12

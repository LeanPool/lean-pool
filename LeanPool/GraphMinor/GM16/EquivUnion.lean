/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Set.UnionLift

/-!
# Gluing compatible equivalences on unions

Local equivalences glue when their forward maps agree on source
intersections and their inverses agree on target intersections.
Glue both maps and check they are inverse on a piece containing
the point. This is used for the vertex and edge isomorphisms of
the union of the subdivision paths in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set
universe u v w

/-- Compatible local equivalences and their compatible inverses give
an equivalence of the unions, with the stated restriction on every piece. -/
theorem exists_equiv_iUnion {α : Type u} {β : Type v} {ι : Type w}
    (S : ι → Set α) (T : ι → Set β) (φ : ∀ i, S i ≃ T i)
    (hForward : ∀ i j x (hxi : x ∈ S i) (hxj : x ∈ S j),
      (φ i ⟨x, hxi⟩).val = (φ j ⟨x, hxj⟩).val)
    (hBackward : ∀ i j y (hyi : y ∈ T i) (hyj : y ∈ T j),
      ((φ i).symm ⟨y, hyi⟩).val = ((φ j).symm ⟨y, hyj⟩).val) :
    ∃ Φ : (⋃ i, S i) ≃ (⋃ i, T i), ∀ i (x : S i),
      (Φ ⟨x.val,mem_iUnion_of_mem i x.property⟩).val = (φ i x).val := by
  let f (i : ι) (x : S i) : β := (φ i x).val
  let g (i : ι) (y : T i) : α := ((φ i).symm y).val
  let F := iUnionLift S f hForward (⋃ i, S i) subset_rfl
  let G := iUnionLift T g hBackward (⋃ i, T i) subset_rfl
  have hFSpec (x : ⋃ i, S i) (i : ι) (hx : x.val ∈ S i) :
      F x = (φ i ⟨x.val,hx⟩).val :=
    iUnionLift_of_mem (f := f) (hf := hForward) (hT := subset_rfl) x hx
  have hGSpec (y : ⋃ i, T i) (i : ι) (hy : y.val ∈ T i) :
      G y = ((φ i).symm ⟨y.val,hy⟩).val :=
    iUnionLift_of_mem (f := g) (hf := hBackward) (hT := subset_rfl) y hy
  have hFR (x : ⋃ i, S i) : F x ∈ ⋃ i, T i := by
    obtain ⟨i,hxi⟩ := mem_iUnion.mp x.property
    rw [hFSpec x i hxi]
    exact mem_iUnion_of_mem i (φ i ⟨x.val,hxi⟩).property
  have hGR (y : ⋃ i, T i) : G y ∈ ⋃ i, S i := by
    obtain ⟨i,hyi⟩ := mem_iUnion.mp y.property
    rw [hGSpec y i hyi]
    exact mem_iUnion_of_mem i ((φ i).symm ⟨y.val,hyi⟩).property
  let fv (x : ⋃ i, S i) : (⋃ i, T i) := ⟨F x,hFR x⟩
  let gv (y : ⋃ i, T i) : (⋃ i, S i) := ⟨G y,hGR y⟩
  have hLeft : Function.LeftInverse gv fv := by
    intro x
    obtain ⟨i,hxi⟩ := mem_iUnion.mp x.property
    have hF : (fv x).val = (φ i ⟨x.val,hxi⟩).val := hFSpec x i hxi
    have hyi : (fv x).val ∈ T i := hF.symm ▸ (φ i ⟨x.val,hxi⟩).property
    have he : (⟨(fv x).val,hyi⟩ : T i) = φ i ⟨x.val,hxi⟩ := Subtype.ext hF
    apply Subtype.ext
    change G (fv x) = x.val
    rw [hGSpec (fv x) i hyi]
    rw [he,Equiv.symm_apply_apply]
  have hRight : Function.RightInverse gv fv := by
    intro y
    obtain ⟨i,hyi⟩ := mem_iUnion.mp y.property
    have hG : (gv y).val = ((φ i).symm ⟨y.val,hyi⟩).val := hGSpec y i hyi
    have hxi : (gv y).val ∈ S i := hG.symm ▸ ((φ i).symm ⟨y.val,hyi⟩).property
    have he : (⟨(gv y).val,hxi⟩ : S i) = (φ i).symm ⟨y.val,hyi⟩ := Subtype.ext hG
    apply Subtype.ext
    change F (gv y) = y.val
    rw [hFSpec (gv y) i hxi]
    rw [he,Equiv.apply_symm_apply]
  refine ⟨⟨fv,gv,hLeft,hRight⟩,?_⟩
  intro i x
  exact hFSpec ⟨x.val,mem_iUnion_of_mem i x.property⟩ i x.property

end GraphMinor.GM16

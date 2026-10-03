/-
Copyright (c) 2019 Jesse Michael Han and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Michael Han, Floris van Doorn, and Flypitch4 contributors
-/

module

/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file
LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/compactness.lean -/

public import LeanPool.NFWeakPartition.Flypitch4.Fol
public import Mathlib.Data.Finset.Image

/-! NF weak partition development: Flypitch4.Compactness. -/


public section

namespace NFChoice

open NFChoice.Set

namespace Fol

universe u v

variable {L : Language.{u}}

/-! ## list_except -/


/-- Given a list xs, an element x, and a set T such that
everything in xs which is not x is in T,
return the sublist excluding x, a proof it's a subset of T, and a
proof none of its
elements equal x. -/
@[expose]
def list_except {α : Type u} [DecidableEq α] (xs : List α) (x : α) (T : Set α)
    (h : ∀ y ∈ xs, y ≠ x → y ∈ T) :
    Σ' ys : List α, ({ϕ | ϕ ∈ ys} ⊆ T ∧ (∀ y ∈ ys, y ≠ x)) ∧ (∀ y ∈ xs, y ≠ x → y ∈ ys) :=
  ⟨xs.filter (fun y => decide (y ≠ x)),
    ⟨fun _ hy => by
      simp only [Set.mem_ofPred, List.mem_filter] at hy
      exact h _ hy.1 (of_decide_eq_true hy.2), fun _ hy =>
      by
      simp only [List.mem_filter] at hy
      exact of_decide_eq_true hy.2⟩,
    fun _ hy hxy => by
    simp only [List.mem_filter]
    exact ⟨hy, decide_eq_true hxy⟩⟩

/-! ## image_lift -/


/-- Given x ∈ f '' S, choose a lift x' in the preimage of x. -/
@[expose]
noncomputable def image_lift {α : Type u} {β : Type v} {f : α → β} {S : Set α} (x : β)
    (hx : x ∈ f '' S) : Σ' (x' : α), x' ∈ S ∧ f x' = x :=
  ⟨hx.choose, hx.choose_spec.1, hx.choose_spec.2⟩

/-- Given a list xs, a set S, and a proof that {x | x ∈ xs} ⊆ f
'' S, return a list of
lifts ys ⊆ S such that f '' {y | y ∈ ys} = {x | x ∈ xs}. -/
@[expose]
noncomputable def image_lift_list {α : Type u} {β : Type v} {f : α → β} {S : Set α}
    {xs : List β} (h_sub : {x | x ∈ xs} ⊆ f '' S) :
    Σ' (ys : List α), ({y' | y' ∈ ys} ⊆ S) ∧ f '' {y | y ∈ ys} = {x | x ∈ xs} :=
  by
  have h_sub' : NFChoice.List.toSet xs ⊆ f '' S := h_sub
  have ex := List.exists_of_toSet_subset_image h_sub'
  refine ⟨ex.choose, fun _ hy => ex.choose_spec.1 hy, ?_⟩
  have hmap : ex.choose.map f = xs := ex.choose_spec.2
  ext b
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : f a ∈ (ex.choose.map f) := List.mem_map_of_mem ha
    rwa [hmap] at this
  · intro hb
    rw [← hmap] at hb
    rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/-! ## proof_compactness -/


/-- Any proof from a set of formulas is provable from a finite
subset. -/
lemma proof_compactness {ψ : formula L} {T : Set (formula L)} :
    (T ⊢' ψ) → ∃ Γ : Finset (formula L), (↑Γ : Set (formula L)) ⊢' ψ ∧ ↑Γ ⊆ T :=
  by
  have : DecidableEq (formula L) := fun x y => Classical.propDecidable _
  intro ⟨P⟩
  induction P with
  | axm h =>
    rename_i _ A₀
    exact ⟨{ A₀ }, ⟨prf.axm (by simp)⟩, by simp [h]⟩
  | impI _ ih =>
    obtain ⟨Γ, H, K⟩ := ih
    rename_i _ A₀ _ _
    refine ⟨Γ \ { A₀ }, impI' (weakening' ?_ H), ?_⟩
    · simp only [Finset.coe_sdiff, Finset.coe_singleton]
      exact Set.subset_insert_sdiff_singleton A₀ ↑Γ
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton] at hx
      rcases K (Finset.mem_coe.mpr hx.1) with rfl | h
      · exact absurd rfl hx.2
      · exact h
  | impE _ _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, H₁, K₁⟩ := ih₁
    obtain ⟨Γ₂, H₂, K₂⟩ := ih₂
    refine ⟨Γ₁ ∪ Γ₂, ?_, ?_⟩
    · apply impE' _
      · exact weakening' (by simp only [Finset.coe_union]; exact Set.subset_union_left) H₁
      · exact
          weakening' (by simp only [Finset.coe_union]; exact Set.subset_union_right) H₂
    · simp only [Finset.coe_union]; exact Set.union_subset K₁ K₂
  | falsumE _ ih =>
    obtain ⟨Γ, H, K⟩ := ih
    rename_i _ A₀ _
    refine ⟨Γ \ {∼A₀}, falsumE' (weakening' ?_ H), ?_⟩
    · simp only [Finset.coe_sdiff, Finset.coe_singleton]
      exact Set.subset_insert_sdiff_singleton (∼A₀) ↑Γ
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton] at hx
      rcases K (Finset.mem_coe.mpr hx.1) with rfl | h
      · exact absurd rfl hx.2
      · exact h
  | allI _ ih =>
    obtain ⟨Γ, H, K⟩ := ih
    rw [Finset.subset_set_image_iff] at K
    obtain ⟨Γ', K', hΓ⟩ := K
    subst hΓ
    rw [Finset.coe_image] at H
    exact ⟨Γ', allI' H, K'⟩
  | allE₂ _ _ _ ih =>
    obtain ⟨Γ, H, K⟩ := ih
    exact ⟨Γ, allE₂' H, K⟩
  | ref => exact ⟨∅, ref' _ _, by simp⟩
  | subst₂ _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, H₁, K₁⟩ := ih₁
    obtain ⟨Γ₂, H₂, K₂⟩ := ih₂
    refine ⟨Γ₁ ∪ Γ₂, ?_, ?_⟩
    · apply subst₂' _ _ _
      · exact weakening' (by simp only [Finset.coe_union]; exact Set.subset_union_left) H₁
      · exact
          weakening' (by simp only [Finset.coe_union]; exact Set.subset_union_right) H₂
    · simp only [Finset.coe_union]; exact Set.union_subset K₁ K₂

/-- Any proof from a sentence theory is provable from a finite
sub-theory. -/
lemma theory_proof_compactness {T : SentTheory L} {ψ : sentence L} (hψ : T ⊢ₛ' ψ) :
    ∃ Γ : Finset (sentence L), (SentTheory.sprovable (↑Γ) ψ) ∧ (↑Γ : SentTheory L) ⊆ T :=
  by
  have : DecidableEq (sentence L) := fun x y => Classical.propDecidable _
  have : DecidableEq (formula L) := fun x y => Classical.propDecidable _
  rcases proof_compactness hψ with ⟨Γ, H, K⟩
  rw [Finset.subset_set_image_iff] at K
  obtain ⟨Γ', K', hΓ⟩ := K
  subst hΓ
  rw [Finset.coe_image] at H
  exact ⟨Γ', H, K'⟩

lemma theory_proof_compactness_iff {T : SentTheory L} {ψ : sentence L} :
    (T ⊢ₛ' ψ) ↔
      ∃ Γ : Finset (sentence L),
        (SentTheory.sprovable (↑Γ) ψ) ∧ (↑Γ : SentTheory L) ⊆ T :=
  ⟨theory_proof_compactness, fun ⟨_Γ, H, K⟩ => weakening' (Set.image_mono K) H⟩

/-! ## sprf_by_cases -/


/-- Sentence-level by-cases principle (wrapper for prf_by_cases).
-/
lemma sprf_by_cases {T : SentTheory L} (f₁ : sentence L) {f₂ : sentence L}
    (H₁ : SentTheory.sprovable (insert f₁ T) f₂)
    (H₂ : SentTheory.sprovable (insert (bd_not f₁) T) f₂) : SentTheory.sprovable T f₂ :=
  by
  simp only [SentTheory.sprovable, SentTheory.fst, Set.image_insert_eq] at H₁ H₂ ⊢
  simp only [bd_not, bounded_preformula.fst] at H₂
  exact prf_by_cases f₁.fst H₁ H₂

/-! ## is_consistent_union -/


lemma is_consistent_union {T₁ T₂ : SentTheory L} (h₁ : T₁.is_consistent)
    (h₂ : ∀ ψ ∈ T₂, SentTheory.sprovable (insert (bd_not ψ) T₁) bd_falsum) :
    (T₁ ∪ T₂).is_consistent :=
  by
  have : DecidableEq (sentence L) := fun x y => Classical.propDecidable _
  have : DecidableEq (formula L) := fun x y => Classical.propDecidable _
  have lem :
    ∀ (T₀ : Finset (sentence L)), (↑T₀ : SentTheory L) ⊆ T₂ → (T₁ ∪ ↑T₀).is_consistent :=
    by
    apply Finset.induction
    · intro _
      simp only [Finset.coe_empty, Set.union_empty]
      exact h₁
    · intro ψ s _ ih hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      intro hT
      rw [Finset.coe_insert] at hT
      exact
        ih hs.2
          (sprf_by_cases ψ (show SentTheory.sprovable (insert ψ (T₁ ∪ ↑s)) bd_falsum from
              weakening' (by
                  simp only [SentTheory.fst, Set.image_insert_eq, Set.image_union]
                  intro x hx
                  simp only [Set.mem_union, Set.mem_insert_iff] at hx ⊢
                  rcases hx with hT₁ | (rfl | hs')
                  · exact Or.inr (Or.inl hT₁)
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr hs')) hT)
            (show SentTheory.sprovable (insert (bd_not ψ) (T₁ ∪ ↑s)) bd_falsum from weakening'
                (by
                  simp only [SentTheory.fst, Set.image_insert_eq, Set.image_union]
                  apply Set.insert_subset_insert
                  exact Set.subset_union_left) (h₂ _ hs.1)))
  intro h
  rcases proof_compactness h with ⟨Γ, hΓ, hΓ_sub⟩
  simp only [SentTheory.fst, Set.image_union] at hΓ_sub
  have : DecidablePred (· ∈ T₁.fst) := fun x => Classical.propDecidable _
  let Γ₂ := Γ.filter (· ∉ T₁.fst)
  have hΓ₂_sub : (↑Γ₂ : Set (formula L)) ⊆ T₂.fst :=
    by
    intro x hx
    simp only [Γ₂, Finset.coe_filter] at hx
    exact (hΓ_sub hx.1).resolve_left hx.2
  rw [Finset.subset_set_image_iff] at hΓ₂_sub
  obtain ⟨Γ₂', hΓ₂'_sub, hΓ₂'_img⟩ := hΓ₂_sub
  apply lem Γ₂' hΓ₂'_sub
  apply weakening' _ hΓ
  simp only [SentTheory.fst, Set.image_union]
  intro x hx
  by_cases hmem : x ∈ T₁.fst
  · exact Set.mem_union_left _ hmem
  · have hx_in_Γ₂ : x ∈ (↑Γ₂ : Set (formula L)) :=
      by
      simp only [Γ₂, Finset.coe_filter]
      exact ⟨Finset.mem_coe.mp hx, hmem⟩
    rw [← hΓ₂'_img] at hx_in_Γ₂
    exact Set.mem_union_right _ (by simpa [Finset.coe_image] using hx_in_Γ₂)

end Fol

end NFChoice

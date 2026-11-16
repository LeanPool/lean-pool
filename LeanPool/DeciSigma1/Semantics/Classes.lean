/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Automata.Basic
public import LeanPool.DeciSigma1.Semantics.Tree
import Mathlib.Data.Set.Finite.List
import Mathlib.Basic.Finite.Prod

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Regular languages of paths and regular trees

A language of paths is regular when it has finitely many residuals. Regular languages are closed
under finite unions and concatenation, and the languages recognized by finite automata and the
finite languages are regular. These closure properties show that the leaf cones of the hull of
finitely many seeds are regular.

For trees over `{⊥, f, ⊤}`, regularity means having finitely many distinct subtrees.
The module defines the subtree set and proves that every finite tree is regular.

## Main declarations

- `Language`, `IsRegular`: sets of words with finitely many residuals.
- `isRegular_dfa`, `isRegular_union`, `isRegular_concat`, `isRegular_finite`: closure properties.
- `Characterization.subtrees`: the distinct subtrees of a tree.
- `Characterization.subtrees_finite_of_dom_finite`: finite trees are regular.
-/

@[expose] public section


namespace DeciSigma1.Semantics

open DeciSigma1.Automata
variable {n : ℕ}

/-- Languages of words over `Fin n`. -/
abbrev Language (n : ℕ) := Set (List (Fin n))
/-- The concatenation of two languages. -/
def concat (A B : Language n) : Language n := {w | ∃ a ∈ A, ∃ b ∈ B, a ++ b = w}
/-- The residual `u⁻¹ L` of a language. -/
abbrev residual (L : Language n) (u : List (Fin n)) : Language n := {v | u ++ v ∈ L}
/-- A regular language: finitely many residuals. -/
def IsRegular (L : Language n) : Prop := (Set.range (residual L)).Finite

theorem residual_append (L : Language n) (u v : List (Fin n)) :
    residual L (u ++ v) = residual (residual L u) v := by
  ext w; simp [residual, List.append_assoc]

theorem isRegular_of_closed {F : Set (Language n)} (hf : F.Finite) {L : Language n}
    (hl : L ∈ F) (hc : ∀ A ∈ F, ∀ c, residual A [c] ∈ F) : IsRegular L := by
  apply hf.subset
  rintro _ ⟨u,rfl⟩
  induction u using List.reverseRecOn with
  | nil => exact hl
  | append_singleton u c ih => rw [residual_append]; exact hc _ ih c

/-- A language recognized by a finite automaton is regular: its residuals are determined by the
reached states. -/
theorem isRegular_dfa {S : Type*} [Finite S] (M : Semiautomaton (Fin n) S) (F : Set S) :
    IsRegular {w | M.run w ∈ F} := by
  apply (Set.finite_range (fun q => {v | runFrom M.step q v ∈ F})).subset
  rintro _ ⟨u,rfl⟩
  exact ⟨M.run u, by ext v; simp [residual, Semiautomaton.run, runFrom_append]⟩

/-- The union of two regular languages is regular. -/
theorem isRegular_union {A B : Language n} (ha : IsRegular A) (hb : IsRegular B) :
    IsRegular (A ∪ B) := by
  apply (ha.image2 (· ∪ ·) hb).subset
  rintro _ ⟨u,rfl⟩
  exact ⟨residual A u, ⟨u,rfl⟩, residual B u, ⟨u,rfl⟩, rfl⟩

theorem isRegular_empty : IsRegular (∅ : Language n) := by
  have he : Set.range (residual (∅ : Language n)) = {∅} := by ext L; simp [residual, eq_comm]
  rw [IsRegular, he]; exact Set.finite_singleton _

/-- The language of all paths is regular. -/
theorem isRegular_univ : IsRegular (Set.univ : Language n) := by
  apply (Set.finite_singleton (Set.univ : Language n)).subset
  rintro _ ⟨u, rfl⟩
  ext v; simp [residual]

theorem isRegular_sUnion {F : Set (Language n)} (hf : F.Finite) (h : ∀ L ∈ F, IsRegular L) :
    IsRegular (⋃₀ F) := by
  induction F, hf using Set.Finite.induction_on with
  | empty => simpa using (isRegular_empty (n := n))
  | @insert L F hn hf ih =>
    rw [Set.sUnion_insert]
    exact isRegular_union (h L (by simp)) (ih (fun A hA => h A (by simp [hA])))

/-- Finite languages are regular. -/
theorem isRegular_finite {L : Language n} (hf : L.Finite) : IsRegular L := by
  let R : Language n := ⋃ w ∈ L, {v | v.IsSuffix w}
  have hR : R.Finite := hf.biUnion fun w _ => by
    apply (List.finite_length_le (Fin n) w.length).subset
    exact fun _ hv => hv.length_le
  apply (hR.powerset).subset
  rintro _ ⟨u,rfl⟩ v hv
  exact Set.mem_iUnion.mpr ⟨u ++ v, Set.mem_iUnion.mpr ⟨hv, u, rfl⟩⟩

/-- The residual of a concatenation by one letter. -/
theorem residual_mul (A B : Language n) (c : Fin n) :
    residual (concat A B) [c] =
      concat (residual A [c]) B ∪
        {v | [] ∈ A ∧ c :: v ∈ B} := by
  classical
  ext v
  constructor
  · rintro ⟨a, ha, b, hb, he⟩
    cases a with
    | nil =>
      right
      simp only [List.nil_append] at he
      subst b
      exact ⟨ha, hb⟩
    | cons d a =>
      have he' := List.cons.inj he
      obtain ⟨rfl, rfl⟩ := he'
      exact Or.inl ⟨a, ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | h)
    · exact ⟨c :: a, ha, b, hb, rfl⟩
    · exact ⟨[], h.1, c :: v, h.2, rfl⟩

/-- The concatenation of two regular languages is regular: each residual of `concat A B` is
determined by a residual of `A` and a set of residuals of `B`. -/
theorem isRegular_concat {A B : Language n} (ha : IsRegular A) (hb : IsRegular B) :
    IsRegular (concat A B) := by
  classical
  let R := Set.range (residual B)
  let F : Set (Language n) := Set.image2 (fun a T =>
    concat a B ∪ ⋃₀ T) (Set.range (residual A)) (𝒫 R)
  apply isRegular_of_closed (ha.image2 _ hb.powerset) (F := F)
  · exact ⟨A, ⟨[], rfl⟩, ∅, Set.empty_subset _, by simp⟩
  · rintro L ⟨a, ⟨u,rfl⟩, T, hT, rfl⟩ c
    let T' : Set (Language n) := (fun l => residual l [c]) '' T ∪
      (if [] ∈ residual A u then {residual B [c]} else ∅)
    refine ⟨residual A (u ++ [c]), ⟨u ++ [c],rfl⟩, T', ?_, ?_⟩
    · rintro L (⟨l,hl,rfl⟩ | hl)
      · obtain ⟨v,rfl⟩ := hT hl
        exact ⟨v ++ [c], residual_append _ _ _⟩
      · by_cases he : [] ∈ residual A u
        · simp only [he, ite_true, Set.mem_singleton_iff] at hl
          exact hl ▸ ⟨[c], rfl⟩
        · simp [he] at hl
    · rw [residual_append]
      have hq : residual ((concat (residual A u) B ∪ ⋃₀ T)) [c] =
          residual (concat (residual A u) B) [c] ∪
            ⋃₀ ((fun l => residual l [c]) '' T) := by
        ext v; simp [residual]
      rw [hq, residual_mul]
      dsimp only [T']
      rw [Set.sUnion_union]
      ext v
      by_cases he : [] ∈ residual A u <;> simp [he, or_assoc, or_left_comm, or_comm]

end DeciSigma1.Semantics

namespace DeciSigma1.Semantics.Characterization
open DeciSigma1.Semantics.Tree

variable {n : ℕ}

/-! ## Finite and regular trees over `{⊥, f, ⊤}` -/

/-- The domain of a tree: the paths it labels. -/
def domain (t : Tree n) : Set (List (Fin n)) := {π | (t.fn π).isSome}

theorem dom_toTree_finite (s : FTree n) : (domain s.toTree).Finite := by
  induction s with
  | bot =>
    apply (Set.finite_singleton ([] : List (Fin n))).subset
    intro π h
    cases π with
    | nil => rfl
    | cons i π => simp [domain] at h
  | top =>
    apply (Set.finite_singleton ([] : List (Fin n))).subset
    intro π h
    cases π with
    | nil => rfl
    | cons i π => simp [domain] at h
  | node a ih =>
    apply ((Set.finite_singleton ([] : List (Fin n))).union
      (Set.finite_iUnion (fun i => (ih i).image (List.cons i)))).subset
    intro π h
    cases π with
    | nil => exact Or.inl rfl
    | cons i π =>
      refine Or.inr (Set.mem_iUnion.mpr ⟨i, π, ?_, rfl⟩)
      simpa [domain] using h

/-- The set of subtrees of a tree. -/
def subtrees (t : Tree n) : Set (Tree n) := {u | ∃ π, t.subtree π = some u}

theorem subtree_nil (t : Tree n) : t.subtree [] = some t := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
    ((subtree_isSome_iff t []).mpr t.root_isSome)
  rw [hv]
  congr 1
  apply Tree.ext; funext ρ
  rw [subtree_fn hv ρ]; rfl

/-- Finite trees are regular. -/
theorem subtrees_finite_of_dom_finite (t : Tree n) (h : (domain t).Finite) :
    (subtrees t).Finite := by
  apply (h.image (fun π => (t.subtree π).getD t)).subset
  rintro u ⟨π, hπ⟩
  refine ⟨π, ?_, by simp [hπ]⟩
  change (t.fn π).isSome
  exact (subtree_isSome_iff t π).mp (by simp [hπ])

end DeciSigma1.Semantics.Characterization

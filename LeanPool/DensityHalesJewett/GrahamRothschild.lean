/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.Canonization
public import LeanPool.DensityHalesJewett.FiniteUnions

/-!
# The Graham--Rothschild theorem for combinatorial lines

The finite-unions focusing argument, block canonization, and the line-colouring form of the
Graham--Rothschild theorem needed by the density proof.

The support canonization lemma `Canonization.exists_canonical_of_le` reduces the colour of a line of
a large subspace to the support of its parameter word, and `FiniteUnions.exists_monochromaticUnions`
produces pairwise disjoint blocks of parameters all of whose nonempty unions are equally coloured.
Reading those blocks as the variable directions of a subspace proves the theorem, in the dimension
`GrahamRothschild.bound`, an explicit expression in the bound for the Hales--Jewett numbers.

Mathlib's `Combinatorics.Subspace` indexes variable directions by an arbitrary function on
coordinates rather than by consecutive blocks of coordinates. Pairwise disjoint blocks therefore
already describe a subspace, and the finite Ramsey theorem that would arrange them in increasing
order is not needed.
-/

@[expose] public section

open Finset Function
open Combinatorics

namespace DensityHalesJewett

namespace GrahamRothschild

open Subspace

/-- A coordinate lies in at most one of pairwise disjoint blocks. -/
private lemma choose_eq {ι : Type*} {m : ℕ} {E : Fin m → Finset ι}
    (hEE : Pairwise (Disjoint on E)) {i : ι} {j : Fin m} (hij : i ∈ E j) (h : ∃ j, i ∈ E j) :
    h.choose = j :=
  by_contra fun hne ↦ disjoint_left.1 (hEE hne) h.choose_spec hij

variable {α ι κ : Type*} [DecidableEq ι] {m n : ℕ}

/-- The subspace whose variable directions are pairwise disjoint nonempty blocks of coordinates,
with a fixed letter on all remaining coordinates. -/
noncomputable def ofBlocks (a₀ : α) (E : Fin m → Finset ι) (hE : ∀ j, (E j).Nonempty)
    (hEE : Pairwise (Disjoint on E)) : Combinatorics.Subspace (Fin m) α ι where
  idxFun i := if h : ∃ j, i ∈ E j then Sum.inr h.choose else Sum.inl a₀
  proper e := by
    obtain ⟨i, hi⟩ := hE e
    exact ⟨i, by rw [dite_eq_left ⟨e, hi⟩, choose_eq hEE hi]⟩

variable {a₀ : α} {E : Fin m → Finset ι} {hE : ∀ j, (E j).Nonempty}
  {hEE : Pairwise (Disjoint on E)}

lemma ofBlocks_idxFun_of_mem {i : ι} {j : Fin m} (hij : i ∈ E j) :
    (ofBlocks a₀ E hE hEE).idxFun i = Sum.inr j := by
  simp only [ofBlocks]
  rw [dite_eq_left ⟨j, hij⟩, choose_eq hEE hij]

lemma ofBlocks_idxFun_of_notMem {i : ι} (hi : ∀ j, i ∉ E j) :
    (ofBlocks a₀ E hE hEE).idxFun i = Sum.inl a₀ :=
  dite_eq_right (by simpa using hi)

/-- The support of a word substituted into `ofBlocks` is the union of the blocks indexed by the
support of that word. -/
lemma sameSupport_wordMap_ofBlocks {x : Fin m → Option α} {J : Finset (Fin m)}
    (hJ : ∀ j, j ∈ J ↔ x j = none) :
    SameSupport (wordMap (ofBlocks a₀ E hE hEE) x)
      fun i ↦ if i ∈ J.biUnion E then none else some a₀ := by
  intro i
  have hite : (if i ∈ J.biUnion E then none else some a₀ : Option α) = none ↔
      i ∈ J.biUnion E := by
    split <;> simp [*]
  rw [wordMap, hite, mem_biUnion]
  by_cases h : ∃ j, i ∈ E j
  · obtain ⟨j, hj⟩ := h
    rw [ofBlocks_idxFun_of_mem hj, Sum.elim_inr, ← hJ j]
    refine ⟨fun hjJ ↦ ⟨j, hjJ, hj⟩, ?_⟩
    rintro ⟨j', hj'J, hij'⟩
    by_contra hjJ
    exact disjoint_left.1 (hEE fun h : j = j' ↦ hjJ (h ▸ hj'J)) hj hij'
  · rw [not_exists] at h
    rw [ofBlocks_idxFun_of_notMem h]
    simp [h]

/-- Extend a colouring of the lines of a cube to a colouring of all words over `Option α`. -/
private noncomputable def extend [Nonempty κ] (C : Combinatorics.Line α (Fin n) → κ)
    (w : Fin n → Option α) : κ :=
  if h : ∃ i, w i = none then C ⟨w, h⟩ else Classical.arbitrary κ

private lemma extend_idxFun [Nonempty κ] (C : Combinatorics.Line α (Fin n) → κ)
    (l : Combinatorics.Line α (Fin n)) : extend C l.idxFun = C l :=
  dite_eq_left l.proper

/-- A sufficient dimension for Graham--Rothschild for lines with `k` letters, `r` colours and
subspace dimension `m`, as an explicit expression in Shelah's bound
`Combinatorics.Line.shelahBound` for the Hales--Jewett numbers. -/
def bound (k r m : ℕ) : ℕ :=
  Canonization.bound k r (FiniteUnions.monochromaticUnionsBound r m) 0 0

/-- **Graham--Rothschild for lines**: beyond a dimension depending only on the alphabet, the
number of colours and `m`, every colouring of the lines of a cube is constant on the lines of some
`m`-dimensional combinatorial subspace. -/
theorem exists_mapLine_eq {α κ : Type*} [Fintype α] [Nonempty α] [Fintype κ] [Nonempty κ]
    {m n : ℕ} (hn : bound (Fintype.card α) (Fintype.card κ) m ≤ n)
    (C : Combinatorics.Line α (Fin n) → κ) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      ∃ c, ∀ l : Combinatorics.Line α (Fin m), C (mapLine V l) = c := by
  classical
  obtain ⟨V, hV⟩ := Canonization.exists_canonical_of_le hn (extend C)
  obtain ⟨E, hE, hEE, c, hc⟩ := FiniteUnions.exists_monochromaticUnions fun I ↦
    extend C (wordMap V fun i ↦ if i ∈ I then none else some (Classical.arbitrary α))
  refine ⟨compose V (ofBlocks (Classical.arbitrary α) E hE hEE), c, ?_⟩
  intro l
  rw [mapLine_eq_composeLine, ← extend_idxFun C, composeLine_idxFun, wordMap_compose,
    hV _ _ (sameSupport_wordMap_ofBlocks (J := {j | l.idxFun j = none}) fun j ↦ by simp)]
  obtain ⟨j, hj⟩ := l.proper
  exact hc _ ⟨j, by simpa using hj⟩

/-- The two-colour form of Graham--Rothschild used by the density argument: some `m`-dimensional
subspace has all of its lines in a given set of lines, or none of them. -/
lemma exists_mapLine_mem_or_notMem {α : Type*} [Fintype α] [Nonempty α] {m n : ℕ}
    (hn : bound (Fintype.card α) 2 m ≤ n) (L : Finset (Combinatorics.Line α (Fin n))) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      (∀ l : Combinatorics.Line α (Fin m), mapLine V l ∈ L) ∨
        (∀ l : Combinatorics.Line α (Fin m), mapLine V l ∉ L) := by
  classical
  obtain ⟨V, c, hc⟩ := exists_mapLine_eq (κ := Bool) hn fun l ↦ decide (l ∈ L)
  use V
  cases c
  · exact .inr fun l ↦ by simpa using hc l
  · exact .inl fun l ↦ by simpa using hc l

end GrahamRothschild
end DensityHalesJewett

/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Finset.Max
public import LeanPool.ShelahHalesJewett.HalesJewett
import LeanPool.DensityHalesJewett.DensityHalesJewett.HalesJewett
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort

/-!
# Finite unions of disjoint sets from the multidimensional Hales--Jewett theorem

For a colouring of the subsets of a large finite index set we produce pairwise disjoint nonempty
blocks all of whose nonempty unions receive the same colour. The multidimensional Hales--Jewett
theorem over the alphabet `Bool` gives a translated combinatorial cube of sets, iterating it
canonizes the colour of a union in terms of its least block, and the pigeonhole principle
extracts a monochromatic family.

Every step is carried out in an explicit dimension, written in terms of Shelah's bound
`Combinatorics.Line.shelahBound` for the Hales--Jewett numbers.
-/

@[expose] public section

open Finset Function
open Combinatorics

namespace DensityHalesJewett
namespace FiniteUnions

variable {κ : Type*} [Fintype κ]

/-- The multidimensional Hales--Jewett theorem over the alphabet `Bool`, read as a statement about
sets of coordinates: a base set `S` and pairwise disjoint nonempty blocks `X` such that every
union of `S` with a subfamily of the `X` has the same colour. -/
private lemma exists_mono_blocks {ι η : Type*} [Fintype ι] [DecidableEq ι] [Fintype η]
    (h : Fintype.card ι = Line.shelahBound (2 ^ Fintype.card η) (Fintype.card κ) * Fintype.card η)
    (C : Finset ι → κ) :
    ∃ (S : Finset ι) (X : η → Finset ι), (∀ j, (X j).Nonempty) ∧ (∀ j, Disjoint S (X j)) ∧
      Pairwise (Disjoint on X) ∧ ∃ c, ∀ J : Finset η, C (S ∪ J.biUnion X) = c := by
  classical
  obtain ⟨W, c, hc⟩ :=
    Subspace.exists_mono_of_card_eq (α := Bool) (by simpa using h) fun x ↦ C {i | x i}
  refine ⟨univ.filter fun i ↦ W.idxFun i = .inl true,
    fun j ↦ univ.filter fun i ↦ W.idxFun i = .inr j, ?_, ?_, ?_, c, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := W.proper j
    exact ⟨i, by simp [hi]⟩
  · intro j
    simp only [disjoint_left, mem_filter, mem_univ, true_and]
    grind
  · intro j j' hjj'
    simp only [onFun, disjoint_left, mem_filter, mem_univ, true_and]
    grind
  · intro J
    rw [← hc fun j ↦ decide (j ∈ J)]
    congr 1
    ext i
    simp only [mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
    rw [Subspace.coe_apply]
    cases h : W.idxFun i with
    | inl b => cases b <;> simp
    | inr j => simp

/-- A dimension in which every colouring with `c` colours has a translated combinatorial cube of
`n` wildcard blocks. -/
def translatedCubeBound (c n : ℕ) : ℕ :=
  Line.shelahBound (2 ^ (n + 1)) c * (n + 1)

/-- A translated combinatorial cube of sets: a base block `E` and wildcard blocks `G` such that
every union of `E` with a subfamily of the `G` has the same colour. -/
lemma exists_translatedCube {n : ℕ}
    (C : Finset (Fin (translatedCubeBound (Fintype.card κ) n)) → κ) :
    ∃ (E : Finset (Fin (translatedCubeBound (Fintype.card κ) n)))
      (G : Fin n → Finset (Fin (translatedCubeBound (Fintype.card κ) n))),
      E.Nonempty ∧ (∀ i, (G i).Nonempty) ∧ (∀ i, Disjoint E (G i)) ∧ Pairwise (Disjoint on G) ∧
        ∃ c, ∀ I : Finset (Fin n), C (E ∪ I.biUnion G) = c := by
  classical
  obtain ⟨S, X, hX, hSX, hXX, c, hc⟩ :=
    exists_mono_blocks (η := Fin (n + 1))
      (by rw [Fintype.card_fin, Fintype.card_fin, translatedCubeBound]) C
  refine ⟨S ∪ X 0, fun i ↦ X i.succ, (hX 0).mono subset_union_right, fun i ↦ hX _,
    fun i ↦ disjoint_union_left.2 ⟨hSX _, hXX (Fin.succ_ne_zero i).symm⟩,
    fun i j hij ↦ hXX fun h ↦ hij (Fin.succ_injective _ h), c, ?_⟩
  intro I
  convert hc (insert 0 (I.image Fin.succ)) using 2
  simp [union_assoc, image_biUnion]

/-- A dimension in which the colour of a union of `t` blocks is canonized by its least block:
the translated cube iterated `t` times. -/
def minCanonicalBound (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => translatedCubeBound c (minCanonicalBound c t)

/-- A block disjoint from pairwise disjoint blocks can be prepended to them. -/
private lemma pairwise_disjoint_cons {ι : Type*} {t : ℕ} {E₀ : Finset ι} {F : Fin t → Finset ι}
    (h₀ : ∀ j, Disjoint E₀ (F j)) (hF : Pairwise (Disjoint on F)) :
    Pairwise (Disjoint on (Fin.cons E₀ F : Fin (t + 1) → Finset ι)) := by
  intro i j hij
  induction i using Fin.cases <;> induction j using Fin.cases
  · exact absurd rfl hij
  · simpa [onFun] using h₀ _
  · simpa [onFun] using (h₀ _).symm
  · simpa [onFun] using hF fun h ↦ hij (congrArg Fin.succ h)

/-- Unions of pairwise disjoint blocks over pairwise disjoint index sets are pairwise disjoint. -/
private lemma pairwise_disjoint_biUnion {ι : Type*} [DecidableEq ι] {t n : ℕ}
    {I : Fin t → Finset (Fin n)} {G : Fin n → Finset ι} (hI : Pairwise (Disjoint on I))
    (hG : Pairwise (Disjoint on G)) : Pairwise (Disjoint on fun j ↦ (I j).biUnion G) := by
  intro i j hij
  simp only [onFun, disjoint_biUnion_left, disjoint_biUnion_right]
  intro b hb a ha
  exact hG fun h ↦ disjoint_left.1 (hI hij) ha (by rwa [h])

/-- A set of indices in `Fin (t + 1)` is the image of a set of indices in `Fin t`, with or without
`0`. -/
private lemma eq_image_succ_or_insert_zero {t : ℕ} (J : Finset (Fin (t + 1))) :
    ∃ K : Finset (Fin t), J = K.image Fin.succ ∨ J = insert 0 (K.image Fin.succ) := by
  refine ⟨univ.filter fun j ↦ j.succ ∈ J, ?_⟩
  by_cases h0 : 0 ∈ J
  · right
    ext i
    induction i using Fin.cases <;> simp [h0, Fin.succ_ne_zero]
  · left
    ext i
    induction i using Fin.cases <;> simp [h0, Fin.succ_ne_zero]

private lemma min'_image_succ {t : ℕ} {K : Finset (Fin t)} (hK : K.Nonempty) :
    (K.image Fin.succ).min' (hK.image _) = (K.min' hK).succ :=
  min'_image (fun _ _ h ↦ Fin.succ_le_succ_iff.2 h) K _

private lemma min'_insert_zero {t : ℕ} (s : Finset (Fin (t + 1))) :
    (insert 0 s).min' (insert_nonempty 0 s) = 0 :=
  le_antisymm (min'_le _ _ (mem_insert_self 0 s)) (Fin.zero_le _)

/-- Iterating the translated cube canonizes the colour of a union of blocks in terms of the least
block that it contains. -/
lemma exists_minCanonical {t : ℕ} :
    ∀ C : Finset (Fin (minCanonicalBound (Fintype.card κ) t)) → κ,
      ∃ E : Fin t → Finset (Fin (minCanonicalBound (Fintype.card κ) t)),
        (∀ i, (E i).Nonempty) ∧ Pairwise (Disjoint on E) ∧
          ∃ f : Fin t → κ, ∀ (J : Finset (Fin t)) (hJ : J.Nonempty),
            C (J.biUnion E) = f (J.min' hJ) := by
  classical
  induction t with
  | zero =>
    intro C
    refine ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, Fin.elim0, ?_⟩
    intro J hJ
    simp [eq_empty_of_isEmpty J] at hJ
  | succ t ih =>
    rw [minCanonicalBound]
    intro C
    obtain ⟨E₀, G, hE₀, hG, hE₀G, hGG, c, hc⟩ := exists_translatedCube C
    obtain ⟨I, hI, hII, f, hf⟩ := ih fun K ↦ C (K.biUnion G)
    refine ⟨Fin.cons E₀ fun j ↦ (I j).biUnion G, ?_,
      pairwise_disjoint_cons ?_ (pairwise_disjoint_biUnion hII hGG), Fin.cons c f, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hE₀
      | succ j => simpa using (hI j).biUnion fun g _ ↦ hG g
    · intro j
      exact (disjoint_biUnion_right _ _ _).2 fun g _ ↦ hE₀G g
    · intro J hJ
      obtain ⟨K, rfl | rfl⟩ := eq_image_succ_or_insert_zero J
      · obtain hK := image_nonempty.1 hJ
        rw [min'_image_succ hK, Fin.cons_succ, image_biUnion]
        simpa [biUnion_biUnion] using hf K hK
      · rw [min'_insert_zero, Fin.cons_zero, biUnion_insert, image_biUnion]
        simpa [biUnion_biUnion] using hc (K.biUnion I)

/-- A dimension for the finite disjoint unions theorem with `c` colours and `m` blocks: by the
pigeonhole principle, `m * c + 1` canonized blocks contain `m + 1` whose colours agree. -/
def monochromaticUnionsBound (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => minCanonicalBound c (m * c + 1)

/-- The finite disjoint unions theorem: for every colouring of the subsets of a large enough
finite index set there are `m` pairwise disjoint nonempty blocks all of whose nonempty unions
receive the same colour. -/
lemma exists_monochromaticUnions {m : ℕ} :
    ∀ C : Finset (Fin (monochromaticUnionsBound (Fintype.card κ) m)) → κ,
      ∃ E : Fin m → Finset (Fin (monochromaticUnionsBound (Fintype.card κ) m)),
        (∀ i, (E i).Nonempty) ∧ Pairwise (Disjoint on E) ∧
          ∃ c, ∀ J : Finset (Fin m), J.Nonempty → C (J.biUnion E) = c := by
  classical
  obtain _ | m := m
  · intro C
    refine ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, C ∅, ?_⟩
    intro J hJ
    simp [eq_empty_of_isEmpty J] at hJ
  rw [monochromaticUnionsBound]
  intro C
  obtain ⟨E, hE, hEE, f, hf⟩ := exists_minCanonical C
  obtain ⟨c, -, hc⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := univ)
    (t := (univ : Finset κ)) (f := f) (n := m) (fun _ _ ↦ mem_univ _) (by simp [mul_comm])
  obtain ⟨T, hT, hTcard⟩ := exists_subset_card_eq (s := {i | f i = c}) (n := m + 1) hc
  refine ⟨fun j ↦ E (T.orderEmbOfFin hTcard j), fun j ↦ hE _,
    fun i j hij ↦ hEE fun h ↦ hij ((T.orderEmbOfFin hTcard).injective h), c, ?_⟩
  intro J hJ
  rw [← image_biUnion, hf _ (hJ.image _)]
  obtain ⟨j, -, hj⟩ := mem_image.1 (min'_mem _ (hJ.image (T.orderEmbOfFin hTcard)))
  rw [← hj]
  simpa using hT (T.orderEmbOfFin_mem hTcard j)

end FiniteUnions
end DensityHalesJewett

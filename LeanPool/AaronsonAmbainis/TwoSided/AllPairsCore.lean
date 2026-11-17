/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Positivity
public import LeanPool.AaronsonAmbainis.TwoSided.Glue

/-!
# The all-pairs inequality for one set `F` of free coordinates (`allPairs_core`)

Step 1 of the proof of Proposition 5.2 of the paper: the antipodal inequality (Theorem 4.3)
applied to all subcubes with free coordinates `F`, added up:

  `∑ x, allPairsTerm g w lam F x ≤ ∑ j ∈ F, bdry g j / w j`,

where `allPairsTerm g w lam F x = (∑ j ∈ F, w j * lam x j * lam (x^F) j)⁻¹` if `g x = true` and
`g (x^F) = false`, and `0` otherwise (the term `T_F(x)` of the paper).

The subcube through `z` with free coordinates `F` is parametrised by `u ↦ glue F z u`
(`u : Cube ι`; the coordinates of `u` off `F` are dummies).  The antipodal inequality is applied
to `u ↦ g (glue F z u)` with the rows `lam (glue F z u)` restricted to `F`, for every `z`,
and the results are added over all `z`; `sum_sum_glue` removes the multiplicity `2 ^ n`.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The term `T_F(x)` of the paper: `(∑ j ∈ F, w j * lam x j * lam (x^F) j)⁻¹` if `g x = true`
and `g (x^F) = false`, and `0` otherwise. -/
noncomputable def allPairsTerm (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ)
    (F : Finset ι) (x : Cube ι) : ℝ :=
  if g x = true ∧ g (flipSet x F) = false then
    (∑ j ∈ F, w j * lam x j * lam (flipSet x F) j)⁻¹ else 0

omit [Fintype ι] in
/-- The restriction of a row to the free coordinates is a row of the restricted function. -/
lemma isRow_glue {g : Cube ι → Bool} {lam : Cube ι → ι → ℝ} (hlam : ∀ x, IsRow g x (lam x))
    (F : Finset ι) (z u : Cube ι) :
    IsRow (fun u => g (glue F z u)) u (fun j => if j ∈ F then lam (glue F z u) j else 0) := by
  constructor
  · intro j
    dsimp only
    split_ifs
    · exact (hlam _).1 j
    · exact le_rfl
  · intro S hS
    have hS' : g (flipSet (glue F z u) (S ∩ F)) ≠ g (glue F z u) := by
      rw [← glue_flipSet]
      exact hS
    calc (1 : ℝ) ≤ ∑ j ∈ S ∩ F, lam (glue F z u) j := (hlam (glue F z u)).2 (S ∩ F) hS'
      _ = ∑ j ∈ S, if j ∈ F then lam (glue F z u) j else 0 :=
          (Finset.sum_ite_mem S F (fun j => lam (glue F z u) j)).symm

/-- A sum of products of two restricted vectors is a sum over the restriction set. -/
lemma sum_ite_ite_mem (F : Finset ι) (w a b : ι → ℝ) :
    ∑ j, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0)
      = ∑ j ∈ F, w j * a j * b j := by
  have h1 : ∑ j ∈ F, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0)
      = ∑ j, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0) := by
    apply Finset.sum_subset (Finset.subset_univ F)
    intro j _ hj
    simp [hj]
  rw [← h1]
  apply Finset.sum_congr rfl
  intro j hj
  simp [hj]

/-- The left side of the antipodal inequality for the restricted function, in terms of
`allPairsTerm`. -/
lemma zone_sum_glue (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ)
    (F : Finset ι) (z : Cube ι) :
    ∑ u ∈ zone (fun u => g (glue F z u)),
        (∑ j, w j * (if j ∈ F then lam (glue F z u) j else 0)
          * (if j ∈ F then lam (glue F z (antipode u)) j else 0))⁻¹
      = ∑ u, allPairsTerm g w lam F (glue F z u) := by
  unfold zone
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  simp only [glue_antipode, sum_ite_ite_mem, allPairsTerm]

/-- `bdry` as a real sum of indicators. -/
lemma bdry_eq_sum (g : Cube ι → Bool) (j : ι) :
    (bdry g j : ℝ) = ∑ x, (if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0) := by
  unfold bdry
  rw [Finset.sum_boole]

/-- A coordinate that is not free has no bichromatic edge in the subcube. -/
lemma bdry_glue_of_not_mem (g : Cube ι → Bool) {F : Finset ι} {j : ι} (hj : j ∉ F)
    (z : Cube ι) : bdry (fun u => g (glue F z u)) j = 0 := by
  unfold bdry
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _
  simp only [glue_flipSet_singleton_of_not_mem hj]
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- A free coordinate: the bichromatic `j`-edges of all subcubes with free coordinates `F`
are the bichromatic `j`-edges of `g`, each `2 ^ n` times. -/
lemma sum_bdry_glue_of_mem (g : Cube ι → Bool) {F : Finset ι} {j : ι} (hj : j ∈ F) :
    ∑ z, (bdry (fun u => g (glue F z u)) j : ℝ) = 2 ^ Fintype.card ι * (bdry g j : ℝ) := by
  have h1 : ∀ z, (bdry (fun u => g (glue F z u)) j : ℝ)
      = ∑ u, (fun x => if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0)
          (glue F z u) := by
    intro z
    rw [bdry_eq_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [glue_flipSet_singleton_of_mem hj]
  rw [Finset.sum_congr rfl (fun z _ => h1 z), bdry_eq_sum]
  exact sum_sum_glue F (fun x => if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0)

/-- The inequality for one set `F` of free coordinates (Step 1 of the proof of Proposition 5.2
of the paper), from the antipodal inequality. -/
lemma allPairs_core (hAntipodal : AntipodalInequality) {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → Bool) (w : ι → ℝ) (hw : ∀ j, 0 < w j)
    (lam : Cube ι → ι → ℝ) (hlam : ∀ x, IsRow g x (lam x)) (F : Finset ι) :
    ∑ x, allPairsTerm g w lam F x ≤ ∑ j ∈ F, (bdry g j : ℝ) / w j := by
  -- the antipodal inequality on the subcube through `z`
  have hz : ∀ z : Cube ι, ∑ u, allPairsTerm g w lam F (glue F z u)
      ≤ ∑ j, (bdry (fun u => g (glue F z u)) j : ℝ) / w j := by
    intro z
    have h := hAntipodal ι (fun u => g (glue F z u)) w hw
      (fun u j => if j ∈ F then lam (glue F z u) j else 0) (fun u => isRow_glue hlam F z u)
    rw [← zone_sum_glue]
    exact h
  -- add over all `z`
  have hsum : ∑ z, ∑ u, allPairsTerm g w lam F (glue F z u)
      ≤ ∑ z, ∑ j, (bdry (fun u => g (glue F z u)) j : ℝ) / w j :=
    Finset.sum_le_sum fun z _ => hz z
  rw [sum_sum_glue] at hsum
  have hj : ∀ j, ∑ z, (bdry (fun u => g (glue F z u)) j : ℝ) / w j
      = if j ∈ F then 2 ^ Fintype.card ι * ((bdry g j : ℝ) / w j) else 0 := by
    intro j
    split_ifs with hjF
    · rw [← Finset.sum_div, sum_bdry_glue_of_mem g hjF, mul_div_assoc]
    · apply Finset.sum_eq_zero
      intro z _
      rw [bdry_glue_of_not_mem g hjF z]
      simp
  have hR : ∑ z, ∑ j, (bdry (fun u => g (glue F z u)) j : ℝ) / w j
      = 2 ^ Fintype.card ι * ∑ j ∈ F, (bdry g j : ℝ) / w j := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => hj j), Fintype.sum_ite_mem,
      Finset.mul_sum]
  rw [hR] at hsum
  exact le_of_mul_le_mul_left hsum (by positivity)

end AaronsonAmbainis

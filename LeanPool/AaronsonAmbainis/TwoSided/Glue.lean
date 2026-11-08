/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import LeanPool.AaronsonAmbainis.TwoSided.Basic

/-!
# Gluing two points along a set of coordinates

`glue F z u` agrees with `u` on `F` and with `z` off `F`; it is the point `γ_F(z,u)` of
Section 5.1 of the paper.  For fixed `F` and `z` the map `u ↦ glue F z u` parametrises the
subcube through `z` with free coordinates `F` (with multiplicity `2 ^ (n - |F|)`), and
`(z, u) ↦ (glue F z u, glue F u z)` is an involution of `Cube ι × Cube ι`.

The file proves the gluing lemma (Lemma 5.1 of the paper): part (i) is `glue_flipSet`, with the
special cases `glue_antipode`, `glue_flipSet_singleton_of_mem` and
`glue_flipSet_singleton_of_not_mem`; part (ii) is `sum_sum_glue`.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

section NoFintype

variable {ι : Type*} [DecidableEq ι]

/-- `glue F z u` agrees with `u` on `F` and with `z` off `F`. -/
def glue (F : Finset ι) (z u : Cube ι) : Cube ι := fun i => if i ∈ F then u i else z i

lemma glue_flipSet (F : Finset ι) (z u : Cube ι) (S : Finset ι) :
    glue F z (flipSet u S) = flipSet (glue F z u) (S ∩ F) := by
  funext i
  by_cases hF : i ∈ F <;> by_cases hS : i ∈ S <;> simp [glue, flipSet, hF, hS]

lemma glue_antipode (F : Finset ι) (z u : Cube ι) :
    glue F z (antipode u) = flipSet (glue F z u) F := by
  funext i
  by_cases hF : i ∈ F <;> simp [glue, flipSet, antipode, hF]

lemma glue_flipSet_singleton_of_mem {F : Finset ι} {j : ι} (hj : j ∈ F) (z u : Cube ι) :
    glue F z (flipSet u {j}) = flipSet (glue F z u) {j} := by
  rw [glue_flipSet, Finset.singleton_inter_of_mem hj]

lemma glue_flipSet_singleton_of_not_mem {F : Finset ι} {j : ι} (hj : j ∉ F) (z u : Cube ι) :
    glue F z (flipSet u {j}) = glue F z u := by
  rw [glue_flipSet, Finset.singleton_inter_of_notMem hj, flipSet_empty]

lemma glue_glue_swap (F : Finset ι) (z u : Cube ι) :
    glue F (glue F z u) (glue F u z) = z := by
  funext i
  by_cases hF : i ∈ F <;> simp [glue, hF]

/-- The double-counting involution `(z, u) ↦ (glue F z u, glue F u z)`. -/
def glueEquiv (F : Finset ι) : (Cube ι × Cube ι) ≃ (Cube ι × Cube ι) where
  toFun p := (glue F p.1 p.2, glue F p.2 p.1)
  invFun q := (glue F q.1 q.2, glue F q.2 q.1)
  left_inv p := Prod.ext (glue_glue_swap F p.1 p.2) (glue_glue_swap F p.2 p.1)
  right_inv p := Prod.ext (glue_glue_swap F p.1 p.2) (glue_glue_swap F p.2 p.1)

end NoFintype

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every point `x` is `glue F z u` for exactly `2 ^ n` pairs `(z, u)`. -/
lemma sum_sum_glue (F : Finset ι) (φ : Cube ι → ℝ) :
    ∑ z, ∑ u, φ (glue F z u) = 2 ^ Fintype.card ι * ∑ x, φ x := by
  calc ∑ z, ∑ u, φ (glue F z u)
      = ∑ p : Cube ι × Cube ι, φ ((glueEquiv F p).1) :=
        (Fintype.sum_prod_type (fun p : Cube ι × Cube ι => φ ((glueEquiv F p).1))).symm
    _ = ∑ q : Cube ι × Cube ι, φ q.1 :=
        Equiv.sum_comp (glueEquiv F) (fun q : Cube ι × Cube ι => φ q.1)
    _ = ∑ x : Cube ι, ∑ _x' : Cube ι, φ x :=
        Fintype.sum_prod_type (fun q : Cube ι × Cube ι => φ q.1)
    _ = 2 ^ Fintype.card ι * ∑ x, φ x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_const, Finset.card_univ, card_cube, nsmul_eq_mul]
        push_cast
        ring

end AaronsonAmbainis

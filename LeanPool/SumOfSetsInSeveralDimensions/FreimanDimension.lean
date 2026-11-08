/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.Additive.FreimanHom
public import LeanPool.SumOfSetsInSeveralDimensions.AffineDim

/-!
# The Freiman dimension

The Freiman dimension of a finite subset `X` of an abelian group is the largest `d ≤ |X|` such that
`X` is Freiman isomorphic of order `2` to a subset of `ℚ^d` that is not contained in a proper
affine subspace. The affine dimension of the image is the `Finset.affineDim` of its inclusion in
`ℝ^d`.

## Main definitions

* `rationalVectorToReal`: the coordinatewise inclusion of `ℚ^d` into `ℝ^d`.
* `freimanModelDim X d`: `X` is Freiman isomorphic to a subset of `ℚ^d` of affine dimension `d`.
* `freimanDim X`: the Freiman dimension of `X`.

## Main statements

* `le_freimanDim_of_model`: if `d ≤ |X|` and `freimanModelDim X d`, then `d ≤ freimanDim X`.
* `freimanDim_add_one_le_card`: a nonempty set `X` has Freiman dimension at most `|X| - 1`.
-/

@[expose] public section

namespace SumOfSetsInSeveralDimensions

open Finset

/-- The coordinatewise inclusion of rational vectors into real vectors. -/
def rationalVectorToReal {d : ℕ} (v : Fin d → ℚ) : Fin d → ℝ := fun i ↦ (v i : ℝ)

/-- The set `X` has a Freiman model of dimension `d`: there is a Freiman isomorphism of order `2`
from `X` onto a subset of `ℚ^d` of affine dimension `d`. -/
def freimanModelDim {G : Type*} [AddCommMonoid G] (X : Finset G) (d : ℕ) : Prop :=
  ∃ f : G → (Fin d → ℚ), IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin d → ℚ)) f ∧
    ((X.image f).image rationalVectorToReal).affineDim = d

/-- The Freiman dimension of `X`: the largest `d ≤ |X|` such that `X` has a Freiman model of
dimension `d`. -/
noncomputable def freimanDim {G : Type*} [AddCommMonoid G] (X : Finset G) : ℕ := by
  classical
  exact Nat.findGreatest (freimanModelDim X) #X

/-- A Freiman model of `X` of dimension `d ≤ |X|` shows that `d ≤ freimanDim X`. -/
lemma le_freimanDim_of_model {G : Type*} [AddCommMonoid G] {X : Finset G} {d : ℕ}
    (hd : d ≤ #X) (hmodel : freimanModelDim X d) : d ≤ freimanDim X := by
  classical
  exact Nat.le_findGreatest hd hmodel

/-- A nonempty set `X` has Freiman dimension at most `|X| - 1`. -/
lemma freimanDim_add_one_le_card {G : Type*} [AddCommMonoid G] {X : Finset G}
    (hX : X.Nonempty) : freimanDim X + 1 ≤ #X := by
  classical
  by_cases h : freimanDim X = 0
  · grind [hX.card_pos]
  obtain ⟨f, -, hdim⟩ : freimanModelDim X (freimanDim X) := Nat.findGreatest_of_ne_zero rfl h
  grind [affineDim_add_one_le_card ((hX.image f).image rationalVectorToReal),
    card_image_le (s := X) (f := f),
    card_image_le (s := X.image f) (f := rationalVectorToReal)]

end SumOfSetsInSeveralDimensions

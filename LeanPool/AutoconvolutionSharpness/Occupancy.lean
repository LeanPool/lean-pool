/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset

/-!
# Counting the single - occupancy multiplicities

An occupied set of cardinality `k` gives a distinct multiplicity vector
in the antidiagonal. This counts the vectors by Mathlib's
`Finset.card_powersetCard` (the number of combinations).
-/

@[expose] public section

open Finset

namespace Autoconvolutions.Blocks

variable {ι : Type*} [DecidableEq ι]

/-- Embed a set of occupied digit positions into its vector of multiplicities. -/
def indicatorVector : Finset ι ↪ (ι → ℕ) where
  toFun T i := if i ∈ T then 1 else 0
  inj' := by
    intro T U h
    ext i
    have e := congrFun h i
    by_cases hT : i ∈ T <;> by_cases hU : i ∈ U <;> simp_all

/-- Distinct choices of `k` positions, represented as multiplicities. -/
def goodVectors (I : Finset ι) (k : ℕ) : Finset (ι → ℕ) :=
  (I.powersetCard k).map indicatorVector

theorem card_goodVectors (I : Finset ι) (k : ℕ) :
    (goodVectors I k).card = I.card.choose k := by simp [goodVectors]

theorem goodVectors_spec {I : Finset ι} {k : ℕ} {a : ι → ℕ} (ha : a ∈ goodVectors I k) :
    a ∈ I.piAntidiag k ∧ ∀ i, a i ≤ 1 := by
  classical
  obtain ⟨T,hT,rfl⟩ := mem_map.mp ha
  obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hT
  constructor
  · apply mem_piAntidiag.mpr
    constructor
    · simp only [indicatorVector, Function.Embedding.coeFn_mk, sum_boole, Nat.cast_id,
        Finset.filter_mem_eq_inter, inter_eq_right.mpr hsub, hcard]
    · intro i hi
      by_contra hin
      have hT' : i ∉ T := fun h => hin (hsub h)
      simp [indicatorVector, hT'] at hi
  · intro i
    simp only [indicatorVector, Function.Embedding.coeFn_mk]
    split <;> decide

theorem card_goodPairs (I J : Finset ι) (u v : ℕ) :
    ((goodVectors I u) ×ˢ (goodVectors J v)).card = I.card.choose u * J.card.choose v := by
  simp [card_goodVectors]

end Autoconvolutions.Blocks

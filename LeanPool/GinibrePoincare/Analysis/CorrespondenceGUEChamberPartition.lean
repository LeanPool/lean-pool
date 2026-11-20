/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEChamberPartition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEH1Closure
public import Mathlib.Data.Fin.Tuple.Sort
/-!
# Correspondence GUE chamber partition

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueChamber_density_partition`.
-/

@[expose] public section
open MeasureTheory Set Function
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
/-- Classical decidability of every proposition, used locally in this file. -/
local instance instDecidableCorrespondenceGUEChamberPartition (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Permutation of coordinates: `guePermute n σ x` has `i`-th coordinate `x (σ i)`. -/
def guePermute (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => x (σ i))

theorem gueChamber_permutation_unique (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (σ τ : Equiv.Perm (Fin n)) (hσ : guePermute n σ x ∈ gueStrictChamber n)
    (hτ : guePermute n τ x ∈ gueStrictChamber n) : σ=τ := by
  have hI : Injective (fun i => x i) := by
    have h := (show StrictMono (fun i => x (σ i)) from hσ).injective
    intro i j hij
    have he := h (a₁ := σ.symm i) (a₂ := σ.symm j) (by simpa using hij)
    exact σ.symm.injective he
  have he := Tuple.unique_monotone
    (show StrictMono (fun i => x (σ i)) from hσ).monotone
    (show StrictMono (fun i => x (τ i)) from hτ).monotone
  apply Equiv.ext
  intro i
  exact hI (congrFun he i)

theorem gueChamber_sorted (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (hx : Injective (fun i => x i)) :
    guePermute n (Tuple.sort (fun i => x i)) x∈gueStrictChamber n := by
  intro i j hij
  have hm := Tuple.monotone_sort (fun i => x i) hij.le
  exact lt_of_le_of_ne hm (fun he => hij.ne ((Tuple.sort _).injective (hx he)))

theorem gueChamber_density_partition (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑σ : Equiv.Perm (Fin n), gueOrderedRawDensity n (guePermute n σ x))=gueRawDensity n x := by
  by_cases hx : Injective (fun i => x i)
  · let σ := Tuple.sort (fun i => x i)
    rw [Finset.sum_eq_single σ]
    · rw [gueOrderedRawDensity_eq_chamber_density, ite_eq_left (gueChamber_sorted n x hx)]
      exact gueRawDensity_symmetric n σ x
    · intro τ hτ ht
      rw [gueOrderedRawDensity_eq_chamber_density]
      apply ite_eq_right
      intro hch
      exact ht (gueChamber_permutation_unique n x τ σ hch (gueChamber_sorted n x hx))
    · simp
  · have hz : gueRawDensity n x=0 := by
      rw [gueRawDensity_zero_iff_collision]
      simp only [Injective, not_forall] at hx
      obtain ⟨i, j, he, hn⟩ := hx
      exact ⟨i, j, hn, he⟩
    rw [hz]
    apply Finset.sum_eq_zero
    intro σ hσ
    rw [gueOrderedRawDensity_eq_chamber_density]
    by_cases hc : guePermute n σ x∈gueStrictChamber n
    · rw [ite_eq_left hc]
      exact (gueRawDensity_symmetric n σ x).trans hz
    · exact ite_eq_right hc

end
end GinibrePoincare

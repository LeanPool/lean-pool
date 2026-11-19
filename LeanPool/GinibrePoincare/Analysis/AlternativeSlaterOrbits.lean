/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSlaterOrbits.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterPolynomial

/-!
# Alternative Slater orbits

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `slaterOrbit_card`, `inner_slaterL2_eq_zero_of_disjoint_orbits`,
`slaterL2_norm_eq_one`, `slaterL2_eq_zero_of_not_distinct`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory ComplexHermite
open scoped BigOperators

/-- Ordered reindexing of orbital labels under a permutation. -/
def slaterPermutedIndex {n : ℕ} (σ : ParticlePermutation n) (pq : HermiteMultiIndex n) :
    HermiteMultiIndex n := (pq.1 ∘ σ.symm, pq.2 ∘ σ.symm)

/-- A tuple has distinct orbitals precisely when its ordered pair labels are injective. -/
def SlaterDistinct {n : ℕ} (pq : HermiteMultiIndex n) : Prop :=
  Function.Injective (fun i => (pq.1 i, pq.2 i))

/-- The finite orbit of all orderings of an orbital set. -/
def slaterOrbit {n : ℕ} (pq : HermiteMultiIndex n) : Finset (HermiteMultiIndex n) :=
  Finset.univ.image (fun σ : ParticlePermutation n => slaterPermutedIndex σ pq)

/-- Distinct orbital labels imply a free permutation orbit. -/
theorem slaterPermutedIndex_injective {n : ℕ} (pq : HermiteMultiIndex n)
    (hpq : SlaterDistinct pq) : Function.Injective (fun σ => slaterPermutedIndex σ pq) := by
  intro σ τ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have hi : σ.symm = τ.symm := by
    apply Equiv.ext
    intro i
    apply hpq
    exact Prod.ext (congrFun h1 i) (congrFun h2 i)
  have he := congrArg (fun e : ParticlePermutation n => e.symm) hi
  simpa only [Equiv.symm_symm] using he

/-- Exactly `n!` ordered tuples represent each distinct unordered orbital set. -/
theorem slaterOrbit_card {n : ℕ} (pq : HermiteMultiIndex n) (hpq : SlaterDistinct pq) :
    (slaterOrbit pq).card = n.factorial := by
  rw [slaterOrbit, Finset.card_image_of_injective _ (slaterPermutedIndex_injective pq hpq)]
  simp [ParticlePermutation, Fintype.card_perm]

/-- The full determinant inner product is the signed permutation Kronecker sum. -/
theorem inner_slaterL2 {n : ℕ} (hn : 0 < n) (pq rs : HermiteMultiIndex n) :
    inner ℂ (slaterL2 hn pq) (slaterL2 hn rs) =
      ∑ σ : ParticlePermutation n, permutationSign σ *
        (if pq = slaterPermutedIndex σ rs then (1 : ℂ) else 0) := by
  have hcoef := slaterCoefficient_eq_hermite hn (slaterL2 hn rs)
    (slaterL2_mem_alternating hn rs) pq
  change inner ℂ (slaterL2 hn pq) (slaterL2 hn rs) = _ at hcoef
  rw [hcoef, gaussianHermiteCoefficient_eq_inner]
  change (Real.sqrt (slaterMultiplicity n) : ℂ) *
    inner ℂ (hermiteL2Family n hn pq) (slaterL2 hn rs) = _
  rw [slaterL2, inner_smul_right, gaussianAlternationOperator_apply,
    inner_smul_right, inner_sum]
  simp_rw [inner_smul_right, gaussianPermutationL2_hermiteL2Family n hn _ rs.1 rs.2]
  have ho := orthonormal_iff_ite.mp (orthonormal_hermiteL2Family_gaussian n hn)
  simp_rw [ho]
  have hr : (Real.sqrt (slaterMultiplicity n) : ℂ) ^ 2 = (slaterMultiplicity n : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (le_of_lt (slaterMultiplicity_pos n))
  have hc : (slaterMultiplicity n : ℂ) ≠ 0 := by exact_mod_cast (slaterMultiplicity_pos n).ne'
  have hcard : (Fintype.card (ParticlePermutation n) : ℂ) = (slaterMultiplicity n : ℂ) := by
    simp [slaterMultiplicity]
  rw [hcard]
  calc
    _ = ((Real.sqrt (slaterMultiplicity n) : ℂ)^2 * (slaterMultiplicity n : ℂ)⁻¹) *
        ∑ σ : ParticlePermutation n, permutationSign σ *
          (if pq = slaterPermutedIndex σ rs then (1 : ℂ) else 0) := by
      unfold slaterPermutedIndex
      ring
    _ = _ := by rw [hr, mul_inv_cancel₀ hc, one_mul]

/-- Distinct Slater orbitals have signed unit pairings precisely on a common
unordered orbital set; there is at most one contributing permutation. -/
theorem inner_slaterL2_of_permuted {n : ℕ} (hn : 0 < n)
    (pq rs : HermiteMultiIndex n) (hrs : SlaterDistinct rs)
    (σ : ParticlePermutation n) (hσ : pq = slaterPermutedIndex σ rs) :
    inner ℂ (slaterL2 hn pq) (slaterL2 hn rs) = permutationSign σ := by
  rw [inner_slaterL2]
  rw [Finset.sum_eq_single σ]
  · rw [ite_eq_left hσ, mul_one]
  · intro τ hτ hτσ
    have ht : pq ≠ slaterPermutedIndex τ rs := by
      intro ht
      exact hτσ ((slaterPermutedIndex_injective rs hrs) (ht.symm.trans hσ))
    rw [ite_eq_right ht, mul_zero]
  · simp

/-- Slater vectors from different unordered orbital sets are orthogonal. -/
theorem inner_slaterL2_eq_zero_of_disjoint_orbits {n : ℕ} (hn : 0 < n)
    (pq rs : HermiteMultiIndex n) (h : ∀ σ, pq ≠ slaterPermutedIndex σ rs) :
    inner ℂ (slaterL2 hn pq) (slaterL2 hn rs) = 0 := by
  rw [inner_slaterL2]
  simp [h]

/-- A determinant with distinct orbitals has exactly unit norm. -/
theorem slaterL2_norm_eq_one {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) (hpq : SlaterDistinct pq) : ‖slaterL2 hn pq‖ = 1 := by
  have h := inner_slaterL2_of_permuted hn pq pq hpq 1 (by rfl)
  have hs : permutationSign (1 : ParticlePermutation n) = 1 := by simp [permutationSign]
  rw [hs] at h
  have he : ‖slaterL2 hn pq‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h]
    exact RCLike.one_re
  nlinarith [norm_nonneg (slaterL2 hn pq)]

/-- Every nondistinct ordered tuple contributes the zero vector; together
with the free-orbit cardinality and signed unit pairings this justifies the
`n!` quotient in the ordered Parseval formulas. -/
theorem slaterL2_eq_zero_of_not_distinct {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) (hpq : ¬ SlaterDistinct pq) : slaterL2 hn pq = 0 := by
  simp only [SlaterDistinct, Function.Injective] at hpq
  push Not at hpq
  obtain ⟨i, j, hij, hne⟩ := hpq
  exact slaterL2_eq_zero_of_repeated hn pq hne (congrArg Prod.fst hij) (congrArg Prod.snd hij)

end
end GinibrePoincare


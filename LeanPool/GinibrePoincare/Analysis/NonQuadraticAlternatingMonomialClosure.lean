/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticAlternatingMonomialClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBergmanMonomials

/-!
# Non quadratic alternating monomial closure

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarPiBergman_alternating_mem_alternated_monomial_closure`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- The antisymmetrisation operator `(1 / d!) ∑ σ, sign σ • (· ∘ σ)` on `L²` of Lebesgue
measure on `ℂ^d`. -/
def volumeAlternationOperator (d : ℕ) :
    PlanarPiLebesgueL2 d →L[ℂ] PlanarPiLebesgueL2 d :=
  ((Fintype.card (ParticlePermutation d) : ℂ)⁻¹) •
    ∑ σ : ParticlePermutation d, permutationSign σ • (volumePermutationL2 σ).toContinuousLinearMap

theorem volumeAlternationOperator_apply {d : ℕ} (F : PlanarPiLebesgueL2 d) :
    volumeAlternationOperator d F = ((Fintype.card (ParticlePermutation d) : ℂ)⁻¹) •
      ∑ σ : ParticlePermutation d,
        permutationSign σ • (volumePermutationL2 σ F : PlanarPiLebesgueL2 d) := by
  unfold volumeAlternationOperator configurationVolume
  simp only [_root_.smul_apply, _root_.sum_apply]
  rfl

theorem volumeAlternationOperator_fixed {d : ℕ} (F : PlanarPiLebesgueL2 d)
    (hF : ∀ σ : ParticlePermutation d, volumePermutationL2 σ F = permutationSign σ • F) :
    volumeAlternationOperator d F = F := by
  have hs (σ : ParticlePermutation d) : permutationSign σ * permutationSign σ = 1 := by
    unfold permutationSign
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [volumeAlternationOperator_apply]
  unfold configurationVolume at hF ⊢
  simp_rw [hF, smul_smul, hs, one_smul]
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [Finset.card_univ]
  have hcard : (Fintype.card (ParticlePermutation d) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- The antisymmetrisations of products of weighted monomials, as a subset of `L²(ℂ^d)`. -/
def planarPiAlternatedWeightedMonomialVectors (d n : ℕ) (V : ℂ → ℝ) : Set (PlanarPiLebesgueL2 d) :=
  volumeAlternationOperator d '' planarPiWeightedMonomialVectors d n V

theorem planarPiBergman_alternating_mem_alternated_monomial_closure {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z)
    (F : PlanarPiLebesgueL2 (d+1))
    (hF : ∀ σ : ParticlePermutation (d+1), volumePermutationL2 σ F = permutationSign σ • F) :
    planarPiBergmanProjection n V hV F ∈
      (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) n V)).topologicalClosure :=
          by
  let K := (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) n
      V)).topologicalClosure
  let A := K.comap (volumeAlternationOperator (d+1)).toLinearMap
  have hK : IsClosed (K : Set (PlanarPiLebesgueL2 (d+1))) :=
    (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) n
        V)).isClosed_topologicalClosure
  have hA : IsClosed (A : Set (PlanarPiLebesgueL2 (d+1))) :=
    hK.preimage (volumeAlternationOperator (d+1)).continuous
  have hb : Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V) ≤ A := by
    apply Submodule.span_le.mpr
    intro u hu
    exact (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) n
        V)).le_topologicalClosure
      (Submodule.subset_span ⟨u, hu, rfl⟩)
  have hle := (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n
      V)).topologicalClosure_minimal hb hA
  have hx := hle (planarPiBergmanProjection_mem_weighted_monomial_closure n V hV hr F)
  change volumeAlternationOperator (d+1) (planarPiBergmanProjection n V hV F) ∈ K at hx
  rw [volumeAlternationOperator_fixed _ (fun σ =>
    planarPiBergmanProjection_preserves_alternating n V hV F hF σ)] at hx
  exact hx
end
end GinibrePoincare

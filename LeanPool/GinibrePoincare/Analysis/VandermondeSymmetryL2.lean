/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/VandermondeSymmetryL2.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PermutationLp
public import LeanPool.GinibrePoincare.Analysis.VandermondeL2

/-! # Vandermonde multiplication and permutation symmetry in `L²` -/


@[expose] public section


open MeasureTheory

namespace GinibrePoincare

noncomputable section

private theorem normalizedVandermondeL2_coeFn {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) :
    normalizedVandermondeL2 n hn u =ᵐ[complexGaussianMeasure n]
      fun z ↦ normalizedVandermondeMultiplier n z * u z := by
  unfold normalizedVandermondeL2
  dsimp only
  generalize_proofs h1 h2 h3 h4 h5
  exact (h5 u).coeFn_toLp

private theorem normalizedMultiplier_permute {n : ℕ}
    (σ : ParticlePermutation n) (z : Configuration n) :
    normalizedVandermondeMultiplier n (permute σ z) =
      permutationSign σ * normalizedVandermondeMultiplier n z := by
  unfold normalizedVandermondeMultiplier
  rw [vandermonde_permute]
  ring

/-- Normalized Vandermonde multiplication intertwines the permutation action
with its sign twist. -/
theorem normalizedVandermondeL2_intertwines {n : ℕ} (hn : 0 < n)
    (σ : ParticlePermutation n) (u : Lp ℂ 2 (ginibreMeasure n)) :
    gaussianPermutationL2 σ (normalizedVandermondeL2 n hn u) =
      permutationSign σ •
        normalizedVandermondeL2 n hn (ginibrePermutationL2 σ u) := by
  unfold gaussianPermutationL2 ginibrePermutationL2
  change Lp.compMeasurePreserving (permute σ)
      (gaussian_measurePreserving_permute σ) (normalizedVandermondeL2 n hn u) =
    permutationSign σ • normalizedVandermondeL2 n hn
      (Lp.compMeasurePreserving (permute σ)
        (ginibre_measurePreserving_permute σ) u)
  apply Lp.ext
  have hvalid := ginibreMassEvaluation n hn
  have hac := complexGaussianMeasure_absolutelyContinuous_ginibreMeasure hvalid
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (normalizedVandermondeL2 n hn u)
      (gaussian_measurePreserving_permute σ),
    (gaussian_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
      (normalizedVandermondeL2_coeFn hn u),
    normalizedVandermondeL2_coeFn hn
      (Lp.compMeasurePreserving (permute σ)
        (ginibre_measurePreserving_permute σ) u),
    hac.ae_eq (Lp.coeFn_compMeasurePreserving u
      (ginibre_measurePreserving_permute σ)),
    Lp.coeFn_smul (permutationSign σ)
      (normalizedVandermondeL2 n hn
        (Lp.compMeasurePreserving (permute σ)
          (ginibre_measurePreserving_permute σ) u))] with
      z hleft hFu hFperm huperm hsmul
  rw [hleft, hFu, hsmul]
  simp only [Pi.smul_apply]
  rw [hFperm, huperm]
  simp only [Function.comp_apply, smul_eq_mul]
  rw [normalizedMultiplier_permute]
  ring

/-- The normalized Vandermonde isometry sends AE-symmetric Ginibre functions
to AE-alternating Gaussian functions. -/
theorem normalizedVandermondeL2_mem_gaussianAlternating {n : ℕ} (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    normalizedVandermondeL2 n hn u.1 ∈ gaussianAlternatingL2 n := by
  intro σ
  rw [normalizedVandermondeL2_intertwines hn σ u.1, u.2 σ]

/-- Restriction of the normalized Vandermonde isometry from the symmetric
Ginibre subspace to the alternating Gaussian subspace. -/
def normalizedVandermondeSymmetricL2 (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricL2 n →ₗᵢ[ℂ] gaussianAlternatingL2 n where
  toFun u := ⟨normalizedVandermondeL2 n hn u.1,
    normalizedVandermondeL2_mem_gaussianAlternating hn u⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add (normalizedVandermondeL2 n hn) u.1 v.1
  map_smul' c u := by
    apply Subtype.ext
    exact map_smul (normalizedVandermondeL2 n hn) c u.1
  norm_map' u := (normalizedVandermondeL2 n hn).norm_map u.1

/-- Isometric equivalence of the symmetric Ginibre subspace with the range of
normalized Vandermonde multiplication inside the alternating Gaussian
subspace. -/
def normalizedVandermondeSymmetricL2EquivRange (n : ℕ) (hn : 0 < n) :=
  (normalizedVandermondeSymmetricL2 n hn).equivRange

/-- The ambient range of the restricted map is contained in the alternating
Gaussian subspace. -/
theorem normalizedVandermondeL2_range_symmetry_le {n : ℕ} (hn : 0 < n) :
    LinearMap.range
        ((normalizedVandermondeL2 n hn).toLinearMap.comp
          (ginibreSymmetricL2 n).subtype) ≤
      gaussianAlternatingL2 n := by
  rintro v ⟨u, rfl⟩
  exact normalizedVandermondeL2_mem_gaussianAlternating hn u

end

end GinibrePoincare

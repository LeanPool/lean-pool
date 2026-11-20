/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialVandermondeSymmetry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondeInverse

/-!
# General potential Vandermonde symmetry

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialVandermondeL2_intertwines`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem measurePreserving_permute_configurationVolume {n : ℕ} (σ : ParticlePermutation n) :
    MeasurePreserving (permute σ) (configurationVolume n) (configurationVolume n) := by
  unfold configurationVolume
  rw [volume_pi]
  convert measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℂ)) σ.symm using 1
  funext z
  exact (permutationMeasurableEquiv_apply σ z).symm

/-- Composition with the particle permutation `σ`, as a linear isometry of `L²` of Lebesgue
measure on configurations. -/
def volumePermutationL2 {n : ℕ} (σ : ParticlePermutation n) :
    Lp ℂ 2 (configurationVolume n) →ₗᵢ[ℂ] Lp ℂ 2 (configurationVolume n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (permute σ) (measurePreserving_permute_configurationVolume σ)

/-- Composition with the particle permutation `σ`, as a linear isometry of
`L²(potentialMeasure n V)`. -/
def potentialPermutationL2 (n : ℕ) {V : Potential} (hV : Continuous V)
    (σ : ParticlePermutation n) :
    Lp ℂ 2 (potentialMeasure n V) →ₗᵢ[ℂ] Lp ℂ 2 (potentialMeasure n V) :=
  Lp.compMeasurePreservingₗᵢ ℂ (permute σ) (measurePreserving_permute_potentialMeasure n hV σ)

theorem potentialVandermondeMultiplier_permute {n : ℕ} (V : Potential)
    (σ : ParticlePermutation n) (z : Configuration n) :
    potentialVandermondeMultiplier n V (permute σ z) =
      permutationSign σ * potentialVandermondeMultiplier n V z := by
  have hs : (∑ i : Fin n, V (permute σ z i)) = ∑ i : Fin n, V (z i) := by
    simpa [permute] using Equiv.sum_comp σ (fun i => V (z i))
  unfold potentialVandermondeMultiplier
  rw [hs, vandermonde_permute]
  ring

theorem potentialVandermondeL2_intertwines {n : ℕ} (hn : 0 < n) {V : Potential} (hV : Continuous V)
    (hfin : potentialPartition n V < ⊤)
    (σ : ParticlePermutation n) (u : Lp ℂ 2 (potentialMeasure n V)) :
    volumePermutationL2 σ (potentialVandermondeL2 n hn hV hfin u) =
      permutationSign σ •
        potentialVandermondeL2 n hn hV hfin (potentialPermutationL2 n hV σ u) := by
  unfold volumePermutationL2 potentialPermutationL2
  change Lp.compMeasurePreserving (permute σ)
      (measurePreserving_permute_configurationVolume σ) (potentialVandermondeL2 n hn hV hfin u) =
    permutationSign σ • potentialVandermondeL2 n hn hV hfin
      (Lp.compMeasurePreserving (permute σ)
        (measurePreserving_permute_potentialMeasure n hV σ) u)
  apply Lp.ext
  have hac := configurationVolume_absolutelyContinuous_potentialMeasure n hn hV hfin
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (potentialVandermondeL2 n hn hV hfin u)
      (measurePreserving_permute_configurationVolume σ),
    (measurePreserving_permute_configurationVolume σ).quasiMeasurePreserving.ae_eq_comp
      (potentialVandermondeL2_coeFn_public n hn hV hfin u),
    potentialVandermondeL2_coeFn_public n hn hV hfin
      (Lp.compMeasurePreserving (permute σ)
        (measurePreserving_permute_potentialMeasure n hV σ) u),
    hac.ae_eq (Lp.coeFn_compMeasurePreserving u
      (measurePreserving_permute_potentialMeasure n hV σ)),
    Lp.coeFn_smul (permutationSign σ)
      (potentialVandermondeL2 n hn hV hfin
        (Lp.compMeasurePreserving (permute σ)
          (measurePreserving_permute_potentialMeasure n hV σ) u))] with
      z hleft hFu hFperm huperm hsmul
  rw [hleft, hFu, hsmul]
  simp only [Pi.smul_apply]
  rw [hFperm, huperm]
  simp only [Function.comp_apply, smul_eq_mul]
  rw [potentialVandermondeMultiplier_permute V]
  ring

end
end GinibrePoincare

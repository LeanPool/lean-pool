/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorSymmetry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreCompatibility

/-!
# Ginibre Full Generator Symmetry
-/


@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

/-- The ordinary full weak value domain detects every real Ginibre L² class. -/
theorem ginibreFullL2_orthogonal_weak_eq_zero (n : ℕ) (hn : 0 < n)
    (a : GinibreFullValueL2 n)
    (ha : ∀ u : GinibreFullValueL2 n, ∀ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u g → inner ℝ a u = 0) : a = 0 := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have htest (ψ : Configuration n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
      (∫ z, ψ z • a z ∂ginibreMeasure n) = 0 := by
    obtain ⟨hm, hg⟩ := ginibreFull_smoothCompact_memLp n hn ψ hψ hc
    let u := hm.toLp ψ
    let g := hg.toLp (ginibreEuclideanGradient ψ)
    have hweak := ginibre_smooth_distributional_gradient n hn u g ψ hψ hm.coeFn_toLp hg.coeFn_toLp
    have hinner := ha u g hweak
    rw [L2.inner_def] at hinner
    rw [← hinner]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with z hz
    change u z = ψ z at hz
    change ψ z * a z = u z * a z
    rw [hz]
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp a).integrable (by norm_num)).locallyIntegrable htest
  apply Lp.ext
  filter_upwards [hz] with z hz
  simpa using hz

/-- Particle pullback and its inverse are genuine inverse L² maps. -/
theorem ginibreFullRealPermutation_inverse {n : ℕ} (σ : ParticlePermutation n)
    (a : GinibreFullValueL2 n) :
    ginibreRealPermutationL2 σ (ginibreRealPermutationL2 σ.symm a) = a := by
  apply Lp.ext
  have hc := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
    (ginibreRealPermutationL2_ae σ.symm a)
  filter_upwards [ginibreRealPermutationL2_ae σ (ginibreRealPermutationL2 σ.symm a), hc] with z hp
    hc
  simp only [Function.comp_apply] at hc
  rw [hp, hc]
  have he : permute σ.symm (permute σ z) = z := by
    ext i
    simp [permute]
  rw [he]

/-- The adjoint of particle pullback is the inverse pullback. -/
theorem ginibreFullRealPermutation_inner {n : ℕ} (σ : ParticlePermutation n)
    (u a : GinibreFullValueL2 n) :
    inner ℝ (ginibreRealPermutationL2 σ u) a =
      inner ℝ u (ginibreRealPermutationL2 σ.symm a) := by
  have h := (ginibreRealPermutationL2 σ).inner_map_map u (ginibreRealPermutationL2 σ.symm a)
  rw [ginibreFullRealPermutation_inverse] at h
  exact h

/-- The natural gradient representation is an inner-product isometry. -/
theorem ginibreFullGradientPermutation_inner {n : ℕ} (σ : ParticlePermutation n)
    (g h : GinibreFullGradientL2 n) :
    inner ℝ (ginibreGradientPermutationL2 σ g) (ginibreGradientPermutationL2 σ h) =
      inner ℝ g h := by
  have hp := norm_add_sq_real (ginibreGradientPermutationL2 σ g) (ginibreGradientPermutationL2 σ h)
  rw [← map_add, ginibreGradientPermutationL2_norm, ginibreGradientPermutationL2_norm,
    ginibreGradientPermutationL2_norm] at hp
  have hq := norm_add_sq_real g h
  linarith

/-- The actual concrete core pregenerator is permutation invariant as an L²
class; this follows from its full weak Green identity, without a symmetry
assumption on the generator image. -/
theorem ginibreFullCorePregenerator_symmetric {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreFullCorePregenerator hn f hf ∈ ginibreFullSymmetricValues n := by
  intro σ
  have hfixed := (ginibreFullCorePair hn f hf).property.2
  have hpair (τ : ParticlePermutation n) (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
      (hu : IsGinibreDistributionalGradient n u g) :
      inner ℝ (ginibreRealPermutationL2 τ u) (ginibreFullCorePregenerator hn f hf) =
        inner ℝ u (ginibreFullCorePregenerator hn f hf) := by
    have hpu := ginibreDistributionalGradient_permute hn τ u g hu
    have hp := ginibreFullGenerator_weak_core_green hn _ _ hpu f hf
    have h := ginibreFullGenerator_weak_core_green hn u g hu f hf
    have hi := ginibreFullGradientPermutation_inner τ g (ginibreFullCoreGradient hn f hf)
    have hfixedG : ginibreGradientPermutationL2 τ (ginibreFullCoreGradient hn f hf) =
        ginibreFullCoreGradient hn f hf := (hfixed τ).2
    rw [hfixedG] at hi
    rw [hi] at hp
    linarith
  have hz : ginibreRealPermutationL2 σ (ginibreFullCorePregenerator hn f hf) -
      ginibreFullCorePregenerator hn f hf = 0 := by
    apply ginibreFullL2_orthogonal_weak_eq_zero n hn
    intro u g hu
    have h := hpair σ.symm u g hu
    rw [ginibreFullRealPermutation_inner] at h
    simp only [Equiv.symm_symm] at h
    rw [inner_sub_left]
    have h' : inner ℝ (ginibreRealPermutationL2 σ (ginibreFullCorePregenerator hn f hf)) u =
        inner ℝ (ginibreFullCorePregenerator hn f hf) u := by
      simpa only [real_inner_comm] using h
    exact sub_eq_zero.mpr h'
  exact sub_eq_zero.mp hz

end
end GinibrePoincare

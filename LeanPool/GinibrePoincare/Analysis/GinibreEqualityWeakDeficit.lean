/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityWeakDeficit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorHermiteLowering
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakHolomorphic

/-! # Passing the Hermite deficit to the full weak domain

Approximate a symmetric distributional value-gradient pair by smooth
collision-free core pairs. Variance and holomorphic projection norms are
continuous in the value, so the core Pythagorean and zero-mode identities pass
to the limit. The lowering/energy results identify the weighted positive modes;
the scalar series identity then gives the first deficit without a polynomial
or smoothness hypothesis. This module supplies the weak-domain input to the
subsequent generator-domain square completion.
-/


@[expose] public section


noncomputable section
namespace GinibrePoincare
open MeasureTheory Filter ComplexHermite
open scoped Topology

lemma ginibreFullCenteredValue_core {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f)
    (u : GinibreFullValueL2 n) (hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f) :
    ginibreFullComplexOfReal n (ginibreFullCenter n hn u) = centeredObservableL2 hn f hf := by
  rw [ginibreFullCenter_apply]
  apply Lp.ext
  have hm : ginibreL2Mean n u = smoothGinibreMean n f := integral_congr_ae hu
  filter_upwards [ginibreFullComplexOfReal_ae n (u - ginibreRealConstantL2 n hn (ginibreL2Mean n
    u)),
    Lp.coeFn_sub u (ginibreRealConstantL2 n hn (ginibreL2Mean n u)),
    ginibreRealConstantL2_ae n hn (ginibreL2Mean n u), hu,
    centeredObservableL2_coeFn hn f hf] with z hz hs hc hfz hcenter
  rw [hz, hs]
  change ((u z - (ginibreRealConstantL2 n hn (ginibreL2Mean n u)) z : ℝ) : ℂ) = _
  rw [hc, hfz, hm, hcenter]
  rfl

lemma ginibreFullCenteredValue_norm_sq {n : ℕ} (hn : 0 < n) (u : GinibreFullValueL2 n) :
    ‖ginibreFullComplexOfReal n (ginibreFullCenter n hn u)‖ ^ 2 = ginibreL2Variance n hn u := by
  rw [← ginibreFullCenter_variance,
    ← integral_norm_sq_eq_L2_norm_sq (ginibreMeasure n),
    ← integral_norm_sq_eq_L2_norm_sq (ginibreMeasure n)]
  apply integral_congr_ae
  filter_upwards [ginibreFullComplexOfReal_ae n (ginibreFullCenter n hn u)] with z hz
  simp [hz]

/-- Continuous holomorphic/remainder geometry extends to the actual full weak domain. -/
theorem ginibreFullWeak_holomorphic_geometry {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreL2Variance n hn u = 2 * ‖ginibreFullHolomorphicPart n hn u‖ ^ 2 +
      ‖ginibreFullHolomorphicRemainder n hn u‖ ^ 2 := by
  obtain ⟨q, hq, hlim⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn u g hu hs
  let L := fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n => ginibreL2Variance n hn p.1
  let R := fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
    2 * ‖ginibreFullHolomorphicPart n hn p.1‖ ^ 2 + ‖ginibreFullHolomorphicRemainder n hn p.1‖ ^ 2
  have hL : Continuous L := (ginibreL2Variance_continuous n hn).comp continuous_fst
  have hR : Continuous R := (continuous_const.mul
    (((ginibreFullHolomorphicPart_continuous n hn).comp continuous_fst).norm.pow 2)).add
    (((ginibreFullHolomorphicRemainder_continuous n hn).comp continuous_fst).norm.pow 2)
  have hc : IsClosed {p | L p = R p} := isClosed_eq hL hR
  have hmem : ∀ m, q m ∈ {p | L p = R p} := by
    intro m
    obtain ⟨f, hf, hv, hg⟩ := hq m
    have he := (centeredHolomorphicRemainderGeometry hn f hf).2.2.2
    have hval := ginibreFullCenteredValue_core hn f hf (q m).1 hv
    change ginibreL2Variance n hn (q m).1 = _
    rw [← ginibreFullCenteredValue_norm_sq, hval, norm_sq_centeredObservableL2]
    simpa only [R, ginibreFullHolomorphicPart, ginibreFullHolomorphicRemainder, hval] using he
  have htarget : (u, g) ∈ {p | L p = R p} := hc.mem_of_tendsto hlim (Eventually.of_forall hmem)
  exact htarget

/-- The actual Gaussian zero mode has precisely the holomorphic projection norm. -/
theorem ginibreFullWeak_zero_mode_norm {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ‖gaussianHermiteMode hn 0 (ginibreFullCenteredTransform n hn u)‖ ^ 2 =
      ‖ginibreFullHolomorphicPart n hn u‖ ^ 2 := by
  obtain ⟨q, hq, hlim⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn u g hu hs
  let L := fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
    ‖gaussianHermiteMode hn 0 (ginibreFullCenteredTransform n hn p.1)‖ ^ 2
  let R := fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
    ‖ginibreFullHolomorphicPart n hn p.1‖ ^ 2
  have hL : Continuous L := by
    simp only [L, gaussianHermiteMode_eq_antiDegreeProjection]
    exact ((hermiteAntiDegreeProjection n hn 0).continuous.comp
      ((normalizedVandermondeL2 n hn).continuous.comp
        ((ginibreFullComplexOfReal n).continuous.comp
          ((ginibreFullCenter n hn).continuous.comp continuous_fst)))).norm.pow 2
  have hR : Continuous R := ((ginibreFullHolomorphicPart_continuous n hn).comp
    continuous_fst).norm.pow 2
  have hc : IsClosed {p | L p = R p} := isClosed_eq hL hR
  have hmem : ∀ m, q m ∈ {p | L p = R p} := by
    intro m
    obtain ⟨f, hf, hv, hg⟩ := hq m
    change ‖gaussianHermiteMode hn 0 (ginibreFullCenteredTransform n hn (q m).1)‖ ^ 2 = _
    rw [ginibreFullCenteredTransform_core hn f hf _ hv]
    simpa only [R, ginibreFullHolomorphicPart, ginibreFullCenteredValue_core hn f hf _ hv] using
      concreteZeroMode_norm_sq_eq_holomorphicProjection hn f hf
  have htarget : (u, g) ∈ {p | L p = R p} := hc.mem_of_tendsto hlim (Eventually.of_forall hmem)
  exact htarget

/-- The exact first Poincaré deficit identity on the entire actual symmetric
ordinary weak domain, including convergence of the weighted Hermite tail. -/
theorem ginibreFullWeak_first_deficit_identity {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    Summable (fun k : ℕ => (k : ℝ) *
      positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u) k) ∧
    ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u =
      2 * ‖ginibreFullHolomorphicRemainder n hn u‖ ^ 2 +
        4 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u)) := by
  let a := positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u)
  have ha : Summable a := summable_positiveHermiteModeMass hn _
  have he := ginibreFullWeak_weighted_hermite_energy hn u g hu hs
  have ht : Summable (fun k : ℕ => (k : ℝ) * a k) := by
    have hs := he.summable.sub ha
    apply hs.congr
    intro k
    dsimp [a]
    ring
  have henergy : ginibreWeakEnergy n g = 4 * modeEnergy a := by
    unfold modeEnergy
    simp only [a, Nat.cast_add, Nat.cast_one]
    rw [he.tsum_eq]
    ring
  have hp : ginibreL2Variance n hn u =
      ‖ginibreFullHolomorphicPart n hn u‖ ^ 2 + modeMass a := by
    have hp := norm_sq_eq_zeroMode_add_positiveModeMass hn
      (ginibreFullCenteredTransform n hn u)
    have hnorm : ‖ginibreFullCenteredTransform n hn u‖ =
        ‖ginibreFullComplexOfReal n (ginibreFullCenter n hn u)‖ :=
      (normalizedVandermondeL2 n hn).norm_map _
    rw [hnorm, ginibreFullCenteredValue_norm_sq,
      ginibreFullWeak_zero_mode_norm hn u g hu hs] at hp
    exact hp
  exact ⟨ht, infinite_deficit_identity a ha ht _ _ _ _ hp
    (ginibreFullWeak_holomorphic_geometry hn u g hu hs) henergy⟩

/-- Exhaustive spectral equality criterion on the actual full weak domain. -/
theorem ginibreEquality_full_weak_spectral_iff {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u ↔
      ginibreFullHolomorphicRemainder n hn u = 0 ∧
        ∀ k : ℕ, 0 < k → ginibreFullHigherMode n hn k u = 0 := by
  constructor
  · intro he
    exact ⟨ginibreEquality_weak_holomorphic_remainder_zero hn u g hu hs he,
      ginibreEquality_weak_higher_modes_vanish hn u g hu hs he⟩
  · rintro ⟨hr, hm⟩
    obtain ⟨ht, hi⟩ := ginibreFullWeak_first_deficit_identity hn u g hu hs
    have hz : modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u)) = 0 := by
      apply (ginibreEquality_modeTail_eq_zero_iff _ (fun k => sq_nonneg _) ht).mpr
      intro k hk
      have hmode := hm k hk
      change hermiteAntiDegreeProjection n hn (k + 1)
        (ginibreFullCenteredTransform n hn u) = 0 at hmode
      simp only [
        gaussianHermiteMode_eq_antiDegreeProjection, hmode, norm_zero, zero_pow (by decide : 2≠0)]
    rw [hr, norm_zero, zero_pow (by decide : 2≠0), hz] at hi
    linarith

end GinibrePoincare

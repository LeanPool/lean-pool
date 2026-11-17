/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityWeakModes.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityCore
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakVariational
public import LeanPool.GinibrePoincare.Analysis.GinibreComplexL2

/-!
# Ginibre Equality Weak Modes
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory Filter ComplexHermite
open scoped Topology

/-- Actual centered Vandermonde transform on the full real L² domain. -/
def ginibreFullCenteredTransform (n : ℕ) (hn : 0 < n) (u : GinibreFullValueL2 n) :=
  normalizedVandermondeL2 n hn (ginibreFullComplexOfReal n (ginibreFullCenter n hn u))

/-- The actual higher antiholomorphic mode on full real Ginibre L². -/
def ginibreFullHigherMode (n : ℕ) (hn : 0 < n) (k : ℕ) (u : GinibreFullValueL2 n) :=
  hermiteAntiDegreeProjection n hn (k + 1) (ginibreFullCenteredTransform n hn u)

theorem ginibreFullHigherMode_continuous (n : ℕ) (hn : 0 < n) (k : ℕ) :
    Continuous (ginibreFullHigherMode n hn k) :=
  (hermiteAntiDegreeProjection n hn (k + 1)).continuous.comp
    ((normalizedVandermondeL2 n hn).continuous.comp
      ((ginibreFullComplexOfReal n).continuous.comp (ginibreFullCenter n hn).continuous))

lemma ginibreFullCenteredTransform_core {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f)
    (u : GinibreFullValueL2 n) (hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f) :
    ginibreFullCenteredTransform n hn u = transformedCenteredObservableL2 hn f hf := by
  have hm : ginibreL2Mean n u = smoothGinibreMean n f := integral_congr_ae hu
  unfold ginibreFullCenteredTransform transformedCenteredObservableL2
  congr 1
  apply Lp.ext
  rw [ginibreFullCenter_apply]
  filter_upwards [ginibreFullComplexOfReal_ae n (u - ginibreRealConstantL2 n hn (ginibreL2Mean n
    u)),
    Lp.coeFn_sub u (ginibreRealConstantL2 n hn (ginibreL2Mean n u)),
    ginibreRealConstantL2_ae n hn (ginibreL2Mean n u), hu,
    centeredObservableL2_coeFn hn f hf] with z hz hs hc hfz hcenter
  rw [hz, hs]
  change ((u z - (ginibreRealConstantL2 n hn (ginibreL2Mean n u)) z : ℝ) : ℂ) = _
  rw [hc, hfz, hm, hcenter]
  rfl

lemma ginibreEquality_core_pair_mode_bound {n : ℕ} (hn : 0 < n)
    (p : GinibreFullValueL2 n × GinibreFullGradientL2 n)
    (hp : p ∈ ginibreTheoremOneNineCorePairs n) (k : ℕ) :
    4 * (k : ℝ) * ‖ginibreFullHigherMode n hn k p.1‖ ^ 2 ≤
      ginibreWeakEnergy n p.2 - 2 * ginibreL2Variance n hn p.1 := by
  obtain ⟨f, hf, hv, hg⟩ := hp
  have hmode : ‖ginibreFullHigherMode n hn k p.1‖ ^ 2 =
      concretePositiveHermiteModeMass hn f hf k := by
    unfold ginibreFullHigherMode concretePositiveHermiteModeMass positiveHermiteModeMass
    rw [ginibreFullCenteredTransform_core hn f hf _ hv,
      gaussianHermiteMode_eq_antiDegreeProjection]
  have he := ginibreWeakEnergy_eq_smoothGinibreEnergy p.2 f hg
  have hvar := ginibreL2Variance_eq_smoothGinibreVariance hn p.1 f hv
  rw [hmode, he, hvar]
  exact ginibreEquality_core_mode_bound hn f hf k

/-- Every individual high Hermite mode is bounded by the actual full weak
Poincaré deficit, with precisely the core theorem's coefficient. -/
theorem ginibreEquality_weak_mode_bound {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g))
    (k : ℕ) :
    4 * (k : ℝ) * ‖ginibreFullHigherMode n hn k u‖ ^ 2 ≤
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u := by
  obtain ⟨q, hq, hlim⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn u g hu hs
  have hclosed : IsClosed {p : GinibreFullValueL2 n × GinibreFullGradientL2 n |
      4 * (k : ℝ) * ‖ginibreFullHigherMode n hn k p.1‖ ^ 2 ≤
        ginibreWeakEnergy n p.2 - 2 * ginibreL2Variance n hn p.1} := by
    have hleft : Continuous (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
        4 * (k : ℝ) * ‖ginibreFullHigherMode n hn k p.1‖ ^ 2) :=
      continuous_const.mul (((ginibreFullHigherMode_continuous n hn k).comp
        continuous_fst).norm.pow 2)
    have hright : Continuous (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
        ginibreWeakEnergy n p.2 - 2 * ginibreL2Variance n hn p.1) :=
      ((ginibreWeakEnergy_continuous n).comp continuous_snd).sub
        (continuous_const.mul ((ginibreL2Variance_continuous n hn).comp continuous_fst))
    exact isClosed_le hleft hright
  have hqmem : ∀ m, q m ∈ {p : GinibreFullValueL2 n × GinibreFullGradientL2 n |
      4 * (k : ℝ) * ‖ginibreFullHigherMode n hn k p.1‖ ^ 2 ≤
        ginibreWeakEnergy n p.2 - 2 * ginibreL2Variance n hn p.1} :=
    fun m => ginibreEquality_core_pair_mode_bound hn (q m) (hq m) k
  have hmem : (u, g) ∈ {p : GinibreFullValueL2 n × GinibreFullGradientL2 n |
      4 * (k : ℝ) * ‖ginibreFullHigherMode n hn k p.1‖ ^ 2 ≤
        ginibreWeakEnergy n p.2 - 2 * ginibreL2Variance n hn p.1} :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall hqmem)
  exact hmem

/-- Full weak equality forces all actual antiholomorphic modes of degree at
least two to vanish, without a smoothness or polynomial assumption. -/
theorem ginibreEquality_weak_higher_modes_vanish {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g))
    (heq : ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u)
    (k : ℕ) (hk : 0 < k) : ginibreFullHigherMode n hn k u = 0 := by
  have hb := ginibreEquality_weak_mode_bound hn u g hu hs k
  rw [heq, sub_self] at hb
  have hp : 0 < (4 : ℝ) * k := by positivity
  have hz : ‖ginibreFullHigherMode n hn k u‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg (‖ginibreFullHigherMode n hn k u‖)]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ginibreFullHigherMode n hn k u)])

/-- The entire centered Vandermonde transform of a full weak equality
attainer consists exactly of its antiholomorphic degrees zero and one. -/
theorem ginibreEquality_weak_transform_low_modes {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g))
    (heq : ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u) :
    ginibreFullCenteredTransform n hn u =
      hermiteAntiDegreeProjection n hn 0 (ginibreFullCenteredTransform n hn u) +
      hermiteAntiDegreeProjection n hn 1 (ginibreFullCenteredTransform n hn u) := by
  have hz (d : ℕ) (hd : d ∉ ({0, 1} : Finset ℕ)) :
      gaussianHermiteMode hn d (ginibreFullCenteredTransform n hn u) = 0 := by
    have h0 : d ≠ 0 := by simpa using fun h => hd (by simp [h])
    have h1 : d ≠ 1 := by simpa using fun h => hd (by simp [h])
    have hd2 : 2 ≤ d := by omega
    have h := ginibreEquality_weak_higher_modes_vanish hn u g hu hs heq (d - 1) (by omega)
    unfold ginibreFullHigherMode at h
    rw [Nat.sub_add_cancel (by omega : 1 ≤ d)] at h
    rw [gaussianHermiteMode_eq_antiDegreeProjection]
    exact h
  calc
    ginibreFullCenteredTransform n hn u = ∑' d, gaussianHermiteMode hn d
        (ginibreFullCenteredTransform n hn u) := (tsum_gaussianHermiteMode hn _).symm
    _ = ∑ d ∈ ({0, 1} : Finset ℕ), gaussianHermiteMode hn d
        (ginibreFullCenteredTransform n hn u) := tsum_eq_sum hz
    _ = _ := by
      simp only [Finset.sum_insert (by simp : (0 : ℕ) ∉ ({1} : Finset ℕ)), Finset.sum_singleton,
        gaussianHermiteMode_eq_antiDegreeProjection]

end GinibrePoincare

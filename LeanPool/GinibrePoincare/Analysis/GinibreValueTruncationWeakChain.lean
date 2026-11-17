/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreValueTruncationWeakChain.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreValueTruncationChainLimits
public import LeanPool.GinibrePoincare.Analysis.GinibreWeightedInteriorMollification
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradientSupport
public import LeanPool.GinibrePoincare.Analysis.SmoothTestLocalization

/-! # Concrete nonlinear chain rule on the independent weak-gradient domain -/


@[expose] public section


open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section

/-- The actual weak nonlinear chain rule for compact values supported away from
collisions; the local smooth approximation is proved, not supplied. -/
theorem ginibreValueTruncation_chain_interior (n : ℕ) (hn : 0 < n) (m : ℕ)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ {z | CollisionFree z}) :
    IsGinibreDistributionalGradient n
      ((ginibreValueTruncation_memLp n m u (Lp.memLp u)).toLp (fun z => sobolevValueTruncation m
        (u z)))
      ((ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g (Lp.memLp g)).toLp
        (fun z => deriv (sobolevValueTruncation m) (u z) • g z)) := by
  obtain ⟨h, hh, hhc, hhs⟩ := ginibre_distributional_gradient_exists_supported_representative n hn
    u g hg f hf hc
  let φ := ginibreInteriorBump n 1 (by norm_num)
  obtain ⟨v, w, he, ht⟩ := ginibre_weighted_interior_mollification n hn u g hg
    f h hf hh hc hhc hs (hhs.trans hs) φ
    (ginibreInteriorBump_radius_tendsto n 1 (by norm_num))
  exact ginibreValueTruncation_chain_of_smooth_limits n hn m u g v w
    (fun j => (φ j).normed volume ⋆[lsmul ℝ ℝ, volume] f)
    (fun j => (he j).1) (fun j => (he j).2.2.1) (fun j => (he j).2.2.2)
    (continuous_fst.tendsto _ |>.comp ht) (continuous_snd.tendsto _ |>.comp ht)

/-- A compact interior test has an actual compact smooth interior cutoff equal
to one near its entire support. -/
theorem exists_compact_collisionFree_test_cutoff (n : ℕ)
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z}) :
    ∃ χ : Configuration n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ {z | CollisionFree z} ∧ ∀ z ∈ K, χ =ᶠ[𝓝 z] 1 := by
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.exists_pos_norm_lt
  obtain ⟨χ, hχ, hχs, hχ1⟩ := exists_smooth_open_cutoff K
    ({z | CollisionFree z} ∩ Metric.ball 0 R) hK.isClosed
    ((isOpen_collisionFree n).inter Metric.isOpen_ball)
    (fun z hz => ⟨hs hz, by simpa only [Metric.mem_ball, dist_zero_right] using hR z hz⟩)
  refine ⟨χ, hχ,?_, hχs.trans Set.inter_subset_left, hχ1⟩
  exact (isCompact_closedBall (0 : Configuration n) R).of_isClosed_subset
    (isClosed_tsupport χ) (hχs.trans (Set.inter_subset_right.trans Metric.ball_subset_closedBall))

/-- The actual distributional nonlinear chain rule holds for every independently
defined Ginibre weak Sobolev pair, with no support or bounded-value premise. -/
theorem ginibreValueTruncation_distributional (n : ℕ) (hn : 0 < n) (m : ℕ)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g) :
    IsGinibreDistributionalGradient n
      ((ginibreValueTruncation_memLp n m u (Lp.memLp u)).toLp (fun z => sobolevValueTruncation m
        (u z)))
      ((ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g (Lp.memLp g)).toLp
        (fun z => deriv (sobolevValueTruncation m) (u z) • g z)) := by
  let U := (ginibreValueTruncation_memLp n m u (Lp.memLp u)).toLp (fun z => sobolevValueTruncation
    m (u z))
  let G := (ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g (Lp.memLp
    g)).toLp
    (fun z => deriv (sobolevValueTruncation m) (u z) • g z)
  have hU : (U : Configuration n → ℝ) =ᵐ[volume] fun z => sobolevValueTruncation m (u z) :=
    (ginibre_ae_eq_iff_volume n hn _ _).mp (ginibreValueTruncation_memLp n m u (Lp.memLp
      u)).coeFn_toLp
  have hG : (G : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[volume]
      fun z => deriv (sobolevValueTruncation m) (u z) • g z :=
    (ginibre_ae_eq_iff_volume n hn _ _).mp
      (ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g (Lp.memLp
        g)).coeFn_toLp
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn U (Lp.memLp U), ?_, ?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) k
    exact ginibre_memLp_locallyIntegrable_collisionFree hn _ (P.comp_memLp G)
  · intro k θ hθ hc hs
    obtain ⟨χ, hχ, hχc, hχs, hχ1⟩ := exists_compact_collisionFree_test_cutoff n (tsupport θ) hc hs
    let q := ginibreWeakMultiplierPair n hn u g χ hχ hχc
    have hq := ginibreWeakMultiplierPair_distributional n hn u g hg χ hχ hχc
    have hv := (ginibre_weak_multiplier_memLp n hn u g χ hχ hχc).1.coeFn_toLp
    have hw := (ginibre_weak_multiplier_memLp n hn u g χ hχ hχc).2.coeFn_toLp
    have hqt := ginibreValueTruncation_chain_interior n hn m q.1 q.2 hq
      (fun z => χ z * u z) hv hχc.mul_right
      (tsupport_mul_subset_left.trans hχs)
    have hqU := (ginibre_ae_eq_iff_volume n hn _ _).mp
      (ginibreValueTruncation_memLp n m q.1 (Lp.memLp q.1)).coeFn_toLp
    have hqG := (ginibre_ae_eq_iff_volume n hn _ _).mp
      (ginibreValueTruncation_vector_memLp n m q.1 (Lp.aestronglyMeasurable q.1) q.2 (Lp.memLp
        q.2)).coeFn_toLp
    have hv' := (ginibre_ae_eq_iff_volume n hn _ _).mp hv
    have hw' := (ginibre_ae_eq_iff_volume n hn _ _).mp hw
    have hχzero (z : Configuration n) (hz : z ∈ tsupport θ) :
        χ z = 1 ∧ ginibreEuclideanGradient χ z = 0 := by
      have he := hχ1 z hz
      refine ⟨he.eq_of_nhds, ?_⟩
      have hd : fderiv ℝ χ z = 0 := by rw [he.fderiv_eq]; simp
      ext l
      simp [ginibreEuclideanGradient, hd]
    have he := hqt.2.2 k θ hθ hc hs
    have hl : (∫ z, G z k * θ z) =
        ∫ z, ((ginibreValueTruncation_vector_memLp n m q.1 (Lp.aestronglyMeasurable q.1) q.2
          (Lp.memLp q.2)).toLp
          (fun z => deriv (sobolevValueTruncation m) (q.1 z) • q.2 z)) z k * θ z := by
      apply integral_congr_ae
      filter_upwards [hG, hqG, hv', hw'] with z h1 h2 h3 h4
      by_cases hz : z ∈ tsupport θ
      · obtain ⟨hχz, hχdz⟩ := hχzero z hz
        change q.1 z = _ at h3
        change q.2 z = _ at h4
        rw [h1, h2, h3, h4, hχz, hχdz]
        simp
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have hr : (∫ z, U z * fderiv ℝ θ z (ginibreCoordinateDirection k)) =
        ∫ z, ((ginibreValueTruncation_memLp n m q.1 (Lp.memLp q.1)).toLp
          (fun z => sobolevValueTruncation m (q.1 z))) z * fderiv ℝ θ z
            (ginibreCoordinateDirection k) := by
      apply integral_congr_ae
      filter_upwards [hU, hqU, hv'] with z h1 h2 h3
      by_cases hz : z ∈ tsupport θ
      · change q.1 z = _ at h3
        rw [h1, h2, h3, (hχzero z hz).1, one_mul]
      · rw [fderiv_of_notMem_tsupport ℝ hz]
        simp
    rw [hl, hr]
    exact he
end
end GinibrePoincare

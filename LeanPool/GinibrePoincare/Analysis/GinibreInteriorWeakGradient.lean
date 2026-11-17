/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreInteriorWeakGradient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreLocalSobolev
public import LeanPool.GinibrePoincare.Analysis.SobolevTruncation
public import LeanPool.GinibrePoincare.Analysis.WeakDerivativeMollification

/-! # Interior compact weak-gradient pairs and ordinary mollification

The ordinary local Ginibre weak derivative identity extends to all Lebesgue
tests when both representatives have compact support away from collisions.
This allows genuine smooth convolution of those representatives.
-/


@[expose] public section


open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section


/-- A smooth density cutoff supported away from collisions and equal to one
on a neighbourhood of every point of an interior compact set. -/
theorem exists_ginibreInteriorCutoff (n : ℕ) (hn : 0 < n)
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z}) :
    ∃ χ : Configuration n → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ {z | CollisionFree z} ∧ ∀ z ∈ K, χ =ᶠ[𝓝 z] 1 := by
  classical
  by_cases hne : K.Nonempty
  · let ρ := ginibreLebesgueDensityReal n
    obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne
      (contDiff_ginibreLebesgueDensityReal n).continuous.continuousOn
    have hp : 0 < ρ x := lt_of_le_of_ne (ginibreLebesgueDensityReal_nonneg n x)
      (ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn (hs hx)).symm
    let a := ρ x / 4
    have ha : 0 < a := by dsimp [a]; positivity
    let χ : Configuration n → ℝ := fun z => 1 - sobolevCutoffBump (ρ z / a)
    have hχ : ContDiff ℝ ∞ χ := contDiff_const.sub
      (sobolevCutoffBump.contDiff.comp ((contDiff_ginibreLebesgueDensityReal n).div_const a))
    refine ⟨χ, hχ, ?_, ?_⟩
    · have hsub : tsupport χ ⊆ {z | a ≤ ρ z} := by
        apply closure_minimal ?_ (isClosed_le continuous_const
          (contDiff_ginibreLebesgueDensityReal n).continuous)
        intro z hz
        by_contra hlt
        have hlt' : ρ z < a := lt_of_not_ge hlt
        have hunit : ρ z / a ∈ Metric.closedBall (0 : ℝ) sobolevCutoffBump.rIn := by
          simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, sobolevCutoffBump]
          rw [abs_of_nonneg (div_nonneg (ginibreLebesgueDensityReal_nonneg n z) ha.le)]
          exact ((div_lt_one ha).mpr hlt').le
        exact hz (by dsimp [χ]; rw [sobolevCutoffBump.one_of_mem_closedBall hunit]; simp)
      intro z hz
      have hzpos : 0 < ρ z := ha.trans_le (hsub hz)
      apply (vandermonde_ne_zero_iff z).mp
      intro hv
      have hw : vandermondeWeight z = 0 := by simp [vandermondeWeight, hv]
      have hzero : ρ z = 0 := by simp [ρ, ginibreLebesgueDensityReal, hw]
      exact hzpos.ne' hzero
    · intro z hz
      have hzlt : 2 * a < ρ z := by
        have hm : ρ x ≤ ρ z := hmin hz
        dsimp [a]
        linarith
      have he : ∀ᶠ y in 𝓝 z, 2 * a < ρ y :=
        (contDiff_ginibreLebesgueDensityReal n).continuous.continuousAt.eventually
          (lt_mem_nhds hzlt)
      filter_upwards [he] with y hy
      dsimp [χ]
      have hb : sobolevCutoffBump (ρ y / a) = 0 := by
        apply sobolevCutoffBump.zero_of_le_dist
        simp only [Real.dist_eq, sub_zero, sobolevCutoffBump]
        exact (le_abs_self _).trans' ((le_div_iff₀ ha).mpr hy.le)
      simp [hb]
  · refine ⟨0, contDiff_const, ?_, ?_⟩
    · simp
    · intro z hz
      exact (hne ⟨z, hz⟩).elim

/-- Interior compact representatives satisfy the ordinary weak-gradient identity
against every smooth compact test on the whole configuration space. -/
theorem ginibre_interior_weak_gradient_global_identity (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | CollisionFree z}) (hhs : tsupport h ⊆ {z | CollisionFree z})
    (k : Fin n × Fin 2) (θ : Configuration n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    (∫ z, h z k * θ z) = -(∫ z, f z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
  obtain ⟨χ, hχ, hsχ, heχ⟩ := exists_ginibreInteriorCutoff n hn
    (tsupport f ∪ tsupport h) (hfc.union hhc) (Set.union_subset hfs hhs)
  have htest : tsupport (χ * θ) ⊆ {z | CollisionFree z} := tsupport_mul_subset_left.trans hsχ
  have he := hg.2.2 k (χ * θ) (hχ.mul hθ) hc.mul_left htest
  have hf' := (ginibre_ae_eq_iff_volume n hn _ _).mp hf
  have hh' := (ginibre_ae_eq_iff_volume n hn _ _).mp hh
  have hl : (∫ z, g z k * (χ * θ) z) = ∫ z, h z k * θ z := by
    apply integral_congr_ae
    filter_upwards [hh'] with z hz
    rw [hz]
    by_cases ht : z ∈ tsupport h
    · have hone : χ z = 1 := (heχ z (Or.inr ht)).eq_of_nhds
      simp only [Pi.mul_apply, hone, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport ht]
  have hr : (∫ z, u z * fderiv ℝ (χ * θ) z (ginibreCoordinateDirection k)) =
      ∫ z, f z * fderiv ℝ θ z (ginibreCoordinateDirection k) := by
    apply integral_congr_ae
    filter_upwards [hf'] with z hz
    rw [hz]
    by_cases ht : z ∈ tsupport f
    · have hnear := heχ z (Or.inl ht)
      have hone : χ z = 1 := hnear.eq_of_nhds
      have hd : fderiv ℝ χ z = 0 := by rw [hnear.fderiv_eq]; simp
      rw [fderiv_mul (hχ.differentiable (by simp)).differentiableAt
        (hθ.differentiable (by simp)).differentiableAt]
      simp [hone, hd]
    · simp [image_eq_zero_of_notMem_tsupport ht]
  rwa [hl, hr] at he

/-- Genuine smooth convolution of an actual interior weak pair has the convolved
weak gradient as its actual classical Euclidean gradient. -/
theorem ginibre_interior_weak_gradient_mollification (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | CollisionFree z}) (hhs : tsupport h ⊆ {z | CollisionFree z})
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (φ ⋆[lsmul ℝ ℝ, volume] f) ∧
      ∀ z k, ginibreEuclideanGradient (φ ⋆[lsmul ℝ ℝ, volume] f) z k =
        (φ ⋆[lsmul ℝ ℝ, volume] (fun y => h y k)) z := by
  have hfv : MemLp f 2 volume := ginibre_memLp_volume_of_interior_compactSupport hn f
    ((memLp_congr_ae hf).mp (Lp.memLp u)) hfc hfs
  have hfl : LocallyIntegrable f volume := hfv.locallyIntegrable (by norm_num)
  refine ⟨hφc.contDiff_convolution_left _ hφ hfl, ?_⟩
  intro z k
  rw [ginibreEuclideanGradient_coordinate]
  exact weakDirectionalDerivative_convolution volume f (fun y => h y k) φ
    (ginibreCoordinateDirection k) hfl hφ hφc
    (ginibre_interior_weak_gradient_global_identity n hn u g hg f h hf hh hfc hhc hfs hhs k) z

end
end GinibrePoincare

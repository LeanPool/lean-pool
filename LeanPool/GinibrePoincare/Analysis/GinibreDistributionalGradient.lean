/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDistributionalGradient.lean.
Also incorporates the local L¹ integrability theorem from the upstream
GinibrePoincare/Analysis/GinibreLocalSobolev.lean under the same MIT notice.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradient

/-! # Ordinary distributional gradients on the collision-free open set

Weighted L² values and gradients are locally Lebesgue integrable where the
Ginibre density is positive. The density-weighted weak identities imply the
usual distributional derivative identity against every smooth test compactly
supported in this open set. No reverse smooth-core approximation is assumed.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section


theorem ginibreLebesgueDensityReal_ne_zero_of_collisionFree {n : ℕ} (hn : 0 < n)
    {z : Configuration n} (hz : CollisionFree z) : ginibreLebesgueDensityReal n z ≠ 0 := by
  have hw : vandermondeWeight z ≠ 0 := by
    intro h
    exact ((vandermonde_ne_zero_iff z).mpr hz) (Complex.normSq_eq_zero.mp h)
  unfold ginibreLebesgueDensityReal gaussianWeight
  exact mul_ne_zero (mul_ne_zero
    (pow_ne_zero _ (div_ne_zero (Nat.cast_ne_zero.mpr hn.ne') Real.pi_ne_zero)) hw)
    (Real.exp_ne_zero _)

theorem isOpen_collisionFree (n : ℕ) : IsOpen {z : Configuration n | CollisionFree z} := by
  have he : {z : Configuration n | CollisionFree z} =
      (vandermonde : Configuration n → ℂ) ⁻¹' ({0}ᶜ : Set ℂ) := by
    ext z
    simp [← vandermonde_ne_zero_iff]
  rw [he]
  exact isClosed_singleton.isOpen_compl.preimage (contDiff_vandermonde n).continuous

/-- The concrete normalized density measure, with its positive normalizing scalar. -/
theorem ginibreMeasure_eq_real_withDensity {n : ℕ} (hn : 0 < n) :
    ginibreMeasure n = (ginibreNormalizingMass n)⁻¹ •
      (volume : Measure (Configuration n)).withDensity
        (fun z => ENNReal.ofReal (ginibreLebesgueDensityReal n z)) := by
  unfold ginibreMeasure rawGinibreMeasure
  rw [complexGaussianDensityIdentification n hn]
  unfold complexGaussianDensityMeasure configurationVolume
  rw [← withDensity_mul _ (measurable_complexGaussianDensity n) measurable_vandermondeDensity]
  congr 2
  funext z
  rw [Pi.mul_apply, mul_comm, vandermondeDensity_mul_complexGaussianDensity]

/-- Weighted integrability is exactly integrability after multiplying by the real density. -/
theorem integrable_ginibre_iff_density {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) :
    Integrable f (ginibreMeasure n) ↔
      Integrable (fun z => ginibreLebesgueDensityReal n z * f z) := by
  rw [ginibreMeasure_eq_real_withDensity hn,
    integrable_smul_measure (ENNReal.inv_ne_zero.mpr (ginibreMassEvaluation n hn).2.ne)
      (ENNReal.inv_ne_top.mpr (ginibreMassEvaluation n hn).1.ne')]
  rw [integrable_withDensity_iff
    ((contDiff_ginibreLebesgueDensityReal n).continuous.measurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (ginibreLebesgueDensityReal_nonneg n _), mul_comm]

/-- Weighted L¹ functions are locally Lebesgue integrable where the density is positive. -/
theorem ginibre_integrable_locallyIntegrable_collisionFree {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : Integrable f (ginibreMeasure n)) :
    LocallyIntegrableOn f {z : Configuration n | CollisionFree z} volume := by
  have hi := (integrable_ginibre_iff_density hn f).mp hf
  have hc : ContinuousOn (fun z => (ginibreLebesgueDensityReal n z)⁻¹)
      {z : Configuration n | CollisionFree z} :=
    (contDiff_ginibreLebesgueDensityReal n).continuous.continuousOn.inv₀
      (fun z hz => ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn hz)
  have hl := (hi.locallyIntegrable.locallyIntegrableOn
    {z : Configuration n | CollisionFree z}).mul_continuousOn hc
      (isOpen_collisionFree n).isLocallyClosed
  apply hl.congr
  apply ae_restrict_of_forall_mem (isOpen_collisionFree n).measurableSet
  intro z hz
  dsimp
  field_simp [ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn hz]

/-- Every Ginibre L² scalar function is locally Lebesgue integrable away from collisions. -/
theorem ginibre_memLp_locallyIntegrable_collisionFree {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (ginibreMeasure n)) :
    LocallyIntegrableOn f {z : Configuration n | CollisionFree z} volume := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact ginibre_integrable_locallyIntegrable_collisionFree hn f
    (hf.integrable (by norm_num))

/-- Divide an interior test by the density squared. It remains globally smooth,
because the test vanishes on a neighbourhood of every collision. -/
theorem contDiff_collisionFree_test_div_density_sq {n : ℕ} (hn : 0 < n)
    (θ : Configuration n → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hs : tsupport θ ⊆ {z | CollisionFree z}) :
    ContDiff ℝ ∞ (fun z => θ z / ginibreLebesgueDensityReal n z ^ 2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : ginibreLebesgueDensityReal n z = 0
  · have ht : z ∉ tsupport θ := by
      intro ht
      exact (ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn (hs ht)) hz
    have he : θ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp ht
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]
  · exact hθ.contDiffAt.div ((contDiff_ginibreLebesgueDensityReal n).contDiffAt.pow 2)
      (pow_ne_zero _ hz)

theorem compactSupport_collisionFree_test_div_density_sq {n : ℕ}
    (θ : Configuration n → ℝ) (hc : HasCompactSupport θ) :
    HasCompactSupport (fun z => θ z / ginibreLebesgueDensityReal n z ^ 2) := by
  apply hc.mono
  intro z hz hzero
  apply hz
  simp [hzero]

/-- The ordinary (unweighted) distributional gradient on the collision-free open set. -/
def IsGinibreDistributionalGradient (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) : Prop :=
  LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume ∧
    (∀ k : Fin n × Fin 2,
      LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume) ∧
    ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
        (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k))

/-- Weighted weak identities give the actual distributional gradient, locally away from
  collisions. -/
theorem ginibre_weak_gradient_distributional (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreWeakGradient n u g) : IsGinibreDistributionalGradient n u g := by
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn u (Lp.memLp u), ?_, ?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
      PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
    have hm : MemLp (fun z => g z k) 2 (ginibreMeasure n) := P.comp_memLp g
    exact ginibre_memLp_locallyIntegrable_collisionFree hn (fun z => g z k) hm
  · intro k θ hθ hc hs
    let ρ := ginibreLebesgueDensityReal n
    let ψ : Configuration n → ℝ := fun z => θ z / ρ z ^ 2
    have hψ : ContDiff ℝ ∞ ψ := contDiff_collisionFree_test_div_density_sq hn θ hθ hs
    have hψc : HasCompactSupport ψ := compactSupport_collisionFree_test_div_density_sq θ hc
    have heq : (fun z => ρ z ^ 2 * ψ z) = θ := by
      funext z
      by_cases hz : ρ z = 0
      · have ht : z ∉ tsupport θ := by
          intro ht
          exact (ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn (hs ht)) hz
        simp [hz, image_eq_zero_of_notMem_tsupport ht]
      · dsimp [ψ]
        field_simp [hz]
    have hd (z : Configuration n) :
        ρ z ^ 2 * fderiv ℝ ψ z (ginibreCoordinateDirection k) +
          2 * ρ z * fderiv ℝ ρ z (ginibreCoordinateDirection k) * ψ z =
          fderiv ℝ θ z (ginibreCoordinateDirection k) := by
      rw [← heq]
      have hρ := ((contDiff_ginibreLebesgueDensityReal n).differentiable (by simp)).differentiableAt
        (x := z)
      have hψd := (hψ.differentiable (by simp)).differentiableAt (x := z)
      have hp : (fun z => ρ z ^ 2 * ψ z) = (ρ * ρ) * ψ := by funext z; simp [pow_two]
      rw [hp, fderiv_mul (hρ.mul hρ) hψd, fderiv_mul hρ hρ]
      simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
      ring
    have he := ginibre_weak_gradient_distribution_identity n hn u g hg k ψ hψ hψc
    change (∫ z, ρ z ^ 2 * g z k * ψ z) =
      -(∫ z, u z * (ρ z ^ 2 * fderiv ℝ ψ z (ginibreCoordinateDirection k) +
        2 * ρ z * fderiv ℝ ρ z (ginibreCoordinateDirection k) * ψ z)) at he
    simp_rw [hd] at he
    have hl : (fun z => ρ z ^ 2 * g z k * ψ z) = (fun z => g z k * θ z) := by
      funext z
      have ht := congrFun heq z
      calc
        ρ z ^ 2 * g z k * ψ z = g z k * (ρ z ^ 2 * ψ z) := by ring
        _ = g z k * θ z := by rw [ht]
    rwa [hl] at he

/-- The actual radial completion embeds into the ordinary local weak-gradient graph. -/
theorem radialSobolevClosure_distributional_gradient (n : ℕ) (hn : 0 < n)
    (p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hp : p ∈ radialSobolevClosure n) : IsGinibreDistributionalGradient n p.1 p.2 :=
  ginibre_weak_gradient_distributional n hn p.1 p.2
    (radialSobolevClosure_weak_gradient n hn p hp)

/-- Local integrability suffices for pairing with an interior compact test. -/
theorem integrable_mul_collisionFree_test {n : ℕ}
    (f θ : Configuration n → ℝ)
    (hf : LocallyIntegrableOn f {z : Configuration n | CollisionFree z} volume)
    (hθ : Continuous θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ {z | CollisionFree z}) : Integrable (fun z => f z * θ z) := by
  have hl := hf.mul_continuousOn hθ.continuousOn (isOpen_collisionFree n).isLocallyClosed
  have hi : IntegrableOn (fun z => f z * θ z) (tsupport θ) volume :=
    hl.integrableOn_compact_subset hs hc
  apply hi.integrable_of_forall_notMem_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- The ordinary local distributional gradient determines the global Ginibre L² gradient. -/
theorem ginibre_distributional_gradient_unique (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g h : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (hh : IsGinibreDistributionalGradient n u h) : g = h := by
  have hac : ginibreMeasure n ≪ (volume : Measure (Configuration n)) := by
    rw [ginibreMeasure_eq_real_withDensity hn]
    exact (withDensity_absolutelyContinuous _ _).smul_left _
  have hcf : ∀ᵐ z ∂(volume : Measure (Configuration n)), CollisionFree z := by
    rw [ae_iff]
    have he : {z : Configuration n | ¬ CollisionFree z} = collisionSet n := by
      ext z
      simp [collisionFree_iff_not_mem_collisionSet]
    rw [he]
    exact configurationVolume_collisionSet hn
  have he (k : Fin n × Fin 2) : ∀ᵐ z ∂ginibreMeasure n, g z k = h z k := by
    have hl : LocallyIntegrableOn (fun z => g z k - h z k)
        {z : Configuration n | CollisionFree z} volume := (hg.2.1 k).sub (hh.2.1 k)
    have hz := (isOpen_collisionFree n).ae_eq_zero_of_integral_contDiff_smul_eq_zero hl
      (fun θ hθ hc hs => by
        have hi₁ := integrable_mul_collisionFree_test (fun z => g z k) θ
          (hg.2.1 k) hθ.continuous hc hs
        have hi₂ := integrable_mul_collisionFree_test (fun z => h z k) θ
          (hh.2.1 k) hθ.continuous hc hs
        have heq : (∫ z, θ z • (g z k - h z k)) =
            (∫ z, g z k * θ z) - ∫ z, h z k * θ z := by
          rw [← integral_sub hi₁ hi₂]
          apply integral_congr_ae
          exact ae_of_all _ (fun z => by simp only [smul_eq_mul]; ring)
        rw [heq, hg.2.2 k θ hθ hc hs, hh.2.2 k θ hθ hc hs, sub_self])
    apply hac.ae_le
    filter_upwards [hz, hcf] with z hz hzcf
    exact sub_eq_zero.mp (hz hzcf)
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr he] with z hz
  exact PiLp.ext hz

end
end GinibrePoincare

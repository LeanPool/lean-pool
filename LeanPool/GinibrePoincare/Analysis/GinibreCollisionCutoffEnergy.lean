/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreCollisionCutoffEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoff
public import LeanPool.GinibrePoincare.Analysis.GinibreDensityBound
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevTruncation

/-! # Vanishing energy of collision-avoiding cutoffs -/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The phase where cutoff derivatives are nonzero eventually disappears
pointwise at every collision-free configuration. -/
theorem ginibreCollisionCutoff_gradient_tendsto (n : ℕ) (z : Configuration n)
    (hz : CollisionFree z) :
    Tendsto (fun m => ginibreEuclideanGradient (ginibreCollisionCutoff n m) z)
      atTop (𝓝 0) := by
  have he : (fun m => ginibreEuclideanGradient (ginibreCollisionCutoff n m) z) =ᶠ[atTop]
      (fun _ => 0) :=
    (ginibreCollisionCutoff_eventually_one_gradient_zero n z hz).mono (fun _ h => h.2)
  exact tendsto_const_nhds.congr' he.symm

/-- The concrete Ginibre measure gives full mass to configurations with no
collisions. -/
theorem ginibre_ae_collisionFree (n : ℕ) (hn : 0 < n) :
    ∀ᵐ z ∂ginibreMeasure n, CollisionFree z := by
  have hcf : ∀ᵐ z ∂(volume : Measure (Configuration n)), CollisionFree z := by
    rw [ae_iff]
    have he : {z : Configuration n | ¬ CollisionFree z} = collisionSet n := by
      ext z
      simp [collisionFree_iff_not_mem_collisionSet]
    rw [he]
    exact configurationVolume_collisionSet hn
  obtain ⟨c, hc, hm⟩ := ginibreMeasure_le_finite_smul_volume n hn
  exact (Measure.absolutelyContinuous_of_le_smul hm).ae_le hcf

/-- Actual weighted L² is preserved by bounded collision-cutoff multiplication. -/
theorem ginibreCollisionCutoff_L2_mul_memLp {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (n m : ℕ) (f : Configuration n → V)
    (hf : MemLp f 2 (ginibreMeasure n)) :
    MemLp (fun z => ginibreCollisionCutoff n m z • f z) 2 (ginibreMeasure n) := by
  apply hf.of_le ((ginibreCollisionCutoff_smooth n m).continuous.aestronglyMeasurable.smul
    hf.aestronglyMeasurable)
  apply ae_of_all
  intro z
  change ‖ginibreCollisionCutoff n m z • f z‖ ≤ ‖f z‖
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (ginibreCollisionCutoff_mem_unit n m z).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (ginibreCollisionCutoff_mem_unit n m z).2

/-- Multiplication by collision cutoffs converges strongly in actual weighted
L² for every L² representative. -/
theorem ginibreCollisionCutoff_L2_error_tendsto {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (n : ℕ) (hn : 0 < n) (f : Configuration n → V)
    (hf : MemLp f 2 (ginibreMeasure n)) :
    Tendsto (fun m => ∫ z,
      ‖ginibreCollisionCutoff n m z • f z - f z‖ ^ 2 ∂ginibreMeasure n)
      atTop (𝓝 0) := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun z => ‖f z‖ ^ 2)
    (fun m => (((ginibreCollisionCutoff_smooth n m).continuous.aestronglyMeasurable.smul
      hf.aestronglyMeasurable).sub hf.aestronglyMeasurable).norm.pow 2) hi
    (fun m => ae_of_all _ (fun z => by
      change ‖‖ginibreCollisionCutoff n m z • f z - f z‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have he : ginibreCollisionCutoff n m z • f z - f z =
          (ginibreCollisionCutoff n m z - 1) • f z := by rw [sub_smul, one_smul]
      rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      obtain ⟨h0, h1⟩ := ginibreCollisionCutoff_mem_unit n m z
      have hb : (ginibreCollisionCutoff n m z - 1) ^ 2 ≤ 1 := by nlinarith
      simpa using mul_le_mul_of_nonneg_right hb (sq_nonneg ‖f z‖)))
    ?_
  · simpa using ht
  · filter_upwards [ginibre_ae_collisionFree n hn] with z hz
    have he : (fun m => ‖ginibreCollisionCutoff n m z • f z - f z‖ ^ 2) =ᶠ[atTop]
        (fun _ => 0) :=
      (ginibreCollisionCutoff_eventually_one_gradient_zero n z hz).mono
        (fun _ hm => by simp [hm.1])
    exact tendsto_const_nhds.congr' he.symm

/-- L² classes multiplied by the symmetric collision cutoff converge to the
original value. -/
theorem ginibreCollisionCutoff_mul_L2_tendsto {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (n : ℕ) (hn : 0 < n)
    (u : Lp V 2 (ginibreMeasure n)) :
    Tendsto (fun m => (ginibreCollisionCutoff_L2_mul_memLp n m u (Lp.memLp u)).toLp
      (fun z => ginibreCollisionCutoff n m z • u z)) atTop (𝓝 u) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (m : ℕ) : dist ((ginibreCollisionCutoff_L2_mul_memLp n m u (Lp.memLp u)).toLp
      (fun z => ginibreCollisionCutoff n m z • u z)) u =
      Real.sqrt (∫ z, ‖ginibreCollisionCutoff n m z • u z - u z‖ ^ 2
        ∂ginibreMeasure n) := by
    rw [L2_dist_eq_sqrt_integral_norm_error]
    congr 1
    apply integral_congr_ae
    filter_upwards [(ginibreCollisionCutoff_L2_mul_memLp n m u (Lp.memLp u)).coeFn_toLp] with z hz
    rw [hz]
  simp_rw [he]
  simpa using (ginibreCollisionCutoff_L2_error_tendsto n hn u (Lp.memLp u)).sqrt

/-- The actual collision-cutoff gradient energy vanishes on compact sets for
the concrete Ginibre probability measure. -/
theorem ginibreCollisionCutoff_energy_tendsto (n : ℕ) (hn : 0 < n)
    (K : Set (Configuration n)) (hK : IsCompact K) :
    Tendsto (fun m => ∫ z in K,
      ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2 ∂ginibreMeasure n)
      atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC0, hC⟩ := ginibreCollisionCutoff_weighted_gradient_bound
  let q : ℝ := ((n : ℝ) / Real.pi) ^ n
  let D (z : Configuration n) := q * C * gaussianWeight n z *
    complexDirectionalEnergy (vandermonde : Configuration n → ℂ) z
  let φ (m : ℕ) : Configuration n → ℝ := K.indicator (fun z =>
    ginibreLebesgueDensityReal n z *
      ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2)
  have hDcont : Continuous D := by
    have hg : Continuous (gaussianWeight n) := by
      have harg : Continuous (fun z : Configuration n =>
          (-(n : ℝ)) * configurationNormSq z) :=
        (continuous_const : Continuous (fun _ : Configuration n => -(n : ℝ))).mul
          contDiff_configurationNormSq.continuous
      change Continuous (Real.exp ∘ fun z : Configuration n =>
        (-(n : ℝ)) * configurationNormSq z)
      exact Real.continuous_exp.comp harg
    change Continuous (fun z => q * C * gaussianWeight n z *
      complexDirectionalEnergy vandermonde z)
    have hconst : Continuous (fun _ : Configuration n => q * C) := continuous_const
    exact (hconst.mul hg).mul
      (continuous_complexDirectionalEnergy vandermonde (contDiff_vandermonde n))
  have hDnonneg (z : Configuration n) : 0 ≤ D z := by
    dsimp [D, q]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC0)
      (gaussianWeight_nonneg n z)) (complexDirectionalEnergy_nonneg _ z)
  have hi : Integrable D (volume.restrict K) := by
    have hI : IntegrableOn D K (volume : Measure (Configuration n)) :=
      hDcont.continuousOn.integrableOn_compact hK
    exact hI
  have hbound (m : ℕ) (z : Configuration n) : φ m z ≤ D z := by
    by_cases hz : z ∈ K
    · change (K.indicator (fun z => ginibreLebesgueDensityReal n z *
          ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2)) z ≤ D z
      rw [Set.indicator_of_mem hz]
      unfold ginibreLebesgueDensityReal D
      dsimp [q]
      have he : (((n : ℝ) / Real.pi) ^ n * vandermondeWeight z * gaussianWeight n z) *
          ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2 =
          ((n : ℝ) / Real.pi) ^ n * gaussianWeight n z *
            (vandermondeWeight z * ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2)
              := by
              ring
      rw [he]
      calc
        _ ≤ ((n : ℝ) / Real.pi) ^ n * gaussianWeight n z *
            (C * complexDirectionalEnergy vandermonde z) :=
          mul_le_mul_of_nonneg_left (hC n m z)
            (mul_nonneg (by positivity) (gaussianWeight_nonneg n z))
        _ = _ := by ring
    · simp [φ, hz, hDnonneg]
  have hmeas (m : ℕ) : AEStronglyMeasurable (φ m) (volume.restrict K) := by
    exact (((contDiff_ginibreLebesgueDensityReal n).continuous.mul
      ((continuous_ginibreEuclideanGradient _ (ginibreCollisionCutoff_smooth n m)).norm.pow
        2)).aestronglyMeasurable).indicator
        hK.measurableSet
  have hpoint (z : Configuration n) : Tendsto (fun m => φ m z) atTop (𝓝 0) := by
    by_cases hz : CollisionFree z
    · have he : (fun m => φ m z) =ᶠ[atTop] (fun _ => 0) := by
        filter_upwards [ginibreCollisionCutoff_eventually_one_gradient_zero n z hz] with m hm
        simp [φ, hm.2]
      exact tendsto_const_nhds.congr' he.symm
    · have hzcol : z ∈ collisionSet n := by
        simpa [collisionFree_iff_not_mem_collisionSet] using hz
      have hv : vandermondeWeight z = 0 := (vandermondeWeight_eq_zero_iff z).2 hzcol
      have he : (fun m => φ m z) =ᶠ[atTop] (fun _ => 0) := by
        filter_upwards [] with m
        simp [φ, ginibreLebesgueDensityReal, hv]
      exact tendsto_const_nhds.congr' he.symm
  have hvol := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) D
    hmeas hi
    (fun m => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        by_cases hz : z ∈ K
        · rw [show φ m z = ginibreLebesgueDensityReal n z *
              ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2 by
                simp [φ, hz]]
          exact mul_nonneg (ginibreLebesgueDensityReal_nonneg n z) (sq_nonneg _)
        · simp [φ, hz])]
      exact hbound m z))
    (ae_of_all _ hpoint)
  have hμ (m : ℕ) :
      (∫ z in K, ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2
        ∂ginibreMeasure n) = (ginibreNormalizingMass n).toReal⁻¹ * ∫ z, φ m z := by
    rw [← integral_indicator hK.measurableSet]
    rw [integral_ginibreMeasure_eq_density_volume hn]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with z
    change ginibreLebesgueDensityReal n z *
      K.indicator (fun y => ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) y‖ ^ 2) z =
      K.indicator (fun y => ginibreLebesgueDensityReal n y *
        ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) y‖ ^ 2) z
    by_cases hz : z ∈ K
    · simp [hz]
    · simp [hz]
  have hfull (m : ℕ) : (∫ z, φ m z ∂volume) = ∫ z in K, φ m z ∂volume := by
    rw [show φ m = K.indicator (fun z => ginibreLebesgueDensityReal n z *
      ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2) from rfl,
      integral_indicator hK.measurableSet]
    apply setIntegral_congr_fun hK.measurableSet
    intro z hz
    simp [hz]
  have hlim := hvol.const_mul ((ginibreNormalizingMass n).toReal⁻¹)
  simpa [hμ, hfull] using hlim

/-- A bounded compact value multiplied by the collision-cutoff gradient
belongs to actual Ginibre L² at every scale. -/
theorem ginibreCollisionCutoff_bounded_gradient_memLp
    (n : ℕ) (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : AEStronglyMeasurable f (ginibreMeasure n)) (hc : HasCompactSupport f)
    (A : ℝ) (hA : ∀ z, ‖f z‖ ≤ A) (m : ℕ) :
    MemLp (fun z => f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z)
      2 (ginibreMeasure n) := by
  classical
  let := ginibreMeasure_isProbabilityMeasure hn
  let K := tsupport f
  have hK : IsCompact K := hc
  let G (z : Configuration n) :=
    ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2
  have hGc : Continuous G := by
    exact ((continuous_ginibreEuclideanGradient _
      (ginibreCollisionCutoff_smooth n m)).norm.pow 2)
  have hG : IntegrableOn G K (ginibreMeasure n) := hGc.continuousOn.integrableOn_compact hK
  have hdom : IntegrableOn (fun z => A ^ 2 * G z) K (ginibreMeasure n) := by
    change Integrable (fun z => A ^ 2 * G z) ((ginibreMeasure n).restrict K)
    simpa [G] using hG.integrable.const_mul (A ^ 2)
  have hm := hf.smul (continuous_ginibreEuclideanGradient _
    (ginibreCollisionCutoff_smooth n m)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hlocal : IntegrableOn (fun z =>
      ‖f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2)
      K (ginibreMeasure n) := by
    apply hdom.mono' (hm.norm.pow 2).restrict
    apply ae_of_all
    intro z
    change ‖‖f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2‖ ≤ A ^ 2 * G z
    rw [norm_smul, mul_pow]
    have ha : ‖f z‖ ^ 2 ≤ A ^ 2 := by nlinarith [norm_nonneg (f z), hA z]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg ‖f z‖) (sq_nonneg
        ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖))]
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg
      ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖)
  apply hlocal.integrable_of_forall_notMem_eq_zero
  intro z hz
  simp [image_eq_zero_of_notMem_tsupport hz]

/-- For bounded compact values, the Ginibre-weighted L² norm of the cutoff
gradient term tends to zero. -/
theorem ginibreCollisionCutoff_bounded_gradient_energy_tendsto
    (n : ℕ) (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : AEStronglyMeasurable f (ginibreMeasure n)) (hc : HasCompactSupport f)
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    Tendsto (fun m => ∫ z,
      ‖f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2
        ∂ginibreMeasure n) atTop (𝓝 0) := by
  let K := tsupport f
  have hK : IsCompact K := hc
  let := ginibreMeasure_isProbabilityMeasure hn
  have hgrad m : IntegrableOn
      (fun z => ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2)
      K (ginibreMeasure n) := by
    exact (((continuous_ginibreEuclideanGradient _
      (ginibreCollisionCutoff_smooth n m)).norm.pow 2).continuousOn.integrableOn_compact hK)
  have hprod m : IntegrableOn
      (fun z => ‖f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2)
      K (ginibreMeasure n) := by
    have hq := ginibreCollisionCutoff_bounded_gradient_memLp n hn f hf hc A hA m
    have hsq := (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq
    exact hsq.integrableOn
  have hdom m : IntegrableOn
      (fun z => A ^ 2 * ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2)
      K (ginibreMeasure n) := by
    exact (hgrad m).integrable.const_mul (A ^ 2)
  have hle (m : ℕ) :
      (∫ z, ‖f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2
        ∂ginibreMeasure n) ≤ A ^ 2 * ∫ z in K,
          ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2 ∂ginibreMeasure n := by
    have hglobal : (∫ z, ‖f z • ginibreEuclideanGradient
        (ginibreCollisionCutoff n m) z‖ ^ 2 ∂ginibreMeasure n) =
        ∫ z in K, ‖f z • ginibreEuclideanGradient
          (ginibreCollisionCutoff n m) z‖ ^ 2 ∂ginibreMeasure n := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      simp [image_eq_zero_of_notMem_tsupport hz]
    rw [hglobal]
    calc
      _ ≤ ∫ z in K, A ^ 2 *
          ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2 ∂ginibreMeasure n :=
        setIntegral_mono_on (hprod m) (hdom m) hK.measurableSet (by
          intro z hz
          rw [norm_smul, mul_pow]
          have ha : ‖f z‖ ^ 2 ≤ A ^ 2 := by nlinarith [norm_nonneg (f z), hA z]
          exact mul_le_mul_of_nonneg_right ha (sq_nonneg _))
      _ = A ^ 2 * ∫ z in K,
          ‖ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2 ∂ginibreMeasure n :=
        integral_const_mul _ _
  have hlim := (ginibreCollisionCutoff_energy_tendsto n hn K hK).const_mul (A ^ 2)
  apply squeeze_zero (fun m => integral_nonneg (fun z => sq_nonneg _)) hle
  simpa using hlim

/-- The actual L² classes of bounded compact cutoff-gradient terms converge
strongly to zero. -/
theorem ginibreCollisionCutoff_bounded_gradient_L2_tendsto
    (n : ℕ) (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : AEStronglyMeasurable f (ginibreMeasure n)) (hc : HasCompactSupport f)
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    Tendsto (fun m => (ginibreCollisionCutoff_bounded_gradient_memLp
      n hn f hf hc A hA m).toLp
      (fun z => f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z))
      atTop (𝓝 0) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (m : ℕ) : dist ((ginibreCollisionCutoff_bounded_gradient_memLp
      n hn f hf hc A hA m).toLp
      (fun z => f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z)) 0 =
      Real.sqrt (∫ z, ‖f z • ginibreEuclideanGradient
        (ginibreCollisionCutoff n m) z‖ ^ 2 ∂ginibreMeasure n) := by
    rw [L2_dist_eq_sqrt_integral_norm_error]
    apply congrArg Real.sqrt
    apply integral_congr_ae
    filter_upwards [(ginibreCollisionCutoff_bounded_gradient_memLp
      n hn f hf hc A hA m).coeFn_toLp,
      Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin n × Fin 2)) (p := 2)
        (μ := ginibreMeasure n)] with z hz hzero
    change ((0 : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :
      Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) z = 0 at hzero
    rw [hz, hzero, sub_zero]
  have ht := (ginibreCollisionCutoff_bounded_gradient_energy_tendsto
    n hn f hf hc A hA0 hA).sqrt
  have ht0 : Tendsto (fun m => Real.sqrt (∫ z,
      ‖f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z‖ ^ 2
        ∂ginibreMeasure n)) atTop (𝓝 0) := by simpa using ht
  exact (Filter.tendsto_congr' (Filter.Eventually.of_forall he)).mpr ht0
end
end GinibrePoincare

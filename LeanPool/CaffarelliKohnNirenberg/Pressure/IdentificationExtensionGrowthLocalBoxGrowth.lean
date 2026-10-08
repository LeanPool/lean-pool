/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowthLocalBoxSupport

/-!
# Identification Extension Growth Local Box Growth

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN
open CKN.Foundation.Euclidean

private theorem pressureUTensor_memLp_three_halves_of_velocity_memLp_six
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s ρ : ℝ} {z : Vec3}
    (η : Vec3 → ℝ)
    (hgu6 : MemLp (fun y => vec3EuclideanNorm (u (y, s)))
      (ENNReal.ofReal (6 : ℝ)) (volume.restrict (vec3Ball z ρ)))
    (huMeas : AEMeasurable (fun x : Vec3 => u (x, s))
      (volume.restrict (vec3Ball z ρ)))
    (hηmeas : AEStronglyMeasurable η (volume.restrict (vec3Ball z ρ)))
    (hηbound : ∀ y, |η y| ≤ 1)
    (hηsupport : tsupport η ⊆ vec3Ball z ρ) :
    (∀ i j, AEStronglyMeasurable
      (fun y => pressureUTensor u c (y, s) i j) (volume.restrict (vec3Ball z ρ))) ∧
    (∀ i j, MemLp (fun y => pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ))) ∧
    (∀ i j, MemLp (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) := by
  have hμtop : (volume.restrict (vec3Ball z ρ)) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, volume_vec3Ball_eq]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top
  let : IsFiniteMeasure (volume.restrict (vec3Ball z ρ)) := ⟨hμtop⟩
  let gu : Vec3 → ℝ := fun y => vec3EuclideanNorm (u (y, s))
  have hc6 : MemLp (fun _ : Vec3 => vec3EuclideanNorm (c s)) 6
      (volume.restrict (vec3Ball z ρ)) := memLp_const _
  have hc6' : MemLp (fun _ : Vec3 => vec3EuclideanNorm (c s))
      (ENNReal.ofReal (6 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
    simpa using hc6
  have hgu6' : MemLp gu (ENNReal.ofReal (6 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
    simpa [gu] using hgu6
  have hsum6' : MemLp (fun y => gu y + vec3EuclideanNorm (c s))
      (ENNReal.ofReal (6 : ℝ)) (volume.restrict (vec3Ball z ρ)) := hgu6'.add hc6'
  let : (ENNReal.ofReal (6 : ℝ)).HolderTriple (ENNReal.ofReal (6 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) := by
    have h : (6 : ℝ).HolderTriple 6 3 := by
      rw [Real.holderTriple_iff]
      norm_num
    exact h.ennrealOfReal
  have hmajor : MemLp (fun y => gu y * (gu y + vec3EuclideanNorm (c s)))
      (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball z ρ)) := hgu6'.mul hsum6'
  have hUmeas (i j : Fin 3) : AEStronglyMeasurable
      (fun y => pressureUTensor u c (y, s) i j) (volume.restrict (vec3Ball z ρ)) := by
    let F : Vec3 → ℝ := fun v => -v i * (v j - c s j)
    have hF : Continuous F := by
      dsimp [F]
      fun_prop
    exact (hF.measurable.comp_aemeasurable huMeas).aestronglyMeasurable
  have hU32 (i j : Fin 3) : MemLp
      (fun y => pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
    have hU3 : MemLp (fun y => pressureUTensor u c (y, s) i j)
        (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
      apply hmajor.of_le (hUmeas i j)
      filter_upwards [] with y
      have hui : |u (y, s) i| ≤ gu y := by
        simpa [gu, vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
          using abs_apply_le_vecEuclideanNorm (u (y, s)) i
      have huj : |u (y, s) j| ≤ gu y := by
        simpa [gu, vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
          using abs_apply_le_vecEuclideanNorm (u (y, s)) j
      have hcj : |c s j| ≤ vec3EuclideanNorm (c s) := by
        simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
          using abs_apply_le_vecEuclideanNorm (c s) j
      calc
        ‖pressureUTensor u c (y, s) i j‖ =
            |-(u (y, s) i * u (y, s) j) + c s j * u (y, s) i| := by
          change ‖-u (y, s) i * (u (y, s) j - c s j)‖ = _
          rw [Real.norm_eq_abs]
          congr 1
          ring
        _ ≤ |u (y, s) i * u (y, s) j| + |c s j * u (y, s) i| := by
          calc
            _ ≤ |-(u (y, s) i * u (y, s) j)| + |c s j * u (y, s) i| :=
              abs_add_le _ _
            _ = |u (y, s) i * u (y, s) j| + |c s j * u (y, s) i| := by
              rw [abs_neg]
        _ ≤ gu y * (gu y + vec3EuclideanNorm (c s)) := by
          rw [abs_mul, abs_mul]
          nlinarith only [hui, huj, hcj, abs_nonneg (u (y, s) i),
            abs_nonneg (u (y, s) j), abs_nonneg (c s j)]
        _ = ‖gu y * (gu y + vec3EuclideanNorm (c s))‖ := by
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (vec3EuclideanNorm_nonneg _),
            abs_of_nonneg (add_nonneg (vec3EuclideanNorm_nonneg _)
              (vec3EuclideanNorm_nonneg _))]
    exact hU3.mono_exponent (by norm_num)
  have hGμ (i j : Fin 3) : MemLp
      (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
    apply (hU32 i j).of_le_mul (c := 1) (hηmeas.mul (hUmeas i j))
    filter_upwards [] with y
    change |η y * pressureUTensor u c (y, s) i j| ≤
      1 * ‖pressureUTensor u c (y, s) i j‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hηbound y) (abs_nonneg _)
  have hG (i j : Fin 3) : MemLp
      (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    exact lift_ball_memLp_growth_sws (hGμ i j)
      ((tsupport_mul_subset_left (f := η)
        (g := fun y => pressureUTensor u c (y, s) i j)).trans hηsupport)
  exact ⟨hUmeas, hU32, hG⟩

private theorem pressureSecondExtension_ball_subset_closedBall
    (z : Vec3) {ρ : ℝ} :
    vec3Ball z ρ ⊆ closedBall (0 : Vec3) (vec3EuclideanNorm z + ρ) := by
  intro y hy
  rw [mem_closedBall_zero_iff]
  have hy' : vec3EuclideanNorm (y - z) < ρ := (mem_vec3Ball).1 hy
  have htri : vec3EuclideanNorm y ≤
      vec3EuclideanNorm (y - z) + vec3EuclideanNorm z := by
    calc
      vec3EuclideanNorm y = vec3EuclideanNorm ((y - z) + z) := by congr 1; abel
      _ ≤ vec3EuclideanNorm (y - z) + vec3EuclideanNorm z := vec3_norm_add_le_sws _ _
  have hyNorm : ‖y‖ ≤ vec3EuclideanNorm y := by
    rw [Pi.norm_def]
    have hnn : Finset.univ.sup (fun i => ‖y i‖₊) ≤
        ⟨vec3EuclideanNorm y, vec3EuclideanNorm_nonneg y⟩ := by
      apply Finset.sup_le
      intro i hi
      have hi' : |y i| ≤ vec3EuclideanNorm y := by
        simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
          using abs_apply_le_vecEuclideanNorm y i
      exact_mod_cast hi'
    exact_mod_cast hnn
  linarith only [hy', htri, hyNorm]

private theorem pressure_cutoff_compact_sources_memLp_six_fifths
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
    {s ρ : ℝ} {z : Vec3}
    (hμFinite : IsFiniteMeasure (volume.restrict (vec3Ball z ρ)))
    (η : Vec3 → ℝ) (R₀ : ℝ)
    (hB0 : vec3Ball z ρ ⊆ closedBall (0 : Vec3) R₀)
    (hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηsupport : tsupport η ⊆ vec3Ball z ρ)
    (hηlapB : tsupport (spatialLaplacian η) ⊆ vec3Ball z ρ)
    (hUmeas : ∀ i j, AEStronglyMeasurable
      (fun y => pressureUTensor u c (y, s) i j) (volume.restrict (vec3Ball z ρ)))
    (hU32 : ∀ i j, MemLp (fun y => pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ)))
    (hp : MemLp (fun y => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ)))
    (hηmBound : ∀ i j, ∀ᵐ y ∂(volume.restrict (vec3Ball z ρ)),
      |mixedSecond η i j y| ≤ cutoffSecondDerivativeConstant / ρ ^ 2)
    (hηdBound : ∀ i, ∀ᵐ y ∂(volume.restrict (vec3Ball z ρ)),
      |spatialDeriv η i y| ≤ cutoffGradientConstant / ρ)
    (hηlapBound : ∀ᵐ y ∂(volume.restrict (vec3Ball z ρ)),
      |spatialLaplacian η y| ≤ (3 * cutoffSecondDerivativeConstant) / ρ ^ 2) :
    (∀ i j, MemLp
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
    (∀ i j, MemLp
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
    (∀ i j, MemLp
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
    MemLp (fun y => p (y, s) * spatialLaplacian η y)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
    (∀ j, MemLp (fun y => spatialDeriv η j y * p (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball z ρ)) := hμFinite
  have hηd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) :=
    contDiff_spatialDeriv_smooth hηsmooth i
  have hηm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) :=
    contDiff_mixedSecond_smooth hηsmooth i j
  have hPmeas : AEStronglyMeasurable (fun y => p (y, s)) (volume.restrict (vec3Ball z ρ)) :=
    hp.aestronglyMeasurable
  have hsupp (g : Vec3 → ℝ) (hgt : tsupport g ⊆ vec3Ball z ρ) :
      ∀ y ∉ closedBall (0 : Vec3) R₀, g y = 0 := by
    intro y hy
    have hyB : y ∉ vec3Ball z ρ := fun hyB => hy (hB0 hyB)
    exact image_eq_zero_of_notMem_tsupport (fun hgy => hyB (hgt hgy))
  have hsrc (g : Vec3 → ℝ)
      (hgb : MemLp g (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball z ρ)))
      (hgt : tsupport g ⊆ vec3Ball z ρ) :
      MemLp g (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    have hgg := lift_ball_memLp_growth_sws hgb hgt
    exact memLp_six_fifths_of_memLp_ofReal (by norm_num) hgg (hsupp g hgt)
  have hsource2 (i j : Fin 3) :
      MemLp (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
    apply (hU32 i j).of_le_mul
      (c := cutoffSecondDerivativeConstant / ρ ^ 2)
      ((hηm i j).continuous.aestronglyMeasurable.mul (hUmeas i j))
    filter_upwards [hηmBound i j] with y hy
    change |mixedSecond η i j y * pressureUTensor u c (y, s) i j| ≤
      (cutoffSecondDerivativeConstant / ρ ^ 2) *
        ‖pressureUTensor u c (y, s) i j‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  have hsource3 (i j : Fin 3) :
      MemLp (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
    apply (hU32 i j).of_le_mul (c := cutoffGradientConstant / ρ)
      ((hUmeas i j).mul (hηd i).continuous.aestronglyMeasurable)
    filter_upwards [hηdBound i] with y hy
    change |pressureUTensor u c (y, s) i j * spatialDeriv η i y| ≤
      (cutoffGradientConstant / ρ) * ‖pressureUTensor u c (y, s) i j‖
    rw [abs_mul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  have hsource4 (i j : Fin 3) :
      MemLp (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
    apply (hU32 i j).of_le_mul (c := cutoffGradientConstant / ρ)
      ((hUmeas i j).mul (hηd j).continuous.aestronglyMeasurable)
    filter_upwards [hηdBound j] with y hy
    change |pressureUTensor u c (y, s) i j * spatialDeriv η j y| ≤
      (cutoffGradientConstant / ρ) * ‖pressureUTensor u c (y, s) i j‖
    rw [abs_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hy (abs_nonneg _)).trans_eq (by ring)
  have hsource5 : MemLp (fun y => p (y, s) * spatialLaplacian η y)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
    apply hp.of_le_mul (c := (3 * cutoffSecondDerivativeConstant) / ρ ^ 2)
      (hPmeas.mul (contDiff_spatialLaplacian_smooth hηsmooth).continuous.aestronglyMeasurable)
    filter_upwards [hηlapBound] with y hy
    change |p (y, s) * spatialLaplacian η y| ≤
      (3 * cutoffSecondDerivativeConstant / ρ ^ 2) * ‖p (y, s)‖
    rw [abs_mul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  have hsource6 (j : Fin 3) : MemLp (fun y => spatialDeriv η j y * p (y, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball z ρ)) := by
    apply hp.of_le_mul (c := cutoffGradientConstant / ρ)
      ((hηd j).continuous.aestronglyMeasurable.mul hPmeas)
    filter_upwards [hηdBound j] with y hy
    change |spatialDeriv η j y * p (y, s)| ≤
      (cutoffGradientConstant / ρ) * ‖p (y, s)‖
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  have hgt2 (i j : Fin 3) :
      tsupport (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) ⊆
        vec3Ball z ρ := by
    exact (tsupport_mul_subset_left (f := mixedSecond η i j)
      (g := fun y => pressureUTensor u c (y, s) i j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport))
  have hgt3 (i j : Fin 3) :
      tsupport (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) ⊆
        vec3Ball z ρ := by
    exact (tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
      (g := spatialDeriv η i)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηsupport)
  have hgt4 (i j : Fin 3) :
      tsupport (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) ⊆
        vec3Ball z ρ := by
    exact (tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
      (g := spatialDeriv η j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport)
  have hgt5 : tsupport (fun y => p (y, s) * spatialLaplacian η y) ⊆ vec3Ball z ρ := by
    exact (tsupport_mul_subset_right (f := fun y => p (y, s))
      (g := spatialLaplacian η)).trans hηlapB
  have hgt6 (j : Fin 3) :
      tsupport (fun y => spatialDeriv η j y * p (y, s)) ⊆ vec3Ball z ρ := by
    exact (tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := fun y => p (y, s))).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport)
  exact ⟨fun i j => hsrc _ (hsource2 i j) (hgt2 i j),
    fun i j => hsrc _ (hsource3 i j) (hgt3 i j),
    fun i j => hsrc _ (hsource4 i j) (hgt4 i j),
    hsrc _ hsource5 hgt5, fun j => hsrc _ (hsource6 j) (hgt6 j)⟩

private theorem pressure_potential_remainder_memLp_growth
    {P2 P3 P4 P5 P6 : Vec3 → ℝ}
    {C2 C3 C4 C5 C6 : ℝ}
    (h2mem : ∀ r : ℝ, 0 < r → MemLp P2 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)))
    (h3mem : ∀ r : ℝ, 0 < r → MemLp P3 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)))
    (h4mem : ∀ r : ℝ, 0 < r → MemLp P4 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)))
    (h5mem : ∀ r : ℝ, 0 < r → MemLp P5 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)))
    (h6mem : ∀ r : ℝ, 0 < r → MemLp P6 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)))
    (h2bound : ∀ r : ℝ, 0 < r → lpNorm P2 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C2 * (1 + r))
    (h3bound : ∀ r : ℝ, 0 < r → lpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C3 * (1 + r))
    (h4bound : ∀ r : ℝ, 0 < r → lpNorm P4 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C4 * (1 + r))
    (h5bound : ∀ r : ℝ, 0 < r → lpNorm P5 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C5 * (1 + r))
    (h6bound : ∀ r : ℝ, 0 < r → lpNorm P6 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C6 * (1 + r)) :
    (∀ r : ℝ, 0 < r → MemLp (((P2 + P3) + P4 + P5) + P6)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r))) ∧
    (∀ r : ℝ, 0 < r → lpNorm (((P2 + P3) + P4 + P5) + P6)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      (C2 + C3 + C4 + C5 + C6) * (1 + r)) := by
  constructor
  · intro r hr
    exact (((((h2mem r hr).add (h3mem r hr)).add (h4mem r hr)).add
      (h5mem r hr)).add (h6mem r hr))
  · intro r hr
    have h23 := lpNorm_add_le (h2mem r hr) (g := P3) (by norm_num)
    have h234 := lpNorm_add_le ((h2mem r hr).add (h3mem r hr))
      (g := P4) (by norm_num)
    have h2345 := lpNorm_add_le ((h2mem r hr).add (h3mem r hr) |>.add (h4mem r hr))
      (g := P5) (by norm_num)
    have h2345mem := (((h2mem r hr).add (h3mem r hr)).add
      (h4mem r hr)).add (h5mem r hr)
    calc
      _ ≤ lpNorm (((P2 + P3) + P4) + P5)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm P6 (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) := by
        exact lpNorm_add_le h2345mem (g := P6) (by norm_num)
      _ ≤ lpNorm P2 (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm P4 (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm P5 (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) +
          lpNorm P6 (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) := by
        linarith only [h23, h234, h2345]
      _ ≤ (C2 + C3 + C4 + C5 + C6) * (1 + r) := by
        linarith only [h2bound r hr, h3bound r hr, h4bound r hr,
          h5bound r hr, h6bound r hr]

private theorem finite_potential_sum_memLp_growth
    {α : Type*} [Fintype α]
    {P : Vec3 → ℝ}
    (f : α → Vec3 → ℝ) (C : α → ℝ)
    (hP : P = fun x => ∑ a, f a x)
    (hmem : ∀ a r, 0 < r → MemLp (f a) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)))
    (hbound : ∀ a r, 0 < r → lpNorm (f a) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C a * (1 + r)) :
    (∀ r, 0 < r → MemLp P (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r))) ∧
    (∀ r, 0 < r → lpNorm P (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      (∑ a, C a) * (1 + r)) := by
  constructor
  · intro r hr
    have hs := memLp_finsetSum (p := ENNReal.ofReal (3 / 2 : ℝ))
      Finset.univ (fun a _ => hmem a r hr)
    rw [hP]
    exact hs
  · intro r hr
    have hb := lpNorm_euclideanBall_growth_sum (s := Finset.univ) (f := f)
      (C := C) (fun a _ r hr => hmem a r hr)
      (fun a _ r hr => hbound a r hr) hr
    rw [hP]
    have hsum : (fun x : Vec3 => ∑ a, f a x) = ∑ a, f a := by
      funext x
      simp
    rw [hsum]
    exact hb

private theorem pressure_cutoff_potential_growth_assembly
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
    {s ρ R₀ : ℝ} {z : Vec3}
    (η : Vec3 → ℝ) (hR₀ : 0 < R₀)
    (hηsupport : tsupport η ⊆ vec3Ball z ρ)
    (hηlapB : tsupport (spatialLaplacian η) ⊆ vec3Ball z ρ)
    (hsupp : ∀ g : Vec3 → ℝ,
      tsupport g ⊆ vec3Ball z ρ →
        ∀ y ∉ closedBall (0 : Vec3) R₀, g y = 0)
    (hg2 : ∀ i j, MemLp
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hg3 : ∀ i j, MemLp
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hg4 : ∀ i j, MemLp
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hg5 : MemLp (fun y => p (y, s) * spatialLaplacian η y)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hg6 : ∀ j, MemLp (fun y => spatialDeriv η j y * p (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    ∃ C_H : ℝ, 0 ≤ C_H ∧
      (∀ r : ℝ, 0 < r → MemLp
        (((pressureP2 η u c s + pressureP3 η u c s) + pressureP4 η u c s +
          pressureP5 η p s) + pressureP6 η p s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r))) ∧
      (∀ r : ℝ, 0 < r → lpNorm
        (((pressureP2 η u c s + pressureP3 η u c s) + pressureP4 η u c s +
          pressureP5 η p s) + pressureP6 η p s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C_H * (1 + r)) := by
  let g2 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    mixedSecond η i j y * pressureUTensor u c (y, s) i j
  let g3 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    pressureUTensor u c (y, s) i j * spatialDeriv η i y
  let g4 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    pressureUTensor u c (y, s) i j * spatialDeriv η j y
  let g5 : Vec3 → ℝ := fun y => p (y, s) * spatialLaplacian η y
  let g6 : Fin 3 → Vec3 → ℝ := fun j y => spatialDeriv η j y * p (y, s)
  have hp2ij (i j : Fin 3) :=
    pressureNewtonianPotential_memLp_and_lpNorm_growth_of_memLp
      (G := g2 i j) hR₀ (by norm_num) (hg2 i j) (hsupp _
        ((tsupport_mul_subset_left (f := mixedSecond η i j)
          (g := fun y => pressureUTensor u c (y, s) i j)).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
              ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport))))
  have hp3ij (i j : Fin 3) :=
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp j hR₀
      (by norm_num) (hg3 i j) (hsupp _
        ((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
          (g := spatialDeriv η i)).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηsupport)))
  have hp4ij (i j : Fin 3) :=
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp i hR₀
      (by norm_num) (hg4 i j) (hsupp _
        ((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
          (g := spatialDeriv η j)).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport)))
  have hp5 := pressureNewtonianPotential_memLp_and_lpNorm_growth_of_memLp
    (G := g5) hR₀ (by norm_num) hg5 (hsupp _
      ((tsupport_mul_subset_right (f := fun y => p (y, s))
        (g := spatialLaplacian η)).trans hηlapB))
  have hp6 (j : Fin 3) :=
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_of_memLp j hR₀
      (by norm_num) (hg6 j) (hsupp _
        ((tsupport_mul_subset_left (f := spatialDeriv η j)
          (g := fun y => p (y, s))).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport)))
  let f2 : Fin 3 × Fin 3 → Vec3 → ℝ := fun ij =>
    pressureNewtonianPotential (g2 ij.1 ij.2)
  let f3 : Fin 3 × Fin 3 → Vec3 → ℝ := fun ij =>
    pressureNewtonianDerivativePotential ij.2 (g3 ij.1 ij.2)
  let f4 : Fin 3 × Fin 3 → Vec3 → ℝ := fun ij =>
    pressureNewtonianDerivativePotential ij.1 (g4 ij.1 ij.2)
  let C2 : Fin 3 × Fin 3 → ℝ := fun ij =>
    newtonianPotentialGrowthConstant (g2 ij.1 ij.2) R₀
  let C3 : Fin 3 × Fin 3 → ℝ := fun ij =>
    newtonianDerivativePotentialGrowthConstant ij.2 (g3 ij.1 ij.2) R₀
  let C4 : Fin 3 × Fin 3 → ℝ := fun ij =>
    newtonianDerivativePotentialGrowthConstant ij.1 (g4 ij.1 ij.2) R₀
  have hf2 : pressureP2 η u c s = fun x => ∑ ij : Fin 3 × Fin 3, f2 ij x := by
    funext x
    simp only [pressureP2, f2, g2]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hf3 : pressureP3 η u c s = fun x => ∑ ij : Fin 3 × Fin 3, f3 ij x := by
    funext x
    simp only [pressureP3, f3, g3]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hf4 : pressureP4 η u c s = fun x => ∑ ij : Fin 3 × Fin 3, f4 ij x := by
    funext x
    simp only [pressureP4, f4, g4]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have ⟨h2mem, h2bound⟩ := finite_potential_sum_memLp_growth
    (P := pressureP2 η u c s) f2 C2 hf2
    (fun ij r hr => (hp2ij ij.1 ij.2).1 r hr)
    (fun ij r hr => (hp2ij ij.1 ij.2).2 r hr)
  have ⟨h3mem, h3bound⟩ := finite_potential_sum_memLp_growth
    (P := pressureP3 η u c s) f3 C3 hf3
    (fun ij r hr => (hp3ij ij.1 ij.2).1 r hr)
    (fun ij r hr => (hp3ij ij.1 ij.2).2 r hr)
  have ⟨h4mem, h4bound⟩ := finite_potential_sum_memLp_growth
    (P := pressureP4 η u c s) f4 C4 hf4
    (fun ij r hr => (hp4ij ij.1 ij.2).1 r hr)
    (fun ij r hr => (hp4ij ij.1 ij.2).2 r hr)
  have hp5mem : ∀ r : ℝ, 0 < r → MemLp (pressureP5 η p s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    change MemLp (fun x => -pressureNewtonianPotential g5 x)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r))
    change MemLp (-(pressureNewtonianPotential g5))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r))
    exact (hp5.1 r hr).neg
  have hp5bound : ∀ r : ℝ, 0 < r → lpNorm (pressureP5 η p s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      newtonianPotentialGrowthConstant g5 R₀ * (1 + r) := by
    intro r hr
    change lpNorm (-(pressureNewtonianPotential g5))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ _
    simpa using hp5.2 r hr
  have hp6mem : ∀ r : ℝ, 0 < r → MemLp (pressureP6 η p s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    have h := memLp_finsetSum (p := ENNReal.ofReal (3 / 2 : ℝ))
      (Finset.univ : Finset (Fin 3)) (fun j _ => (hp6 j).1 r hr)
    change MemLp ((-2 : ℝ) • (fun x => ∑ j : Fin 3,
      pressureNewtonianDerivativePotential j (g6 j) x))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r))
    exact h.const_smul (-2 : ℝ)
  have hp6bound : ∀ r : ℝ, 0 < r → lpNorm (pressureP6 η p s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      (∑ j : Fin 3, 2 * newtonianDerivativePotentialGrowthConstant j (g6 j) R₀) * (1 + r) := by
    intro r hr
    have h := lpNorm_euclideanBall_growth_sum (s := Finset.univ) (f := fun j =>
        pressureNewtonianDerivativePotential j (g6 j))
      (C := fun j => newtonianDerivativePotentialGrowthConstant j (g6 j) R₀)
      (fun j _ r hr => (hp6 j).1 r hr) (fun j _ r hr => (hp6 j).2 r hr) hr
    let S : Vec3 → ℝ := fun x => ∑ j : Fin 3,
      pressureNewtonianDerivativePotential j (g6 j) x
    have hS : lpNorm S (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        (∑ j : Fin 3, newtonianDerivativePotentialGrowthConstant j (g6 j) R₀) *
          (1 + r) := by
      change lpNorm (∑ j : Fin 3, pressureNewtonianDerivativePotential j (g6 j))
        (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ _
      exact h
    calc
      lpNorm (pressureP6 η p s) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) =
          2 * lpNorm S (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) r)) := by
        rw [show pressureP6 η p s = fun x => (-2 : ℝ) * S x by
          funext x; simp [pressureP6, g6, S]]
        rw [show (fun x => (-2 : ℝ) * S x) = (-2 : ℝ) • S by
          funext x; simp [smul_eq_mul]]
        rw [lpNorm_const_smul]
        norm_num
      _ ≤ 2 * ((∑ j : Fin 3,
          newtonianDerivativePotentialGrowthConstant j (g6 j) R₀) * (1 + r)) :=
        mul_le_mul_of_nonneg_left hS (by norm_num)
      _ = (∑ j : Fin 3, 2 *
          newtonianDerivativePotentialGrowthConstant j (g6 j) R₀) * (1 + r) := by
        rw [← Finset.mul_sum]
        ring
  let H : Vec3 → ℝ :=
    (((pressureP2 η u c s + pressureP3 η u c s) + pressureP4 η u c s) +
      pressureP5 η p s) + pressureP6 η p s
  let C_H : ℝ := (∑ ij : Fin 3 × Fin 3, C2 ij) +
    (∑ ij : Fin 3 × Fin 3, C3 ij) + (∑ ij : Fin 3 × Fin 3, C4 ij) +
    newtonianPotentialGrowthConstant g5 R₀ +
    (∑ j : Fin 3, 2 * newtonianDerivativePotentialGrowthConstant j (g6 j) R₀)
  have ⟨hHmem', hHbound'⟩ := pressure_potential_remainder_memLp_growth
    (P2 := pressureP2 η u c s) (P3 := pressureP3 η u c s)
    (P4 := pressureP4 η u c s) (P5 := pressureP5 η p s)
    (P6 := pressureP6 η p s)
    (C2 := ∑ ij : Fin 3 × Fin 3, C2 ij)
    (C3 := ∑ ij : Fin 3 × Fin 3, C3 ij)
    (C4 := ∑ ij : Fin 3 × Fin 3, C4 ij)
    (C5 := newtonianPotentialGrowthConstant g5 R₀)
    (C6 := ∑ j : Fin 3, 2 * newtonianDerivativePotentialGrowthConstant j (g6 j) R₀)
    h2mem h3mem h4mem hp5mem hp6mem h2bound h3bound h4bound hp5bound hp6bound
  have hHmem : ∀ r : ℝ, 0 < r → MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    simpa [H] using hHmem'
  have hHbound : ∀ r : ℝ, 0 < r → lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C_H * (1 + r) := by
    simpa [H, C_H] using hHbound'
  have hC_H : 0 ≤ C_H := by
    dsimp [C_H, C2, C3, C4]
    apply add_nonneg
    · apply add_nonneg
      · apply add_nonneg
        · apply add_nonneg
          · exact Finset.sum_nonneg (fun ij _ =>
              newtonianPotentialGrowthConstant_nonneg _ _)
          · exact Finset.sum_nonneg (fun ij _ =>
              newtonianDerivativePotentialGrowthConstant_nonneg _ hR₀ _)
        · exact Finset.sum_nonneg (fun ij _ =>
            newtonianDerivativePotentialGrowthConstant_nonneg _ hR₀ _)
      · exact newtonianPotentialGrowthConstant_nonneg _ _
    · apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (by norm_num)
        (newtonianDerivativePotentialGrowthConstant_nonneg j hR₀ _)
  refine ⟨C_H, hC_H, ?_, ?_⟩
  · simpa [H] using hHmem
  · simpa [H] using hHbound


/-- On every compact local box, the cutoff tensor source is globally in
`L^(3/2)` on almost every slice, and the difference between `p₁` and its
completed second-Riesz extension has local `L^(3/2)` membership and linear
growth on every origin-centred spatial ball. -/
theorem pressureSecondExtension_residual_growth_ae_of_sws_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox' : localBox Ω I Ω' J)
    (hball : vec3Ball z.1 ρ ⊆ Ω') :
    ∀ᵐ s ∂volume.restrict J,
      (∀ i j, MemLp
        (fun x => mollifiedBallCutoff z.1 hρ x *
          pressureUTensor u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y => u (y, t) j)) (x, s) i j)
        (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ R : ℝ, 0 < R →
          MemLp (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y => u (y, t) j)) p f s x -
            pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
              (fun i j x => mollifiedBallCutoff z.1 hρ x *
                pressureUTensor u
                  (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                    (fun y => u (y, t) j)) (x, s) i j) x)
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
        (∀ R : ℝ, 0 < R →
          lpNorm (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y => u (y, t) j)) p f s x -
            pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
              (fun i j x => mollifiedBallCutoff z.1 hρ x *
                pressureUTensor u
                  (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                    (fun y => u (y, t) j)) (x, s) i j) x)
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R)) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun t j => average (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)
  let R₀ : ℝ := vec3EuclideanNorm z.1 + ρ
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    linarith only [vec3EuclideanNorm_nonneg z.1, hρ]
  have hB0 : vec3Ball z.1 ρ ⊆ closedBall (0 : Vec3) R₀ := by
    simpa [R₀] using pressureSecondExtension_ball_subset_closedBall z.1
  have hslice := slice_memLp_ae_of_sws hsol hbox'
  have hgradJ : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x : Vec3 => u (x, s) i)
        (fun x => Du (x, s) i) := by
    obtain ⟨_, _, _, _, _, _, _, _, hgrad⟩ := hsol.2.2.2.2.2.1 Ω' J hbox'
    filter_upwards [hgrad 0, hgrad 1, hgrad 2] with s h0 h1 h2
    intro i
    fin_cases i <;> assumption
  have hforce := pressure_force_growth_ae_of_localBox (T := I) hsol hbox' hρ hball
  obtain ⟨_, _, _, _, _, _, hpMem, _, _⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox'
  have hpT := memLp_slice_ae_of_localBox (q := 3 / 2) (by norm_num)
    hball hpMem.aestronglyMeasurable hpMem
  filter_upwards [hslice, hgradJ, hforce, hpT] with s hs hg hJ hp
  have hgu6 := velocity_norm_memLp_six_on_ball hρ hball hs.1 hs.2 (hg ·)
  let μ : Measure Vec3 := volume.restrict (vec3Ball z.1 ρ)
  have hμtop : μ Set.univ < ∞ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      (by
        rw [volume_vec3Ball_eq]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top : volume (vec3Ball z.1 ρ) < ∞)
  let : IsFiniteMeasure μ := ⟨hμtop⟩
  have huMeas : AEMeasurable (fun x : Vec3 => u (x, s)) μ := by
    exact (hs.1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hball)).aemeasurable
  have hgu6' : MemLp (fun y => vec3EuclideanNorm (u (y, s)))
      (ENNReal.ofReal (6 : ℝ)) μ := by
    simpa using hgu6
  have hηc : HasCompactSupport η := by
    simpa [η] using mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η] using mollifiedBallCutoff_smooth z.1 hρ
  have hηsupport : tsupport η ⊆ vec3Ball z.1 ρ := by
    simpa [η] using pressure_cutoff_support_subset_ball z.1 hρ
  have hηbound : ∀ y, |η y| ≤ 1 := by
    intro y
    exact abs_le.mpr ⟨by linarith only [mollifiedBallCutoff_nonneg z.1 hρ y],
      by simpa [η] using mollifiedBallCutoff_le_one z.1 hρ y⟩
  have hηboundAE : ∀ᵐ y ∂μ, ‖η y‖ ≤ (1 : ℝ) := by
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs] using hηbound y
  have hηmeas : AEStronglyMeasurable η μ :=
    hηsmooth.continuous.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hball)
  have ⟨hUmeas, hU32, hG⟩ :=
    pressureUTensor_memLp_three_halves_of_velocity_memLp_six (c := c) η
      hgu6' huMeas hηmeas hηbound hηsupport
  have hC₁ : 0 ≤ cutoffGradientConstant := by
    have hx := pressure_cutoff_spatialDeriv_bound z.1 hρ z.1 (0 : Fin 3)
    have hx' : 0 ≤ cutoffGradientConstant / ρ := (abs_nonneg _).trans hx
    rcases (div_nonneg_iff.mp hx') with h | h
    · exact h.1
    · exfalso
      linarith only [hρ, h.2]
  have hC₂ : 0 ≤ cutoffSecondDerivativeConstant := by
    have hx := pressure_cutoff_mixedSecond_bound z.1 hρ z.1 (0 : Fin 3) 0
    have hx' : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := (abs_nonneg _).trans hx
    rcases (div_nonneg_iff.mp hx') with h | h
    · exact h.1
    · exfalso
      linarith only [sq_pos_of_pos hρ, h.2]
  have hsupp (g : Vec3 → ℝ) (ht : tsupport g ⊆ vec3Ball z.1 ρ) :
      ∀ y ∉ closedBall (0 : Vec3) R₀, g y = 0 := by
    intro y hy
    have hyB : y ∉ vec3Ball z.1 ρ := fun hyB => hy (hB0 hyB)
    exact image_eq_zero_of_notMem_tsupport (fun hgy => hyB (ht hgy))
  have hηpB := pressure_cutoff_pressure_memLp_slice hp hηmeas hηboundAE
  have hηpsupp : tsupport (fun y => η y * p (y, s)) ⊆ vec3Ball z.1 ρ :=
    (tsupport_mul_subset_left (f := η) (g := fun y => p (y, s))).trans hηsupport
  have hηp : MemLp (fun y => η y * p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    lift_ball_memLp_growth_sws hηpB hηpsupp
  have hηpBound : ∀ r : ℝ, 0 < r → lpNorm (fun y => η y * p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      lpNorm (fun y => η y * p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume * (1 + r) := by
    intro r hr
    exact lpNorm_euclideanBall_le_of_memLp_volume hηp hr
  have hsrc (g : Vec3 → ℝ) (hgb : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) μ)
      (hgt : tsupport g ⊆ vec3Ball z.1 ρ) :
      MemLp g (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    have hgg := lift_ball_memLp_growth_sws hgb hgt
    exact memLp_six_fifths_of_memLp_ofReal (by norm_num) hgg (hsupp g hgt)
  have hGc : ∀ i j, HasCompactSupport
      (fun y => η y * pressureUTensor u c (y, s) i j) := by
    intro i j
    exact hηc.mul_right
  have hηlapB : tsupport (spatialLaplacian η) ⊆ vec3Ball z.1 ρ := by
    change tsupport (fun x => ∑ i : Fin 3, spatialDeriv (spatialDeriv η i) i x) ⊆ vec3Ball z.1 ρ
    apply decomposition_ts_support_sum₃_sws
    intro i
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηsupport)
  have hηdBound (i : Fin 3) : ∀ᵐ y ∂μ,
      |spatialDeriv η i y| ≤ cutoffGradientConstant / ρ := by
    filter_upwards [] with y
    simpa [η] using pressure_cutoff_spatialDeriv_bound z.1 hρ y i
  have hηmBound (i j : Fin 3) : ∀ᵐ y ∂μ,
      |mixedSecond η i j y| ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := by
    filter_upwards [] with y
    simpa [η] using pressure_cutoff_mixedSecond_bound z.1 hρ y i j
  have hηlapBound : ∀ᵐ y ∂μ,
      |spatialLaplacian η y| ≤ (3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
    filter_upwards [] with y
    exact cutoff_laplacian_bound_sws (x₀ := z.1) hρ (by rfl) y
  let g2 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    mixedSecond η i j y * pressureUTensor u c (y, s) i j
  let g3 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    pressureUTensor u c (y, s) i j * spatialDeriv η i y
  let g4 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y =>
    pressureUTensor u c (y, s) i j * spatialDeriv η j y
  let g5 : Vec3 → ℝ := fun y => p (y, s) * spatialLaplacian η y
  let g6 : Fin 3 → Vec3 → ℝ := fun j y => spatialDeriv η j y * p (y, s)
  have ⟨hg2, hg3, hg4, hg5, hg6⟩ :=
    pressure_cutoff_compact_sources_memLp_six_fifths ⟨hμtop⟩ η R₀ hB0
      hηsmooth hηsupport hηlapB hUmeas hU32 hp
      hηmBound hηdBound hηlapBound
  let H : Vec3 → ℝ :=
    (((pressureP2 η u c s + pressureP3 η u c s) + pressureP4 η u c s) +
      pressureP5 η p s) + pressureP6 η p s
  have ⟨C_H, hC_H, hHmem, hHbound⟩ := pressure_cutoff_potential_growth_assembly
    η hR₀ hηsupport hηlapB hsupp hg2 hg3 hg4 hg5 hg6
  obtain ⟨hJmem, hJnonneg, hJbound⟩ := hJ
  have hT := pressureSecondExtension_memLp rieszSecondL2Input rieszSecondL2_weak_type hG
  have hres := pressureSecondExtension_residual_growth_of_decomposition
    (p₁ := pressureP1 η u c p f s)
    (P := fun y => η y * p (y, s))
    (H := H)
    (J := pressureP7 η f s + pressureP8 η f s)
    (T := pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
      (fun i j y => η y * pressureUTensor u c (y, s) i j))
    (hdecomp := by
      funext x
      simp only [pressureP1, H, Pi.sub_apply, Pi.add_apply]
      ring)
    (C₀ := lpNorm (fun y => η y * p (y, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (C_H := C_H) (C_J :=
      pressureP7GrowthConstant η f s R₀ + pressureP8GrowthConstant η f s R₀)
    (C_T := lpNorm (pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
      (fun i j y => η y * pressureUTensor u c (y, s) i j))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (by intro r hr; exact hηp.restrict _) hηpBound hHmem hHbound hJmem hJbound
      (by intro r hr; exact memLp_euclideanBall_of_memLp_volume hT r)
      (by intro r hr; exact lpNorm_euclideanBall_le_of_memLp_volume hT hr)
  let C : ℝ := lpNorm (fun y => η y * p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume + C_H +
      (pressureP7GrowthConstant η f s R₀ + pressureP8GrowthConstant η f s R₀) +
      lpNorm (pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
        (fun i j y => η y * pressureUTensor u c (y, s) i j))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume
  refine ⟨hG, C, ?_, ?_, ?_⟩
  · dsimp [C]
    exact add_nonneg (add_nonneg (add_nonneg lpNorm_nonneg hC_H) hJnonneg) lpNorm_nonneg
  · intro R hR
    simpa [η, c, R₀, H, C] using (hres R hR).1
  · intro R hR
    simpa [η, c, R₀, H, C] using (hres R hR).2


end CKN

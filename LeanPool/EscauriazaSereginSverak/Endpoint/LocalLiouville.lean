/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.ForceCancellation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Liouville
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.HomogeneousSobolev

/-!
# Liouville theorem for a curl-free `L^3` field

This file proves `lem:liouville-L3` from the weak harmonic Liouville estimate.
-/

public section

open CKN

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


noncomputable section

namespace ESS

private theorem component_mul_smoothCompact_integrable
    {v : Vec3 → Vec3} (hv : MemLp v (ENNReal.ofReal (3 : ℝ)) volume)
    (i : Fin 3) {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    Integrable (fun x => v x i * φ x) volume := by
  have hvi : MemLp (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume :=
    hv.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hli : LocallyIntegrable (fun x => v x i) volume :=
    hvi.locallyIntegrable (by norm_num)
  have hφc' : Continuous φ := hφ.continuous
  have hi := hli.integrable_smul_left_of_hasCompactSupport hφc' hφc
  simpa only [smul_eq_mul, mul_comm] using hi

private theorem spatialDeriv_smoothCompact
    {φ : Vec3 → ℝ} (hφ : CKN.SmoothCompactTest φ) (i : Fin 3) :
    CKN.SmoothCompactTest (CKN.spatialDeriv φ i) := by
  exact ⟨fun n => (CKN.contDiff_spatialDeriv_smooth
      ((contDiff_infty).2 hφ.1) i).of_le (by simp),
    hφ.2.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)⟩

private theorem component_laplacian_integrable
    {v : Vec3 → Vec3} (hv : MemLp v (ENNReal.ofReal (3 : ℝ)) volume)
    (i : Fin 3) {φ : Vec3 → ℝ} (hφ : CKN.SmoothCompactTest φ) :
    Integrable (fun x => v x i * CKN.spatialLaplacian φ x) volume := by
  have hφlap : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialLaplacian φ) :=
    CKN.contDiff_spatialLaplacian_smooth ((contDiff_infty).2 hφ.1)
  have hφlapc : HasCompactSupport (CKN.spatialLaplacian φ) :=
    CKN.hasCompactSupport_spatialLaplacian hφ.2
  exact component_mul_smoothCompact_integrable hv i hφlap hφlapc

private theorem component_weaklyHarmonic
    {v : Vec3 → Vec3} (hv : MemLp v (ENNReal.ofReal (3 : ℝ)) volume)
    (hdiv : CKN.DistributionalDivergenceFree v)
    (hcurl : ∀ (i j : Fin 3) (φ : Vec3 → ℝ), CKN.SmoothCompactTest φ →
      ∫ x, v x i * CKN.spatialDeriv φ j x -
        v x j * CKN.spatialDeriv φ i x = 0)
    (i : Fin 3) :
    WeaklyHarmonicOn Set.univ (fun x => v x i) := by
  intro φ hφ hφc hφU
  have htest : CKN.SmoothCompactTest φ := ⟨fun n => hφ.of_le (by simp), hφc⟩
  have hderivtest (j : Fin 3) : CKN.SmoothCompactTest (CKN.spatialDeriv φ j) :=
    spatialDeriv_smoothCompact htest j
  have hdivTest : CKN.SmoothCompactTest (CKN.spatialDeriv φ i) := hderivtest i
  have hdivzero := hdiv (CKN.spatialDeriv φ i) hdivTest
  have hcurlzero (j : Fin 3) := hcurl i j (CKN.spatialDeriv φ j) (hderivtest j)
  have hsumcurl :
      ∫ x, ∑ j : Fin 3,
        (v x i * CKN.spatialDeriv (CKN.spatialDeriv φ j) j x -
          v x j * CKN.spatialDeriv (CKN.spatialDeriv φ j) i x) = 0 := by
    rw [integral_finsetSum (s := Finset.univ)]
    · simp [hcurlzero]
    · intro j hj
      have h₁ := component_mul_smoothCompact_integrable hv i
        (CKN.contDiff_mixedSecond_smooth hφ j j)
        (CKN.hasCompactSupport_mixedSecond hφc j j)
      have h₂ := component_mul_smoothCompact_integrable hv j
        (CKN.contDiff_mixedSecond_smooth hφ i j)
        (CKN.hasCompactSupport_mixedSecond hφc i j)
      exact h₁.sub h₂
  have hsumdiv : ∫ x, ∑ j : Fin 3,
      v x j * CKN.spatialDeriv (CKN.spatialDeriv φ i) j x = 0 := by
    simpa only [Finset.sum_apply] using hdivzero
  have hcomm (j : Fin 3) (x : Vec3) :
      CKN.spatialDeriv (CKN.spatialDeriv φ j) i x =
        CKN.spatialDeriv (CKN.spatialDeriv φ i) j x := by
    change CKN.mixedSecond φ i j x = CKN.mixedSecond φ j i x
    exact CKN.mixedSecond_swap hφ i j x
  have hsumidentity :
      ∫ x, ∑ j : Fin 3,
        (v x i * CKN.spatialDeriv (CKN.spatialDeriv φ j) j x -
          v x j * CKN.spatialDeriv (CKN.spatialDeriv φ j) i x) =
      ∫ x, v x i * CKN.spatialLaplacian φ x -
        ∑ j : Fin 3, v x j * CKN.spatialDeriv (CKN.spatialDeriv φ i) j x := by
    apply integral_congr_ae
    filter_upwards [] with x
    change (∑ j : Fin 3,
        (v x i * CKN.spatialDeriv (CKN.spatialDeriv φ j) j x -
          v x j * CKN.spatialDeriv (CKN.spatialDeriv φ j) i x)) =
      v x i * (∑ j : Fin 3,
        CKN.spatialDeriv (CKN.spatialDeriv φ j) j x) -
      ∑ j : Fin 3, v x j * CKN.spatialDeriv (CKN.spatialDeriv φ i) j x
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcomm j x]
  have htarget : ∫ x, v x i * CKN.spatialLaplacian φ x = 0 := by
    have hsource : (∫ x, ∑ j : Fin 3,
        (v x i * CKN.spatialDeriv (CKN.spatialDeriv φ j) j x -
          v x j * CKN.spatialDeriv (CKN.spatialDeriv φ j) i x)) =
        (∫ x, v x i * CKN.spatialLaplacian φ x) -
          (∫ x, ∑ j : Fin 3,
            v x j * CKN.spatialDeriv (CKN.spatialDeriv φ i) j x) := by
      have hIntLap := component_laplacian_integrable hv i htest
      have hIntDiv : Integrable (fun x => ∑ j : Fin 3,
          v x j * CKN.spatialDeriv (CKN.spatialDeriv φ i) j x) volume :=
        integrable_finsetSum (s := Finset.univ) (fun j _ =>
          component_mul_smoothCompact_integrable hv j
            (CKN.contDiff_mixedSecond_smooth hφ j i)
            (CKN.hasCompactSupport_mixedSecond hφc j i))
      rw [hsumidentity, integral_sub hIntLap hIntDiv]
    have hcalc : (∫ x, v x i * CKN.spatialLaplacian φ x) -
        (∫ x, ∑ j : Fin 3,
          v x j * CKN.spatialDeriv (CKN.spatialDeriv φ i) j x) = 0 := by
      rw [← hsource, hsumcurl]
    have hcalc' : (∫ x, v x i * CKN.spatialLaplacian φ x) - 0 = 0 := by
      simpa [hsumdiv] using hcalc
    exact sub_eq_zero.mp hcalc'
  simpa only [Measure.restrict_univ] using htarget

private theorem component_memLp_and_growth
    {v : Vec3 → Vec3} (hv : MemLp v (ENNReal.ofReal (3 : ℝ)) volume)
    (i : Fin 3) (ρ : ℝ) (hρ : 0 < ρ) :
    MemLp (fun x => v x i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (CKN.euclideanBall (0 : Vec3) ρ)) ∧
    lpNorm (fun x => v x i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (CKN.euclideanBall (0 : Vec3) ρ)) ≤
      (2 * lpNorm (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume) * (1 + ρ) := by
  let B : Set Vec3 := CKN.euclideanBall 0 ρ
  let μ : Measure Vec3 := volume.restrict B
  have hvi : MemLp (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume :=
    hv.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hμfinite : IsFiniteMeasure μ := by
    change IsFiniteMeasure (volume.restrict B)
    rw [isFiniteMeasure_restrict]
    exact CKN.volume_euclideanBall_ne_top 0 hρ
  let : IsFiniteMeasure μ := hμfinite
  have hlocal₃ := hvi.restrict B
  have hlocal₃₂ : MemLp (fun x => v x i) (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply hlocal₃.mono_exponent
    norm_num
  have hmeas : AEStronglyMeasurable (fun x => v x i) μ :=
    hvi.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show ENNReal.ofReal (3 / 2 : ℝ) ≤ ENNReal.ofReal (3 : ℝ) by norm_num)
    hmeas
  have hvolume := euclideanBall_volume_rpow_third_le hρ
  have hlocalBound :
      eLpNorm (fun x => v x i) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
        eLpNorm (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume *
          ENNReal.ofReal (2 * ρ) := by
    have hexp :
        (1 / (ENNReal.ofReal (3 / 2 : ℝ)).toReal -
          1 / (ENNReal.ofReal (3 : ℝ)).toReal) = (1 / 3 : ℝ) := by
      norm_num [ENNReal.toReal_ofReal]
    have hμuniv : μ Set.univ = volume B := by simp [μ]
    calc
      eLpNorm (fun x => v x i) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
          eLpNorm (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) μ *
            (volume B) ^ (1 / 3 : ℝ) := by
        have hh := hcompare
        rw [hμuniv, hexp] at hh
        exact hh
      _ ≤ eLpNorm (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume *
            ENNReal.ofReal (2 * ρ) := by
        apply mul_le_mul
        · exact eLpNorm_mono_measure _ Measure.restrict_le_self
        · exact hvolume
        · positivity
        · positivity
  have hfinite :
      (eLpNorm (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume *
        ENNReal.ofReal (2 * ρ)) ≠ ∞ := by
    exact (ENNReal.mul_lt_top hvi.eLpNorm_lt_top ENNReal.ofReal_lt_top).ne
  have hlocalBoundR := ENNReal.toReal_mono hfinite hlocalBound
  rw [ENNReal.toReal_mul, toReal_eLpNorm,
    toReal_eLpNorm, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ρ)] at hlocalBoundR
  have hfinal :
      lpNorm (fun x => v x i) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
        (2 * lpNorm (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume) * (1 + ρ) := by
    calc
      lpNorm (fun x => v x i) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
          lpNorm (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume * (2 * ρ) :=
        hlocalBoundR
      _ = (2 * lpNorm (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume) * ρ := by ring
      _ ≤ (2 * lpNorm (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume) * (1 + ρ) := by
        apply mul_le_mul_of_nonneg_left
        · linarith only [hρ]
        · exact mul_nonneg (by norm_num) lpNorm_nonneg
  exact ⟨hlocal₃₂, by simpa [B, μ] using hfinal⟩

/-- A distributionally divergence-free and curl-free `L^3` vector field on
all of space vanishes almost everywhere, as in `lem:liouville-L3`. -/
theorem liouvilleL3
    {v : Vec3 → Vec3}
    (hv : MemLp v (ENNReal.ofReal (3 : ℝ)) volume)
    (hdiv : CKN.DistributionalDivergenceFree v)
    (hcurl : ∀ (i j : Fin 3) (φ : Vec3 → ℝ), CKN.SmoothCompactTest φ →
      ∫ x, v x i * CKN.spatialDeriv φ j x -
        v x j * CKN.spatialDeriv φ i x = 0) :
    v =ᵐ[volume] 0 := by
  have hcomponent : ∀ i : Fin 3, (fun x => v x i) =ᵐ[volume] 0 := by
    intro i
    have hvi : MemLp (fun x => v x i) (ENNReal.ofReal (3 : ℝ)) volume :=
      hv.continuousLinearMap_comp
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
    exact CKN.Foundation.Heat.weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth
      (mul_nonneg (by norm_num) lpNorm_nonneg)
      (fun ρ hρ => (component_memLp_and_growth hv i ρ hρ).1)
      (component_weaklyHarmonic hv hdiv hcurl i)
      (fun ρ hρ => (component_memLp_and_growth hv i ρ hρ).2)
  have hall : ∀ᵐ x ∂volume, ∀ i : Fin 3, v x i = 0 :=
    (ae_all_iff).2 hcomponent
  filter_upwards [hall] with x hx
  funext i
  exact hx i

end ESS

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergySmooth

/-!
# Local Energy Momentum Equation

Local energy identities and limit passages for the endpoint regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace ESS

private theorem smoothMomentum_component_integral_by_parts
    {u : Vec3 × ℝ → ℝ} {F G : Fin 3 → Vec3 × ℝ → ℝ}
    {p ψ : Vec3 × ℝ → ℝ} (k : Fin 3)
    (hA : Integrable (fun z => -(u z * dirDeriv ψ timeDir z)) volume)
    (hF : ∀ j, Integrable
      (fun z => F j z * dirDeriv ψ (spatialDir j) z) volume)
    (hG : ∀ j, Integrable
      (fun z => G j z * dirDeriv ψ (spatialDir j) z) volume)
    (hP : Integrable (fun z => p z * dirDeriv ψ (spatialDir k) z) volume)
    (hU : Integrable (fun z => dirDeriv u timeDir z * ψ z) volume)
    (hFU : ∀ j, Integrable
      (fun z => dirDeriv (F j) (spatialDir j) z * ψ z) volume)
    (hGU : ∀ j, Integrable
      (fun z => dirDeriv (G j) (spatialDir j) z * ψ z) volume)
    (hPU : Integrable (fun z => dirDeriv p (spatialDir k) z * ψ z) volume)
    (hAibp : (∫ z, -(u z * dirDeriv ψ timeDir z) ∂volume) =
      ∫ z, dirDeriv u timeDir z * ψ z ∂volume)
    (hFibp : ∀ j, (∫ z, -(F j z * dirDeriv ψ (spatialDir j) z) ∂volume) =
      ∫ z, dirDeriv (F j) (spatialDir j) z * ψ z ∂volume)
    (hGibp : ∀ j, (∫ z, G j z * dirDeriv ψ (spatialDir j) z ∂volume) =
      -∫ z, dirDeriv (G j) (spatialDir j) z * ψ z ∂volume)
    (hPibp : -(∫ z, p z * dirDeriv ψ (spatialDir k) z ∂volume) =
      ∫ z, dirDeriv p (spatialDir k) z * ψ z ∂volume) :
    (∫ z, (-(u z * dirDeriv ψ timeDir z)
      - ∑ j : Fin 3, F j z * dirDeriv ψ (spatialDir j) z
      + ∑ j : Fin 3, G j z * dirDeriv ψ (spatialDir j) z
      - p z * dirDeriv ψ (spatialDir k) z) ∂volume) =
    ∫ z, (dirDeriv u timeDir z
      + ∑ j : Fin 3, dirDeriv (F j) (spatialDir j) z
      - ∑ j : Fin 3, dirDeriv (G j) (spatialDir j) z
      + dirDeriv p (spatialDir k) z) * ψ z ∂volume := by
  let A := fun z => -(u z * dirDeriv ψ timeDir z)
  let B := fun z => ∑ j : Fin 3, F j z * dirDeriv ψ (spatialDir j) z
  let C := fun z => ∑ j : Fin 3, G j z * dirDeriv ψ (spatialDir j) z
  let D := fun z => p z * dirDeriv ψ (spatialDir k) z
  let U := fun z => dirDeriv u timeDir z * ψ z
  let FU := fun z => ∑ j : Fin 3, dirDeriv (F j) (spatialDir j) z * ψ z
  let GU := fun z => ∑ j : Fin 3, dirDeriv (G j) (spatialDir j) z * ψ z
  let PU := fun z => dirDeriv p (spatialDir k) z * ψ z
  have hB : Integrable B volume :=
    integrable_finsetSum Finset.univ (fun j hj => hF j)
  have hC : Integrable C volume :=
    integrable_finsetSum Finset.univ (fun j hj => hG j)
  have hFU' : Integrable FU volume :=
    integrable_finsetSum Finset.univ (fun j hj => hFU j)
  have hGU' : Integrable GU volume :=
    integrable_finsetSum Finset.univ (fun j hj => hGU j)
  have hleftAB := hA.sub hB
  have hleftABC := hleftAB.add hC
  have hrightAB := hU.add hFU'
  have hrightABC := hrightAB.sub hGU'
  have hleftExpand :
      (∫ z, A z - B z + C z - D z ∂volume) =
        (∫ z, A z ∂volume) - ∫ z, B z ∂volume +
          ∫ z, C z ∂volume - ∫ z, D z ∂volume := by
    calc
      _ = ∫ z, ((A - B + C) z) - D z ∂volume := by rfl
      _ = (∫ z, (A - B + C) z ∂volume) - ∫ z, D z ∂volume :=
        integral_sub hleftABC hP
      _ = ((∫ z, (A - B) z ∂volume) + ∫ z, C z ∂volume) -
          ∫ z, D z ∂volume := by
        rw [show (∫ z, (A - B + C) z ∂volume) =
          (∫ z, (A - B) z ∂volume) + ∫ z, C z ∂volume by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (integral_add hleftAB hC)]
      _ = _ := by
        rw [show (∫ z, (A - B) z ∂volume) =
          (∫ z, A z ∂volume) - ∫ z, B z ∂volume by
            simpa only [Pi.sub_apply] using (integral_sub hA hB)]
  have hrightExpand :
      (∫ z, (dirDeriv u timeDir z +
        ∑ j : Fin 3, dirDeriv (F j) (spatialDir j) z -
        ∑ j : Fin 3, dirDeriv (G j) (spatialDir j) z +
        dirDeriv p (spatialDir k) z) * ψ z ∂volume) =
        (∫ z, U z ∂volume) + ∫ z, FU z ∂volume -
          ∫ z, GU z ∂volume + ∫ z, PU z ∂volume := by
    calc
      _ = ∫ z, U z + FU z - GU z + PU z ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp [U, FU, GU, PU, add_mul, sub_mul, Finset.sum_mul]
      _ = ∫ z, ((U + FU - GU) z) + PU z ∂volume := by rfl
      _ = (∫ z, (U + FU - GU) z ∂volume) + ∫ z, PU z ∂volume :=
        integral_add hrightABC hPU
      _ = ((∫ z, (U + FU) z ∂volume) - ∫ z, GU z ∂volume) +
          ∫ z, PU z ∂volume := by
        rw [show (∫ z, (U + FU - GU) z ∂volume) =
          (∫ z, (U + FU) z ∂volume) - ∫ z, GU z ∂volume by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (integral_sub hrightAB hGU')]
      _ = _ := by
        rw [show (∫ z, (U + FU) z ∂volume) =
          (∫ z, U z ∂volume) + ∫ z, FU z ∂volume by
            simpa only [Pi.add_apply] using (integral_add hU hFU')]
  have hsumF : (∫ z, B z ∂volume) = -(∫ z, FU z ∂volume) := by
    dsimp [B, FU]
    rw [integral_finsetSum Finset.univ (fun j hj => hF j),
      integral_finsetSum Finset.univ (fun j hj => hFU j)]
    calc
      _ = ∑ j : Fin 3, -(∫ z,
          dirDeriv (F j) (spatialDir j) z * ψ z ∂volume) := by
        apply Finset.sum_congr rfl
        intro j hj
        have h := hFibp j
        rw [integral_neg] at h
        linarith
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hsumG : (∫ z, C z ∂volume) = -(∫ z, GU z ∂volume) := by
    dsimp [C, GU]
    rw [integral_finsetSum Finset.univ (fun j hj => hG j),
      integral_finsetSum Finset.univ (fun j hj => hGU j)]
    calc
      _ = ∑ j : Fin 3, -(∫ z,
          dirDeriv (G j) (spatialDir j) z * ψ z ∂volume) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hGibp j
      _ = _ := by rw [Finset.sum_neg_distrib]
  dsimp [A, D, U, PU] at hleftExpand hrightExpand ⊢
  rw [hleftExpand, hrightExpand, hAibp, hsumF, hsumG]
  linear_combination hPibp

/-- A smooth momentum equation gives its weak integral identity for compactly supported
smooth vector tests. -/
theorem smoothMomentumEquation_tested
    {u : Vec3 × ℝ → Vec3} {F G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {p : Vec3 × ℝ → ℝ} {φ : Vec3 × ℝ → Vec3}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => u z i))
    (hF : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => F z i j))
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => G z i j))
    (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hmom : ∀ z, z ∈ tsupport φ → ∀ i,
      dirDeriv (fun y => u y i) timeDir z
        + ∑ j : Fin 3, dirDeriv (fun y => F y i j) (spatialDir j) z
        - ∑ j : Fin 3, dirDeriv (fun y => G y i j) (spatialDir j) z
        + dirDeriv p (spatialDir i) z = 0) :
    ∫ z, smoothMomentumTestIntegrand u
      (fun z i j => F z i j - u z i * u z j) G p φ z = 0 := by
  have hu1 (i : Fin 3) : ContDiff ℝ (1 : ℕ∞) (fun z => u z i) :=
    (hu i).of_le (by norm_num)
  have hF1 (i j : Fin 3) : ContDiff ℝ (1 : ℕ∞) (fun z => F z i j) :=
    (hF i j).of_le (by norm_num)
  have hG1 (i j : Fin 3) : ContDiff ℝ (1 : ℕ∞) (fun z => G z i j) :=
    (hG i j).of_le (by norm_num)
  have hp1 : ContDiff ℝ (1 : ℕ∞) p := hp.of_le (by norm_num)
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z i) :=
    (contDiff_apply ℝ ℝ i).comp hφ
  have hφi1 (i : Fin 3) : ContDiff ℝ (1 : ℕ∞) (fun z => φ z i) :=
    (hφi i).of_le (by norm_num)
  have hφic (i : Fin 3) : HasCompactSupport (fun z => φ z i) := by
    apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    intro z hz
    apply subset_tsupport
    rw [Function.mem_support]
    intro hzero
    exact hz (congrFun hzero i)
  have htestDerivCompact (i : Fin 3) (v : Vec3 × ℝ) :
      HasCompactSupport (fun z => dirDeriv (fun y => φ y i) v z) := by
    have h := (hφic i).fderiv_apply (𝕜 := ℝ) v
    simpa [dirDeriv] using h
  have hprodTest (f : Vec3 × ℝ → ℝ) (hf : ContDiff ℝ (1 : ℕ∞) f)
      (i : Fin 3) (v : Vec3 × ℝ) :
      Integrable (fun z => f z * dirDeriv (fun y => φ y i) v z)
        (volume : Measure (Vec3 × ℝ)) := by
    have hDf : Continuous (fun z => dirDeriv f v z) := by
      exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hDφ : Continuous (fun z => dirDeriv (fun y => φ y i) v z) := by
      exact ((hφi1 i).continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact (hf.continuous.mul hDφ).integrable_of_hasCompactSupport
      ((htestDerivCompact i v).mul_left)
  have hderivTest (f : Vec3 × ℝ → ℝ) (hf : ContDiff ℝ (1 : ℕ∞) f)
      (i : Fin 3) (v : Vec3 × ℝ) :
      Integrable (fun z => dirDeriv f v z * φ z i)
        (volume : Measure (Vec3 × ℝ)) := by
    have hDf : Continuous (fun z => dirDeriv f v z) := by
      exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact (hDf.mul (hφi1 i).continuous).integrable_of_hasCompactSupport
      (hφic i).mul_left
  let W (i : Fin 3) (z : Vec3 × ℝ) : ℝ :=
    -(u z i * dirDeriv (fun y => φ y i) timeDir z)
      - ∑ j : Fin 3, F z i j * dirDeriv (fun y => φ y i) (spatialDir j) z
      + ∑ j : Fin 3, G z i j * dirDeriv (fun y => φ y i) (spatialDir j) z
      - p z * dirDeriv (fun y => φ y i) (spatialDir i) z
  have hWInt (i : Fin 3) : Integrable (W i) (volume : Measure (Vec3 × ℝ)) := by
    have htime := (hprodTest (fun z => u z i) (hu1 i) i timeDir).neg
    have hFsum : Integrable
        (fun z => ∑ j : Fin 3,
          F z i j * dirDeriv (fun y => φ y i) (spatialDir j) z)
        (volume : Measure (Vec3 × ℝ)) := by
      apply integrable_finsetSum
      intro j hj
      exact hprodTest (fun z => F z i j) (hF1 i j) i (spatialDir j)
    have hGsum : Integrable
        (fun z => ∑ j : Fin 3,
          G z i j * dirDeriv (fun y => φ y i) (spatialDir j) z)
        (volume : Measure (Vec3 × ℝ)) := by
      apply integrable_finsetSum
      intro j hj
      exact hprodTest (fun z => G z i j) (hG1 i j) i (spatialDir j)
    have hpterm := hprodTest p hp1 i (spatialDir i)
    dsimp [W]
    exact ((htime.sub hFsum).add hGsum).sub hpterm
  have htimeIBP (i : Fin 3) :
      (∫ z, -(u z i * dirDeriv (fun y => φ y i) timeDir z)
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ z, dirDeriv (fun y => u y i) timeDir z * φ z i
          ∂(volume : Measure (Vec3 × ℝ)) := by
    rw [integral_neg, smoothIntegral_dirDeriv_mul_eq_neg (hu1 i) (hφi1 i)
      (hφic i) timeDir]
    simp
  have hFIBP (i j : Fin 3) :
      (∫ z, -(F z i j * dirDeriv (fun y => φ y i) (spatialDir j) z)
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ z, dirDeriv (fun y => F y i j) (spatialDir j) z * φ z i
          ∂(volume : Measure (Vec3 × ℝ)) := by
    rw [integral_neg, smoothIntegral_dirDeriv_mul_eq_neg (hF1 i j) (hφi1 i)
      (hφic i) (spatialDir j)]
    simp
  have hGIBP (i j : Fin 3) :
      (∫ z, G z i j * dirDeriv (fun y => φ y i) (spatialDir j) z
          ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ z, dirDeriv (fun y => G y i j) (spatialDir j) z * φ z i
          ∂(volume : Measure (Vec3 × ℝ)) := by
    exact smoothIntegral_dirDeriv_mul_eq_neg (hG1 i j) (hφi1 i) (hφic i) (spatialDir j)
  have hpIBP (i : Fin 3) :
      (∫ z, -(p z * dirDeriv (fun y => φ y i) (spatialDir i) z)
          ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ z, dirDeriv p (spatialDir i) z * φ z i
          ∂(volume : Measure (Vec3 × ℝ)) := by
    rw [integral_neg, smoothIntegral_dirDeriv_mul_eq_neg hp1 (hφi1 i)
      (hφic i) (spatialDir i)]
    simp
  have hpIBPneg (i : Fin 3) :
      -(∫ z, p z * dirDeriv (fun y => φ y i) (spatialDir i) z
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ z, dirDeriv p (spatialDir i) z * φ z i
        ∂(volume : Measure (Vec3 × ℝ)) := by
    rw [smoothIntegral_dirDeriv_mul_eq_neg hp1 (hφi1 i) (hφic i) (spatialDir i)]
    ring_nf
  have hWintEq (i : Fin 3) :
      (∫ z, W i z ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ z,
          (dirDeriv (fun y => u y i) timeDir z
            + ∑ j : Fin 3, dirDeriv (fun y => F y i j) (spatialDir j) z
            - ∑ j : Fin 3, dirDeriv (fun y => G y i j) (spatialDir j) z
            + dirDeriv p (spatialDir i) z) * φ z i
          ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [W] using smoothMomentum_component_integral_by_parts
      (u := fun z => u z i) (F := fun j z => F z i j)
      (G := fun j z => G z i j) (p := p) (ψ := fun z => φ z i) i
      ((hprodTest (fun z => u z i) (hu1 i) i timeDir).neg)
      (fun j => hprodTest (fun z => F z i j) (hF1 i j) i (spatialDir j))
      (fun j => hprodTest (fun z => G z i j) (hG1 i j) i (spatialDir j))
      (hprodTest p hp1 i (spatialDir i))
      (hderivTest (fun z => u z i) (hu1 i) i timeDir)
      (fun j => hderivTest (fun z => F z i j) (hF1 i j) i (spatialDir j))
      (fun j => hderivTest (fun z => G z i j) (hG1 i j) i (spatialDir j))
      (hderivTest p hp1 i (spatialDir i))
      (htimeIBP i) (hFIBP i) (hGIBP i) (hpIBPneg i)
  have hWzero (i : Fin 3) : ∫ z, W i z ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    have hzero : (fun z =>
        (dirDeriv (fun y => u y i) timeDir z
          + ∑ j : Fin 3, dirDeriv (fun y => F y i j) (spatialDir j) z
          - ∑ j : Fin 3, dirDeriv (fun y => G y i j) (spatialDir j) z
          + dirDeriv p (spatialDir i) z) * φ z i) = fun _ => 0 := by
      funext z
      by_cases hz : z ∈ tsupport φ
      · simp [hmom z hz i]
      · have hφzero : φ z i = 0 := by
          have h := image_eq_zero_of_notMem_tsupport hz
          exact congrFun h i
        simp [hφzero]
    rw [hWintEq i]
    rw [hzero]
    exact integral_zero (Vec3 × ℝ) ℝ
  have hdecomp (z : Vec3 × ℝ) :
      smoothMomentumTestIntegrand u
        (fun z i j => F z i j - u z i * u z j) G p φ z =
        ∑ i : Fin 3, W i z := by
    simp only [smoothMomentumTestIntegrand, W]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring_nf
  have hsumInt : Integrable (fun z => ∑ i : Fin 3, W i z)
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum
    intro i hi
    exact hWInt i
  calc
    _ = ∫ z, ∑ i : Fin 3, W i z ∂(volume : Measure (Vec3 × ℝ)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hdecomp z
    _ = ∑ i : Fin 3, ∫ z, W i z ∂(volume : Measure (Vec3 × ℝ)) :=
      integral_finsetSum Finset.univ (fun i hi => hWInt i)
    _ = 0 := by simp [hWzero]

private theorem smoothIntegral_dirDeriv_eq_zero
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (1 : ℕ∞) f)
    (hfc : HasCompactSupport f) (v : Vec3 × ℝ) :
    ∫ z, dirDeriv f v z ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
  have hone : ContDiff ℝ (1 : ℕ∞) (fun _ : Vec3 × ℝ => (1 : ℝ)) := contDiff_const
  calc
    _ = ∫ z, (1 : ℝ) * dirDeriv f v z ∂(volume : Measure (Vec3 × ℝ)) := by simp
    _ = -∫ z, dirDeriv (fun _ : Vec3 × ℝ => (1 : ℝ)) v z * f z
        ∂(volume : Measure (Vec3 × ℝ)) :=
      smoothIntegral_dirDeriv_mul_eq_neg hone hf hfc v
    _ = 0 := by simp [dirDeriv]

private theorem smoothDirectionalDerivative_continuous {f : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (1 : ℕ∞) f) (v : Vec3 × ℝ) :
    Continuous (fun z => dirDeriv f v z) := by
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

private theorem smoothEnergyIntegrands_vanish_off_test_support
    {u : Vec3 × ℝ → Vec3} {R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {p ψ : Vec3 × ℝ → ℝ} :
    (∀ z, z ∉ tsupport ψ → smoothEnergyBaseIntegrand u R G p ψ z = 0) ∧
    (∀ z, z ∉ tsupport ψ → smoothEnergyTestIntegrand u R G p ψ z = 0) ∧
    (∀ z, z ∉ tsupport ψ → smoothEnergyTotalDerivative u ψ z = 0) := by
  let T : Vec3 × ℝ → ℝ := fun z => velocitySq u z * ψ z
  have hψFirstSupport (v : Vec3 × ℝ) :
      tsupport (fun z => dirDeriv ψ v z) ⊆ tsupport ψ := by
    simpa [dirDeriv] using (tsupport_fderiv_apply_subset (𝕜 := ℝ) v)
  have hψSecondSupport (j : Fin 3) :
      tsupport (fun z => dirDeriv (fun y => dirDeriv ψ (spatialDir j) y)
        (spatialDir j) z) ⊆ tsupport ψ := by
    have hsecond : tsupport (fun z => dirDeriv
        (fun y => dirDeriv ψ (spatialDir j) y) (spatialDir j) z) ⊆
        tsupport (fun y => dirDeriv ψ (spatialDir j) y) := by
      simpa [dirDeriv] using (tsupport_fderiv_apply_subset
        (𝕜 := ℝ) (f := fun y => dirDeriv ψ (spatialDir j) y) (spatialDir j))
    exact hsecond.trans (hψFirstSupport (spatialDir j))
  have hψzero (z : Vec3 × ℝ) (hnot : z ∉ tsupport ψ) : ψ z = 0 :=
    image_eq_zero_of_notMem_tsupport hnot
  have hψDzero (z : Vec3 × ℝ) (hnot : z ∉ tsupport ψ)
      (v : Vec3 × ℝ) : dirDeriv ψ v z = 0 := by
    rw [dirDeriv, fderiv_of_notMem_tsupport ℝ hnot]
    simp
  have hψDDzero (z : Vec3 × ℝ) (hnot : z ∉ tsupport ψ) (j : Fin 3) :
      dirDeriv (fun y => dirDeriv ψ (spatialDir j) y) (spatialDir j) z = 0 := by
    have hnot' : z ∉ tsupport (fun y => dirDeriv ψ (spatialDir j) y) := by
      intro hz'
      exact hnot (hψFirstSupport (spatialDir j) hz')
    rw [dirDeriv, fderiv_of_notMem_tsupport ℝ hnot']
    simp
  have hbasezero (z : Vec3 × ℝ) (hnot : z ∉ tsupport ψ) :
      smoothEnergyBaseIntegrand u R G p ψ z = 0 := by
    simp [smoothEnergyBaseIntegrand, hψzero z hnot, hψDzero z hnot,
      hψDDzero z hnot]
  have htestzero (z : Vec3 × ℝ) (hnot : z ∉ tsupport ψ) :
      smoothEnergyTestIntegrand u R G p ψ z = 0 := by
    simp [smoothEnergyTestIntegrand, hψzero z hnot, hψDzero z hnot]
  have hTsupport : tsupport T ⊆ tsupport ψ := by
    change tsupport (fun z => velocitySq u z * ψ z) ⊆ tsupport ψ
    exact tsupport_mul_subset_right
  have hTderivSupport : tsupport (fun z => dirDeriv T timeDir z) ⊆
      tsupport ψ := by
    have h := tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := T) timeDir
    simpa [dirDeriv] using h.trans hTsupport
  have hfluxSupport (j : Fin 3) :
      tsupport (fun z => ψ z * velocitySq u z * u z j) ⊆ tsupport ψ := by
    calc
      tsupport (fun z => ψ z * velocitySq u z * u z j) ⊆
          tsupport (fun z => ψ z * velocitySq u z) := tsupport_mul_subset_left
      _ ⊆ tsupport ψ := tsupport_mul_subset_left
  have hfluxDerivSupport (j : Fin 3) :
      tsupport (fun z => dirDeriv (fun y => ψ y * velocitySq u y * u y j)
        (spatialDir j) z) ⊆ tsupport ψ := by
    have h := tsupport_fderiv_apply_subset (𝕜 := ℝ)
      (f := fun z => ψ z * velocitySq u z * u z j) (spatialDir j)
    simpa [dirDeriv] using h.trans (hfluxSupport j)
  have hviscSupport (j : Fin 3) :
      tsupport (fun z => velocitySq u z * dirDeriv ψ (spatialDir j) z) ⊆
        tsupport ψ := by
    exact tsupport_mul_subset_right.trans (hψFirstSupport (spatialDir j))
  have hviscDerivSupport (j : Fin 3) :
      tsupport (fun z => dirDeriv (fun y => velocitySq u y *
        dirDeriv ψ (spatialDir j) y) (spatialDir j) z) ⊆ tsupport ψ := by
    have h := tsupport_fderiv_apply_subset (𝕜 := ℝ)
      (f := fun z => velocitySq u z * dirDeriv ψ (spatialDir j) z) (spatialDir j)
    simpa [dirDeriv] using h.trans (hviscSupport j)
  have htotalzero (z : Vec3 × ℝ) (hnot : z ∉ tsupport ψ) :
      smoothEnergyTotalDerivative u ψ z = 0 := by
    have hTzero : dirDeriv T timeDir z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hz => hnot (hTderivSupport hz))
    have hfluxzero (j : Fin 3) :
        dirDeriv (fun y => ψ y * velocitySq u y * u y j) (spatialDir j) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hz => hnot (hfluxDerivSupport j hz))
    have hvisczero (j : Fin 3) :
        dirDeriv (fun y => velocitySq u y * dirDeriv ψ (spatialDir j) y)
          (spatialDir j) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hz => hnot (hviscDerivSupport j hz))
    simp [smoothEnergyTotalDerivative, T, hTzero, hfluxzero, hvisczero]
  exact ⟨hbasezero, htestzero, htotalzero⟩

private theorem smoothEnergyTotalDerivative_integrable_integral_zero
    {u : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => u z i))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Integrable (smoothEnergyTotalDerivative u ψ) (volume : Measure (Vec3 × ℝ)) ∧
      ∫ z, smoothEnergyTotalDerivative u ψ z ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
  have huVec : ContDiff ℝ (⊤ : ℕ∞) u := by
    rw [contDiff_pi]
    exact hu
  have hq : ContDiff ℝ (⊤ : ℕ∞) (velocitySq u) := by
    unfold velocitySq
    fun_prop
  have hq1 : ContDiff ℝ (1 : ℕ∞) (velocitySq u) := hq.of_le (by norm_num)
  have hψ1 : ContDiff ℝ (1 : ℕ∞) ψ := hψ.of_le (by norm_num)
  let T : Vec3 × ℝ → ℝ := fun z => velocitySq u z * ψ z
  have hT1 : ContDiff ℝ (1 : ℕ∞) T := by
    dsimp [T]
    exact hq1.mul hψ1
  have hTc : HasCompactSupport T := by
    dsimp [T]
    exact hψc.mul_left
  have hflux1 (j : Fin 3) : ContDiff ℝ (1 : ℕ∞)
      (fun z => ψ z * velocitySq u z * u z j) := by
    have hu1 (i : Fin 3) : ContDiff ℝ (1 : ℕ∞) (fun z => u z i) :=
      (hu i).of_le (by norm_num)
    fun_prop
  have hfluxc (j : Fin 3) : HasCompactSupport
      (fun z => ψ z * velocitySq u z * u z j) := by
    have hc : HasCompactSupport
        (fun z => (velocitySq u z * u z j) * ψ z) := hψc.mul_left
    convert hc using 1
    ext z
    ring_nf
  have hvisc1 (j : Fin 3) : ContDiff ℝ (1 : ℕ∞)
      (fun z => velocitySq u z * dirDeriv ψ (spatialDir j) z) := by
    exact hq1.mul (dirDeriv_contDiff_one hψ (spatialDir j))
  have hviscc (j : Fin 3) : HasCompactSupport
      (fun z => velocitySq u z * dirDeriv ψ (spatialDir j) z) := by
    have hψDc : HasCompactSupport (fun z => dirDeriv ψ (spatialDir j) z) := by
      simpa [dirDeriv] using hψc.fderiv_apply (𝕜 := ℝ) (spatialDir j)
    exact hψDc.mul_left
  have hTderivC : HasCompactSupport (fun z => dirDeriv T timeDir z) := by
    have h := hTc.fderiv_apply (𝕜 := ℝ) timeDir
    simpa [dirDeriv] using h
  have hTderivInt : Integrable (fun z => dirDeriv T timeDir z)
      (volume : Measure (Vec3 × ℝ)) :=
    (smoothDirectionalDerivative_continuous hT1 timeDir).integrable_of_hasCompactSupport hTderivC
  have hfluxderivC (j : Fin 3) : HasCompactSupport
      (fun z => dirDeriv (fun y => ψ y * velocitySq u y * u y j)
        (spatialDir j) z) := by
    have h := (hfluxc j).fderiv_apply (𝕜 := ℝ) (spatialDir j)
    simpa [dirDeriv] using h
  have hfluxderivInt (j : Fin 3) : Integrable
      (fun z => dirDeriv (fun y => ψ y * velocitySq u y * u y j)
        (spatialDir j) z) (volume : Measure (Vec3 × ℝ)) :=
    have hcont := smoothDirectionalDerivative_continuous (hflux1 j) (spatialDir j)
    hcont.integrable_of_hasCompactSupport (hfluxderivC j)
  have hviscderivC (j : Fin 3) : HasCompactSupport
      (fun z => dirDeriv (fun y => velocitySq u y * dirDeriv ψ (spatialDir j) y)
        (spatialDir j) z) := by
    have h := (hviscc j).fderiv_apply (𝕜 := ℝ) (spatialDir j)
    simpa [dirDeriv] using h
  have hviscderivInt (j : Fin 3) : Integrable
      (fun z => dirDeriv (fun y => velocitySq u y * dirDeriv ψ (spatialDir j) y)
        (spatialDir j) z) (volume : Measure (Vec3 × ℝ)) :=
    have hcont := smoothDirectionalDerivative_continuous (hvisc1 j) (spatialDir j)
    hcont.integrable_of_hasCompactSupport (hviscderivC j)
  have hfluxSumInt : Integrable
      (fun z => ∑ j : Fin 3,
        dirDeriv (fun y => ψ y * velocitySq u y * u y j) (spatialDir j) z)
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum
    intro j hj
    exact hfluxderivInt j
  have hviscSumInt : Integrable
      (fun z => ∑ j : Fin 3,
        dirDeriv (fun y => velocitySq u y * dirDeriv ψ (spatialDir j) y)
          (spatialDir j) z) (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum
    intro j hj
    exact hviscderivInt j
  have htimeNegInt : Integrable (fun z => -dirDeriv T timeDir z)
      (volume : Measure (Vec3 × ℝ)) := hTderivInt.neg
  have htotalInt : Integrable (smoothEnergyTotalDerivative u ψ)
      (volume : Measure (Vec3 × ℝ)) := by
    exact (htimeNegInt.sub hfluxSumInt).add hviscSumInt
  have htimeZero : ∫ z, dirDeriv T timeDir z
      ∂(volume : Measure (Vec3 × ℝ)) = 0 :=
    smoothIntegral_dirDeriv_eq_zero hT1 hTc timeDir
  have hfluxZero : ∑ j : Fin 3, ∫ z,
      dirDeriv (fun y => ψ y * velocitySq u y * u y j) (spatialDir j) z
      ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact smoothIntegral_dirDeriv_eq_zero (hflux1 j) (hfluxc j) (spatialDir j)
  have hviscZero : ∑ j : Fin 3, ∫ z,
      dirDeriv (fun y => velocitySq u y * dirDeriv ψ (spatialDir j) y)
        (spatialDir j) z ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact smoothIntegral_dirDeriv_eq_zero (hvisc1 j) (hviscc j) (spatialDir j)
  have htotalZero : ∫ z, smoothEnergyTotalDerivative u ψ z
      ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    let A : Vec3 × ℝ → ℝ := fun z => -dirDeriv T timeDir z
    let B : Vec3 × ℝ → ℝ := fun z =>
      ∑ j : Fin 3, dirDeriv (fun y => ψ y * velocitySq u y * u y j)
        (spatialDir j) z
    let C : Vec3 × ℝ → ℝ := fun z =>
      ∑ j : Fin 3, dirDeriv (fun y => velocitySq u y * dirDeriv ψ (spatialDir j) y)
        (spatialDir j) z
    have hadd : (∫ z, ((A - B) z) + C z
        ∂(volume : Measure (Vec3 × ℝ))) =
        (∫ z, (A - B) z ∂(volume : Measure (Vec3 × ℝ))) +
          ∫ z, C z ∂(volume : Measure (Vec3 × ℝ)) :=
      integral_add (htimeNegInt.sub hfluxSumInt) hviscSumInt
    have hsub : (∫ z, (A - B) z ∂(volume : Measure (Vec3 × ℝ))) =
        (∫ z, A z ∂(volume : Measure (Vec3 × ℝ))) -
          ∫ z, B z ∂(volume : Measure (Vec3 × ℝ)) :=
      integral_sub htimeNegInt hfluxSumInt
    have hB : (∫ z, B z ∂(volume : Measure (Vec3 × ℝ))) =
        ∑ j : Fin 3, ∫ z,
          dirDeriv (fun y => ψ y * velocitySq u y * u y j) (spatialDir j) z
          ∂(volume : Measure (Vec3 × ℝ)) := by
      dsimp [B]
      exact integral_finsetSum Finset.univ (fun j hj => hfluxderivInt j)
    have hC : (∫ z, C z ∂(volume : Measure (Vec3 × ℝ))) =
        ∑ j : Fin 3, ∫ z,
          dirDeriv (fun y => velocitySq u y * dirDeriv ψ (spatialDir j) y)
            (spatialDir j) z ∂(volume : Measure (Vec3 × ℝ)) := by
      dsimp [C]
      exact integral_finsetSum Finset.univ (fun j hj => hviscderivInt j)
    calc
      _ = (∫ z, ((A - B) z) + C z ∂(volume : Measure (Vec3 × ℝ))) := by
        rfl
      _ = (∫ z, (A - B) z ∂(volume : Measure (Vec3 × ℝ))) +
          ∫ z, C z ∂(volume : Measure (Vec3 × ℝ)) := hadd
      _ = ((∫ z, A z ∂(volume : Measure (Vec3 × ℝ))) -
          ∫ z, B z ∂(volume : Measure (Vec3 × ℝ))) +
          ∫ z, C z ∂(volume : Measure (Vec3 × ℝ)) := by
        rw [hsub]
      _ = 0 := by
        rw [hB, hC, integral_neg, htimeZero, hfluxZero, hviscZero]
        simp
  exact ⟨htotalInt, htotalZero⟩

/-- Integrating the smooth energy test density removes its total derivative terms. -/
theorem smoothEnergyTestIntegrand_integral_eq_base
    {u : Vec3 × ℝ → Vec3} {R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {p ψ : Vec3 × ℝ → ℝ}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => u z i))
    (hR : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => R z i j))
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => G z i j))
    (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hgrad : ∀ z ∈ tsupport ψ, ∀ i j : Fin 3,
      dirDeriv (fun y => u y i) (spatialDir j) z = G z i j)
    (hdiv : ∀ z ∈ tsupport ψ, ∑ i : Fin 3, G z i i = 0) :
    ∫ z, smoothEnergyTestIntegrand u R G p ψ z
        ∂(volume : Measure (Vec3 × ℝ)) =
      ∫ z, smoothEnergyBaseIntegrand u R G p ψ z
        ∂(volume : Measure (Vec3 × ℝ)) := by
  have ⟨htotalInt, htotalZero⟩ :=
    smoothEnergyTotalDerivative_integrable_integral_zero hu hψ hψc
  have ⟨hbasezero, htestzero, htotalzero⟩ :=
    smoothEnergyIntegrands_vanish_off_test_support
      (u := u) (R := R) (G := G) (p := p) (ψ := ψ)
  have hbaseC : HasCompactSupport (smoothEnergyBaseIntegrand u R G p ψ) := by
    apply HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    intro z hz
    by_contra hnot
    exact hz (by simpa [Function.mem_support] using hbasezero z hnot)
  have hψSecondCont (j : Fin 3) : Continuous
      (fun z => dirDeriv (fun y => dirDeriv ψ (spatialDir j) y)
        (spatialDir j) z) := by
    have hfirst : ContDiff ℝ (1 : ℕ∞)
        (fun y => dirDeriv ψ (spatialDir j) y) := dirDeriv_contDiff_one hψ (spatialDir j)
    exact (hfirst.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hbaseCont : Continuous (smoothEnergyBaseIntegrand u R G p ψ) := by
    have huCont (i : Fin 3) : Continuous (fun z => u z i) :=
      (hu i).continuous
    have huVec : Continuous u := by
      exact continuous_pi (fun i => huCont i)
    have hvelocitySqCont : Continuous (velocitySq u) := by
      unfold velocitySq
      fun_prop
    have htimeCont : Continuous (fun z => dirDeriv ψ timeDir z) :=
      (dirDeriv_contDiff_one hψ timeDir).continuous
    have hspaceCont (j : Fin 3) : Continuous (fun z => dirDeriv ψ (spatialDir j) z) :=
      (dirDeriv_contDiff_one hψ (spatialDir j)).continuous
    unfold smoothEnergyBaseIntegrand
    fun_prop
  have hbaseInt : Integrable (smoothEnergyBaseIntegrand u R G p ψ)
      (volume : Measure (Vec3 × ℝ)) := hbaseCont.integrable_of_hasCompactSupport hbaseC
  have hEqGlobal (z : Vec3 × ℝ) :
      smoothEnergyTestIntegrand u R G p ψ z =
        smoothEnergyBaseIntegrand u R G p ψ z + smoothEnergyTotalDerivative u ψ z := by
    by_cases hz : z ∈ tsupport ψ
    · exact smoothEnergyTestIntegrand_eq_base_add_totalDerivative
        hu hψ hgrad hdiv z hz
    · rw [htestzero z hz, hbasezero z hz, htotalzero z hz]
      ring_nf
  have henergyInt : Integrable (smoothEnergyTestIntegrand u R G p ψ)
      (volume : Measure (Vec3 × ℝ)) := by
    have hsum : Integrable
        (fun z => smoothEnergyBaseIntegrand u R G p ψ z +
          smoothEnergyTotalDerivative u ψ z) (volume : Measure (Vec3 × ℝ)) :=
      hbaseInt.add htotalInt
    refine hsum.congr (Filter.Eventually.of_forall fun z => ?_)
    exact (hEqGlobal z).symm
  calc
    _ = ∫ z, smoothEnergyBaseIntegrand u R G p ψ z +
          smoothEnergyTotalDerivative u ψ z ∂(volume : Measure (Vec3 × ℝ)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hEqGlobal z
    _ = (∫ z, smoothEnergyBaseIntegrand u R G p ψ z
          ∂(volume : Measure (Vec3 × ℝ))) +
        ∫ z, smoothEnergyTotalDerivative u ψ z ∂(volume : Measure (Vec3 × ℝ)) :=
      integral_add hbaseInt htotalInt
    _ = _ := by rw [htotalZero]; simp

end ESS

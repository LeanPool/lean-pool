/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CompactTestCutoffEstimate

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.CompactTestDensity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Compactly supported fractional test fields

Smooth vector fields compactly supported in an open triadic cube are dense in
the normalized fractional square norm below order one half.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open CompactTestDensity
open scoped ENNReal

noncomputable section

private theorem openCubeSet_subset_scaledClosedCubeSet_one
    {d : ℕ} (Q : TriadicCube d) :
    openCubeSet Q ⊆ scaledClosedCubeSet Q 1 := by
  intro x hx i
  rw [← ball_cubeCenter_eq_openCubeSet Q] at hx
  have hcoord : |x i - cubeCenter Q i| ≤ ‖x - cubeCenter Q‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (x - cubeCenter Q) i
  have hrad : ‖x - cubeCenter Q‖ < cubeRadius Q := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  calc
    |x i - cubeCenter Q i| ≤ ‖x - cubeCenter Q‖ := hcoord
    _ ≤ cubeRadius Q := hrad.le
    _ = 1 * cubeRadius Q := (one_mul _).symm

private theorem hsNormSq_congr_of_eqOn
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (s : ℝ) {F G : Vec d → Vec d} (hFG : Set.EqOn F G U) :
    hsNormSq U s F = hsNormSq U s G := by
  have hL2 :
      eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (F x))) =
        eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (G x))) := by
    unfold eVolumeAverage
    congr 1
    apply setLIntegral_congr_fun hU
    intro x hx
    change ENNReal.ofReal (vecNormSq (F x)) =
      ENNReal.ofReal (vecNormSq (G x))
    rw [hFG hx]
  have hFrac : fracSeminormSq U s F = fracSeminormSq U s G := by
    unfold fracSeminormSq eVolumeAverage
    congr 1
    apply setLIntegral_congr_fun hU
    intro x hx
    apply setLIntegral_congr_fun hU
    intro y hy
    change ENNReal.ofReal
        (vecNormSq (F x - F y) /
          Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) =
      ENNReal.ofReal
        (vecNormSq (G x - G y) /
          Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s))
    rw [hFG hx, hFG hy]
  unfold hsNormSq
  rw [hL2, hFrac]

/-- A globally smooth field on a cube can be approximated in the normalized
fractional square norm by globally smooth fields compactly supported in the
open cube whenever the fractional order is below one half. -/
theorem exists_localVecTest_hsNormSq_sub_lt_smooth_of_lt_half
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (h : Vec d → Vec d) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) h)
    {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∃ psi : Vec d → Vec d,
      IsLocalVecTest (openCubeSet Q) psi ∧
        hsNormSq (openCubeSet Q) s (fun x => psi x - h x) < epsilon := by
  let χ : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun Q 1 2
  let h₀ : Vec d → Vec d := fun x => χ x • h x
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ :=
    QuantitativeCubeCutoff.canonicalFun_smooth Q (by norm_num) (by norm_num)
  have hχcompact : HasCompactSupport χ :=
    QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q
      (by norm_num) (by norm_num)
  have h₀smooth : ContDiff ℝ (⊤ : ℕ∞) h₀ := hχsmooth.smul hsmooth
  have h₀compact : HasCompactSupport h₀ := hχcompact.smul_right
  have h₀eq : Set.EqOn h₀ h (openCubeSet Q) := by
    intro x hx
    have hχeq : χ x = 1 :=
      QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner
        (by norm_num) (by norm_num)
        (openCubeSet_subset_scaledClosedCubeSet_one Q hx)
    dsimp only [h₀]
    rw [hχeq, one_smul]
  obtain ⟨M, hM, h₀bound⟩ :=
    exists_norm_bound_of_hasCompactSupport h₀smooth.continuous h₀compact
  obtain ⟨L₀, hL₀, h₀lip⟩ :=
    exists_lipschitz_of_hasCompactSupport h₀smooth h₀compact
  let theta : ℝ := (s + 1 / 2) / 2
  have hstheta : s < theta := by
    dsimp only [theta]
    linarith only [hsHalf]
  have hthetaHalf : theta < 1 / 2 := by
    dsimp only [theta]
    linarith only [hsHalf]
  have htheta0 : 0 < theta := hs.trans hstheta
  let e : ℝ := 2 * theta - (d : ℝ) - 2 * s
  have hed : -(d : ℝ) < e := by
    dsimp only [e]
    linarith only [hstheta]
  have hdNat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast hdNat
  have he0 : e < 0 := by
    dsimp only [e]
    linarith only [hthetaHalf, hs.le, hd]
  obtain ⟨C, hCtop, hC⟩ := exists_bound_lintegral_ball_rpow_scaled d hed he0
  let D : ℝ := (d : ℝ) * smoothTransitionProfile.derivBound * 2 / cubeRadius Q
  let B : ℝ := L₀ + M * D + 1
  let Kvol : ℝ := 2 * (d : ℝ) * cubeVolume Q
  let K₀ : ℝ := (((2 * Real.sqrt d * M) ^ (1 - theta) *
    (Real.sqrt d * B) ^ theta) ^ 2)
  let p : ℝ := 1 - 2 * theta
  let Rpow : ℝ≥0∞ := ENNReal.ofReal
    ((2 * cubeRadius Q) ^
      ((2 * theta - (d : ℝ) - 2 * s) + (d : ℝ)))
  let CL2 : ℝ≥0∞ :=
    volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ)) *
      ((ENNReal.ofReal ((d : ℝ) * M ^ 2) * ENNReal.ofReal Kvol) /
        volume (openCubeSet Q))
  let Cfrac : ℝ≥0∞ :=
    2 * ((ENNReal.ofReal K₀ * ENNReal.ofReal Kvol * C * Rpow) /
      volume (openCubeSet Q))
  have hp : 0 < p := by
    dsimp only [p]
    linarith only [hthetaHalf]
  have hvolEq : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top Q).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg Q)])
  have hvol0 : volume (openCubeSet Q) ≠ 0 := by
    rw [hvolEq]
    exact (ENNReal.ofReal_pos.mpr (cubeVolume_pos Q)).ne'
  have hvoltop : volume (openCubeSet Q) ≠ ⊤ :=
    (volume_openCubeSet_lt_top Q).ne
  have hweightTop :
      volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hvol0 hvoltop
  have hCL2top : CL2 ≠ ⊤ := by
    dsimp only [CL2]
    exact ENNReal.mul_ne_top hweightTop
      (ENNReal.div_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hvol0)
  have hCfracTop : Cfrac ≠ ⊤ := by
    dsimp only [Cfrac, Rpow]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.div_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
              hCtop) ENNReal.ofReal_ne_top) hvol0)
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have htend : Filter.Tendsto t Filter.atTop (nhds 0) := by
    simpa only [t] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (nhds 0))
  have htendE : Filter.Tendsto (fun n => ENNReal.ofReal (t n))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal htend
  have hlin : Filter.Tendsto
      (fun n => CL2 * ENNReal.ofReal (t n)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul htendE (Or.inr hCL2top)
  have hpow : Filter.Tendsto
      (fun n => Cfrac * (ENNReal.ofReal (t n)) ^ p)
      Filter.atTop (nhds 0) := by
    exact (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hCfracTop hp).comp htendE
  have hrhs : Filter.Tendsto
      (fun n => CL2 * ENNReal.ofReal (t n) +
        Cfrac * (ENNReal.ofReal (t n)) ^ p)
      Filter.atTop (nhds 0) := by
    simpa using hlin.add hpow
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      CL2 * ENNReal.ofReal (t n) +
        Cfrac * (ENNReal.ofReal (t n)) ^ p < epsilon :=
    hrhs.eventually_lt_const hepsilon
  have hnlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  rcases (hsmall.and hnlarge).exists with ⟨n, hnsmall, hn⟩
  have htpos : 0 < t n := by
    dsimp only [t]
    positivity
  have hden : (2 : ℝ) < (n : ℝ) + 1 := by
    have hn' : 3 ≤ n + 1 := Nat.succ_le_succ hn
    have hnReal : (3 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hn'
    linarith only [hnReal]
  have hthalf : t n < 1 / 2 := by
    dsimp only [t]
    exact one_div_lt_one_div_of_lt (by norm_num) hden
  let eta : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 - 2 * t n) (1 - t n)
  let psi : Vec d → Vec d := fun x => eta x • h₀ x
  have hρ₁ : 0 < 1 - 2 * t n := by linarith only [hthalf]
  have hρ₁₂ : 1 - 2 * t n < 1 - t n := by linarith only [htpos]
  have hρ₂ : 1 - t n < 1 := by linarith only [htpos]
  have hetasmooth : ContDiff ℝ (⊤ : ℕ∞) eta :=
    QuantitativeCubeCutoff.canonicalFun_smooth Q hρ₁ hρ₁₂
  have hetacompact : HasCompactSupport eta :=
    QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q hρ₁ hρ₁₂
  have hetasupport : tsupport eta ⊆ openCubeSet Q :=
    quantitativeCubeCutoff_canonicalFun_tsupport_subset_openCubeSet
      Q hρ₁ hρ₁₂ hρ₂
  have hpsisupport : tsupport psi ⊆ tsupport eta := by
    apply closure_minimal
    · intro x hx
      exact subset_closure (by
        intro heta0
        apply hx
        simp [psi, heta0])
    · exact isClosed_tsupport eta
  have hpsi : IsLocalVecTest (openCubeSet Q) psi :=
    { contDiff := hetasmooth.smul h₀smooth
      hasCompactSupport := hetacompact.smul_right
      tsupport_subset := hpsisupport.trans hetasupport }
  have hbound := hsNormSq_canonicalCutoff_sub_le Q hs.le hstheta hthetaHalf
    hM hL₀ h₀ h₀smooth h₀bound h₀lip hC htpos hthalf
  have herrEq : Set.EqOn (fun x => psi x - h x)
      (fun x => eta x • h₀ x - h₀ x) (openCubeSet Q) := by
    intro x hx
    change psi x - h x = eta x • h₀ x - h₀ x
    dsimp only [psi]
    rw [h₀eq hx]
  have hnormEq := hsNormSq_congr_of_eqOn (measurableSet_openCubeSet Q) s herrEq
  have hbound' :
      hsNormSq (openCubeSet Q) s (fun x => eta x • h₀ x - h₀ x) ≤
        CL2 * ENNReal.ofReal (t n) +
          Cfrac * ENNReal.ofReal (t n) ^ p := by
    simpa only [eta, D, B, Kvol, K₀, p, Rpow, CL2, Cfrac, t] using hbound
  refine ⟨psi, hpsi, ?_⟩
  rw [hnormEq]
  exact hbound'.trans_lt (by simpa only [CL2, Cfrac] using hnsmall)

end

end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CompactTestCutoffKernel

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.CompactTestCutoffEstimate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quantitative compact cutoff estimate

The canonical cube cutoff has a vanishing boundary-layer error in the
normalized fractional square norm below the trace threshold.
-/

namespace HCPolySupport
namespace HighContrast
namespace CompactTestDensity

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem volume_cubeBoundaryLayer_le_linear
    {d : ℕ} (Q : TriadicCube d) {t : ℝ}
    (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    volume (cubeBoundaryLayer Q t) ≤
      ENNReal.ofReal (2 * (d : ℝ) * cubeVolume Q * t) := by
  have htOne : t ≤ 1 := htHalf.trans (by norm_num)
  have hbern : 1 + (d : ℝ) * (-2 * t) ≤ (1 + (-2 * t)) ^ d := by
    exact one_add_mul_le_pow (by linarith only [htOne]) d
  have hbern' : 1 - 2 * (d : ℝ) * t ≤ (1 - 2 * t) ^ d := by
    convert hbern using 1 <;> ring
  have hreal :
      cubeVolume Q - ((1 - 2 * t) * cubeScaleFactor Q) ^ d ≤
        2 * (d : ℝ) * cubeVolume Q * t := by
    rw [mul_pow, show cubeVolume Q = cubeScaleFactor Q ^ d by rfl]
    have hscale : 0 ≤ cubeScaleFactor Q ^ d := (pow_nonneg (cubeScaleFactor_nonneg Q) d)
    have hsub : 1 - (1 - 2 * t) ^ d ≤ 2 * (d : ℝ) * t := by
      linarith only [hbern']
    calc
      cubeScaleFactor Q ^ d - (1 - 2 * t) ^ d * cubeScaleFactor Q ^ d =
          (1 - (1 - 2 * t) ^ d) * cubeScaleFactor Q ^ d := by ring
      _ ≤ (2 * (d : ℝ) * t) * cubeScaleFactor Q ^ d :=
        mul_le_mul_of_nonneg_right hsub hscale
      _ = 2 * (d : ℝ) * cubeScaleFactor Q ^ d * t := by ring
  have hright : 0 ≤ 2 * (d : ℝ) * cubeVolume Q * t :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
        (cubeVolume_nonneg Q)) ht0
  apply (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top_of_subset
      (cubeBoundaryLayer_subset_cubeSet Q t) (volume_cubeSet_lt_top Q).ne)
    ENNReal.ofReal_ne_top).mp
  rw [volume_cubeBoundaryLayer_toReal_of_nonneg_le_half Q ht0 htHalf,
    ENNReal.toReal_ofReal hright]
  exact hreal

private theorem eVolumeAverage_vecNormSq_le_supported_bound
    {d : ℕ} {U A : Set (Vec d)} (hUmeas : MeasurableSet U)
    (hAmeas : MeasurableSet A) (hAU : A ⊆ U)
    {g : Vec d → Vec d} {V : ℝ}
    (hbound : ∀ x ∈ U, vecNormSq (g x) ≤ V)
    (hzero : ∀ x ∈ U, x ∉ A → g x = 0) :
    eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (g x))) ≤
      (ENNReal.ofReal V * volume A) / volume U := by
  let f : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (vecNormSq (g x))
  have hpoint (x : Vec d) (hx : x ∈ U) :
      f x ≤ A.indicator (fun _ => ENNReal.ofReal V) x := by
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      exact ENNReal.ofReal_le_ofReal (hbound x hx)
    · rw [Set.indicator_of_notMem hxA]
      dsimp only [f]
      rw [hzero x hx hxA]
      simp [vecNormSq, vecDot]
  unfold eVolumeAverage
  apply ENNReal.div_le_div_right
  calc
    (∫⁻ x in U, f x ∂volume) ≤
        ∫⁻ x in U, A.indicator (fun _ => ENNReal.ofReal V) x ∂volume :=
      setLIntegral_mono' hUmeas hpoint
    _ = ∫⁻ x in A, ENNReal.ofReal V ∂volume := by
      rw [setLIntegral_indicator hAmeas, Set.inter_eq_left.mpr hAU]
    _ = ENNReal.ofReal V * volume A := setLIntegral_const A _

private theorem rpow_div_sq_mul_eq
    {a b t theta : ℝ} (hb : 0 ≤ b) (ht : 0 < t) :
    (a ^ (1 - theta) * (b / t) ^ theta) ^ 2 * t =
      (a ^ (1 - theta) * b ^ theta) ^ 2 *
        t ^ (1 - 2 * theta) := by
  have ht0 : 0 ≤ t := ht.le
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0
  have hdivpow : (b / t) ^ theta = b ^ theta * t ^ (-theta) := by
    rw [div_eq_mul_inv, Real.mul_rpow hb htinv, Real.inv_rpow ht0,
      ← Real.rpow_neg ht0]
  have hpow : (t ^ (-theta)) ^ (2 : ℕ) = t ^ (-2 * theta) := by
    calc
      (t ^ (-theta)) ^ (2 : ℕ) = (t ^ (-theta)) ^ (2 : ℝ) :=
        (Real.rpow_natCast (t ^ (-theta)) 2).symm
      _ = t ^ ((-theta) * 2) := (Real.rpow_mul ht0 (-theta) 2).symm
      _ = t ^ (-2 * theta) := by congr 1; ring
  have hcombine : t ^ (-2 * theta) * t = t ^ (1 - 2 * theta) := by
    calc
      t ^ (-2 * theta) * t = t ^ (-2 * theta) * t ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = t ^ ((-2 * theta) + 1) := (Real.rpow_add ht _ _).symm
      _ = t ^ (1 - 2 * theta) := by congr 1; ring
  rw [hdivpow, mul_pow, mul_pow, hpow]
  calc
    (a ^ (1 - theta)) ^ 2 * ((b ^ theta) ^ 2 * t ^ (-2 * theta)) * t =
        (a ^ (1 - theta) * b ^ theta) ^ 2 *
          (t ^ (-2 * theta) * t) := by ring
    _ = (a ^ (1 - theta) * b ^ theta) ^ 2 *
        t ^ (1 - 2 * theta) := by rw [hcombine]

private theorem cubeShrunkSet_subset_scaledClosedCubeSet
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) :
    cubeShrunkSet Q t ⊆ scaledClosedCubeSet Q (1 - 2 * t) := by
  intro x hx i
  have hi := hx i
  rw [abs_le]
  constructor
  · dsimp [cubeCenter, cubeRadius] at hi ⊢
    have hscale : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    linarith only [hi.1, hscale]
  · dsimp [cubeCenter, cubeRadius] at hi ⊢
    have hscale : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    linarith only [hi.2, hscale]

/-- The canonical cube cutoff converges in the fractional square norm below order one half. -/
theorem hsNormSq_canonicalCutoff_sub_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s theta M L₀ : ℝ}
    (hs : 0 ≤ s) (hstheta : s < theta) (hthetaHalf : theta < 1 / 2)
    (hM : 0 ≤ M) (hL₀ : 0 ≤ L₀)
    (h₀ : Vec d → Vec d) (h₀smooth : ContDiff ℝ (⊤ : ℕ∞) h₀)
    (h₀bound : ∀ x, ‖h₀ x‖ ≤ M)
    (h₀lip : ∀ x y, ‖h₀ x - h₀ y‖ ≤ L₀ * ‖x - y‖)
    {C : ℝ≥0∞}
    (hC : ∀ (x : Vec d) {r : ℝ}, 0 < r →
      (∫⁻ y in Metric.ball x r,
        ENNReal.ofReal
          (‖x - y‖ ^ (2 * theta - (d : ℝ) - 2 * s)) ∂volume) ≤
        C * ENNReal.ofReal
          (r ^ ((2 * theta - (d : ℝ) - 2 * s) + (d : ℝ))))
    {t : ℝ} (ht : 0 < t) (htHalf : t < 1 / 2) :
    let η := QuantitativeCubeCutoff.canonicalFun Q (1 - 2 * t) (1 - t)
    let D := (d : ℝ) * smoothTransitionProfile.derivBound * 2 / cubeRadius Q
    let B := L₀ + M * D + 1
    let Kvol := 2 * (d : ℝ) * cubeVolume Q
    let K₀ :=
      (((2 * Real.sqrt d * M) ^ (1 - theta) *
        (Real.sqrt d * B) ^ theta) ^ 2)
    let p := 1 - 2 * theta
    hsNormSq (openCubeSet Q) s (fun x => η x • h₀ x - h₀ x) ≤
      (volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ)) *
          ((ENNReal.ofReal ((d : ℝ) * M ^ 2) * ENNReal.ofReal Kvol) /
            volume (openCubeSet Q))) * ENNReal.ofReal t +
        (2 * ((ENNReal.ofReal K₀ * ENNReal.ofReal Kvol * C *
          ENNReal.ofReal
            ((2 * cubeRadius Q) ^
              ((2 * theta - (d : ℝ) - 2 * s) + (d : ℝ)))) /
          volume (openCubeSet Q))) * (ENNReal.ofReal t) ^ p := by
  let U : Set (Vec d) := openCubeSet Q
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 - 2 * t) (1 - t)
  let g : Vec d → Vec d := fun x => η x • h₀ x - h₀ x
  let A : Set (Vec d) := cubeBoundaryLayer Q t ∩ U
  let D : ℝ := (d : ℝ) * smoothTransitionProfile.derivBound * 2 / cubeRadius Q
  let B : ℝ := L₀ + M * D + 1
  let L : ℝ := B / t
  let Kvol : ℝ := 2 * (d : ℝ) * cubeVolume Q
  let K₀ : ℝ := (((2 * Real.sqrt d * M) ^ (1 - theta) *
    (Real.sqrt d * B) ^ theta) ^ 2)
  let p : ℝ := 1 - 2 * theta
  have ht0 : 0 ≤ t := ht.le
  have htOne : t ≤ 1 := (lt_trans htHalf (by norm_num)).le
  have hρ₁ : 0 < 1 - 2 * t := by linarith only [htHalf]
  have hρ₁₂ : 1 - 2 * t < 1 - t := by linarith only [ht]
  have hρ₂ : 1 - t < 1 := by linarith only [ht]
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η :=
    QuantitativeCubeCutoff.canonicalFun_smooth Q hρ₁ hρ₁₂
  have hηnonneg (x : Vec d) : 0 ≤ η x :=
    QuantitativeCubeCutoff.canonicalFun_nonneg Q (1 - 2 * t) (1 - t) x
  have hηone (x : Vec d) : η x ≤ 1 :=
    QuantitativeCubeCutoff.canonicalFun_le_one Q (1 - 2 * t) (1 - t) x
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg d)
          smoothTransitionProfile.derivBound_nonneg) (by norm_num))
      (cubeRadius_nonneg Q)
  have hB : 0 < B := by
    dsimp only [B]
    have hMD : 0 ≤ M * D := mul_nonneg hM hD
    linarith only [hL₀, hMD]
  have hL : 0 ≤ L := div_nonneg hB.le ht.le
  have hηgrad (x : Vec d) : ‖fderiv ℝ η x‖ ≤ D / t := by
    have hbase := QuantitativeCubeCutoff.canonicalFun_gradient_bound Q hρ₁ hρ₁₂ x
    have hradius : cubeRadius Q ≠ 0 := (cubeRadius_pos Q).ne'
    have hgap : (1 - t) - (1 - 2 * t) = t := by ring
    dsimp only [η] at hbase ⊢
    rw [hgap] at hbase
    calc
      ‖fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q (1 - 2 * t) (1 - t)) x‖ ≤
          (d : ℝ) * smoothTransitionProfile.derivBound *
            (2 / (t * cubeRadius Q)) := hbase
      _ = ((d : ℝ) * smoothTransitionProfile.derivBound * 2 /
          cubeRadius Q) / t := by
        field_simp [ht.ne', hradius]
  have hηlip : ∀ x y, |η x - η y| ≤ (D / t) * ‖x - y‖ := by
    have hDt : 0 ≤ D / t := div_nonneg hD ht.le
    have hlip : LipschitzWith (D / t).toNNReal η := by
      refine lipschitzWith_of_nnnorm_fderiv_le
        (hηsmooth.differentiable (by simp)) ?_
      intro x
      exact (Real.le_toNNReal_iff_coe_le hDt).mpr (by
        simpa using hηgrad x)
    intro x y
    have hxy := hlip.norm_sub_le x y
    simpa only [Real.norm_eq_abs, Real.coe_toNNReal (D / t) hDt] using hxy
  have hgbound (x : Vec d) : ‖g x‖ ≤ M := by
    have heta : |η x - 1| ≤ 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hηone x))]
      linarith only [hηnonneg x]
    have heq : g x = (η x - 1) • h₀ x := by
      dsimp only [g]
      module
    rw [heq, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul heta (h₀bound x) (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul M)
  have hglip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖ := by
    intro x y
    have heta : |η x - 1| ≤ 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hηone x))]
      linarith only [hηnonneg x]
    have hdecomp : g x - g y =
        (η x - 1) • (h₀ x - h₀ y) + (η x - η y) • h₀ y := by
      dsimp only [g]
      module
    have hfirst : ‖(η x - 1) • (h₀ x - h₀ y)‖ ≤
        L₀ * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |η x - 1| * ‖h₀ x - h₀ y‖ ≤
            1 * (L₀ * ‖x - y‖) :=
          mul_le_mul heta (h₀lip x y) (norm_nonneg _) (by norm_num)
        _ = L₀ * ‖x - y‖ := one_mul _
    have hsecond : ‖(η x - η y) • h₀ y‖ ≤
        (D / t * M) * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |η x - η y| * ‖h₀ y‖ ≤
            ((D / t) * ‖x - y‖) * M :=
          mul_le_mul (hηlip x y) (h₀bound y) (norm_nonneg _)
            (mul_nonneg (div_nonneg hD ht.le) (norm_nonneg _))
        _ = (D / t * M) * ‖x - y‖ := by ring
    have hcoef : L₀ + D / t * M ≤ L := by
      apply (le_div_iff₀ ht).2
      have hL₀t : L₀ * t ≤ L₀ :=
        mul_le_of_le_one_right hL₀ htOne
      dsimp only [L, B]
      rw [add_mul]
      field_simp [ht.ne']
      linarith only [hL₀t, hM, hD]
    rw [hdecomp]
    calc
      ‖(η x - 1) • (h₀ x - h₀ y) + (η x - η y) • h₀ y‖ ≤
          ‖(η x - 1) • (h₀ x - h₀ y)‖ +
            ‖(η x - η y) • h₀ y‖ := norm_add_le _ _
      _ ≤ L₀ * ‖x - y‖ + (D / t * M) * ‖x - y‖ :=
        add_le_add hfirst hsecond
      _ = (L₀ + D / t * M) * ‖x - y‖ := by ring
      _ ≤ L * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hAU : A ⊆ U := Set.inter_subset_right
  have hzero : ∀ x ∈ U, x ∉ A → g x = 0 := by
    intro x hxU hxA
    have hxCube : x ∈ cubeSet Q := openCubeSet_subset_cubeSet Q hxU
    have hxLayer : x ∉ cubeBoundaryLayer Q t := by
      intro hx
      exact hxA ⟨hx, hxU⟩
    have hxShrunk : x ∈ cubeShrunkSet Q t := by
      by_contra hnot
      exact hxLayer ⟨hxCube, hnot⟩
    have hηeq : η x = 1 :=
      QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner hρ₁ hρ₁₂
        (cubeShrunkSet_subset_scaledClosedCubeSet Q t hxShrunk)
    dsimp only [g]
    rw [hηeq, one_smul, sub_self]
  have hAmeas : MeasurableSet A :=
    (measurableSet_cubeBoundaryLayer Q t).inter (measurableSet_openCubeSet Q)
  have hAvolume : volume A ≤ ENNReal.ofReal (Kvol * t) := by
    calc
      volume A ≤ volume (cubeBoundaryLayer Q t) :=
        measure_mono Set.inter_subset_left
      _ ≤ ENNReal.ofReal (2 * (d : ℝ) * cubeVolume Q * t) :=
        volume_cubeBoundaryLayer_le_linear Q ht0 htHalf.le
      _ = ENNReal.ofReal (Kvol * t) := by rfl
  have hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact hηsmooth.smul h₀smooth |>.sub h₀smooth
  have hdimM : ∀ x ∈ U, vecNormSq (g x) ≤ (d : ℝ) * M ^ 2 := by
    intro x _hx
    calc
      vecNormSq (g x) ≤ (d : ℝ) * ‖g x‖ ^ 2 :=
        vecNormSq_le_dim_mul_norm_sq (g x)
      _ ≤ (d : ℝ) * M ^ 2 :=
        mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (norm_nonneg _) hM).2 (hgbound x)) (Nat.cast_nonneg d)
  have hL2raw : eVolumeAverage U
      (fun x => ENNReal.ofReal (vecNormSq (g x))) ≤
      (ENNReal.ofReal ((d : ℝ) * M ^ 2) * volume A) / volume U :=
    eVolumeAverage_vecNormSq_le_supported_bound
      (measurableSet_openCubeSet Q) hAmeas hAU hdimM hzero
  have hKvol0 : 0 ≤ Kvol := by
    dsimp only [Kvol]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (cubeVolume_nonneg Q)
  have hL2 : eVolumeAverage U
      (fun x => ENNReal.ofReal (vecNormSq (g x))) ≤
      ((ENNReal.ofReal ((d : ℝ) * M ^ 2) * ENNReal.ofReal Kvol) /
        volume U) * ENNReal.ofReal t := by
    apply hL2raw.trans
    calc
      (ENNReal.ofReal ((d : ℝ) * M ^ 2) * volume A) / volume U ≤
          (ENNReal.ofReal ((d : ℝ) * M ^ 2) *
            ENNReal.ofReal (Kvol * t)) / volume U :=
        by
          simpa only [mul_comm] using
            ENNReal.div_le_div_right
              (mul_le_mul_left hAvolume
                (ENNReal.ofReal ((d : ℝ) * M ^ 2))) (volume U)
      _ = ((ENNReal.ofReal ((d : ℝ) * M ^ 2) * ENNReal.ofReal Kvol) /
          volume U) * ENNReal.ofReal t := by
        rw [ENNReal.ofReal_mul hKvol0]
        simp only [div_eq_mul_inv]
        ring
  have hfracraw := fracSeminormSq_le_supported_bounded_lipschitz
    Q hs hstheta hthetaHalf hM hL g hgsmooth.continuous
      (fun x _ => hgbound x) hglip hAmeas hAU hzero hC
  let Kt : ℝ := (((2 * Real.sqrt d * M) ^ (1 - theta) *
    (Real.sqrt d * L) ^ theta) ^ 2)
  let Rpow : ℝ≥0∞ := ENNReal.ofReal
    ((2 * cubeRadius Q) ^
      ((2 * theta - (d : ℝ) - 2 * s) + (d : ℝ)))
  have hfracvolume : fracSeminormSq U s g ≤
      (2 * ((ENNReal.ofReal Kt * C * Rpow) * ENNReal.ofReal (Kvol * t))) /
        volume U := by
    apply hfracraw.trans
    apply ENNReal.div_le_div_right
    have hmul := mul_le_mul_left hAvolume
      (ENNReal.ofReal Kt * C * Rpow)
    have hmul2 := mul_le_mul_left hmul 2
    simpa only [U, g, A, Kt, Rpow, L, mul_comm] using hmul2
  have hb : 0 ≤ Real.sqrt d * B :=
    mul_nonneg (Real.sqrt_nonneg d) hB.le
  have hbdiv : Real.sqrt d * L = (Real.sqrt d * B) / t := by
    dsimp only [L]
    field_simp [ht.ne']
  have hKt_mul_t : Kt * t = K₀ * t ^ p := by
    simpa only [Kt, K₀, p, hbdiv] using
      (rpow_div_sq_mul_eq
        (a := 2 * Real.sqrt d * M) (b := Real.sqrt d * B)
        (theta := theta) hb ht)
  have hKt0 : 0 ≤ Kt := by dsimp only [Kt]; positivity
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hENNcoef : ENNReal.ofReal Kt * ENNReal.ofReal t =
      ENNReal.ofReal K₀ * (ENNReal.ofReal t) ^ p := by
    rw [← ENNReal.ofReal_mul hKt0, hKt_mul_t,
      ENNReal.ofReal_mul hK₀0, ← ENNReal.ofReal_rpow_of_pos ht]
  have hfrac : fracSeminormSq U s g ≤
      (2 * ((ENNReal.ofReal K₀ * ENNReal.ofReal Kvol * C * Rpow) /
        volume U)) * (ENNReal.ofReal t) ^ p := by
    apply hfracvolume.trans_eq
    rw [ENNReal.ofReal_mul hKvol0]
    simp only [div_eq_mul_inv]
    calc
      2 * (ENNReal.ofReal Kt * C * Rpow *
          (ENNReal.ofReal Kvol * ENNReal.ofReal t)) * (volume U)⁻¹ =
          2 * ((ENNReal.ofReal Kt * ENNReal.ofReal t) *
            ENNReal.ofReal Kvol * C * Rpow) * (volume U)⁻¹ := by ring
      _ = 2 * ((ENNReal.ofReal K₀ * (ENNReal.ofReal t) ^ p) *
            ENNReal.ofReal Kvol * C * Rpow) * (volume U)⁻¹ := by
        rw [hENNcoef]
      _ = 2 * (ENNReal.ofReal K₀ * ENNReal.ofReal Kvol * C * Rpow *
          (volume U)⁻¹) * (ENNReal.ofReal t) ^ p := by ring
  unfold hsNormSq
  change volume U ^ (-(2 * s) / (d : ℝ)) *
      eVolumeAverage U (fun x => ENNReal.ofReal (vecNormSq (g x))) +
      fracSeminormSq U s g ≤ _
  apply add_le_add
  · simpa only [U, Kvol, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_left hL2 (volume U ^ (-(2 * s) / (d : ℝ)))
  · simpa only [U, D, B, Kvol, K₀, p, Rpow] using hfrac


end

end CompactTestDensity
end HighContrast
end HCPolySupport

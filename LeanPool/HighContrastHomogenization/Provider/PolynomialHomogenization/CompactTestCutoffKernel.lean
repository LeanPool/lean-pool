/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CubeFractionalNormBridge

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.CompactTestCutoffKernel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Cutoff kernel estimates

This file collects interpolation and supported-field estimates used to
compactify smooth fractional Sobolev test fields.
-/

namespace HCPolySupport
namespace HighContrast
namespace CompactTestDensity

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem le_rpow_interpolation {a A B theta : ℝ}
    (ha : 0 ≤ a) (haA : a ≤ A) (haB : a ≤ B)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    a ≤ A ^ (1 - theta) * B ^ theta := by
  by_cases ha0 : a = 0
  · rw [ha0]
    exact mul_nonneg (Real.rpow_nonneg (ha.trans haA) _)
      (Real.rpow_nonneg (ha.trans haB) _)
  have hleft : a ^ (1 - theta) ≤ A ^ (1 - theta) :=
    Real.rpow_le_rpow ha haA (sub_nonneg.mpr htheta1)
  have hright : a ^ theta ≤ B ^ theta :=
    Real.rpow_le_rpow ha haB htheta0
  calc
    a = a ^ (1 - theta) * a ^ theta := by
      rw [← Real.rpow_add (lt_of_le_of_ne ha (Ne.symm ha0))]
      rw [show 1 - theta + theta = 1 by ring, Real.rpow_one]
    _ ≤ A ^ (1 - theta) * B ^ theta :=
      mul_le_mul hleft hright (Real.rpow_nonneg ha _)
        (Real.rpow_nonneg (ha.trans haA) _)

private theorem sqrt_vecNormSq_le_sqrt_dim_mul_norm_density
    {d : ℕ} (z : Vec d) :
    Real.sqrt (vecNormSq z) ≤ Real.sqrt d * ‖z‖ := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  calc
    Real.sqrt (vecNormSq z) ≤ Real.sqrt ((d : ℝ) * ‖z‖ ^ 2) :=
      Real.sqrt_le_sqrt (vecNormSq_le_dim_mul_norm_sq z)
    _ = Real.sqrt d * ‖z‖ := by
      rw [Real.sqrt_mul hd, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)]

/-- A bounded Lipschitz field satisfies the interpolated fractional-kernel bound. -/
theorem fractionalKernel_le_of_bounded_lipschitz
    {d : ℕ} [NeZero d] {s theta M L : ℝ}
    (hs : 0 ≤ s) (hstheta : s < theta) (hthetaHalf : theta < 1 / 2)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (g : Vec d → Vec d)
    {x y : Vec d} (hxM : ‖g x‖ ≤ M) (hyM : ‖g y‖ ≤ M)
    (hxyLip : ‖g x - g y‖ ≤ L * ‖x - y‖) :
    ENNReal.ofReal
        (vecNormSq (g x - g y) /
          Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ≤
      ENNReal.ofReal
          (((2 * Real.sqrt d * M) ^ (1 - theta) *
            (Real.sqrt d * L) ^ theta) ^ 2) *
        ENNReal.ofReal (‖x - y‖ ^ (2 * theta - (d : ℝ) - 2 * s)) := by
  by_cases hxy : x = y
  · subst y
    simp [vecNormSq, vecDot]
  have hdNat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd : (0 : ℝ) < d := by exact_mod_cast hdNat
  have hq : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let r : ℝ := Real.sqrt (vecNormSq (x - y))
  have hr : 0 < r := by
    dsimp only [r]
    apply Real.sqrt_pos.2
    exact lt_of_le_of_ne (vecNormSq_nonneg _)
      (Ne.symm (fun hz => (sub_ne_zero.mpr hxy) (vecNormSq_eq_zero hz)))
  let a : ℝ := Real.sqrt (vecNormSq (g x - g y))
  let A : ℝ := 2 * Real.sqrt d * M
  let B : ℝ := Real.sqrt d * L
  let e : ℝ := 2 * theta - (d : ℝ) - 2 * s
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have haA : a ≤ A := by
    calc
      a ≤ Real.sqrt d * ‖g x - g y‖ :=
        sqrt_vecNormSq_le_sqrt_dim_mul_norm_density (g x - g y)
      _ ≤ Real.sqrt d * (‖g x‖ + ‖g y‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le (g x) (g y)) (Real.sqrt_nonneg d)
      _ ≤ Real.sqrt d * (M + M) :=
        mul_le_mul_of_nonneg_left (add_le_add hxM hyM) (Real.sqrt_nonneg d)
      _ = A := by dsimp only [A]; ring
  have haB : a ≤ B * ‖x - y‖ := by
    calc
      a ≤ Real.sqrt d * ‖g x - g y‖ :=
        sqrt_vecNormSq_le_sqrt_dim_mul_norm_density (g x - g y)
      _ ≤ Real.sqrt d * (L * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hxyLip (Real.sqrt_nonneg d)
      _ = B * ‖x - y‖ := by dsimp only [B]; ring
  have htheta0 : 0 ≤ theta := hs.trans (le_of_lt hstheta)
  have htheta1 : theta ≤ 1 := (lt_trans hthetaHalf (by norm_num)).le
  have hinterp : a ≤ A ^ (1 - theta) * (B * ‖x - y‖) ^ theta :=
    le_rpow_interpolation ha haA haB htheta0 htheta1
  have hinterp' : a ≤
      (A ^ (1 - theta) * B ^ theta) * ‖x - y‖ ^ theta := by
    rw [Real.mul_rpow hB hq.le] at hinterp
    simpa only [mul_assoc] using hinterp
  have hright : 0 ≤
      (A ^ (1 - theta) * B ^ theta) * ‖x - y‖ ^ theta := by positivity
  have hsquare : a ^ 2 ≤
      ((A ^ (1 - theta) * B ^ theta) ^ 2) *
        ‖x - y‖ ^ (2 * theta) := by
    have hpowtheta : (‖x - y‖ ^ theta) ^ (2 : ℕ) =
        ‖x - y‖ ^ (2 * theta) := by
      calc
        (‖x - y‖ ^ theta) ^ (2 : ℕ) =
            (‖x - y‖ ^ theta) ^ (2 : ℝ) :=
          (Real.rpow_natCast (‖x - y‖ ^ theta) 2).symm
        _ = ‖x - y‖ ^ (theta * 2) :=
          (Real.rpow_mul hq.le theta 2).symm
        _ = ‖x - y‖ ^ (2 * theta) := by
          congr 1
          ring
    have hsq := (sq_le_sq₀ ha hright).2 hinterp'
    calc
      a ^ 2 ≤
          ((A ^ (1 - theta) * B ^ theta) * ‖x - y‖ ^ theta) ^ 2 := hsq
      _ = ((A ^ (1 - theta) * B ^ theta) ^ 2) *
          ‖x - y‖ ^ (2 * theta) := by
        rw [mul_pow, hpowtheta]
  have hnum : vecNormSq (g x - g y) = a ^ 2 := by
    dsimp only [a]
    exact (Real.sq_sqrt (vecNormSq_nonneg _)).symm
  have hdiv :
      vecNormSq (g x - g y) / r ^ ((d : ℝ) + 2 * s) ≤
        ((A ^ (1 - theta) * B ^ theta) ^ 2) * r ^ e := by
    rw [hnum]
    have hqle : ‖x - y‖ ≤ r := by
      dsimp only [r]
      exact norm_le_sqrt_vecNormSq (x - y)
    have hpow : ‖x - y‖ ^ (2 * theta) ≤ r ^ (2 * theta) :=
      Real.rpow_le_rpow hq.le hqle (mul_nonneg (by norm_num) htheta0)
    have hsquare' : a ^ 2 ≤
        ((A ^ (1 - theta) * B ^ theta) ^ 2) * r ^ (2 * theta) :=
      hsquare.trans (mul_le_mul_of_nonneg_left hpow (sq_nonneg _))
    have hden : 0 ≤ r ^ ((d : ℝ) + 2 * s) := Real.rpow_nonneg hr.le _
    calc
      a ^ 2 / r ^ ((d : ℝ) + 2 * s) ≤
          (((A ^ (1 - theta) * B ^ theta) ^ 2) * r ^ (2 * theta)) /
            r ^ ((d : ℝ) + 2 * s) :=
        div_le_div_of_nonneg_right hsquare' hden
      _ = ((A ^ (1 - theta) * B ^ theta) ^ 2) * r ^ e := by
        rw [mul_div_assoc, ← Real.rpow_sub hr]
        dsimp only [e]
        ring_nf
  have he : e < 0 := by
    dsimp only [e]
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdNat
    linarith only [hthetaHalf, hs, hdOne]
  have hrpow : r ^ e ≤ ‖x - y‖ ^ e := by
    exact Real.rpow_le_rpow_of_nonpos hq (norm_le_sqrt_vecNormSq (x - y)) he.le
  have hreal :
      vecNormSq (g x - g y) /
          Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s) ≤
        ((A ^ (1 - theta) * B ^ theta) ^ 2) * ‖x - y‖ ^ e := by
    change vecNormSq (g x - g y) / r ^ ((d : ℝ) + 2 * s) ≤ _
    exact hdiv.trans (mul_le_mul_of_nonneg_left hrpow (sq_nonneg _))
  calc
    ENNReal.ofReal
        (vecNormSq (g x - g y) /
          Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ≤
        ENNReal.ofReal
          (((A ^ (1 - theta) * B ^ theta) ^ 2) * ‖x - y‖ ^ e) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((A ^ (1 - theta) * B ^ theta) ^ 2) *
        ENNReal.ofReal (‖x - y‖ ^ e) := by
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
    _ = _ := by rfl

/-- The fractional square seminorm of a supported bounded Lipschitz field is controlled by its
support geometry. -/
theorem fracSeminormSq_le_supported_bounded_lipschitz
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s theta M L : ℝ}
    (hs : 0 ≤ s) (hstheta : s < theta) (hthetaHalf : theta < 1 / 2)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (g : Vec d → Vec d)
    (hgcont : Continuous g)
    (hgbound : ∀ x ∈ openCubeSet Q, ‖g x‖ ≤ M)
    (hglip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {A : Set (Vec d)} (hAmeas : MeasurableSet A)
    (hAU : A ⊆ openCubeSet Q)
    (hgzero : ∀ x ∈ openCubeSet Q, x ∉ A → g x = 0)
    {C : ℝ≥0∞} (hC : ∀ (x : Vec d) {r : ℝ}, 0 < r →
      (∫⁻ y in Metric.ball x r,
        ENNReal.ofReal
          (‖x - y‖ ^ (2 * theta - (d : ℝ) - 2 * s)) ∂volume) ≤
        C * ENNReal.ofReal
          (r ^ ((2 * theta - (d : ℝ) - 2 * s) + (d : ℝ)))) :
    fracSeminormSq (openCubeSet Q) s g ≤
      (2 *
          ((ENNReal.ofReal
                (((2 * Real.sqrt d * M) ^ (1 - theta) *
                  (Real.sqrt d * L) ^ theta) ^ 2) * C *
              ENNReal.ofReal
                ((2 * cubeRadius Q) ^
                  ((2 * theta - (d : ℝ) - 2 * s) + (d : ℝ)))) *
            volume A)) /
        volume (openCubeSet Q) := by
  let U : Set (Vec d) := openCubeSet Q
  let e : ℝ := 2 * theta - (d : ℝ) - 2 * s
  let K : Vec d × Vec d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal
      (vecNormSq (g z.1 - g z.2) /
        Real.sqrt (vecNormSq (z.1 - z.2)) ^ ((d : ℝ) + 2 * s))
  let D : ℝ≥0∞ := ENNReal.ofReal
    (((2 * Real.sqrt d * M) ^ (1 - theta) *
      (Real.sqrt d * L) ^ theta) ^ 2)
  let R : ℝ := 2 * cubeRadius Q
  have hUmeas : MeasurableSet U := measurableSet_openCubeSet Q
  have hdist : Continuous (fun z : Vec d × Vec d =>
      Real.sqrt (vecNormSq (z.1 - z.2))) :=
    (continuous_vecNormSq.comp (continuous_fst.sub continuous_snd)).sqrt
  have hp : 0 ≤ (d : ℝ) + 2 * s := by positivity
  have hden : Measurable (fun z : Vec d × Vec d =>
      Real.sqrt (vecNormSq (z.1 - z.2)) ^ ((d : ℝ) + 2 * s)) :=
    (hdist.rpow_const fun _ => Or.inr hp).measurable
  have hnum : Measurable (fun z : Vec d × Vec d =>
      vecNormSq (g z.1 - g z.2)) :=
    continuous_vecNormSq.measurable.comp
      ((hgcont.comp continuous_fst).sub (hgcont.comp continuous_snd)).measurable
  have hK : AEMeasurable K (volume.prod volume) := by
    exact (hnum.div hden).ennreal_ofReal.aemeasurable
  have hKsymm (x y : Vec d) : K (x, y) = K (y, x) := by
    dsimp only [K]
    rw [show g y - g x = -(g x - g y) by abel,
      show y - x = -(x - y) by abel, vecNormSq_neg, vecNormSq_neg]
  let S₁ : Set (Vec d × Vec d) := A ×ˢ U
  let S₂ : Set (Vec d × Vec d) := U ×ˢ A
  let UU : Set (Vec d × Vec d) := U ×ˢ U
  have hS₁meas : MeasurableSet S₁ := hAmeas.prod hUmeas
  have hS₂meas : MeasurableSet S₂ := hUmeas.prod hAmeas
  have hUUmeas : MeasurableSet UU := hUmeas.prod hUmeas
  have hS₁UU : S₁ ⊆ UU := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hAU hx, hy⟩
  have hS₂UU : S₂ ⊆ UU := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hx, hAU hy⟩
  have hpoint (z : Vec d × Vec d) (hz : z ∈ UU) :
      K z ≤ S₁.indicator K z + S₂.indicator K z := by
    rcases hz with ⟨hxU, hyU⟩
    by_cases hxA : z.1 ∈ A
    · have hzS₁ : z ∈ S₁ := ⟨hxA, hyU⟩
      rw [Set.indicator_of_mem hzS₁]
      exact le_add_right le_rfl
    · by_cases hyA : z.2 ∈ A
      · have hzS₂ : z ∈ S₂ := ⟨hxU, hyA⟩
        rw [Set.indicator_of_mem hzS₂]
        exact le_add_left le_rfl
      · rw [Set.indicator_of_notMem (fun hzS => hxA hzS.1),
          Set.indicator_of_notMem (fun hzS => hyA hzS.2)]
        dsimp only [K]
        rw [hgzero z.1 hxU hxA, hgzero z.2 hyU hyA, sub_self]
        simp [vecNormSq, vecDot]
  have hKUU : AEMeasurable K ((volume.prod volume).restrict UU) :=
    hK.mono_measure Measure.restrict_le_self
  have hK₁ : AEMeasurable K ((volume.prod volume).restrict S₁) :=
    hK.mono_measure Measure.restrict_le_self
  have hK₂ : AEMeasurable K ((volume.prod volume).restrict S₂) :=
    hK.mono_measure Measure.restrict_le_self
  have hind₁ : AEMeasurable (S₁.indicator K)
      ((volume.prod volume).restrict UU) :=
    (hK.mono_measure Measure.restrict_le_self).indicator hS₁meas
  have hrectsymm :
      (∫⁻ z in S₂, K z ∂(volume.prod volume)) =
        ∫⁻ z in S₁, K z ∂(volume.prod volume) := by
    rw [setLIntegral_prod_symm K hK₂, setLIntegral_prod K hK₁]
    apply setLIntegral_congr_fun hAmeas
    intro y hy
    apply setLIntegral_congr_fun hUmeas
    intro x hx
    exact hKsymm x y
  have hdouble :
      (∫⁻ z in UU, K z ∂(volume.prod volume)) ≤
        2 * (∫⁻ z in S₁, K z ∂(volume.prod volume)) := by
    calc
      (∫⁻ z in UU, K z ∂(volume.prod volume)) ≤
          ∫⁻ z in UU, S₁.indicator K z + S₂.indicator K z
            ∂(volume.prod volume) :=
        setLIntegral_mono' hUUmeas hpoint
      _ = (∫⁻ z in UU, S₁.indicator K z ∂(volume.prod volume)) +
          ∫⁻ z in UU, S₂.indicator K z ∂(volume.prod volume) := by
        exact lintegral_add_left' hind₁ _
      _ = (∫⁻ z in S₁, K z ∂(volume.prod volume)) +
          ∫⁻ z in S₂, K z ∂(volume.prod volume) := by
        rw [setLIntegral_indicator hS₁meas,
          setLIntegral_indicator hS₂meas,
          Set.inter_eq_left.mpr hS₁UU, Set.inter_eq_left.mpr hS₂UU]
      _ = 2 * (∫⁻ z in S₁, K z ∂(volume.prod volume)) := by
        rw [hrectsymm]
        ring
  have hR : 0 < R := by
    dsimp only [R]
    exact mul_pos (by norm_num) (cubeRadius_pos Q)
  have hUball (x : Vec d) (hx : x ∈ U) : U ⊆ Metric.ball x R := by
    intro y hy
    change x ∈ openCubeSet Q at hx
    change y ∈ openCubeSet Q at hy
    rw [← ball_cubeCenter_eq_openCubeSet Q] at hx hy
    rw [Metric.mem_ball]
    calc
      dist y x ≤ dist y (cubeCenter Q) + dist (cubeCenter Q) x := dist_triangle _ _ _
      _ < cubeRadius Q + cubeRadius Q := by
        exact add_lt_add hy (by simpa only [dist_comm] using! hx)
      _ = R := by dsimp only [R]; ring
  have hDtop : D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hboundinner (x : Vec d) (hx : x ∈ A) :
      (∫⁻ y in U, K (x, y) ∂volume) ≤
        D * C * ENNReal.ofReal (R ^ (e + (d : ℝ))) := by
    have hxU : x ∈ U := hAU hx
    calc
      (∫⁻ y in U, K (x, y) ∂volume) ≤
          ∫⁻ y in U,
            D * ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := by
        apply setLIntegral_mono' hUmeas
        intro y hy
        simpa only [K, D, e] using
          fractionalKernel_le_of_bounded_lipschitz hs hstheta hthetaHalf
            hM hL g (hgbound x hxU) (hgbound y hy) (hglip x y)
      _ = D * (∫⁻ y in U,
          ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) := by
        exact lintegral_const_mul' D _ hDtop
      _ ≤ D * (∫⁻ y in Metric.ball x R,
          ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) := by
        simpa only [mul_comm] using
          mul_le_mul_left (lintegral_mono_set (hUball x hxU)) D
      _ ≤ D * (C * ENNReal.ofReal (R ^ (e + (d : ℝ)))) := by
        simpa only [e, mul_comm] using mul_le_mul_left (hC x hR) D
      _ = D * C * ENNReal.ofReal (R ^ (e + (d : ℝ))) := by
        rw [mul_assoc]
  have hrect :
      (∫⁻ z in S₁, K z ∂(volume.prod volume)) ≤
        (D * C * ENNReal.ofReal (R ^ (e + (d : ℝ)))) * volume A := by
    rw [setLIntegral_prod K hK₁]
    calc
      (∫⁻ x in A, ∫⁻ y in U, K (x, y) ∂volume ∂volume) ≤
          ∫⁻ _x in A,
            D * C * ENNReal.ofReal (R ^ (e + (d : ℝ))) ∂volume :=
        setLIntegral_mono' hAmeas hboundinner
      _ = (D * C * ENNReal.ofReal (R ^ (e + (d : ℝ)))) * volume A :=
        setLIntegral_const A _
  unfold fracSeminormSq eVolumeAverage
  change (∫⁻ x in U, ∫⁻ y in U, K (x, y) ∂volume ∂volume) /
      volume U ≤ _
  rw [← setLIntegral_prod K hKUU]
  apply ENNReal.div_le_div_right
  refine hdouble.trans ?_
  simpa only [D, R, e, mul_comm] using mul_le_mul_left hrect 2

end

end CompactTestDensity
end HighContrast
end HCPolySupport
